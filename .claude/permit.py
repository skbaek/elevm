#!/usr/bin/env python3
"""Claude Code adapter for the shared command policy.

All control logic lives in the canonical policy at
`~/blanc/.claude/permit.py` — the single source of truth. This file holds NO
policy of its own; it only translates Claude Code's PreToolUse hook I/O to and
from that policy's `decide(command, cwd) -> (decision, reason)` interface.

Protocol (same as the canonical policy's own main()):
    stdin : JSON  {"tool_name":"Bash","tool_input":{"command":"..."}, "cwd":...}
    stdout: JSON  {"hookSpecificOutput":{"hookEventName":"PreToolUse",
                   "permissionDecision":"allow"|"deny"|"ask",
                   "permissionDecisionReason":"..."}}

    allow -> runs with NO prompt (bypasses Claude Code's built-in allow/deny)
    ask   -> falls through to the normal permission prompt  (the safe default)
    deny  -> blocked outright, reason shown to Claude

It never fails open: any load/parse error also results in "ask".
"""

from __future__ import annotations

import importlib.util
import json
import sys

# The one canonical policy. Both repos' adapters point here on purpose.
CANONICAL_POLICY = "/Users/bsk/blanc/.claude/permit.py"


def _load_policy():
    spec = importlib.util.spec_from_file_location("blanc_claude_permit", CANONICAL_POLICY)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load policy from {CANONICAL_POLICY}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _emit(decision: str, reason: str) -> None:
    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "permissionDecision": decision,
            "permissionDecisionReason": "permit.py: " + reason,
        }
    }))


def main() -> None:
    try:
        data = json.load(sys.stdin)
    except Exception:
        return _emit("ask", "unreadable hook input")

    if data.get("tool_name") != "Bash":
        return _emit("ask", "non-Bash tool")

    command = (data.get("tool_input") or {}).get("command", "")
    cwd = data.get("cwd") or ""

    try:
        policy = _load_policy()
    except Exception:
        return _emit("ask", "canonical policy unavailable: " + CANONICAL_POLICY)

    try:
        decision, reason = policy.decide(command, cwd)
    except policy.Unsafe as exc:
        decision, reason = exc.decision, exc.reason
    except Exception as exc:
        decision, reason = "ask", "permit.py error: " + type(exc).__name__
    _emit(decision, reason)


if __name__ == "__main__":
    main()
