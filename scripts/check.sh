#!/usr/bin/env bash
# Fixture-test harness for elevm (REFACTOR.md Phase 0, step 0.1).
#
# Usage: scripts/check.sh (--depth | --smoke | --full | --patch | --rlp4 | --dir <path>) [--rebase] [--no-build]
#
#   --depth       run the fuel/call-depth stress set (scripts/depth-tests.txt)
#   --smoke       run the smoke set (scripts/smoke-tests.txt)
#   --full        run every .json fixture under the fixture root
#   --patch       run the patch-plan target set (scripts/patch-tests.txt): the
#                 ten historical FAIL files plus CALLBlake2f_MaxRounds.json
#   --rlp4        run the four invalid-RLP/header files (scripts/rlp4-tests.txt),
#                 a subset of --patch
#   --dir <path>  run every .json fixture under <path> (must be inside the
#                 fixture root); ad hoc — if no baseline-dir.txt exists, the
#                 gate passes iff every file PASSes
#   --rebase      accept the current results as the new committed baseline
#                 (rejected for --patch/--rlp4: their desired result is fixed)
#   --no-build    skip `lake build elevm`
#
# --patch and --rlp4 are target gates, not baseline-comparison tiers: each
# succeeds if and only if every listed file is PASS. They have no baseline and
# never rebase. Their reports additionally record per-file elapsed wall time.
#
# Environment:
#   ELEVM_FIXTURES  fixture root (default:
#                   ~/execution-specs/tests/fixtures/ethereum_tests/BlockchainTests)
#   ELEVM_TIMEOUT   per-file timeout in seconds (default: 300)
#
# A failing test makes elevm throw and abort the whole invocation, so each
# fixture file runs in its own process, under a perl-alarm timeout (macOS has
# no coreutils timeout). Per-file classification PASS / FAIL / TIMEOUT is
# written to scripts/report-<tier>.txt (gitignored). The gate passes iff every
# file's classification equals the committed scripts/baseline-<tier>.txt —
# NOT iff every file passes. A PASS/FAIL change is a functional regression.
# A change involving TIMEOUT is environment/performance-sensitive, so it is
# reported separately as REVIEW rather than asserted to be a regression.
#
# CLI contract: exit 0 if and only if the gate passes; the last line of
# output is a single unambiguous verdict line.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
FIXTURES="${ELEVM_FIXTURES:-$HOME/execution-specs/tests/fixtures/ethereum_tests/BlockchainTests}"
TIMEOUT="${ELEVM_TIMEOUT:-100}"
BIN="$ROOT/.lake/build/bin/elevm"

usage() {
  echo "usage: scripts/check.sh (--depth | --smoke | --full | --patch | --rlp4 | --dir <path>) [--rebase] [--no-build]" >&2
  exit 2
}

TIER=""
DIR_PATH=""
REBASE=0
BUILD=1
while [ $# -gt 0 ]; do
  case "$1" in
    --depth|--smoke|--full|--patch|--rlp4) TIER="${1#--}" ;;
    --dir)
      TIER="dir"
      shift
      [ $# -gt 0 ] || usage
      DIR_PATH="$1"
      ;;
    --rebase) REBASE=1 ;;
    --no-build) BUILD=0 ;;
    *) echo "unknown argument: $1" >&2; usage ;;
  esac
  shift
done
[ -n "$TIER" ] || usage

# Target-gate tiers succeed iff every listed file is PASS; they have no
# baseline and never rebase.
case "$TIER" in
  patch|rlp4) IS_TARGET=1 ;;
  *)          IS_TARGET=0 ;;
esac
if [ "$IS_TARGET" -eq 1 ] && [ "$REBASE" -eq 1 ]; then
  echo "usage error: --rebase is not supported for the $TIER target gate; its desired result is fixed at all-PASS" >&2
  exit 2
fi

if [ ! -d "$FIXTURES" ]; then
  echo "REGRESSION — $TIER: fixture root not found: $FIXTURES"
  exit 1
fi

# Assemble the file list (paths relative to the fixture root, sorted).
case "$TIER" in
  depth|smoke|patch|rlp4)
    LIST_FILE="$SCRIPT_DIR/$TIER-tests.txt"
    if [ ! -f "$LIST_FILE" ]; then
      echo "REGRESSION — $TIER: file list not found: $LIST_FILE"
      exit 1
    fi
    FILES="$(grep -v '^[[:space:]]*$' "$LIST_FILE")"
    ;;
  full)
    # .meta/ holds fixture-index metadata, not tests.
    FILES="$(find "$FIXTURES" -name '*.json' | sed "s|^$FIXTURES/||" \
      | grep -v -e '^\.meta/' -e '/\.meta/' | sort)"
    ;;
  dir)
    if [ ! -d "$DIR_PATH" ]; then
      echo "REGRESSION — dir: not a directory: $DIR_PATH"
      exit 1
    fi
    ABS="$(cd "$DIR_PATH" && pwd)"
    case "$ABS" in
      "$FIXTURES"|"$FIXTURES"/*) : ;;
      *)
        echo "REGRESSION — dir: $ABS is not under the fixture root $FIXTURES"
        exit 1
        ;;
    esac
    FILES="$(find "$ABS" -name '*.json' | sed "s|^$FIXTURES/||" | sort)"
    ;;
esac

TOTAL="$(printf '%s\n' "$FILES" | grep -c .)"
if [ "$TOTAL" -eq 0 ]; then
  echo "REGRESSION — $TIER: no fixture files selected"
  exit 1
fi

if [ "$BUILD" -eq 1 ]; then
  if ! (cd "$ROOT" && lake build elevm); then
    echo "REGRESSION — $TIER: lake build elevm failed"
    exit 1
  fi
fi
if [ ! -x "$BIN" ]; then
  echo "REGRESSION — $TIER: elevm binary not found: $BIN"
  exit 1
fi

REPORT="$SCRIPT_DIR/report-$TIER.txt"
BASELINE="$SCRIPT_DIR/baseline-$TIER.txt"
: > "$REPORT"

NPASS=0
NFAIL=0
NTIMEOUT=0
I=0
while IFS= read -r REL; do
  [ -n "$REL" ] || continue
  I=$((I + 1))
  START="$(perl -MTime::HiRes=time -e 'printf "%.3f", time')"
  # alarm(2) persists across exec: when the timeout fires, SIGALRM kills the
  # exec'd elevm (exit status 128 + 14 = 142).
  perl -e 'alarm shift @ARGV; exec @ARGV' "$TIMEOUT" "$BIN" "$FIXTURES/$REL" \
    > /dev/null 2>&1
  RC=$?
  ELAPSED="$(perl -e 'printf "%.2f", $ARGV[1] - $ARGV[0]' \
    "$START" "$(perl -MTime::HiRes=time -e 'printf "%.3f", time')")"
  if [ "$RC" -eq 0 ]; then
    CLS=PASS; NPASS=$((NPASS + 1))
  elif [ "$RC" -eq 142 ]; then
    CLS=TIMEOUT; NTIMEOUT=$((NTIMEOUT + 1))
  else
    CLS=FAIL; NFAIL=$((NFAIL + 1))
  fi
  if [ "$IS_TARGET" -eq 1 ]; then
    printf '%s\t%ss\t%s\n' "$CLS" "$ELAPSED" "$REL" >> "$REPORT"
    printf '[%d/%d] %s %ss %s\n' "$I" "$TOTAL" "$CLS" "$ELAPSED" "$REL" >&2
  else
    printf '%s\t%s\n' "$CLS" "$REL" >> "$REPORT"
    printf '[%d/%d] %s %s\n' "$I" "$TOTAL" "$CLS" "$REL" >&2
  fi
done <<EOF
$FILES
EOF

SUMMARY="$NPASS PASS, $NFAIL FAIL, $NTIMEOUT TIMEOUT"

# Target gates: fixed all-PASS end condition, no baseline, no rebase.
if [ "$IS_TARGET" -eq 1 ]; then
  if [ "$NFAIL" -eq 0 ] && [ "$NTIMEOUT" -eq 0 ]; then
    echo "OK — $TIER: $NPASS/$TOTAL PASS ($SUMMARY)"
    exit 0
  fi
  echo "RED — $TIER: $NPASS/$TOTAL PASS, target not met ($SUMMARY); see $REPORT"
  exit 1
fi

if [ "$REBASE" -eq 1 ]; then
  cp "$REPORT" "$BASELINE"
  echo "OK — $TIER: baseline rebased with $TOTAL files ($SUMMARY)"
  exit 0
fi

if [ ! -f "$BASELINE" ]; then
  if [ "$TIER" = "dir" ]; then
    if [ "$NFAIL" -eq 0 ] && [ "$NTIMEOUT" -eq 0 ]; then
      echo "OK — dir: $TOTAL files, all PASS, no baseline ($SUMMARY)"
      exit 0
    fi
    echo "REGRESSION — dir: $NFAIL FAIL / $NTIMEOUT TIMEOUT with no baseline; see $REPORT"
    exit 1
  fi
  echo "REGRESSION — $TIER: no baseline at $BASELINE (run once with --rebase)"
  exit 1
fi

CHANGES="$(awk -F'\t' '
  NR == FNR { base[$2] = $1; next }
  {
    old = ($2 in base) ? base[$2] : "MISSING"
    if (old != $1) {
      kind = (old == "TIMEOUT" || $1 == "TIMEOUT") ? "TIMEOUT" : "FUNCTIONAL"
      print kind "\t" old "\t" $1 "\t" $2
    }
    delete base[$2]
  }
  END {
    for (file in base) {
      kind = (base[file] == "TIMEOUT") ? "TIMEOUT" : "FUNCTIONAL"
      print kind "\t" base[file] "\tMISSING\t" file
    }
  }
' "$BASELINE" "$REPORT")"

if [ -z "$CHANGES" ]; then
  NCHANGED=0
  NFUNCTIONAL=0
  NTIMEOUT_CHANGED=0
else
  NCHANGED="$(printf '%s\n' "$CHANGES" | grep -c .)"
  NFUNCTIONAL="$(printf '%s\n' "$CHANGES" | grep -c '^FUNCTIONAL')"
  NTIMEOUT_CHANGED="$(printf '%s\n' "$CHANGES" | grep -c '^TIMEOUT')"

  printf '%s\n' "$CHANGES" | while IFS="$(printf '\t')" read -r KIND OLD NEW REL; do
    if [ "$KIND" = "TIMEOUT" ]; then
      printf 'REVIEW — %s: %s -> %s (timeout-sensitive; may reflect machine load or performance)\n' \
        "$REL" "$OLD" "$NEW"
    else
      printf 'CHANGE — %s: %s -> %s\n' "$REL" "$OLD" "$NEW"
    fi
  done
fi

if [ "$NCHANGED" -eq 0 ]; then
  echo "OK — $TIER: $TOTAL files match baseline ($SUMMARY)"
  exit 0
fi
if [ "$NFUNCTIONAL" -gt 0 ]; then
  if [ "$NTIMEOUT_CHANGED" -gt 0 ]; then
    echo "REGRESSION — $NFUNCTIONAL functional classification changes; additionally $NTIMEOUT_CHANGED timeout-sensitive changes need review; see $REPORT"
  else
    echo "REGRESSION — $NFUNCTIONAL functional classification changes vs baseline; see $REPORT"
  fi
  exit 1
fi
echo "REVIEW — $NTIMEOUT_CHANGED timeout-sensitive classification changes; not definitive regressions, inspect machine load/performance and $REPORT"
exit 1
