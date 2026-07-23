#!/usr/bin/env python3
"""Read-only diagnostic for ELEVM's external-source environment (Step 1).

Checks the manifest in scripts/sources.json against the local filesystem and
Git state: execution-specs, the nested ethereum/tests + LegacyTests checkout,
the EEST release archive/extraction, and the Python oracle venv when present.

This script never edits, fetches, clones, initializes, activates, or repairs
anything. It only reads. Bootstrap/repair tooling is later-step work.

Python-standard-library only.

Exit codes:
  0  every checked component is present and matches the manifest
  1  at least one component is missing, dirty, or does not match the manifest
  2  usage error or a malformed manifest
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Optional

DEFAULT_MANIFEST = Path(__file__).resolve().parent / "sources.json"

STATUS_OK = "ok"
STATUS_MISSING = "missing"
STATUS_FAIL = "fail"


@dataclass
class Check:
    name: str
    status: str
    detail: str


def load_manifest(path: Path) -> dict:
    try:
        text = path.read_text()
    except OSError as error:
        raise ManifestError(f"cannot read manifest {path}: {error}") from error
    try:
        data = json.loads(text)
    except json.JSONDecodeError as error:
        raise ManifestError(f"manifest {path} is not valid JSON: {error}") from error

    required_top = (
        "execution_specs",
        "ethereum_tests",
        "legacy_tests_submodule",
        "eest",
        "python_oracle",
    )
    for key in required_top:
        if key not in data:
            raise ManifestError(f"manifest {path} is missing required key {key!r}")

    required_fields = {
        "execution_specs": ("repo_url", "commit"),
        "ethereum_tests": ("repo_url", "commit", "relative_path_from_execution_specs"),
        "legacy_tests_submodule": ("commit", "relative_path_from_ethereum_tests"),
        "eest": (
            "release_tag",
            "archive_url",
            "archive_filename",
            "archive_sha256",
            "fixtures_subpath",
            "expected_top_level_dirs",
        ),
        "python_oracle": ("intended_version", "known_packages"),
    }
    for section, fields in required_fields.items():
        for field in fields:
            if field not in data[section]:
                raise ManifestError(
                    f"manifest {path} section {section!r} is missing field {field!r}"
                )
    return data


class ManifestError(Exception):
    pass


def run_git(args: list[str], cwd: Path) -> Optional[str]:
    """Run a read-only git command; None on any failure (never raises)."""
    try:
        result = subprocess.run(
            ["git", *args],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError:
        return None
    if result.returncode != 0:
        return None
    return result.stdout.strip()


def check_git_checkout(
    label: str, path: Path, expected_url: Optional[str], expected_commit: str
) -> list[Check]:
    checks: list[Check] = []
    if not path.is_dir():
        checks.append(Check(f"{label}: directory", STATUS_MISSING, f"not found: {path}"))
        return checks
    if not (path / ".git").exists():
        checks.append(
            Check(f"{label}: git repo", STATUS_FAIL, f"{path} is not a Git checkout")
        )
        return checks

    head = run_git(["rev-parse", "HEAD"], path)
    if head is None:
        checks.append(Check(f"{label}: HEAD", STATUS_FAIL, f"could not read HEAD in {path}"))
    elif head != expected_commit:
        checks.append(
            Check(
                f"{label}: HEAD",
                STATUS_FAIL,
                f"expected {expected_commit}, got {head}",
            )
        )
    else:
        checks.append(Check(f"{label}: HEAD", STATUS_OK, head))

    if expected_url is not None:
        origin = run_git(["remote", "get-url", "origin"], path)
        if origin is None:
            checks.append(
                Check(f"{label}: origin", STATUS_FAIL, "no 'origin' remote configured")
            )
        elif _normalize_git_url(origin) != _normalize_git_url(expected_url):
            checks.append(
                Check(
                    f"{label}: origin",
                    STATUS_FAIL,
                    f"expected {expected_url}, got {origin}",
                )
            )
        else:
            checks.append(Check(f"{label}: origin", STATUS_OK, origin))

    status = run_git(["status", "--porcelain"], path)
    if status is None:
        checks.append(Check(f"{label}: tracked dirtiness", STATUS_FAIL, "git status failed"))
    else:
        # "??" lines are untracked files (e.g. an unrelated stray
        # .python-version); they are not modifications to tracked source and
        # must not be reported as dirty. Every other porcelain line reflects a
        # change to a tracked file (modified/added/deleted/renamed/staged).
        dirty_lines = [
            line for line in status.splitlines() if line and not line.startswith("??")
        ]
        untracked_count = sum(1 for line in status.splitlines() if line.startswith("??"))
        if dirty_lines:
            checks.append(
                Check(
                    f"{label}: tracked dirtiness",
                    STATUS_FAIL,
                    f"{len(dirty_lines)} tracked change(s): "
                    + "; ".join(dirty_lines[:5]),
                )
            )
        else:
            detail = "clean"
            if untracked_count:
                detail += f" ({untracked_count} untracked file(s) ignored by this check)"
            checks.append(Check(f"{label}: tracked dirtiness", STATUS_OK, detail))

    return checks


def _normalize_git_url(url: str) -> str:
    url = url.strip()
    if url.endswith("/"):
        url = url[:-1]
    if url.endswith(".git"):
        url = url[: -len(".git")]
    return url.lower()


def check_execution_specs(manifest: dict, root: Path) -> list[Check]:
    spec = manifest["execution_specs"]
    return check_git_checkout("execution-specs", root, spec["repo_url"], spec["commit"])


def check_ethereum_tests(manifest: dict, execution_specs_root: Path) -> list[Check]:
    spec = manifest["ethereum_tests"]
    path = execution_specs_root / spec["relative_path_from_execution_specs"]
    checks = check_git_checkout("ethereum/tests", path, spec["repo_url"], spec["commit"])

    legacy = manifest["legacy_tests_submodule"]
    legacy_path = path / legacy["relative_path_from_ethereum_tests"]
    # The submodule has no independent 'origin' expectation in the manifest
    # (only its pinned commit); its remote is whatever ethereum/tests'
    # .gitmodules declares.
    checks.extend(
        check_git_checkout(
            f"ethereum/tests/{legacy['relative_path_from_ethereum_tests']}",
            legacy_path,
            None,
            legacy["commit"],
        )
    )
    return checks


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def check_eest(manifest: dict, eest_root: Path) -> list[Check]:
    spec = manifest["eest"]
    checks: list[Check] = []

    if not eest_root.is_dir():
        checks.append(
            Check("eest: root directory", STATUS_MISSING, f"not found: {eest_root}")
        )
        return checks
    checks.append(Check("eest: root directory", STATUS_OK, str(eest_root)))

    archive_path = eest_root / spec["archive_filename"]
    if not archive_path.is_file():
        checks.append(
            Check("eest: archive", STATUS_MISSING, f"not found: {archive_path}")
        )
    else:
        actual_hash = sha256_file(archive_path)
        if actual_hash != spec["archive_sha256"]:
            checks.append(
                Check(
                    "eest: archive sha256",
                    STATUS_FAIL,
                    f"expected {spec['archive_sha256']}, got {actual_hash}",
                )
            )
        else:
            checks.append(Check("eest: archive sha256", STATUS_OK, actual_hash))

    fixtures_root = eest_root / spec["fixtures_subpath"]
    if not fixtures_root.is_dir():
        checks.append(
            Check(
                "eest: extracted fixtures",
                STATUS_MISSING,
                f"not found: {fixtures_root}",
            )
        )
    else:
        missing_dirs = [
            d for d in spec["expected_top_level_dirs"] if not (fixtures_root / d).is_dir()
        ]
        if missing_dirs:
            checks.append(
                Check(
                    "eest: extracted fixtures",
                    STATUS_FAIL,
                    f"missing expected subdirectories: {', '.join(missing_dirs)}",
                )
            )
        else:
            checks.append(
                Check(
                    "eest: extracted fixtures",
                    STATUS_OK,
                    f"{len(spec['expected_top_level_dirs'])} expected top-level dirs present",
                )
            )
    return checks


def check_python_oracle(manifest: dict, venv_path: Path) -> list[Check]:
    spec = manifest["python_oracle"]
    checks: list[Check] = []

    python_bin = venv_path / "bin" / "python"
    if not python_bin.is_file():
        checks.append(
            Check("python-oracle: venv", STATUS_MISSING, f"not found: {python_bin}")
        )
        return checks
    checks.append(Check("python-oracle: venv", STATUS_OK, str(python_bin)))

    probe = (
        "import json, sys\n"
        "from importlib.metadata import PackageNotFoundError, version\n"
        "info = {'python_version': '%d.%d.%d' % sys.version_info[:3]}\n"
        "packages = {}\n"
        f"for name in {list(spec['known_packages'].keys())!r}:\n"
        "    try:\n"
        "        packages[name] = version(name)\n"
        "    except PackageNotFoundError:\n"
        "        packages[name] = None\n"
        "info['packages'] = packages\n"
        "print(json.dumps(info))\n"
    )
    try:
        result = subprocess.run(
            [str(python_bin), "-c", probe],
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError as error:
        checks.append(
            Check("python-oracle: interpreter", STATUS_FAIL, f"could not run venv python: {error}")
        )
        return checks
    if result.returncode != 0:
        checks.append(
            Check(
                "python-oracle: interpreter",
                STATUS_FAIL,
                f"venv python exited {result.returncode}: {result.stderr.strip()}",
            )
        )
        return checks
    try:
        info = json.loads(result.stdout.strip())
    except json.JSONDecodeError:
        checks.append(
            Check("python-oracle: interpreter", STATUS_FAIL, "could not parse venv probe output")
        )
        return checks

    actual_version = info["python_version"]
    if actual_version != spec["intended_version"]:
        checks.append(
            Check(
                "python-oracle: version",
                STATUS_FAIL,
                f"expected {spec['intended_version']}, got {actual_version}",
            )
        )
    else:
        checks.append(Check("python-oracle: version", STATUS_OK, actual_version))

    for name, expected_version in spec["known_packages"].items():
        actual = info["packages"].get(name)
        if actual is None:
            checks.append(Check(f"python-oracle: {name}", STATUS_MISSING, "not installed"))
        elif actual != expected_version:
            checks.append(
                Check(
                    f"python-oracle: {name}",
                    STATUS_FAIL,
                    f"expected {expected_version}, got {actual}",
                )
            )
        else:
            checks.append(Check(f"python-oracle: {name}", STATUS_OK, actual))

    return checks


def check_required_commands() -> list[Check]:
    checks = []
    git_path = shutil.which("git")
    if git_path is None:
        checks.append(Check("command: git", STATUS_MISSING, "git not found on PATH"))
    else:
        checks.append(Check("command: git", STATUS_OK, git_path))
    return checks


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        "--manifest",
        type=Path,
        default=DEFAULT_MANIFEST,
        help=f"path to the source manifest (default: {DEFAULT_MANIFEST})",
    )
    parser.add_argument(
        "--execution-specs",
        type=Path,
        default=None,
        help="execution-specs checkout root (default: $EELS_ROOT or ~/execution-specs)",
    )
    parser.add_argument(
        "--eest-root",
        type=Path,
        default=None,
        help="EEST install root containing the archive and extracted fixtures/ "
        "(default: $EEST_ROOT or ~/eest-fixtures; distinct from check.sh's "
        "ELEVM_FIXTURES, which points directly at a tier's leaf fixture dir)",
    )
    parser.add_argument(
        "--venv",
        type=Path,
        default=None,
        help="Python oracle venv path (default: <execution-specs root>/venv)",
    )
    parser.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    return parser


def main(argv: list[str]) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)

    try:
        manifest = load_manifest(args.manifest)
    except ManifestError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    if args.execution_specs is not None:
        execution_specs_root = args.execution_specs.expanduser()
    elif os.environ.get("EELS_ROOT"):
        execution_specs_root = Path(os.environ["EELS_ROOT"]).expanduser()
    else:
        execution_specs_root = Path.home() / manifest["execution_specs"]["default_subpath_from_home"]

    if args.eest_root is not None:
        eest_root = args.eest_root.expanduser()
    elif os.environ.get("EEST_ROOT"):
        eest_root = Path(os.environ["EEST_ROOT"]).expanduser()
    else:
        eest_root = Path.home() / manifest["eest"]["default_subpath_from_home"]

    venv_path = args.venv or (execution_specs_root / "venv")

    checks: list[Check] = []
    checks.extend(check_required_commands())
    checks.extend(check_execution_specs(manifest, execution_specs_root))
    checks.extend(check_ethereum_tests(manifest, execution_specs_root))
    checks.extend(check_eest(manifest, eest_root))
    checks.extend(check_python_oracle(manifest, venv_path))

    ok = all(check.status == STATUS_OK for check in checks)

    if args.json:
        payload = {
            "ok": ok,
            "checks": [asdict(check) for check in checks],
        }
        print(json.dumps(payload, indent=2))
    else:
        for check in checks:
            marker = {"ok": "OK", "missing": "MISSING", "fail": "FAIL"}[check.status]
            print(f"{marker:8} {check.name}: {check.detail}")
        print()
        print("OK — all checks passed" if ok else "NOT OK — see failures/missing components above")

    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
