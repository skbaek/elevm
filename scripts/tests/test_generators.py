#!/usr/bin/env python3
"""Network-free tests for shared generator configuration and U256 output."""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

SCRIPTS_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS_DIR))


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


common = load_module("generator_common", SCRIPTS_DIR / "generator_common.py")


def git(path: Path, *args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(path), *args],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def make_checkout(path: Path) -> str:
    subprocess.run(["git", "init", "-q", str(path)], check=True)
    git(path, "config", "user.email", "test@example.com")
    git(path, "config", "user.name", "Test")
    git(path, "config", "commit.gpgsign", "false")
    for relative in (
        "src/ethereum/crypto/kzg.py",
        "src/ethereum/prague/vm/instructions/arithmetic.py",
        "src/ethereum/prague/vm/instructions/comparison.py",
        "src/ethereum/prague/vm/instructions/bitwise.py",
        "src/ethereum/prague/vm/instructions/keccak.py",
        "src/ethereum/prague/vm/gas.py",
    ):
        target = path / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text("# synthetic pinned source\n")
    git(path, "add", ".")
    git(path, "commit", "-q", "-m", "pinned")
    return git(path, "rev-parse", "HEAD")


def make_manifest(path: Path, commit: str) -> None:
    data = {
        "schema_version": 1,
        "execution_specs": {
            "repo_url": "https://example.invalid/execution-specs.git",
            "commit": commit,
            "default_env_var": "EELS_ROOT",
            "default_subpath_from_home": "execution-specs",
        },
        "ethereum_tests": {
            "repo_url": "https://example.invalid/tests.git",
            "commit": "1" * 40,
            "relative_path_from_execution_specs": "tests/fixtures/ethereum_tests",
        },
        "legacy_tests_submodule": {
            "commit": "2" * 40,
            "relative_path_from_ethereum_tests": "LegacyTests",
        },
        "eest": {
            "release_tag": "v0",
            "archive_url": "https://example.invalid/eest.tar.gz",
            "archive_filename": "eest.tar.gz",
            "archive_sha256": "3" * 64,
            "fixtures_subpath": "fixtures",
            "expected_top_level_dirs": ["blockchain_tests"],
        },
        "python_oracle": {
            "intended_version": "3.11.9",
            "patch_policy": "exact",
            "package_manager": "uv",
            "requirements_lock": "oracle/requirements.lock",
            "requirements_lock_sha256": "4" * 64,
            "known_packages": {"py-ecc": "8.0.0", "coincurve": "20.0.0"},
            "full_lock_status": "locked",
        },
    }
    path.write_text(json.dumps(data))


class GeneratorTests(unittest.TestCase):
    def test_u256_explicit_path_with_spaces_is_deterministic(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            checkout = root / "execution specs"
            commit = make_checkout(checkout)
            manifest = root / "sources.json"
            make_manifest(manifest, commit)
            output_one = root / "output one.json"
            output_two = root / "output two.json"

            for output in (output_one, output_two):
                subprocess.run(
                    [
                        sys.executable,
                        str(SCRIPTS_DIR / "gen-u256-vectors.py"),
                        "--manifest",
                        str(manifest),
                        "--execution-specs",
                        str(checkout),
                        "--output",
                        str(output),
                    ],
                    check=True,
                    capture_output=True,
                    text=True,
                )
            self.assertEqual(output_one.read_bytes(), output_two.read_bytes())
            payload = json.loads(output_one.read_text())
            self.assertEqual(payload["header"]["eels_revision"], commit)

    def test_explicit_generator_path_precedes_eels_root(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            good = root / "good"
            commit = make_checkout(good)
            manifest_path = root / "sources.json"
            make_manifest(manifest_path, commit)
            parser = argparse.ArgumentParser()
            with patch.dict(os.environ, {"EELS_ROOT": str(root / "wrong")}):
                _, selected, _ = common.load_generator_source(
                    parser, manifest_path, good
                )
            self.assertEqual(selected, good)

    def test_eels_root_is_used_without_explicit_path(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            checkout = root / "from environment"
            commit = make_checkout(checkout)
            manifest_path = root / "sources.json"
            make_manifest(manifest_path, commit)
            parser = argparse.ArgumentParser()
            with patch.dict(os.environ, {"EELS_ROOT": str(checkout)}):
                _, selected, _ = common.load_generator_source(
                    parser, manifest_path, None
                )
            self.assertEqual(selected, checkout)

    def test_wrong_checkout_revision_is_clear_failure(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            checkout = root / "checkout"
            old_commit = make_checkout(checkout)
            manifest_path = root / "sources.json"
            make_manifest(manifest_path, old_commit)
            (checkout / "new.txt").write_text("new commit\n")
            git(checkout, "add", "new.txt")
            git(checkout, "commit", "-q", "-m", "new")
            result = subprocess.run(
                [
                    sys.executable,
                    str(SCRIPTS_DIR / "gen-u256-vectors.py"),
                    "--manifest",
                    str(manifest_path),
                    "--execution-specs",
                    str(checkout),
                    "--output",
                    str(root / "must-not-exist.json"),
                ],
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("revision mismatch", result.stderr)
            self.assertFalse((root / "must-not-exist.json").exists())

    def test_bls_package_checks_report_missing_and_wrong_versions(self):
        manifest = {
            "python_oracle": {
                "known_packages": {"py-ecc": "8.0.0", "coincurve": "20.0.0"}
            }
        }
        parser = argparse.ArgumentParser()
        with patch.object(
            common,
            "version",
            side_effect=common.PackageNotFoundError("py-ecc"),
        ), self.assertRaises(SystemExit):
            common.require_known_packages(parser, manifest)

        parser = argparse.ArgumentParser()
        with patch.object(common, "version", return_value="7.0.0"), self.assertRaises(
            SystemExit
        ):
            common.require_known_packages(parser, manifest)


if __name__ == "__main__":
    unittest.main()
