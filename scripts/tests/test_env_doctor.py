#!/usr/bin/env python3
"""Unit tests for scripts/env_doctor.py and scripts/sources.json parsing.

Uses only temporary directories and tiny local Git repositories. Never
touches the real home directory, the real manifest defaults, or the network.

Run with: python3 -m unittest discover -s scripts/tests
"""
from __future__ import annotations

import importlib.util
import io
import json
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parents[1]


def _load_env_doctor():
    spec = importlib.util.spec_from_file_location("env_doctor", SCRIPTS_DIR / "env_doctor.py")
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


env_doctor = _load_env_doctor()


def make_git_repo(path: Path, origin: str | None = None) -> str:
    path.mkdir(parents=True, exist_ok=True)
    run = lambda *args: subprocess.run(  # noqa: E731
        ["git", "-C", str(path), *args], check=True, capture_output=True, text=True
    )
    subprocess.run(["git", "init", "-q", str(path)], check=True)
    run("config", "user.email", "test@example.com")
    run("config", "user.name", "Test")
    run("config", "commit.gpgsign", "false")
    (path / "file.txt").write_text("hello\n")
    run("add", ".")
    run("commit", "-q", "-m", "init")
    if origin is not None:
        run("remote", "add", "origin", origin)
    return run("rev-parse", "HEAD").stdout.strip()


def make_fake_venv(root: Path, version: str, packages: dict) -> None:
    bin_dir = root / "bin"
    bin_dir.mkdir(parents=True)
    python_path = bin_dir / "python"
    payload = json.dumps({"python_version": version, "packages": packages})
    python_path.write_text(f"#!/bin/sh\ncat <<'EOF'\n{payload}\nEOF\n")
    python_path.chmod(0o755)


def make_manifest(path: Path, **overrides) -> dict:
    data = {
        "schema_version": 1,
        "execution_specs": {
            "repo_url": "https://example.invalid/execution-specs.git",
            "commit": "0" * 40,
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
            "release_tag": "v0.0.0",
            "archive_url": "https://example.invalid/fixtures.tar.gz",
            "archive_filename": "fixtures.tar.gz",
            "archive_sha256": "0" * 64,
            "default_env_var": "EEST_ROOT",
            "default_subpath_from_home": "eest-fixtures",
            "fixtures_subpath": "fixtures",
            "expected_top_level_dirs": ["blockchain_tests", "state_tests"],
        },
        "python_oracle": {
            "intended_version": "3.11.9",
            "known_packages": {"py-ecc": "8.0.0", "coincurve": "20.0.0"},
            "full_lock_status": "deferred_to_step_4",
        },
    }
    data.update(overrides)
    path.write_text(json.dumps(data))
    return data


class ManifestParsingTests(unittest.TestCase):
    def test_valid_manifest_parses(self):
        with tempfile.TemporaryDirectory() as tmp:
            manifest_path = Path(tmp) / "sources.json"
            make_manifest(manifest_path)
            data = env_doctor.load_manifest(manifest_path)
            self.assertEqual(data["execution_specs"]["commit"], "0" * 40)

    def test_malformed_json_raises(self):
        with tempfile.TemporaryDirectory() as tmp:
            manifest_path = Path(tmp) / "sources.json"
            manifest_path.write_text("{ not valid json ")
            with self.assertRaises(env_doctor.ManifestError):
                env_doctor.load_manifest(manifest_path)

    def test_missing_top_level_key_raises(self):
        with tempfile.TemporaryDirectory() as tmp:
            manifest_path = Path(tmp) / "sources.json"
            manifest_path.write_text(json.dumps({"execution_specs": {}}))
            with self.assertRaises(env_doctor.ManifestError):
                env_doctor.load_manifest(manifest_path)

    def test_missing_nested_field_raises(self):
        with tempfile.TemporaryDirectory() as tmp:
            manifest_path = Path(tmp) / "sources.json"
            data_path = manifest_path
            make_manifest(data_path)
            data = json.loads(data_path.read_text())
            del data["eest"]["archive_sha256"]
            data_path.write_text(json.dumps(data))
            with self.assertRaises(env_doctor.ManifestError):
                env_doctor.load_manifest(data_path)

    def test_missing_manifest_file_raises(self):
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaises(env_doctor.ManifestError):
                env_doctor.load_manifest(Path(tmp) / "does-not-exist.json")

    def test_non_object_section_raises(self):
        with tempfile.TemporaryDirectory() as tmp:
            manifest_path = Path(tmp) / "sources.json"
            data = make_manifest(manifest_path)
            data["execution_specs"] = []
            manifest_path.write_text(json.dumps(data))
            with self.assertRaises(env_doctor.ManifestError):
                env_doctor.load_manifest(manifest_path)

    def test_unsupported_schema_raises(self):
        with tempfile.TemporaryDirectory() as tmp:
            manifest_path = Path(tmp) / "sources.json"
            data = make_manifest(manifest_path)
            data["schema_version"] = 2
            manifest_path.write_text(json.dumps(data))
            with self.assertRaises(env_doctor.ManifestError):
                env_doctor.load_manifest(manifest_path)


class GitCheckoutTests(unittest.TestCase):
    def test_success(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp) / "repo"
            commit = make_git_repo(repo, origin="https://example.invalid/repo.git")
            checks = env_doctor.check_git_checkout(
                "x", repo, "https://example.invalid/repo.git", commit
            )
            statuses = {c.name: c.status for c in checks}
            self.assertEqual(statuses["x: HEAD"], env_doctor.STATUS_OK)
            self.assertEqual(statuses["x: origin"], env_doctor.STATUS_OK)
            self.assertEqual(statuses["x: tracked dirtiness"], env_doctor.STATUS_OK)

    def test_missing_directory(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp) / "nope"
            checks = env_doctor.check_git_checkout("x", repo, "https://example.invalid/repo.git", "abc")
            self.assertEqual(len(checks), 1)
            self.assertEqual(checks[0].status, env_doctor.STATUS_MISSING)

    def test_wrong_commit(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp) / "repo"
            make_git_repo(repo, origin="https://example.invalid/repo.git")
            checks = env_doctor.check_git_checkout(
                "x", repo, "https://example.invalid/repo.git", "f" * 40
            )
            statuses = {c.name: c.status for c in checks}
            self.assertEqual(statuses["x: HEAD"], env_doctor.STATUS_FAIL)

    def test_wrong_origin(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp) / "repo"
            commit = make_git_repo(repo, origin="https://example.invalid/actual.git")
            checks = env_doctor.check_git_checkout(
                "x", repo, "https://example.invalid/expected.git", commit
            )
            statuses = {c.name: c.status for c in checks}
            self.assertEqual(statuses["x: origin"], env_doctor.STATUS_FAIL)

    def test_origin_url_normalization_ignores_trailing_git_and_slash(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp) / "repo"
            commit = make_git_repo(repo, origin="https://example.invalid/repo.git")
            checks = env_doctor.check_git_checkout(
                "x", repo, "https://example.invalid/repo/", commit
            )
            statuses = {c.name: c.status for c in checks}
            self.assertEqual(statuses["x: origin"], env_doctor.STATUS_OK)

    def test_dirty_tracked_file_is_reported(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp) / "repo"
            commit = make_git_repo(repo)
            (repo / "file.txt").write_text("modified\n")
            checks = env_doctor.check_git_checkout("x", repo, None, commit)
            statuses = {c.name: c.status for c in checks}
            self.assertEqual(statuses["x: tracked dirtiness"], env_doctor.STATUS_FAIL)

    def test_harmless_untracked_file_is_not_dirty(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp) / "repo"
            commit = make_git_repo(repo)
            (repo / ".python-version").write_text("3.11.9\n")
            checks = env_doctor.check_git_checkout("x", repo, None, commit)
            statuses = {c.name: c.status for c in checks}
            self.assertEqual(statuses["x: tracked dirtiness"], env_doctor.STATUS_OK)


class EestChecksTests(unittest.TestCase):
    def test_missing_root(self):
        with tempfile.TemporaryDirectory() as tmp:
            manifest = make_manifest(Path(tmp) / "m.json")
            checks = env_doctor.check_eest(manifest, Path(tmp) / "nope")
            self.assertEqual(checks[0].status, env_doctor.STATUS_MISSING)

    def test_archive_checksum_ok_and_fixture_dirs_ok(self):
        with tempfile.TemporaryDirectory() as tmp:
            eest_root = Path(tmp) / "eest"
            eest_root.mkdir()
            archive = eest_root / "fixtures.tar.gz"
            archive.write_bytes(b"synthetic archive contents")
            actual_hash = env_doctor.sha256_file(archive)
            manifest = make_manifest(
                Path(tmp) / "m.json",
                eest={
                    "release_tag": "v0.0.0",
                    "archive_url": "https://example.invalid/fixtures.tar.gz",
                    "archive_filename": "fixtures.tar.gz",
                    "archive_sha256": actual_hash,
                    "default_env_var": "EEST_ROOT",
                    "default_subpath_from_home": "eest-fixtures",
                    "fixtures_subpath": "fixtures",
                    "expected_top_level_dirs": ["blockchain_tests", "state_tests"],
                },
            )
            (eest_root / "fixtures" / "blockchain_tests").mkdir(parents=True)
            (eest_root / "fixtures" / "state_tests").mkdir(parents=True)
            checks = env_doctor.check_eest(manifest, eest_root)
            statuses = {c.name: c.status for c in checks}
            self.assertEqual(statuses["eest: archive sha256"], env_doctor.STATUS_OK)
            self.assertEqual(statuses["eest: extracted fixtures"], env_doctor.STATUS_OK)

    def test_archive_checksum_mismatch(self):
        with tempfile.TemporaryDirectory() as tmp:
            eest_root = Path(tmp) / "eest"
            eest_root.mkdir()
            (eest_root / "fixtures.tar.gz").write_bytes(b"tampered contents")
            manifest = make_manifest(Path(tmp) / "m.json")
            checks = env_doctor.check_eest(manifest, eest_root)
            statuses = {c.name: c.status for c in checks}
            self.assertEqual(statuses["eest: archive sha256"], env_doctor.STATUS_FAIL)

    def test_missing_expected_fixture_dirs(self):
        with tempfile.TemporaryDirectory() as tmp:
            eest_root = Path(tmp) / "eest"
            (eest_root / "fixtures" / "blockchain_tests").mkdir(parents=True)
            manifest = make_manifest(Path(tmp) / "m.json")
            checks = env_doctor.check_eest(manifest, eest_root)
            statuses = {c.name: c.status for c in checks}
            self.assertEqual(statuses["eest: extracted fixtures"], env_doctor.STATUS_FAIL)


class PythonOracleTests(unittest.TestCase):
    def test_missing_venv(self):
        with tempfile.TemporaryDirectory() as tmp:
            manifest = make_manifest(Path(tmp) / "m.json")
            checks = env_doctor.check_python_oracle(manifest, Path(tmp) / "nope")
            self.assertEqual(checks[0].status, env_doctor.STATUS_MISSING)

    def test_matching_version_and_packages(self):
        with tempfile.TemporaryDirectory() as tmp:
            venv = Path(tmp) / "venv"
            make_fake_venv(venv, "3.11.9", {"py-ecc": "8.0.0", "coincurve": "20.0.0"})
            manifest = make_manifest(Path(tmp) / "m.json")
            checks = env_doctor.check_python_oracle(manifest, venv)
            statuses = {c.name: c.status for c in checks}
            self.assertEqual(statuses["python-oracle: version"], env_doctor.STATUS_OK)
            self.assertEqual(statuses["python-oracle: py-ecc"], env_doctor.STATUS_OK)
            self.assertEqual(statuses["python-oracle: coincurve"], env_doctor.STATUS_OK)

    def test_wrong_version(self):
        with tempfile.TemporaryDirectory() as tmp:
            venv = Path(tmp) / "venv"
            make_fake_venv(venv, "3.12.0", {"py-ecc": "8.0.0", "coincurve": "20.0.0"})
            manifest = make_manifest(Path(tmp) / "m.json")
            checks = env_doctor.check_python_oracle(manifest, venv)
            statuses = {c.name: c.status for c in checks}
            self.assertEqual(statuses["python-oracle: version"], env_doctor.STATUS_FAIL)

    def test_absent_package(self):
        with tempfile.TemporaryDirectory() as tmp:
            venv = Path(tmp) / "venv"
            make_fake_venv(venv, "3.11.9", {"py-ecc": None, "coincurve": "20.0.0"})
            manifest = make_manifest(Path(tmp) / "m.json")
            checks = env_doctor.check_python_oracle(manifest, venv)
            statuses = {c.name: c.status for c in checks}
            self.assertEqual(statuses["python-oracle: py-ecc"], env_doctor.STATUS_MISSING)

    def test_wrong_package_version(self):
        with tempfile.TemporaryDirectory() as tmp:
            venv = Path(tmp) / "venv"
            make_fake_venv(venv, "3.11.9", {"py-ecc": "7.0.0", "coincurve": "20.0.0"})
            manifest = make_manifest(Path(tmp) / "m.json")
            checks = env_doctor.check_python_oracle(manifest, venv)
            statuses = {c.name: c.status for c in checks}
            self.assertEqual(statuses["python-oracle: py-ecc"], env_doctor.STATUS_FAIL)


class MainCliTests(unittest.TestCase):
    def _build_good_environment(self, tmp: Path):
        execution_specs = tmp / "execution-specs"
        es_commit = make_git_repo(execution_specs, origin="https://example.invalid/execution-specs.git")
        ethereum_tests = execution_specs / "tests" / "fixtures" / "ethereum_tests"
        make_git_repo(ethereum_tests, origin="https://example.invalid/tests.git")
        (ethereum_tests / "BlockchainTests").mkdir()
        (ethereum_tests / "BlockchainTests" / "fixture.json").write_text("{}\n")
        legacy = ethereum_tests / "LegacyTests"
        legacy_commit = make_git_repo(legacy)
        (ethereum_tests / ".gitmodules").write_text(
            "[submodule \"LegacyTests\"]\n"
            "\tpath = LegacyTests\n"
            "\turl = https://example.invalid/legacytests.git\n"
        )
        subprocess.run(
            [
                "git",
                "-C",
                str(ethereum_tests),
                "add",
                ".gitmodules",
                "BlockchainTests",
                "LegacyTests",
            ],
            check=True,
            capture_output=True,
            text=True,
        )
        subprocess.run(
            [
                "git",
                "-C",
                str(ethereum_tests),
                "commit",
                "-q",
                "-m",
                "add fixtures and LegacyTests gitlink",
            ],
            check=True,
            capture_output=True,
            text=True,
        )
        et_commit = subprocess.run(
            ["git", "-C", str(ethereum_tests), "rev-parse", "HEAD"],
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()

        eest_root = tmp / "eest-fixtures"
        eest_root.mkdir()
        archive = eest_root / "fixtures.tar.gz"
        archive.write_bytes(b"synthetic archive")
        archive_hash = env_doctor.sha256_file(archive)
        (eest_root / "fixtures" / "blockchain_tests").mkdir(parents=True)
        (eest_root / "fixtures" / "state_tests").mkdir(parents=True)

        venv = tmp / "venv"
        make_fake_venv(venv, "3.11.9", {"py-ecc": "8.0.0", "coincurve": "20.0.0"})

        manifest_path = tmp / "sources.json"
        make_manifest(
            manifest_path,
            execution_specs={
                "repo_url": "https://example.invalid/execution-specs.git",
                "commit": es_commit,
                "default_env_var": "EELS_ROOT",
                "default_subpath_from_home": "execution-specs",
            },
            ethereum_tests={
                "repo_url": "https://example.invalid/tests.git",
                "commit": et_commit,
                "relative_path_from_execution_specs": "tests/fixtures/ethereum_tests",
            },
            legacy_tests_submodule={
                "commit": legacy_commit,
                "relative_path_from_ethereum_tests": "LegacyTests",
            },
            eest={
                "release_tag": "v0.0.0",
                "archive_url": "https://example.invalid/fixtures.tar.gz",
                "archive_filename": "fixtures.tar.gz",
                "archive_sha256": archive_hash,
                "default_env_var": "EEST_ROOT",
                "default_subpath_from_home": "eest-fixtures",
                "fixtures_subpath": "fixtures",
                "expected_top_level_dirs": ["blockchain_tests", "state_tests"],
            },
        )
        return manifest_path, execution_specs, eest_root, venv

    def test_full_environment_json_ok(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            manifest_path, execution_specs, eest_root, venv = self._build_good_environment(tmp_path)
            buf = io.StringIO()
            with redirect_stdout(buf):
                rc = env_doctor.main(
                    [
                        "--manifest", str(manifest_path),
                        "--execution-specs", str(execution_specs),
                        "--eest-root", str(eest_root),
                        "--venv", str(venv),
                        "--json",
                    ]
                )
            self.assertEqual(rc, 0)
            payload = json.loads(buf.getvalue())
            self.assertTrue(payload["ok"])
            self.assertTrue(all(c["status"] == "ok" for c in payload["checks"]))

    def test_legacy_only_skips_deferred_eest_and_python(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            manifest_path, execution_specs, _, _ = self._build_good_environment(
                tmp_path
            )
            missing = tmp_path / "deliberately-missing"
            buf = io.StringIO()
            with redirect_stdout(buf):
                rc = env_doctor.main(
                    [
                        "--manifest",
                        str(manifest_path),
                        "--execution-specs",
                        str(execution_specs),
                        "--eest-root",
                        str(missing / "eest"),
                        "--venv",
                        str(missing / "venv"),
                        "--legacy-only",
                        "--json",
                    ]
                )
            self.assertEqual(rc, 0)
            payload = json.loads(buf.getvalue())
            self.assertTrue(payload["ok"])
            self.assertFalse(
                any(check["name"].startswith("eest:") for check in payload["checks"])
            )
            self.assertFalse(
                any(
                    check["name"].startswith("python-oracle:")
                    for check in payload["checks"]
                )
            )

    def test_missing_environment_fails_without_creating_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            manifest_path = tmp_path / "sources.json"
            make_manifest(manifest_path)
            missing_root = tmp_path / "missing-root"
            buf = io.StringIO()
            with redirect_stdout(buf):
                rc = env_doctor.main(
                    [
                        "--manifest", str(manifest_path),
                        "--execution-specs", str(missing_root / "execution-specs"),
                        "--eest-root", str(missing_root / "eest-fixtures"),
                        "--venv", str(missing_root / "venv"),
                    ]
                )
            self.assertEqual(rc, 1)
            self.assertFalse(missing_root.exists())

    def test_malformed_manifest_exit_code_2(self):
        with tempfile.TemporaryDirectory() as tmp:
            manifest_path = Path(tmp) / "sources.json"
            manifest_path.write_text("{ not json")
            buf = io.StringIO()
            with redirect_stdout(buf), redirect_stderr(io.StringIO()):
                rc = env_doctor.main(["--manifest", str(manifest_path)])
            self.assertEqual(rc, 2)

    def test_one_dirty_component_breaks_full_environment(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            manifest_path, execution_specs, eest_root, venv = self._build_good_environment(tmp_path)
            (execution_specs / "file.txt").write_text("dirtied\n")
            buf = io.StringIO()
            with redirect_stdout(buf):
                rc = env_doctor.main(
                    [
                        "--manifest", str(manifest_path),
                        "--execution-specs", str(execution_specs),
                        "--eest-root", str(eest_root),
                        "--venv", str(venv),
                        "--json",
                    ]
                )
            self.assertEqual(rc, 1)
            payload = json.loads(buf.getvalue())
            self.assertFalse(payload["ok"])


if __name__ == "__main__":
    unittest.main()
