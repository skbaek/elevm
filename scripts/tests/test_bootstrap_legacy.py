#!/usr/bin/env python3
"""Synthetic integration tests for scripts/bootstrap_legacy.py.

Every clone uses temporary file:// remotes. The suite never contacts GitHub
or reads/writes the user's real external-source destinations.
"""
from __future__ import annotations

import importlib.util
import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest import mock

SCRIPTS_DIR = Path(__file__).resolve().parents[1]
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))


def _load_bootstrap():
    spec = importlib.util.spec_from_file_location(
        "bootstrap_legacy", SCRIPTS_DIR / "bootstrap_legacy.py"
    )
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


bootstrap = _load_bootstrap()


def git(*args: str, cwd: Path | None = None, check: bool = True) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", *args],
        cwd=None if cwd is None else str(cwd),
        check=check,
        capture_output=True,
        text=True,
    )


def init_repo(path: Path, files: dict[str, str]) -> str:
    path.mkdir(parents=True)
    git("init", "-q", str(path))
    git("config", "user.email", "test@example.com", cwd=path)
    git("config", "user.name", "Test", cwd=path)
    git("config", "commit.gpgsign", "false", cwd=path)
    for relative, contents in files.items():
        file_path = path / relative
        file_path.parent.mkdir(parents=True, exist_ok=True)
        file_path.write_text(contents)
    git("add", ".", cwd=path)
    git("commit", "-q", "-m", "initial", cwd=path)
    return git("rev-parse", "HEAD", cwd=path).stdout.strip()


def bare_clone(source: Path, destination: Path) -> str:
    git("clone", "--bare", "--", str(source), str(destination))
    return destination.as_uri()


class FixtureSources:
    def __init__(self, root: Path):
        sources = root / "source repositories with spaces"
        sources.mkdir(parents=True)

        legacy_work = sources / "legacy work"
        self.legacy_commit = init_repo(
            legacy_work, {"README.md": "legacy fixtures\n"}
        )
        self.legacy_remote = sources / "legacy remote.git"
        legacy_url = bare_clone(legacy_work, self.legacy_remote)

        tests_work = sources / "tests work"
        init_repo(
            tests_work,
            {
                "README.md": "ethereum tests\n",
                "BlockchainTests/sample/fixture.json": "{}\n",
            },
        )
        git(
            "-c",
            "protocol.file.allow=always",
            "submodule",
            "add",
            "--name",
            "LegacyTests",
            legacy_url,
            "LegacyTests",
            cwd=tests_work,
        )
        git("commit", "-q", "-am", "add LegacyTests", cwd=tests_work)
        self.tests_commit = git("rev-parse", "HEAD", cwd=tests_work).stdout.strip()
        self.tests_remote = sources / "tests remote.git"
        self.tests_url = bare_clone(tests_work, self.tests_remote)

        execution_work = sources / "execution specs work"
        init_repo(
            execution_work,
            {
                "README.md": "execution specs, first revision\n",
                ".gitignore": "tests/fixtures\nvenv/\n",
            },
        )
        self.execution_previous_commit = git(
            "rev-parse", "HEAD", cwd=execution_work
        ).stdout.strip()
        (execution_work / "README.md").write_text(
            "execution specs, pinned revision\n"
        )
        git("add", "README.md", cwd=execution_work)
        git("commit", "-q", "-m", "pinned revision", cwd=execution_work)
        self.execution_commit = git(
            "rev-parse", "HEAD", cwd=execution_work
        ).stdout.strip()
        self.execution_remote = sources / "execution remote.git"
        self.execution_url = bare_clone(execution_work, self.execution_remote)

        self.manifest_path = root / "sources.json"
        manifest = {
            "schema_version": 1,
            "execution_specs": {
                "repo_url": self.execution_url,
                "commit": self.execution_commit,
                "default_env_var": "EELS_ROOT",
                "default_subpath_from_home": "execution-specs",
            },
            "ethereum_tests": {
                "repo_url": self.tests_url,
                "commit": self.tests_commit,
                "relative_path_from_execution_specs": (
                    "tests/fixtures/ethereum_tests"
                ),
            },
            "legacy_tests_submodule": {
                "name": "LegacyTests",
                "commit": self.legacy_commit,
                "relative_path_from_ethereum_tests": "LegacyTests",
            },
            "eest": {
                "release_tag": "v0",
                "archive_url": "https://example.invalid/fixtures.tar.gz",
                "archive_filename": "fixtures.tar.gz",
                "archive_sha256": "0" * 64,
                "default_env_var": "EEST_ROOT",
                "default_subpath_from_home": "eest-fixtures",
                "fixtures_subpath": "fixtures",
                "expected_top_level_dirs": ["blockchain_tests"],
            },
            "python_oracle": {
                "intended_version": "3.11.9",
                "patch_policy": "exact",
                "package_manager": "uv",
                "requirements_lock": "oracle/requirements.lock",
                "requirements_lock_sha256": "0" * 64,
                "known_packages": {
                    "py-ecc": "8.0.0",
                    "coincurve": "20.0.0",
                },
                "full_lock_status": "locked",
            },
        }
        self.manifest_path.write_text(json.dumps(manifest))

    def manifest(self) -> dict:
        return json.loads(self.manifest_path.read_text())

    def write_manifest(self, data: dict) -> None:
        self.manifest_path.write_text(json.dumps(data))


class BootstrapIntegrationTests(unittest.TestCase):
    def run_cli(
        self, sources: FixtureSources, destination: Path, *extra: str
    ) -> tuple[int, str, str]:
        stdout = io.StringIO()
        stderr = io.StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            rc = bootstrap.main(
                [
                    "--manifest",
                    str(sources.manifest_path),
                    "--execution-specs",
                    str(destination),
                    *extra,
                ]
            )
        return rc, stdout.getvalue(), stderr.getvalue()

    def install(
        self, sources: FixtureSources, destination: Path
    ) -> tuple[str, str]:
        rc, stdout, stderr = self.run_cli(sources, destination)
        self.assertEqual(rc, 0, stderr)
        return stdout, stderr

    def assert_no_temporary_sibling(self, destination: Path) -> None:
        leftovers = list(
            destination.parent.glob(f".{destination.name}.bootstrap-*")
        )
        self.assertEqual(leftovers, [])

    def test_fresh_install_has_exact_detached_layout(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sources = FixtureSources(root)
            destination = root / "installed execution-specs"
            stdout, _ = self.install(sources, destination)

            nested = destination / "tests/fixtures/ethereum_tests"
            legacy = nested / "LegacyTests"
            self.assertEqual(
                git("rev-parse", "HEAD", cwd=destination).stdout.strip(),
                sources.execution_commit,
            )
            self.assertEqual(
                git("rev-parse", "HEAD", cwd=nested).stdout.strip(),
                sources.tests_commit,
            )
            self.assertEqual(
                git("rev-parse", "HEAD", cwd=legacy).stdout.strip(),
                sources.legacy_commit,
            )
            self.assertNotEqual(
                git("symbolic-ref", "-q", "HEAD", cwd=destination, check=False).returncode,
                0,
            )
            self.assertNotEqual(
                git("symbolic-ref", "-q", "HEAD", cwd=nested, check=False).returncode,
                0,
            )
            self.assertTrue(
                (nested / "BlockchainTests/sample/fixture.json").is_file()
            )
            checks = [
                *bootstrap.env_doctor.check_execution_specs(
                    sources.manifest(), destination
                ),
                *bootstrap.env_doctor.check_ethereum_tests(
                    sources.manifest(), destination
                ),
            ]
            self.assertTrue(
                all(check.status == bootstrap.env_doctor.STATUS_OK for check in checks)
            )
            doctor_output = io.StringIO()
            with redirect_stdout(doctor_output):
                doctor_rc = bootstrap.env_doctor.main(
                    [
                        "--manifest",
                        str(sources.manifest_path),
                        "--execution-specs",
                        str(destination),
                        "--legacy-only",
                        "--json",
                    ]
                )
            self.assertEqual(doctor_rc, 0)
            self.assertTrue(json.loads(doctor_output.getvalue())["ok"])
            self.assertIn("OK — installed", stdout)
            self.assert_no_temporary_sibling(destination)

    def test_correct_rerun_is_network_free_no_op(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sources = FixtureSources(root)
            destination = root / "execution-specs"
            self.install(sources, destination)

            sources.execution_remote.rename(
                sources.execution_remote.with_name("execution remote.offline")
            )
            sources.tests_remote.rename(
                sources.tests_remote.with_name("tests remote.offline")
            )
            sources.legacy_remote.rename(
                sources.legacy_remote.with_name("legacy remote.offline")
            )

            rc, stdout, stderr = self.run_cli(sources, destination)
            self.assertEqual(rc, 0, stderr)
            self.assertIn("NO-OP", stdout)
            self.assertIn("No network or filesystem changes", stdout)

            rc, stdout, stderr = self.run_cli(
                sources, destination, "--dry-run"
            )
            self.assertEqual(rc, 0, stderr)
            self.assertIn("NO-OP", stdout)

    def test_refuses_wrong_commit_dirty_file_and_wrong_origin(self):
        scenarios = ("wrong-commit", "dirty", "wrong-origin")
        for scenario in scenarios:
            with self.subTest(scenario=scenario), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                sources = FixtureSources(root)
                destination = root / "execution-specs"
                self.install(sources, destination)

                if scenario == "wrong-commit":
                    git(
                        "checkout",
                        "--detach",
                        sources.execution_previous_commit,
                        cwd=destination,
                    )
                elif scenario == "dirty":
                    (destination / "README.md").write_text("locally modified\n")
                else:
                    git(
                        "remote",
                        "set-url",
                        "origin",
                        "https://example.invalid/wrong.git",
                        cwd=destination,
                    )

                rc, _, stderr = self.run_cli(sources, destination)
                self.assertEqual(rc, 1)
                self.assertIn("refusing existing destination", stderr)
                self.assertIn("will not repair or overwrite", stderr)

    def test_refuses_nonempty_and_partial_existing_targets(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sources = FixtureSources(root)

            ambiguous = root / "ambiguous"
            ambiguous.mkdir()
            marker = ambiguous / "keep.txt"
            marker.write_text("do not touch\n")
            rc, _, stderr = self.run_cli(sources, ambiguous)
            self.assertEqual(rc, 1)
            self.assertEqual(marker.read_text(), "do not touch\n")
            self.assertIn("not a Git checkout", stderr)

            partial = root / "partial execution-specs"
            git(
                "clone",
                "--no-recurse-submodules",
                "--",
                sources.execution_url,
                str(partial),
            )
            git("checkout", "--detach", sources.execution_commit, cwd=partial)
            rc, _, stderr = self.run_cli(sources, partial)
            self.assertEqual(rc, 1)
            self.assertIn("ethereum/tests", stderr)
            self.assertFalse(
                (partial / "tests/fixtures/ethereum_tests").exists()
            )

    def test_failed_nested_clone_leaves_no_partial_final_target(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sources = FixtureSources(root)
            manifest = sources.manifest()
            manifest["ethereum_tests"]["repo_url"] = (
                root / "missing tests remote.git"
            ).as_uri()
            sources.write_manifest(manifest)
            destination = root / "execution-specs"

            rc, _, stderr = self.run_cli(sources, destination)
            self.assertEqual(rc, 1)
            self.assertIn("bootstrap failed safely", stderr)
            self.assertFalse(destination.exists())
            self.assert_no_temporary_sibling(destination)

    def test_dry_run_plans_fresh_install_without_creating_paths(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sources = FixtureSources(root)
            destination = root / "missing parent" / "execution specs"

            rc, stdout, stderr = self.run_cli(
                sources, destination, "--dry-run"
            )
            self.assertEqual(rc, 0, stderr)
            self.assertIn("DRY RUN", stdout)
            self.assertIn("Would clone", stdout)
            self.assertIn("No network or filesystem changes", stdout)
            self.assertFalse(destination.parent.exists())

    def test_fresh_install_supports_destination_paths_with_spaces(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sources = FixtureSources(root)
            destination = root / "parent with spaces" / "execution specs"
            self.install(sources, destination)
            self.assertTrue(
                (
                    destination
                    / "tests/fixtures/ethereum_tests/BlockchainTests"
                ).is_dir()
            )

    def test_manifest_path_traversal_is_usage_error(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sources = FixtureSources(root)
            manifest = sources.manifest()
            manifest["ethereum_tests"][
                "relative_path_from_execution_specs"
            ] = "../outside"
            sources.write_manifest(manifest)

            rc, _, stderr = self.run_cli(
                sources, root / "execution-specs"
            )
            self.assertEqual(rc, 2)
            self.assertIn("safe relative path", stderr)

    def test_explicit_destination_precedes_eels_root(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sources = FixtureSources(root)
            environment_destination = root / "from environment"
            explicit_destination = root / "explicit"
            with mock.patch.dict(
                os.environ,
                {"EELS_ROOT": str(environment_destination)},
                clear=False,
            ):
                self.assertEqual(
                    bootstrap.destination_from_args(
                        explicit_destination, sources.manifest()
                    ),
                    explicit_destination,
                )
                self.assertEqual(
                    bootstrap.destination_from_args(None, sources.manifest()),
                    environment_destination,
                )


if __name__ == "__main__":
    unittest.main()
