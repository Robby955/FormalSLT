from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "generate_release_receipt.py"
RESOLVER = ROOT / "scripts" / "release_tag_identity.py"
AGGREGATE = ROOT / "scripts" / "verify_release_receipts.py"
TAG_INSTALL = ROOT / "scripts" / "check_tag_install.sh"
MATHLIB_REVISION = "905b95818eb32af7874a58b427f50c1711a5e96c"


def git(repository: Path, *arguments: str) -> str:
    completed = subprocess.run(
        ["git", "-C", str(repository), *arguments],
        check=True,
        capture_output=True,
        text=True,
    )
    return completed.stdout.strip()


def write_source_metadata(repository: Path) -> None:
    (repository / "lean-toolchain").write_text(
        "leanprover/lean4:v4.32.2\n", encoding="utf-8"
    )
    (repository / "lake-manifest.json").write_text(
        json.dumps(
            {
                "packages": [
                    {
                        "name": "mathlib",
                        "type": "git",
                        "url": "https://github.com/leanprover-community/mathlib4.git",
                        "rev": MATHLIB_REVISION,
                        "inputRev": "v4.32.2",
                    }
                ]
            }
        )
        + "\n",
        encoding="utf-8",
    )


def make_repository(tmp_path: Path, *, annotated: bool = False) -> Path:
    repository = tmp_path / "tag-source"
    repository.mkdir()
    subprocess.run(["git", "init", "-q", str(repository)], check=True)
    git(repository, "config", "user.name", "FormalSLT test")
    git(repository, "config", "user.email", "test@example.invalid")
    write_source_metadata(repository)
    git(repository, "add", "lean-toolchain", "lake-manifest.json")
    git(repository, "commit", "-q", "-m", "test source")
    if annotated:
        git(repository, "tag", "-a", "v0.2.0", "-m", "test release")
    else:
        git(repository, "tag", "v0.2.0")
    return repository


def tag_identity(repository: Path, tag: str = "v0.2.0") -> tuple[str, str]:
    return (
        git(repository, "rev-parse", f"refs/tags/{tag}"),
        git(repository, "rev-parse", f"refs/tags/{tag}^{{commit}}"),
    )


def run_generator(
    repository: Path,
    output: Path,
    tag: str = "v0.2.0",
    extra_environment: dict[str, str] | None = None,
    expected_tag_object: str | None = None,
    expected_commit: str | None = None,
) -> subprocess.CompletedProcess[str]:
    default_tag_object, default_commit = tag_identity(repository)
    environment = os.environ.copy()
    if extra_environment:
        environment.update(extra_environment)
    return subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--tag",
            tag,
            "--repository-url",
            str(repository),
            "--checkout",
            str(repository),
            "--expected-tag-object",
            expected_tag_object or default_tag_object,
            "--expected-commit",
            expected_commit or default_commit,
            "--output",
            str(output),
        ],
        check=False,
        capture_output=True,
        text=True,
        env=environment,
    )


@pytest.mark.parametrize("annotated", [False, True])
def test_receipt_binds_exact_tag_tree_and_environment(
    tmp_path: Path, annotated: bool
) -> None:
    repository = make_repository(tmp_path, annotated=annotated)
    output = tmp_path / "receipts" / "v0.2.0.json"

    result = run_generator(
        repository,
        output,
        extra_environment={
            "GITHUB_SERVER_URL": "https://github.example",
            "GITHUB_REPOSITORY": "Robby955/FormalSLT",
            "GITHUB_RUN_ID": "12345",
            "RUNNER_OS": "test-os",
        },
    )

    assert result.returncode == 0, result.stderr
    receipt = json.loads(output.read_text(encoding="utf-8"))
    commit = git(repository, "rev-parse", "HEAD^{commit}")
    assert receipt["schema"] == "formalslt.exact-tag-verification-receipt.v2"
    assert receipt["verification_scope"] == (
        "resolver_bound_tag_identity_and_source_environment_only"
    )
    assert receipt["tag"] == "v0.2.0"
    assert receipt["tag_object"] == git(repository, "rev-parse", "refs/tags/v0.2.0")
    assert receipt["resolved_commit"] == commit
    assert receipt["resolved_tree"] == git(repository, "rev-parse", "HEAD^{tree}")
    assert receipt["lean_toolchain"] == "leanprover/lean4:v4.32.2"
    assert receipt["mathlib"]["revision"] == MATHLIB_REVISION
    assert receipt["operating_system"]["runner_os"] == "test-os"
    assert receipt["run_url"] == (
        "https://github.example/Robby955/FormalSLT/actions/runs/12345"
    )
    assert re.fullmatch(r"[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z", receipt["generated_at_utc"])
    assert "a GitHub Release exists" in receipt["does_not_assert"]
    assert "a DOI exists or resolves" in receipt["does_not_assert"]


def test_resolver_exposes_one_tag_object_and_peeled_commit(tmp_path: Path) -> None:
    repository = make_repository(tmp_path, annotated=True)
    output = tmp_path / "github-output.txt"
    expected_object, expected_commit = tag_identity(repository)

    result = subprocess.run(
        [
            sys.executable,
            str(RESOLVER),
            "resolve",
            "--tag",
            "v0.2.0",
            "--repository-url",
            str(repository),
            "--expected-commit",
            expected_commit,
            "--github-output",
            str(output),
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stderr
    outputs = dict(line.split("=", 1) for line in output.read_text().splitlines())
    assert outputs == {
        "release_tag": "v0.2.0",
        "tag_object": expected_object,
        "resolved_commit": expected_commit,
    }


def test_resolver_refuses_push_event_commit_mismatch(tmp_path: Path) -> None:
    repository = make_repository(tmp_path)
    output = tmp_path / "github-output.txt"

    result = subprocess.run(
        [
            sys.executable,
            str(RESOLVER),
            "resolve",
            "--tag",
            "v0.2.0",
            "--repository-url",
            str(repository),
            "--expected-commit",
            "0" * 40,
            "--github-output",
            str(output),
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode != 0
    assert "push event commit mismatch" in result.stderr
    assert not output.exists()


def test_receipt_refuses_missing_tag(tmp_path: Path) -> None:
    repository = make_repository(tmp_path)
    output = tmp_path / "missing.json"

    result = run_generator(repository, output, tag="v0.2.1")

    assert result.returncode != 0
    assert "does not exist" in result.stderr
    assert not output.exists()


def test_receipt_refuses_checkout_at_different_commit(tmp_path: Path) -> None:
    repository = make_repository(tmp_path)
    output = tmp_path / "mismatch.json"
    (repository / "later.txt").write_text("later\n", encoding="utf-8")
    git(repository, "add", "later.txt")
    git(repository, "commit", "-q", "-m", "later source")

    result = run_generator(repository, output)

    assert result.returncode != 0
    assert "checkout mismatch" in result.stderr
    assert not output.exists()


def test_receipt_refuses_mismatched_resolver_commit(tmp_path: Path) -> None:
    repository = make_repository(tmp_path)
    output = tmp_path / "wrong-expected.json"
    expected_object, _ = tag_identity(repository)

    result = run_generator(
        repository,
        output,
        expected_tag_object=expected_object,
        expected_commit="0" * 40,
    )

    assert result.returncode != 0
    assert "remote peeled commit changed" in result.stderr
    assert not output.exists()


def test_receipt_refuses_mismatched_resolver_tag_object(tmp_path: Path) -> None:
    repository = make_repository(tmp_path, annotated=True)
    output = tmp_path / "wrong-object.json"
    _, expected_commit = tag_identity(repository)

    result = run_generator(
        repository,
        output,
        expected_tag_object="0" * 40,
        expected_commit=expected_commit,
    )

    assert result.returncode != 0
    assert "remote tag object changed" in result.stderr
    assert not output.exists()


def test_receipt_refuses_tag_mutation_after_resolution(tmp_path: Path) -> None:
    repository = make_repository(tmp_path)
    output = tmp_path / "moved-tag.json"
    expected_object, expected_commit = tag_identity(repository)
    (repository / "later.txt").write_text("later\n", encoding="utf-8")
    git(repository, "add", "later.txt")
    git(repository, "commit", "-q", "-m", "later source")
    git(repository, "tag", "-f", "v0.2.0")

    result = run_generator(
        repository,
        output,
        expected_tag_object=expected_object,
        expected_commit=expected_commit,
    )

    assert result.returncode != 0
    assert "remote tag object changed" in result.stderr
    assert not output.exists()


def test_receipt_refuses_dirty_tagged_checkout(tmp_path: Path) -> None:
    repository = make_repository(tmp_path)
    output = tmp_path / "dirty.json"
    (repository / "lean-toolchain").write_text("modified\n", encoding="utf-8")

    result = run_generator(repository, output)

    assert result.returncode != 0
    assert "tracked changes" in result.stderr
    assert not output.exists()


def test_receipt_refuses_unpinned_mathlib_revision(tmp_path: Path) -> None:
    repository = make_repository(tmp_path)
    output = tmp_path / "unpinned.json"
    manifest = json.loads((repository / "lake-manifest.json").read_text(encoding="utf-8"))
    manifest["packages"][0]["rev"] = "v4.32.2"
    (repository / "lake-manifest.json").write_text(
        json.dumps(manifest) + "\n", encoding="utf-8"
    )
    git(repository, "add", "lake-manifest.json")
    git(repository, "commit", "-q", "-m", "bad pin")
    git(repository, "tag", "-f", "v0.2.0")

    result = run_generator(repository, output)

    assert result.returncode != 0
    assert "pinned Mathlib revision" in result.stderr
    assert not output.exists()


def write_receipt_pair(repository: Path, directory: Path) -> tuple[str, str]:
    expected_object, expected_commit = tag_identity(repository)
    for runner in ("Linux", "macOS"):
        result = run_generator(
            repository,
            directory / f"receipt-{runner}.json",
            expected_tag_object=expected_object,
            expected_commit=expected_commit,
            extra_environment={
                "RUNNER_OS": runner,
                "FORMALSLT_RUN_URL": "https://github.example/actions/runs/12345",
            },
        )
        assert result.returncode == 0, result.stderr
    return expected_object, expected_commit


def run_aggregate(
    repository: Path,
    directory: Path,
    expected_object: str,
    expected_commit: str,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            str(AGGREGATE),
            "--receipt-dir",
            str(directory),
            "--checkout",
            str(repository),
            "--repository-url",
            str(repository),
            "--tag",
            "v0.2.0",
            "--expected-tag-object",
            expected_object,
            "--expected-commit",
            expected_commit,
        ],
        check=False,
        capture_output=True,
        text=True,
    )


def test_aggregate_accepts_matching_linux_macos_pair(tmp_path: Path) -> None:
    repository = make_repository(tmp_path)
    directory = tmp_path / "receipts"
    expected_object, expected_commit = write_receipt_pair(repository, directory)

    result = run_aggregate(repository, directory, expected_object, expected_commit)

    assert result.returncode == 0, result.stderr
    assert "matched Linux/macOS exact-tag receipts" in result.stdout


def test_aggregate_refuses_tree_mismatch(tmp_path: Path) -> None:
    repository = make_repository(tmp_path)
    directory = tmp_path / "receipts"
    expected_object, expected_commit = write_receipt_pair(repository, directory)
    macos_path = directory / "receipt-macOS.json"
    macos = json.loads(macos_path.read_text(encoding="utf-8"))
    macos["resolved_tree"] = "0" * 40
    macos_path.write_text(json.dumps(macos) + "\n", encoding="utf-8")

    result = run_aggregate(repository, directory, expected_object, expected_commit)

    assert result.returncode != 0
    assert "resolved_tree" in result.stderr


def test_aggregate_refuses_remote_move_after_receipts(tmp_path: Path) -> None:
    repository = make_repository(tmp_path)
    directory = tmp_path / "receipts"
    expected_object, expected_commit = write_receipt_pair(repository, directory)
    (repository / "later.txt").write_text("later\n", encoding="utf-8")
    git(repository, "add", "later.txt")
    git(repository, "commit", "-q", "-m", "later source")
    git(repository, "tag", "-f", "v0.2.0")
    git(repository, "checkout", "-q", "--detach", expected_commit)

    result = run_aggregate(repository, directory, expected_object, expected_commit)

    assert result.returncode != 0
    assert "remote tag object changed" in result.stderr


def write_mutating_fake_lake(tmp_path: Path) -> Path:
    fake_lake = tmp_path / "fake-lake"
    fake_lake.write_text(
        """#!/usr/bin/env bash
set -euo pipefail
case "$1" in
  update)
    git -C "$FAKE_REPOSITORY" tag -f "$FAKE_TAG" "$FAKE_MUTATION_COMMIT" >/dev/null
    mkdir -p .lake/packages
    git clone -q --branch "$FAKE_TAG" "$FAKE_REPOSITORY" .lake/packages/formal-slt
    ;;
  exe|build)
    ;;
  *)
    exit 64
    ;;
esac
""",
        encoding="utf-8",
    )
    fake_lake.chmod(0o755)
    return fake_lake


def run_tag_install_with_mutation(
    repository: Path,
    fake_lake: Path,
    expected_object: str,
    expected_commit: str,
    mutation_commit: str,
) -> subprocess.CompletedProcess[str]:
    environment = os.environ.copy()
    environment.update(
        {
            "LAKE": str(fake_lake),
            "FORMALSLT_REPOSITORY_URL": str(repository),
            "FAKE_REPOSITORY": str(repository),
            "FAKE_TAG": "v0.2.0",
            "FAKE_MUTATION_COMMIT": mutation_commit,
        }
    )

    return subprocess.run(
        [
            "bash",
            str(TAG_INSTALL),
            "v0.2.0",
            expected_object,
            expected_commit,
        ],
        check=False,
        capture_output=True,
        text=True,
        env=environment,
    )


def test_tag_install_detects_commit_mutation_during_lake_update(tmp_path: Path) -> None:
    repository = make_repository(tmp_path)
    expected_object, expected_commit = tag_identity(repository)
    (repository / "later.txt").write_text("later\n", encoding="utf-8")
    git(repository, "add", "later.txt")
    git(repository, "commit", "-q", "-m", "later source")
    mutation_commit = git(repository, "rev-parse", "HEAD")

    result = run_tag_install_with_mutation(
        repository,
        write_mutating_fake_lake(tmp_path),
        expected_object,
        expected_commit,
        mutation_commit,
    )

    assert result.returncode != 0
    assert "Lake installed" in result.stderr
    assert expected_commit in result.stderr


def test_tag_install_detects_tag_object_mutation_with_same_commit(
    tmp_path: Path,
) -> None:
    repository = make_repository(tmp_path, annotated=True)
    expected_object, expected_commit = tag_identity(repository)

    result = run_tag_install_with_mutation(
        repository,
        write_mutating_fake_lake(tmp_path),
        expected_object,
        expected_commit,
        expected_commit,
    )

    assert result.returncode != 0
    assert "remote tag object changed" in result.stderr
    assert expected_object in result.stderr
