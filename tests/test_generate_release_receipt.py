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
    repository = tmp_path / "tag source"
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


def run_generator(
    repository: Path,
    output: Path,
    tag: str = "v0.2.0",
    extra_environment: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
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
    assert receipt["schema"] == "formalslt.exact-tag-verification-receipt.v1"
    assert receipt["verification_scope"] == "tag_identity_and_source_environment_only"
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
