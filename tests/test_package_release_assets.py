from __future__ import annotations

import hashlib
import io
import json
import os
import subprocess
import sys
import tarfile
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "package_release_assets.py"
TAG = "v0.2.0"
REPOSITORY_URL = "https://github.com/Robby955/FormalSLT.git"


def _run(command: list[str], *, cwd: Path) -> str:
    completed = subprocess.run(
        command,
        cwd=cwd,
        check=True,
        capture_output=True,
        text=True,
    )
    return completed.stdout.strip()


def _fixture_checkout(tmp_path: Path) -> tuple[Path, str, str]:
    checkout = tmp_path / "repo"
    checkout.mkdir()
    _run(["git", "init", "-b", "main"], cwd=checkout)
    _run(["git", "config", "user.name", "Release Asset Test"], cwd=checkout)
    _run(
        ["git", "config", "user.email", "release-assets@example.invalid"], cwd=checkout
    )

    (checkout / ".gitignore").write_text(".cache/\n", encoding="utf-8")
    (checkout / "README.md").write_text("# fixture\n", encoding="utf-8")
    (checkout / "lean-toolchain").write_text(
        "leanprover/lean4:v4.19.0\n", encoding="utf-8"
    )
    (checkout / "lake-manifest.json").write_text(
        json.dumps(
            {
                "packages": [
                    {
                        "name": "mathlib",
                        "type": "git",
                        "url": "https://github.com/leanprover-community/mathlib4.git",
                        "rev": "b" * 40,
                        "inputRev": "master",
                    }
                ]
            }
        )
        + "\n",
        encoding="utf-8",
    )
    executable = checkout / "bin" / "tool.sh"
    executable.parent.mkdir()
    executable.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
    executable.chmod(0o755)
    _run(["git", "add", "."], cwd=checkout)
    _run(["git", "commit", "-m", "fixture"], cwd=checkout)
    commit = _run(["git", "rev-parse", "HEAD^{commit}"], cwd=checkout)
    tree = _run(["git", "rev-parse", "HEAD^{tree}"], cwd=checkout)
    _run(["git", "tag", "-a", TAG, "-m", "fixture release"], cwd=checkout)

    ignored = checkout / ".cache" / "not-source.txt"
    ignored.parent.mkdir()
    ignored.write_text("ignored build output\n", encoding="utf-8")
    return checkout, commit, tree


def _fixture_docs(tmp_path: Path, commit: str) -> Path:
    docs = tmp_path / "staged-docs"
    (docs / "theorems").mkdir(parents=True)
    (docs / "assets").mkdir()
    (docs / "index.html").write_text(
        '<html data-formalslt-site="research">'
        f'<a href="https://github.com/Robby955/FormalSLT/tree/{commit}">source</a>'
        "</html>\n",
        encoding="utf-8",
    )
    (docs / "api.html").write_text("<html>api</html>\n", encoding="utf-8")
    (docs / "search.html").write_text("<html>search</html>\n", encoding="utf-8")
    (docs / "FormalSLT.html").write_text("<html>module</html>\n", encoding="utf-8")
    (docs / "theorems" / "index.html").write_text(
        f'<a href="https://github.com/Robby955/FormalSLT/blob/{commit}/FormalSLT.lean">'
        "theorem</a>\n",
        encoding="utf-8",
    )
    (docs / "assets" / "site.css").write_text(
        "body { color: #111; }\n", encoding="utf-8"
    )
    return docs


def _command(
    mode: str,
    *,
    checkout: Path,
    commit: str,
    docs: Path,
    output: Path,
) -> list[str]:
    tag_object = _run(["git", "rev-parse", f"refs/tags/{TAG}"], cwd=checkout)
    return [
        sys.executable,
        str(SCRIPT),
        mode,
        "--tag",
        TAG,
        "--expected-tag-object",
        tag_object,
        "--expected-commit",
        commit,
        "--checkout",
        str(checkout),
        "--doc-root",
        str(docs),
        "--output-dir",
        str(output),
        "--repository-url",
        REPOSITORY_URL,
    ]


def _package(
    tmp_path: Path, *, output_name: str = "assets"
) -> tuple[Path, str, str, Path, Path]:
    checkout, commit, tree = _fixture_checkout(tmp_path)
    docs = _fixture_docs(tmp_path, commit)
    output = tmp_path / output_name
    completed = subprocess.run(
        _command("build", checkout=checkout, commit=commit, docs=docs, output=output),
        check=True,
        capture_output=True,
        text=True,
    )
    assert "release assets build verified" in completed.stdout
    return checkout, commit, tree, docs, output


def test_build_is_deterministic_and_bound_to_exact_inputs(tmp_path: Path) -> None:
    checkout, commit, tree = _fixture_checkout(tmp_path)
    docs = _fixture_docs(tmp_path, commit)
    first = tmp_path / "assets-one"
    second = tmp_path / "assets-two"
    for output in (first, second):
        subprocess.run(
            _command(
                "build", checkout=checkout, commit=commit, docs=docs, output=output
            ),
            check=True,
            capture_output=True,
            text=True,
        )
        subprocess.run(
            _command(
                "verify", checkout=checkout, commit=commit, docs=docs, output=output
            ),
            check=True,
            capture_output=True,
            text=True,
        )

    assert sorted(path.name for path in first.iterdir()) == [
        "SHA256SUMS",
        "formalslt-v0.2.0-docs.tar.gz",
        "formalslt-v0.2.0-release-assets.json",
        "formalslt-v0.2.0-source.tar.gz",
    ]
    for first_asset in first.iterdir():
        assert first_asset.read_bytes() == (second / first_asset.name).read_bytes()

    source = first / "formalslt-v0.2.0-source.tar.gz"
    docs_archive = first / "formalslt-v0.2.0-docs.tar.gz"
    assert source.read_bytes()[4:8] == b"\0\0\0\0"
    assert docs_archive.read_bytes()[4:8] == b"\0\0\0\0"
    with tarfile.open(source, "r:gz") as package:
        members = {member.name: member for member in package.getmembers()}
        assert "FormalSLT-v0.2.0/README.md" in members
        assert "FormalSLT-v0.2.0/.cache/not-source.txt" not in members
        assert members["FormalSLT-v0.2.0/bin/tool.sh"].mode & 0o777 == 0o755
    with tarfile.open(docs_archive, "r:gz") as package:
        files = [member for member in package.getmembers() if member.isfile()]
        assert files
        assert all(
            member.mtime == 0 and member.mode & 0o777 == 0o644 for member in files
        )

    manifest = json.loads(
        (first / "formalslt-v0.2.0-release-assets.json").read_text(encoding="utf-8")
    )
    assert manifest["schema"] == "formalslt.release-assets.v1"
    assert manifest["tag_object"] == _run(
        ["git", "rev-parse", f"refs/tags/{TAG}"], cwd=checkout
    )
    assert manifest["resolved_commit"] == commit
    assert manifest["resolved_tree"] == tree
    assert "a GitHub Release exists" in manifest["does_not_assert"]

    sums = (first / "SHA256SUMS").read_text(encoding="utf-8").splitlines()
    assert len(sums) == 3
    for row in sums:
        digest, filename = row.split("  ", 1)
        assert digest == hashlib.sha256((first / filename).read_bytes()).hexdigest()


@pytest.mark.parametrize("mutation", ["tracked", "untracked"])
def test_build_refuses_nonexact_checkout(tmp_path: Path, mutation: str) -> None:
    checkout, commit, _ = _fixture_checkout(tmp_path)
    docs = _fixture_docs(tmp_path, commit)
    if mutation == "tracked":
        (checkout / "README.md").write_text("changed\n", encoding="utf-8")
    else:
        (checkout / "not-committed.txt").write_text("new\n", encoding="utf-8")
    completed = subprocess.run(
        _command(
            "build",
            checkout=checkout,
            commit=commit,
            docs=docs,
            output=tmp_path / "assets",
        ),
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.returncode == 1
    assert "tracked or untracked changes" in completed.stderr


def test_build_refuses_commit_mismatch(tmp_path: Path) -> None:
    checkout, commit, _ = _fixture_checkout(tmp_path)
    docs = _fixture_docs(tmp_path, commit)
    completed = subprocess.run(
        _command(
            "build",
            checkout=checkout,
            commit="0" * 40,
            docs=docs,
            output=tmp_path / "assets",
        ),
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.returncode == 1
    assert "checkout mismatch" in completed.stderr


@pytest.mark.parametrize(
    "mutation",
    [
        "wrong-source",
        "extra-wrong-link",
        "case-variant-wrong-link",
        "unresolved-token",
    ],
)
def test_build_refuses_unstaged_docs(tmp_path: Path, mutation: str) -> None:
    checkout, commit, _ = _fixture_checkout(tmp_path)
    docs = _fixture_docs(tmp_path, commit)
    root = docs / "index.html"
    if mutation == "wrong-source":
        root.write_text(
            root.read_text(encoding="utf-8").replace(commit, "c" * 40),
            encoding="utf-8",
        )
    elif mutation in {"extra-wrong-link", "case-variant-wrong-link"}:
        repository = (
            "Robby955/FormalSLT"
            if mutation == "extra-wrong-link"
            else "robBY955/formalSLT"
        )
        (docs / "api.html").write_text(
            f'<a href="https://github.com/{repository}/blob/main/README.md">'
            "moving source</a>\n",
            encoding="utf-8",
        )
    else:
        root.write_text(
            root.read_text(encoding="utf-8") + "__FORMALSLT_SOURCE_REF__\n",
            encoding="utf-8",
        )
    completed = subprocess.run(
        _command(
            "build",
            checkout=checkout,
            commit=commit,
            docs=docs,
            output=tmp_path / "assets",
        ),
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.returncode == 1
    expected = {
        "wrong-source": "not pinned",
        "extra-wrong-link": "source link not pinned",
        "case-variant-wrong-link": "source link not pinned",
        "unresolved-token": "unresolved source token",
    }[mutation]
    assert expected in completed.stderr


def test_build_refuses_docs_symlink_and_unsafe_output(tmp_path: Path) -> None:
    checkout, commit, _ = _fixture_checkout(tmp_path)
    docs = _fixture_docs(tmp_path, commit)
    os.symlink(docs / "api.html", docs / "api-copy.html")
    symlink_result = subprocess.run(
        _command(
            "build",
            checkout=checkout,
            commit=commit,
            docs=docs,
            output=tmp_path / "assets",
        ),
        check=False,
        capture_output=True,
        text=True,
    )
    assert symlink_result.returncode == 1
    assert "docs tree contains symlink" in symlink_result.stderr

    (docs / "api-copy.html").unlink()
    docs_link = tmp_path / "staged-docs-link"
    os.symlink(docs, docs_link)
    root_symlink = subprocess.run(
        _command(
            "build",
            checkout=checkout,
            commit=commit,
            docs=docs_link,
            output=tmp_path / "linked-docs-assets",
        ),
        check=False,
        capture_output=True,
        text=True,
    )
    assert root_symlink.returncode == 1
    assert "docs root must be one real directory" in root_symlink.stderr

    dangling_output = tmp_path / "dangling-output-link"
    os.symlink(tmp_path / "never-create-this-target", dangling_output)
    output_symlink = subprocess.run(
        _command(
            "build",
            checkout=checkout,
            commit=commit,
            docs=docs,
            output=dangling_output,
        ),
        check=False,
        capture_output=True,
        text=True,
    )
    assert output_symlink.returncode == 1
    assert "output path contains a symlink" in output_symlink.stderr
    assert not (tmp_path / "never-create-this-target").exists()

    inside_checkout = subprocess.run(
        _command(
            "build",
            checkout=checkout,
            commit=commit,
            docs=docs,
            output=checkout / "release-assets",
        ),
        check=False,
        capture_output=True,
        text=True,
    )
    assert inside_checkout.returncode == 1
    assert "output directory must be outside" in inside_checkout.stderr


def test_build_refuses_hardlinked_docs_file(tmp_path: Path) -> None:
    checkout, commit, _ = _fixture_checkout(tmp_path)
    docs = _fixture_docs(tmp_path, commit)
    outside = tmp_path / "outside-boundary.txt"
    outside.write_text("outside boundary\n", encoding="utf-8")
    os.link(outside, docs / "assets" / "hardlinked.txt")

    completed = subprocess.run(
        _command(
            "build",
            checkout=checkout,
            commit=commit,
            docs=docs,
            output=tmp_path / "assets",
        ),
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.returncode == 1
    assert "docs tree contains hardlinked file" in completed.stderr


def test_verify_refuses_tampering_and_build_refuses_overwrite(tmp_path: Path) -> None:
    checkout, commit, _, docs, output = _package(tmp_path)
    overwrite = subprocess.run(
        _command("build", checkout=checkout, commit=commit, docs=docs, output=output),
        check=False,
        capture_output=True,
        text=True,
    )
    assert overwrite.returncode == 1
    assert "refusing to overwrite" in overwrite.stderr

    manifest = output / "formalslt-v0.2.0-release-assets.json"
    manifest.write_text(manifest.read_text(encoding="utf-8") + " ", encoding="utf-8")
    tampered = subprocess.run(
        _command("verify", checkout=checkout, commit=commit, docs=docs, output=output),
        check=False,
        capture_output=True,
        text=True,
    )
    assert tampered.returncode == 1
    assert "release-asset manifest is not canonical JSON" in tampered.stderr


def test_verify_refuses_noncanonical_manifest_with_regenerated_checksums(
    tmp_path: Path,
) -> None:
    checkout, commit, _, docs, output = _package(tmp_path)
    manifest_path = output / "formalslt-v0.2.0-release-assets.json"
    manifest_path.write_text(
        " " + manifest_path.read_text(encoding="utf-8"), encoding="utf-8"
    )
    checksum_inputs = sorted(
        path for path in output.iterdir() if path.name != "SHA256SUMS"
    )
    (output / "SHA256SUMS").write_text(
        "".join(
            f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.name}\n"
            for path in checksum_inputs
        ),
        encoding="utf-8",
    )

    completed = subprocess.run(
        _command("verify", checkout=checkout, commit=commit, docs=docs, output=output),
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.returncode == 1
    assert "release-asset manifest is not canonical JSON" in completed.stderr


def test_verify_refuses_type_changed_manifest_with_regenerated_checksums(
    tmp_path: Path,
) -> None:
    checkout, commit, _, docs, output = _package(tmp_path)
    manifest_path = output / "formalslt-v0.2.0-release-assets.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    source_entry = manifest["assets"]["source_archive"]
    source_entry["file_count"] = float(source_entry["file_count"])
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    checksum_inputs = sorted(
        path for path in output.iterdir() if path.name != "SHA256SUMS"
    )
    (output / "SHA256SUMS").write_text(
        "".join(
            f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.name}\n"
            for path in checksum_inputs
        ),
        encoding="utf-8",
    )

    completed = subprocess.run(
        _command("verify", checkout=checkout, commit=commit, docs=docs, output=output),
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.returncode == 1
    assert "release-asset manifest does not match the exact inputs" in completed.stderr


@pytest.mark.parametrize(
    ("filename", "size", "expected"),
    [
        (
            "formalslt-v0.2.0-release-assets.json",
            (1 << 20) + 1,
            "release-asset manifest exceeds 1048576 bytes",
        ),
        ("SHA256SUMS", (1 << 16) + 1, "SHA256SUMS exceeds 65536 bytes"),
    ],
)
def test_verify_refuses_oversized_metadata(
    tmp_path: Path, filename: str, size: int, expected: str
) -> None:
    checkout, commit, _, docs, output = _package(tmp_path)
    (output / filename).write_bytes(b" " * size)

    completed = subprocess.run(
        _command("verify", checkout=checkout, commit=commit, docs=docs, output=output),
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.returncode == 1
    assert expected in completed.stderr


def test_verify_refuses_repacked_archive_with_regenerated_hashes(
    tmp_path: Path,
) -> None:
    checkout, commit, _, docs, output = _package(tmp_path)
    source = output / "formalslt-v0.2.0-source.tar.gz"
    replacement = tmp_path / "repacked-source.tar.gz"
    with tarfile.open(source, "r:gz") as original:
        members_and_data = [
            (member, original.extractfile(member).read() if member.isfile() else None)
            for member in original.getmembers()
        ]
    with tarfile.open(replacement, "w:gz") as repacked:
        for member, data in members_and_data:
            member.mtime = 123456789
            member.uid = 1000
            member.gid = 1000
            repacked.addfile(member, io.BytesIO(data) if data is not None else None)
    replacement.replace(source)

    manifest_path = output / "formalslt-v0.2.0-release-assets.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    source_entry = manifest["assets"]["source_archive"]
    source_entry["sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
    source_entry["size_bytes"] = source.stat().st_size
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    checksum_inputs = sorted(
        path for path in output.iterdir() if path.name != "SHA256SUMS"
    )
    (output / "SHA256SUMS").write_text(
        "".join(
            f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.name}\n"
            for path in checksum_inputs
        ),
        encoding="utf-8",
    )

    completed = subprocess.run(
        _command("verify", checkout=checkout, commit=commit, docs=docs, output=output),
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.returncode == 1
    assert "not the canonical exact-commit archive" in completed.stderr


def test_build_refuses_mismatched_local_tag_object(tmp_path: Path) -> None:
    checkout, commit, _ = _fixture_checkout(tmp_path)
    docs = _fixture_docs(tmp_path, commit)
    command = _command(
        "build",
        checkout=checkout,
        commit=commit,
        docs=docs,
        output=tmp_path / "assets",
    )
    tag_object_index = command.index("--expected-tag-object") + 1
    command[tag_object_index] = "c" * 40
    completed = subprocess.run(
        command,
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.returncode == 1
    assert "local tag object mismatch" in completed.stderr


def test_tag_workflow_packages_only_after_receipt_verification() -> None:
    workflow = (ROOT / ".github" / "workflows" / "release-tag-smoke.yml").read_text(
        encoding="utf-8"
    )
    assert "package_release_assets:" in workflow
    packaging_job = workflow.split("  package_release_assets:\n", 1)[1]
    assert "needs: [resolve_tag, verify_receipts]" in packaging_job
    assert (
        "actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02"
        in packaging_job
    )
    assert "scripts/package_release_assets.py build" in packaging_job
    assert "scripts/package_release_assets.py verify" in packaging_job
    assert "scripts/release_tag_identity.py verify" in packaging_job
    assert (
        packaging_job.index("scripts/package_release_assets.py verify")
        < packaging_job.index("scripts/release_tag_identity.py verify")
        < packaging_job.index("actions/upload-artifact@")
    )
    lowered = packaging_job.lower()
    for forbidden in (
        "contents: write",
        "deploy-pages",
        "create-release",
        "gh release",
        "zenodo",
    ):
        assert forbidden not in lowered
