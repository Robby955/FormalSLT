#!/usr/bin/env python3
"""Build or verify deterministic release assets from one exact checkout.

The bundle contains an exact-commit source archive, an archive of already
staged documentation, a deterministic identity manifest, and SHA256SUMS.  It
is a local packaging artifact only: this script never creates a tag, publishes
a GitHub Release, deploys documentation, or contacts an archival service.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Sequence

from release_tag_identity import (
    DEFAULT_REPOSITORY_URL,
    ReceiptError,
    run,
    validate_sha,
    validate_tag,
)

SITE_MARKER = 'data-formalslt-site="research"'
SOURCE_REF_TOKEN = "__FORMALSLT_SOURCE_REF__"
SOURCE_URL_RE = re.compile(
    r"https://github\.com/Robby955/FormalSLT/(?:blob|tree)/([^/\"'?#<>&]+)",
    flags=re.IGNORECASE,
)
REQUIRED_DOC_PATHS = (
    "index.html",
    "api.html",
    "search.html",
    "FormalSLT.html",
    "theorems/index.html",
)
MANIFEST_SCHEMA = "formalslt.release-assets.v1"
MAX_MANIFEST_BYTES = 1 << 20
MAX_CHECKSUMS_BYTES = 1 << 16


@dataclass(frozen=True)
class GitFile:
    path: str
    mode: int
    object_id: str


@dataclass(frozen=True)
class DocEntry:
    path: str
    source: Path
    is_directory: bool
    size: int
    mtime_ns: int
    inode: int


def _run_bytes(command: Sequence[str], *, cwd: Path) -> bytes:
    completed = subprocess.run(
        command,
        cwd=cwd,
        check=False,
        capture_output=True,
    )
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        if not detail:
            detail = completed.stdout.decode("utf-8", errors="replace").strip()
        suffix = f": {detail}" if detail else ""
        raise ReceiptError(f"command failed ({' '.join(command)}){suffix}")
    return completed.stdout


def _safe_relative_path(value: str, description: str) -> PurePosixPath:
    if not value or "\\" in value or "\x00" in value:
        raise ReceiptError(f"unsafe {description}: {value!r}")
    path = PurePosixPath(value)
    if path.is_absolute() or any(part in {"", ".", ".."} for part in path.parts):
        raise ReceiptError(f"unsafe {description}: {value!r}")
    return path


def _is_within(path: Path, parent: Path) -> bool:
    return path == parent or parent in path.parents


def _reject_symlink_components(path: Path, description: str) -> None:
    absolute = path.expanduser().absolute()
    current = Path(absolute.anchor)
    for component in absolute.parts[1:]:
        current /= component
        try:
            metadata = current.lstat()
        except FileNotFoundError:
            # No deeper component can exist until this real directory is created.
            break
        except OSError as exc:
            raise ReceiptError(
                f"unable to inspect {description} path {current}: {exc}"
            ) from exc
        if stat.S_ISLNK(metadata.st_mode):
            raise ReceiptError(f"{description} path contains a symlink: {current}")


def _validate_output_location(
    output_dir: Path, *, checkout: Path, doc_root: Path, must_exist: bool
) -> Path:
    requested_output = output_dir.expanduser().absolute()
    _reject_symlink_components(requested_output, "output")
    output_dir = requested_output.resolve(strict=False)
    checkout = checkout.resolve()
    doc_root = doc_root.resolve()
    if _is_within(output_dir, checkout) or _is_within(checkout, output_dir):
        raise ReceiptError(
            "output directory must be outside and not contain the checkout"
        )
    if _is_within(output_dir, doc_root) or _is_within(doc_root, output_dir):
        raise ReceiptError(
            "output directory must be outside and not contain the docs tree"
        )
    if must_exist:
        if not output_dir.is_dir():
            raise ReceiptError(
                f"release-asset directory is missing or unsafe: {output_dir}"
            )
    elif output_dir.exists():
        raise ReceiptError(f"refusing to overwrite existing output path: {output_dir}")
    return output_dir


def _validate_checkout(checkout: Path, expected_commit: str) -> tuple[str, str]:
    checkout = checkout.expanduser().resolve()
    if not checkout.is_dir():
        raise ReceiptError(f"checkout is not a directory: {checkout}")
    if run(["git", "rev-parse", "--is-inside-work-tree"], cwd=checkout) != "true":
        raise ReceiptError(f"checkout is not a Git worktree: {checkout}")
    top_level = Path(
        run(["git", "rev-parse", "--show-toplevel"], cwd=checkout)
    ).resolve()
    if top_level != checkout:
        raise ReceiptError(
            f"--checkout must name the worktree root: expected {top_level}, got {checkout}"
        )

    expected_commit = validate_sha(expected_commit, "expected release commit")
    commit = validate_sha(
        run(["git", "rev-parse", "--verify", "HEAD^{commit}"], cwd=checkout),
        "checkout commit",
    )
    if commit != expected_commit:
        raise ReceiptError(
            f"checkout mismatch: expected {expected_commit}, but HEAD is {commit}"
        )
    changes = run(
        ["git", "status", "--porcelain=v1", "--untracked-files=all"], cwd=checkout
    )
    if changes:
        raise ReceiptError("checkout has tracked or untracked changes")
    tree = validate_sha(
        run(
            ["git", "rev-parse", "--verify", f"{expected_commit}^{{tree}}"],
            cwd=checkout,
        ),
        "expected commit tree",
    )
    return commit, tree


def _validate_local_tag_identity(
    checkout: Path, tag: str, expected_tag_object: str, expected_commit: str
) -> None:
    tag = validate_tag(tag)
    expected_tag_object = validate_sha(expected_tag_object, "expected tag object")
    expected_commit = validate_sha(expected_commit, "expected release commit")
    tag_ref = f"refs/tags/{tag}"
    local_object = validate_sha(
        run(["git", "rev-parse", "--verify", tag_ref], cwd=checkout),
        "local tag object",
    )
    if local_object != expected_tag_object:
        raise ReceiptError(
            f"local tag object mismatch: expected {expected_tag_object}, "
            f"found {local_object}"
        )
    local_commit = validate_sha(
        run(["git", "rev-parse", "--verify", f"{tag_ref}^{{commit}}"], cwd=checkout),
        "local peeled tag commit",
    )
    if local_commit != expected_commit:
        raise ReceiptError(
            f"local tag commit mismatch: expected {expected_commit}, found {local_commit}"
        )


def _git_files(checkout: Path, commit: str) -> list[GitFile]:
    output = _run_bytes(
        ["git", "ls-tree", "-r", "-z", "--full-tree", commit], cwd=checkout
    )
    files: list[GitFile] = []
    seen: set[str] = set()
    for record in output.split(b"\0"):
        if not record:
            continue
        try:
            metadata, raw_path = record.split(b"\t", 1)
            mode_text, object_type, object_id = metadata.decode("ascii").split()
            path = raw_path.decode("utf-8")
        except (UnicodeDecodeError, ValueError) as exc:
            raise ReceiptError("malformed or non-UTF-8 Git tree entry") from exc
        _safe_relative_path(path, "Git tree path")
        if object_type != "blob" or mode_text not in {"100644", "100755"}:
            raise ReceiptError(
                f"release source contains unsupported Git entry {mode_text} "
                f"{object_type} {path!r}"
            )
        object_id = validate_sha(object_id, f"blob id for {path}")
        if path in seen:
            raise ReceiptError(f"duplicate Git tree path: {path!r}")
        seen.add(path)
        files.append(
            GitFile(
                path=path,
                mode=0o755 if mode_text == "100755" else 0o644,
                object_id=object_id,
            )
        )
    if not files:
        raise ReceiptError("release source tree has no files")
    return files


def _read_git_blobs(checkout: Path, files: Sequence[GitFile]) -> dict[str, bytes]:
    process = subprocess.Popen(
        ["git", "cat-file", "--batch"],
        cwd=checkout,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    request = "".join(f"{entry.object_id}\n" for entry in files).encode("ascii")
    stdout, stderr = process.communicate(request)
    if process.returncode != 0:
        detail = stderr.decode("utf-8", errors="replace").strip()
        suffix = f": {detail}" if detail else ""
        raise ReceiptError(f"git cat-file --batch failed{suffix}")

    stream = io.BytesIO(stdout)
    blobs: dict[str, bytes] = {}
    for entry in files:
        header = stream.readline().rstrip(b"\n")
        fields = header.split()
        if (
            len(fields) != 3
            or fields[0].decode("ascii", errors="ignore") != entry.object_id
        ):
            raise ReceiptError(f"unexpected git cat-file header for {entry.path!r}")
        if fields[1] != b"blob":
            raise ReceiptError(f"Git object for {entry.path!r} is not a blob")
        try:
            size = int(fields[2])
        except ValueError as exc:
            raise ReceiptError(f"invalid Git blob size for {entry.path!r}") from exc
        data = stream.read(size)
        if len(data) != size or stream.read(1) != b"\n":
            raise ReceiptError(f"truncated Git blob for {entry.path!r}")
        blobs[entry.path] = data
    if stream.read(1):
        raise ReceiptError("unexpected trailing data from git cat-file --batch")
    return blobs


def _gzip_file(source: Path, destination: Path) -> None:
    with source.open("rb") as raw, destination.open("wb") as encoded:
        with gzip.GzipFile(
            filename="", mode="wb", fileobj=encoded, compresslevel=9, mtime=0
        ) as compressed:
            shutil.copyfileobj(raw, compressed)


def _build_source_archive(
    checkout: Path, commit: str, tag: str, destination: Path
) -> None:
    files = _git_files(checkout, commit)
    blobs = _read_git_blobs(checkout, files)
    prefix = f"FormalSLT-{tag}"
    with tempfile.NamedTemporaryFile(
        "wb", prefix="formalslt-source.", suffix=".tar", delete=False
    ) as raw_tar:
        raw_tar_path = Path(raw_tar.name)
    try:
        directories: set[str] = set()
        for entry in files:
            parts = PurePosixPath(entry.path).parts[:-1]
            for depth in range(1, len(parts) + 1):
                directories.add("/".join(parts[:depth]))
        with tarfile.open(raw_tar_path, mode="w", format=tarfile.PAX_FORMAT) as package:
            package.addfile(_tar_info(prefix, directory=True))
            for directory in sorted(directories):
                package.addfile(_tar_info(f"{prefix}/{directory}", directory=True))
            for entry in files:
                data = blobs[entry.path]
                info = _tar_info(
                    f"{prefix}/{entry.path}", directory=False, size=len(data)
                )
                info.mode = entry.mode
                package.addfile(info, io.BytesIO(data))
        _gzip_file(raw_tar_path, destination)
    finally:
        raw_tar_path.unlink(missing_ok=True)


def _validate_archive_member(member: tarfile.TarInfo, prefix: str) -> str | None:
    name = member.name.rstrip("/")
    root = prefix.rstrip("/")
    if name == root:
        if not member.isdir():
            raise ReceiptError("archive root entry is not a directory")
        return None
    required_prefix = f"{root}/"
    if not name.startswith(required_prefix):
        raise ReceiptError(
            f"archive member escapes its top-level prefix: {member.name!r}"
        )
    relative = name[len(required_prefix) :]
    _safe_relative_path(relative, "archive member path")
    if not (member.isdir() or member.isreg()):
        raise ReceiptError(f"archive contains unsupported entry: {member.name!r}")
    return relative


def _verify_source_archive(archive: Path, checkout: Path, commit: str, tag: str) -> int:
    expected_files = _git_files(checkout, commit)
    expected_blobs = _read_git_blobs(checkout, expected_files)
    expected = {entry.path: entry for entry in expected_files}
    observed: set[str] = set()
    prefix = f"FormalSLT-{tag}/"
    with tarfile.open(archive, mode="r:gz") as package:
        for member in package.getmembers():
            relative = _validate_archive_member(member, prefix)
            if relative is None or member.isdir():
                continue
            if relative in observed:
                raise ReceiptError(f"duplicate source archive member: {relative!r}")
            observed.add(relative)
            entry = expected.get(relative)
            if entry is None:
                raise ReceiptError(
                    f"source archive contains non-tree file: {relative!r}"
                )
            if member.mode & 0o777 != entry.mode:
                raise ReceiptError(f"source archive mode mismatch for {relative!r}")
            extracted = package.extractfile(member)
            if extracted is None or extracted.read() != expected_blobs[relative]:
                raise ReceiptError(f"source archive content mismatch for {relative!r}")
    missing = sorted(set(expected) - observed)
    if missing:
        raise ReceiptError(f"source archive is missing Git tree file: {missing[0]!r}")
    return len(observed)


def _scan_docs(doc_root: Path) -> list[DocEntry]:
    original_root = doc_root.expanduser()
    try:
        root_stat = original_root.lstat()
    except OSError as exc:
        raise ReceiptError(
            f"unable to inspect docs tree {original_root}: {exc}"
        ) from exc
    if stat.S_ISLNK(root_stat.st_mode) or not stat.S_ISDIR(root_stat.st_mode):
        raise ReceiptError(f"docs root must be one real directory: {original_root}")
    doc_root = original_root.resolve()
    entries: list[DocEntry] = []

    def visit(directory: Path, relative_parent: PurePosixPath | None = None) -> None:
        try:
            with os.scandir(directory) as scanner:
                children = sorted(scanner, key=lambda entry: entry.name)
        except OSError as exc:
            raise ReceiptError(
                f"unable to scan docs directory {directory}: {exc}"
            ) from exc
        for child in children:
            relative = (
                PurePosixPath(child.name)
                if relative_parent is None
                else relative_parent / child.name
            )
            relative_text = relative.as_posix()
            _safe_relative_path(relative_text, "docs path")
            metadata = child.stat(follow_symlinks=False)
            mode = metadata.st_mode
            source = Path(child.path)
            if stat.S_ISLNK(mode):
                raise ReceiptError(f"docs tree contains symlink: {relative_text!r}")
            if stat.S_ISDIR(mode):
                entries.append(
                    DocEntry(
                        relative_text,
                        source,
                        True,
                        0,
                        metadata.st_mtime_ns,
                        metadata.st_ino,
                    )
                )
                visit(source, relative)
            elif stat.S_ISREG(mode):
                if metadata.st_nlink != 1:
                    raise ReceiptError(
                        f"docs tree contains hardlinked file: {relative_text!r}"
                    )
                entries.append(
                    DocEntry(
                        relative_text,
                        source,
                        False,
                        metadata.st_size,
                        metadata.st_mtime_ns,
                        metadata.st_ino,
                    )
                )
            else:
                raise ReceiptError(
                    f"docs tree contains special file: {relative_text!r}"
                )

    visit(doc_root)
    if not any(not entry.is_directory for entry in entries):
        raise ReceiptError("docs tree has no files")
    return entries


def _read_stable_doc(entry: DocEntry) -> bytes:
    data = entry.source.read_bytes()
    metadata = entry.source.stat(follow_symlinks=False)
    if (
        not stat.S_ISREG(metadata.st_mode)
        or metadata.st_size != entry.size
        or metadata.st_mtime_ns != entry.mtime_ns
        or metadata.st_ino != entry.inode
        or metadata.st_nlink != 1
        or len(data) != entry.size
    ):
        raise ReceiptError(f"docs file changed while packaging: {entry.path!r}")
    return data


def _validate_staged_docs(doc_root: Path, commit: str) -> list[DocEntry]:
    entries = _scan_docs(doc_root)
    files = {entry.path: entry for entry in entries if not entry.is_directory}
    missing = [path for path in REQUIRED_DOC_PATHS if path not in files]
    if missing:
        raise ReceiptError("staged docs are incomplete: " + ", ".join(missing))

    html: dict[str, str] = {}
    for path, entry in files.items():
        if path.endswith(".html"):
            try:
                html[path] = _read_stable_doc(entry).decode("utf-8")
            except UnicodeDecodeError as exc:
                raise ReceiptError(f"staged HTML is not UTF-8: {path!r}") from exc
    if SITE_MARKER not in html["index.html"]:
        raise ReceiptError(
            "staged docs root is missing the FormalSLT research-site marker"
        )
    if f"/tree/{commit}" not in html["index.html"]:
        raise ReceiptError("staged docs root is not pinned to the expected commit")
    if f"/blob/{commit}/" not in html["theorems/index.html"]:
        raise ReceiptError("staged theorem index is not pinned to the expected commit")
    for path, contents in html.items():
        if SOURCE_REF_TOKEN in contents:
            raise ReceiptError(
                f"staged HTML contains an unresolved source token: {path!r}"
            )
        for source_ref in SOURCE_URL_RE.findall(contents):
            if source_ref != commit:
                raise ReceiptError(
                    f"staged HTML contains a FormalSLT source link not pinned to "
                    f"{commit}: {path!r} uses {source_ref!r}"
                )
    return entries


def _tar_info(name: str, *, directory: bool, size: int = 0) -> tarfile.TarInfo:
    info = tarfile.TarInfo(name + ("/" if directory and not name.endswith("/") else ""))
    info.type = tarfile.DIRTYPE if directory else tarfile.REGTYPE
    info.mode = 0o755 if directory else 0o644
    info.size = 0 if directory else size
    info.mtime = 0
    info.uid = 0
    info.gid = 0
    info.uname = ""
    info.gname = ""
    return info


def _build_docs_archive(
    entries: Sequence[DocEntry], tag: str, destination: Path
) -> None:
    prefix = f"FormalSLT-{tag}-docs"
    with tempfile.NamedTemporaryFile(
        "wb", prefix="formalslt-docs.", suffix=".tar", delete=False
    ) as raw_tar:
        raw_tar_path = Path(raw_tar.name)
    try:
        with tarfile.open(raw_tar_path, mode="w", format=tarfile.PAX_FORMAT) as package:
            package.addfile(_tar_info(prefix, directory=True))
            for entry in entries:
                archive_path = f"{prefix}/{entry.path}"
                if entry.is_directory:
                    package.addfile(_tar_info(archive_path, directory=True))
                else:
                    data = _read_stable_doc(entry)
                    package.addfile(
                        _tar_info(archive_path, directory=False, size=len(data)),
                        io.BytesIO(data),
                    )
        _gzip_file(raw_tar_path, destination)
    finally:
        raw_tar_path.unlink(missing_ok=True)


def _verify_docs_archive(archive: Path, doc_root: Path, commit: str, tag: str) -> int:
    entries = _validate_staged_docs(doc_root, commit)
    expected = {entry.path: entry for entry in entries if not entry.is_directory}
    observed: set[str] = set()
    prefix = f"FormalSLT-{tag}-docs/"
    with tarfile.open(archive, mode="r:gz") as package:
        for member in package.getmembers():
            relative = _validate_archive_member(member, prefix)
            if relative is None or member.isdir():
                continue
            if relative in observed:
                raise ReceiptError(f"duplicate docs archive member: {relative!r}")
            observed.add(relative)
            entry = expected.get(relative)
            if entry is None:
                raise ReceiptError(
                    f"docs archive contains unexpected file: {relative!r}"
                )
            if member.mode & 0o777 != 0o644:
                raise ReceiptError(f"docs archive mode mismatch for {relative!r}")
            extracted = package.extractfile(member)
            if extracted is None or extracted.read() != _read_stable_doc(entry):
                raise ReceiptError(f"docs archive content mismatch for {relative!r}")
    missing = sorted(set(expected) - observed)
    if missing:
        raise ReceiptError(f"docs archive is missing staged file: {missing[0]!r}")
    return len(observed)


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _files_equal(first: Path, second: Path) -> bool:
    if first.stat().st_size != second.stat().st_size:
        return False
    with first.open("rb") as first_stream, second.open("rb") as second_stream:
        while True:
            first_chunk = first_stream.read(1024 * 1024)
            second_chunk = second_stream.read(1024 * 1024)
            if first_chunk != second_chunk:
                return False
            if not first_chunk:
                return True


def _asset_names(tag: str) -> tuple[str, str, str, str]:
    validate_tag(tag)
    return (
        f"formalslt-{tag}-source.tar.gz",
        f"formalslt-{tag}-docs.tar.gz",
        f"formalslt-{tag}-release-assets.json",
        "SHA256SUMS",
    )


def _read_commit_file(checkout: Path, commit: str, path: str) -> bytes:
    _safe_relative_path(path, "commit metadata path")
    return _run_bytes(["git", "show", f"{commit}:{path}"], cwd=checkout)


def _read_commit_metadata(
    checkout: Path, commit: str
) -> tuple[str, str, str, str | None]:
    try:
        toolchain_text = _read_commit_file(checkout, commit, "lean-toolchain").decode(
            "utf-8"
        )
    except UnicodeDecodeError as exc:
        raise ReceiptError("lean-toolchain at the release commit is not UTF-8") from exc
    toolchain_lines = [line.strip() for line in toolchain_text.splitlines()]
    if len(toolchain_lines) != 1 or not toolchain_lines[0]:
        raise ReceiptError(
            "lean-toolchain at the release commit must contain one nonempty line"
        )

    try:
        lake_manifest = json.loads(
            _read_commit_file(checkout, commit, "lake-manifest.json").decode("utf-8")
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ReceiptError(
            "lake-manifest.json at the release commit is invalid"
        ) from exc
    packages = (
        lake_manifest.get("packages") if isinstance(lake_manifest, dict) else None
    )
    if not isinstance(packages, list):
        raise ReceiptError("release commit lake-manifest.json has no package list")
    matches = [
        package
        for package in packages
        if isinstance(package, dict) and package.get("name") == "mathlib"
    ]
    if len(matches) != 1:
        raise ReceiptError(
            "release commit lake-manifest.json must contain exactly one mathlib package"
        )
    package = matches[0]
    if package.get("type") != "git":
        raise ReceiptError("Mathlib must be pinned as a git dependency")
    mathlib_revision = validate_sha(
        str(package.get("rev", "")), "pinned Mathlib revision"
    )
    mathlib_url = package.get("url")
    if not isinstance(mathlib_url, str) or not mathlib_url:
        raise ReceiptError("the pinned Mathlib package has no repository URL")
    mathlib_input_revision = package.get("inputRev")
    if mathlib_input_revision is not None and not isinstance(
        mathlib_input_revision, str
    ):
        raise ReceiptError("the Mathlib input revision must be a string when present")
    return (
        toolchain_lines[0],
        mathlib_url,
        mathlib_revision,
        mathlib_input_revision,
    )


def _expected_manifest(
    *,
    checkout: Path,
    repository_url: str,
    tag: str,
    tag_object: str,
    commit: str,
    tree: str,
    source_archive: Path,
    source_count: int,
    docs_archive: Path,
    docs_count: int,
) -> dict[str, Any]:
    (
        toolchain,
        mathlib_url,
        mathlib_revision,
        mathlib_input_revision,
    ) = _read_commit_metadata(checkout, commit)
    return {
        "schema": MANIFEST_SCHEMA,
        "verification_scope": "local_exact_commit_and_staged_docs_packaging_only",
        "tag": tag,
        "repository_url": repository_url,
        "tag_object": tag_object,
        "resolved_commit": commit,
        "resolved_tree": tree,
        "lean_toolchain": toolchain,
        "mathlib": {
            "repository_url": mathlib_url,
            "revision": mathlib_revision,
            "input_revision": mathlib_input_revision,
        },
        "assets": {
            "source_archive": {
                "filename": source_archive.name,
                "sha256": _sha256(source_archive),
                "size_bytes": source_archive.stat().st_size,
                "file_count": source_count,
            },
            "docs_archive": {
                "filename": docs_archive.name,
                "sha256": _sha256(docs_archive),
                "size_bytes": docs_archive.stat().st_size,
                "file_count": docs_count,
            },
        },
        "does_not_assert": [
            "the public tag exists or is immutable",
            "continuous integration succeeded",
            "a GitHub Release exists",
            "the documentation archive is deployed",
            "an archival deposit or DOI exists",
        ],
    }


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(_canonical_json_text(payload), encoding="utf-8")


def _canonical_json_text(payload: dict[str, Any]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def _read_bounded_utf8(path: Path, *, limit: int, description: str) -> str:
    try:
        with path.open("rb") as stream:
            raw = stream.read(limit + 1)
    except OSError as exc:
        raise ReceiptError(f"unable to read {description} {path}: {exc}") from exc
    if len(raw) > limit:
        raise ReceiptError(f"{description} exceeds {limit} bytes")
    try:
        return raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ReceiptError(f"{description} is not UTF-8: {path}") from exc


def _checksums_text(paths: Sequence[Path]) -> str:
    return "".join(f"{_sha256(path)}  {path.name}\n" for path in sorted(paths))


def _load_manifest(path: Path) -> tuple[dict[str, Any], str]:
    text = _read_bounded_utf8(
        path,
        limit=MAX_MANIFEST_BYTES,
        description="release-asset manifest",
    )
    try:
        payload = json.loads(text)
    except json.JSONDecodeError as exc:
        raise ReceiptError(f"release-asset manifest is invalid JSON: {exc}") from exc
    if not isinstance(payload, dict):
        raise ReceiptError("release-asset manifest must be a JSON object")
    if text != _canonical_json_text(payload):
        raise ReceiptError("release-asset manifest is not canonical JSON")
    return payload, text


def verify_bundle(
    *,
    checkout: Path,
    repository_url: str,
    tag: str,
    expected_tag_object: str,
    expected_commit: str,
    doc_root: Path,
    output_dir: Path,
) -> dict[str, Any]:
    tag = validate_tag(tag)
    tag_object = validate_sha(expected_tag_object, "expected tag object")
    commit, tree = _validate_checkout(checkout, expected_commit)
    _validate_local_tag_identity(checkout, tag, tag_object, commit)
    output_dir = _validate_output_location(
        output_dir, checkout=checkout, doc_root=doc_root, must_exist=True
    )
    source_name, docs_name, manifest_name, sums_name = _asset_names(tag)
    expected_names = {source_name, docs_name, manifest_name, sums_name}
    observed_names = {path.name for path in output_dir.iterdir()}
    if observed_names != expected_names or any(
        not path.is_file() or path.is_symlink() for path in output_dir.iterdir()
    ):
        raise ReceiptError(
            "release-asset directory must contain exactly the four expected regular files"
        )

    source_archive = output_dir / source_name
    docs_archive = output_dir / docs_name
    manifest_path = output_dir / manifest_name
    sums_path = output_dir / sums_name
    source_files = _git_files(checkout, commit)
    docs_entries = _validate_staged_docs(doc_root, commit)
    with tempfile.TemporaryDirectory(prefix="formalslt-release-verify-") as temporary:
        expected_source = Path(temporary) / source_name
        expected_docs = Path(temporary) / docs_name
        _build_source_archive(checkout, commit, tag, expected_source)
        _build_docs_archive(docs_entries, tag, expected_docs)
        if not _files_equal(source_archive, expected_source):
            raise ReceiptError(
                "source archive is not the canonical exact-commit archive"
            )
        if not _files_equal(docs_archive, expected_docs):
            raise ReceiptError("docs archive is not the canonical staged-docs archive")
    source_count = len(source_files)
    docs_count = sum(not entry.is_directory for entry in docs_entries)
    expected_manifest = _expected_manifest(
        checkout=checkout,
        repository_url=repository_url,
        tag=tag,
        tag_object=tag_object,
        commit=commit,
        tree=tree,
        source_archive=source_archive,
        source_count=source_count,
        docs_archive=docs_archive,
        docs_count=docs_count,
    )
    manifest, manifest_text = _load_manifest(manifest_path)
    if manifest_text != _canonical_json_text(expected_manifest):
        raise ReceiptError("release-asset manifest does not match the exact inputs")
    expected_sums = _checksums_text([source_archive, docs_archive, manifest_path])
    if _read_bounded_utf8(
        sums_path,
        limit=MAX_CHECKSUMS_BYTES,
        description="SHA256SUMS",
    ) != expected_sums:
        raise ReceiptError("SHA256SUMS does not match the packaged assets")
    _validate_checkout(checkout, commit)
    _validate_local_tag_identity(checkout, tag, tag_object, commit)
    return manifest


def build_bundle(
    *,
    checkout: Path,
    repository_url: str,
    tag: str,
    expected_tag_object: str,
    expected_commit: str,
    doc_root: Path,
    output_dir: Path,
) -> dict[str, Any]:
    tag = validate_tag(tag)
    tag_object = validate_sha(expected_tag_object, "expected tag object")
    commit, tree = _validate_checkout(checkout, expected_commit)
    _validate_local_tag_identity(checkout, tag, tag_object, commit)
    doc_root = doc_root.expanduser()
    entries = _validate_staged_docs(doc_root, commit)
    output_dir = _validate_output_location(
        output_dir, checkout=checkout, doc_root=doc_root, must_exist=False
    )
    output_dir.parent.mkdir(parents=True, exist_ok=True)
    source_name, docs_name, manifest_name, sums_name = _asset_names(tag)

    with tempfile.TemporaryDirectory(
        prefix=f".{output_dir.name}.", dir=output_dir.parent
    ) as temporary:
        staging = Path(temporary) / "bundle"
        staging.mkdir()
        source_archive = staging / source_name
        docs_archive = staging / docs_name
        manifest_path = staging / manifest_name
        sums_path = staging / sums_name

        _build_source_archive(checkout, commit, tag, source_archive)
        source_count = _verify_source_archive(source_archive, checkout, commit, tag)
        _build_docs_archive(entries, tag, docs_archive)
        docs_count = _verify_docs_archive(docs_archive, doc_root, commit, tag)
        manifest = _expected_manifest(
            checkout=checkout,
            repository_url=repository_url,
            tag=tag,
            tag_object=tag_object,
            commit=commit,
            tree=tree,
            source_archive=source_archive,
            source_count=source_count,
            docs_archive=docs_archive,
            docs_count=docs_count,
        )
        _write_json(manifest_path, manifest)
        sums_path.write_text(
            _checksums_text([source_archive, docs_archive, manifest_path]),
            encoding="utf-8",
        )
        verify_bundle(
            checkout=checkout,
            repository_url=repository_url,
            tag=tag,
            expected_tag_object=tag_object,
            expected_commit=commit,
            doc_root=doc_root,
            output_dir=staging,
        )

        _validate_output_location(
            output_dir, checkout=checkout, doc_root=doc_root, must_exist=False
        )
        try:
            staging.rename(output_dir)
        except FileExistsError as exc:
            raise ReceiptError(
                f"refusing to overwrite existing output path: {output_dir}"
            ) from exc
    return manifest


def _add_common_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--tag", required=True)
    parser.add_argument("--expected-tag-object", required=True)
    parser.add_argument("--expected-commit", required=True)
    parser.add_argument("--checkout", type=Path, default=Path.cwd())
    parser.add_argument("--doc-root", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument(
        "--repository-url",
        default=os.environ.get("FORMALSLT_REPOSITORY_URL", DEFAULT_REPOSITORY_URL),
    )


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    build = subparsers.add_parser("build", help="create a new verified bundle")
    verify = subparsers.add_parser("verify", help="verify an existing bundle")
    _add_common_arguments(build)
    _add_common_arguments(verify)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    if not args.repository_url:
        print(
            "ERROR: release-asset packaging refused: repository URL is empty",
            file=sys.stderr,
        )
        return 1
    try:
        operation = build_bundle if args.command == "build" else verify_bundle
        manifest = operation(
            checkout=args.checkout,
            repository_url=args.repository_url,
            tag=args.tag,
            expected_tag_object=args.expected_tag_object,
            expected_commit=args.expected_commit,
            doc_root=args.doc_root,
            output_dir=args.output_dir,
        )
    except (ReceiptError, OSError, tarfile.TarError) as exc:
        print(f"ERROR: release-asset packaging refused: {exc}", file=sys.stderr)
        return 1
    print(
        f"release assets {args.command} verified: {manifest['tag']} -> "
        f"{manifest['resolved_commit']} ({args.output_dir})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
