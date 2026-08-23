#!/usr/bin/env python3
"""Build or verify the frozen controlled-queue OSF registration binding.

The output binds the immutable protocol commit to the exact, already-green
prospective trace and receipt tools.  It contains no OSF registration id,
registration time, beacon response, seed, trace, or endpoint.  This script is
offline: it invokes only local Git and never performs registration, fetches a
beacon, or generates prospective data.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
import unicodedata
from pathlib import Path
from typing import Any, NoReturn, Sequence


ROOT = Path(__file__).resolve().parents[1]

PROTOCOL_PATH = "applications/controlled_queue/structured-ope-protocol-v1.json"
PROTOCOL_COMMIT = "65d8d56245e3862821fce09bcf30b017f03d2baa"
PROTOCOL_TREE = "8dbe01780fd2cec94b8b954f6ef1c8c210afee53"
PROTOCOL_SHA256 = "070519615ba7cdaf0198a72a03ab6f691a7ff9b37c2eaa97a363d7fd4c3bf153"

CODE_FREEZE_COMMIT = "6c3f7de49d545be3e6bcfbb32f70b4aa86ef55de"
CODE_FREEZE_TREE = "12248252ab3dc2bcd549b61f2678d40618fb1c7e"

BINDING_SCHEMA = "controlled-queue-prospective-code-freeze-binding-v1"
BINDING_STATUS = "PUBLIC OSF CODE FREEZE BINDING"
EXPECTED_BINDING_BYTES = 1_501
EXPECTED_BINDING_SHA256 = (
    "9dea4b601331717358bf0b9e8610384a4f7fbe71c332c563700ec91dd3a2064e"
)
BINDING_PATH = (
    "applications/controlled_queue/prospective/evidence/"
    "code-freeze-binding-v1.json"
)
DEFAULT_OUTPUT = ROOT / BINDING_PATH

CODE_FILES = (
    ("trace_generator", "scripts/generate_controlled_queue_prospective_trace.py"),
    ("trace_verifier", "scripts/verify_controlled_queue_prospective_trace.py"),
    ("receipt_generator", "scripts/generate_controlled_queue_prospective_receipt.py"),
    ("receipt_verifier", "scripts/verify_controlled_queue_prospective_receipt.py"),
)

FRESH_OUTPUT_PATHS = (
    "applications/controlled_queue/prospective/generated/structured-ope-trace-v1.bin",
    "applications/controlled_queue/prospective/generated/structured-ope-trace-v1-counts.json",
    "applications/controlled_queue/prospective/generated/structured-ope-trace-v1-manifest.json",
    "applications/controlled_queue/prospective/generated/structured-ope-receipt-v1.json",
    "applications/controlled_queue/prospective/generated/structured-ope-receipt-v1-manifest.json",
    "FormalSLT/Applications/ControlledQueueProspectiveStructuredOPEData.lean",
)

OID_RE = re.compile(r"[0-9a-f]{40}\Z")


class RegistrationBindingError(RuntimeError):
    """Fail-closed registration-binding error."""


def _fail(message: str) -> NoReturn:
    raise RegistrationBindingError(message)


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, indent=2, sort_keys=True, separators=(",", ": ")) + "\n"
    ).encode("utf-8")


def _oid(value: str, description: str) -> str:
    if OID_RE.fullmatch(value) is None:
        _fail(f"{description} must be a full lowercase 40-character Git object id")
    return value


def _run_git(arguments: Sequence[str], *, root: Path = ROOT) -> bytes:
    try:
        completed = subprocess.run(
            [
                "/usr/bin/git",
                "--no-replace-objects",
                "--no-lazy-fetch",
                "-C",
                str(root),
                *arguments,
            ],
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            env={
                "GIT_CONFIG_NOSYSTEM": "1",
                "GIT_TERMINAL_PROMPT": "0",
                "LC_ALL": "C",
                "PATH": "/usr/bin:/bin",
            },
        )
    except OSError as error:
        raise RegistrationBindingError(
            f"cannot execute local Git object check: {error}"
        ) from error
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        suffix = f": {detail}" if detail else ""
        _fail(f"Git verification failed for {' '.join(arguments)}{suffix}")
    return completed.stdout


def _git_text(arguments: Sequence[str], *, root: Path = ROOT) -> str:
    return _run_git(arguments, root=root).decode("utf-8").strip()


def _reject_symlink_components(path: Path, description: str) -> None:
    absolute = path.expanduser().absolute()
    current = Path(absolute.anchor)
    for component in absolute.parts[1:]:
        current /= component
        try:
            metadata = current.lstat()
        except FileNotFoundError:
            break
        except OSError as error:
            raise RegistrationBindingError(
                f"unable to inspect {description} path {current}: {error}"
            ) from error
        if stat.S_ISLNK(metadata.st_mode):
            _fail(f"{description} path contains a symbolic link: {current}")


def _read_regular(path: Path, description: str) -> bytes:
    _reject_symlink_components(path, description)
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except FileNotFoundError as error:
        raise RegistrationBindingError(f"missing {description}: {path}") from error
    try:
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode):
            _fail(f"{description} is not a regular file: {path}")
        with os.fdopen(descriptor, "rb") as handle:
            return handle.read()
    except Exception:
        try:
            os.close(descriptor)
        except OSError:
            pass
        raise


def _verify_commit_tree(commit: str, tree: str, description: str, *, root: Path) -> None:
    _oid(commit, f"{description} commit")
    _oid(tree, f"{description} tree")
    object_type = _git_text(("cat-file", "-t", commit), root=root)
    if object_type != "commit":
        _fail(f"{description} object is not a Git commit")
    actual_tree = _git_text(("show", "-s", "--format=%T", commit), root=root)
    if actual_tree != tree:
        _fail(f"{description} tree mismatch: expected {tree}, found {actual_tree}")


def _verify_current_bytes(
    path_text: str, frozen_raw: bytes, description: str, *, root: Path
) -> None:
    current_raw = _read_regular(root / path_text, description)
    if current_raw != frozen_raw:
        _fail(f"current {description} bytes differ from the frozen Git object")


def _verify_fresh_outputs_absent(*, root: Path) -> None:
    for path_text in FRESH_OUTPUT_PATHS:
        path = root / path_text
        if path.exists() or path.is_symlink():
            _fail(f"prospective output already exists: {path_text}")
        _reject_symlink_components(path, f"prospective output {path_text}")


def build_binding(*, root: Path = ROOT) -> dict[str, Any]:
    """Reconstruct the exact pre-registration binding from local Git objects."""

    root = root.resolve()
    _verify_fresh_outputs_absent(root=root)
    protocol_commit = _oid(PROTOCOL_COMMIT, "protocol commit")
    protocol_tree = _oid(PROTOCOL_TREE, "protocol tree")
    freeze_commit = _oid(CODE_FREEZE_COMMIT, "code-freeze commit")
    freeze_tree = _git_text(
        ("show", "-s", "--format=%T", freeze_commit), root=root
    )
    if freeze_tree != CODE_FREEZE_TREE:
        _fail(
            "code-freeze tree mismatch: "
            f"expected {CODE_FREEZE_TREE}, found {freeze_tree}"
        )
    if protocol_commit == freeze_commit:
        _fail("the code-freeze commit must postdate the protocol commit")

    _verify_commit_tree(protocol_commit, protocol_tree, "protocol", root=root)
    _verify_commit_tree(freeze_commit, freeze_tree, "code freeze", root=root)
    _run_git(("merge-base", "--is-ancestor", protocol_commit, freeze_commit), root=root)

    protocol_raw = _run_git(
        ("show", f"{protocol_commit}:{PROTOCOL_PATH}"), root=root
    )
    if sha256_bytes(protocol_raw) != PROTOCOL_SHA256:
        _fail("protocol Git bytes do not match the frozen protocol SHA-256")
    _verify_current_bytes(PROTOCOL_PATH, protocol_raw, "protocol", root=root)

    code_rows: list[dict[str, Any]] = []
    for role, path_text in CODE_FILES:
        raw = _run_git(("show", f"{freeze_commit}:{path_text}"), root=root)
        _verify_current_bytes(path_text, raw, f"code file {role}", root=root)
        code_rows.append(
            {
                "bytes": len(raw),
                "path": path_text,
                "role": role,
                "sha256": sha256_bytes(raw),
            }
        )

    return {
        "artifact_status": BINDING_STATUS,
        "code_files": code_rows,
        "code_freeze": {"commit": freeze_commit, "tree": freeze_tree},
        "protocol": {
            "bytes": len(protocol_raw),
            "commit": protocol_commit,
            "path": PROTOCOL_PATH,
            "sha256": sha256_bytes(protocol_raw),
            "tree": protocol_tree,
        },
        "schema_version": BINDING_SCHEMA,
    }


def expected_binding_bytes(*, root: Path = ROOT) -> bytes:
    raw = canonical_json_bytes(build_binding(root=root))
    if b"registration_id" in raw:
        _fail("pre-registration binding must not contain registration_id")
    if len(raw) != EXPECTED_BINDING_BYTES:
        _fail(
            "registration-binding byte length drift: "
            f"expected {EXPECTED_BINDING_BYTES}, found {len(raw)}"
        )
    digest = sha256_bytes(raw)
    if digest != EXPECTED_BINDING_SHA256:
        _fail(
            "registration-binding SHA-256 drift: "
            f"expected {EXPECTED_BINDING_SHA256}, found {digest}"
        )
    return raw


def validate_existing_consumers(raw: bytes, *, root: Path = ROOT) -> None:
    """Require all existing production binding consumers to accept the bytes."""

    root = root.resolve()
    if root != ROOT.resolve():
        _fail("existing-consumer validation requires the repository checkout")
    protocol_raw = _read_regular(root / PROTOCOL_PATH, "protocol")
    binding = json.loads(raw)

    def load_frozen(path_text: str) -> dict[str, Any]:
        source = _run_git(("show", f"{CODE_FREEZE_COMMIT}:{path_text}"), root=root)
        _verify_current_bytes(path_text, source, f"consumer source {path_text}", root=root)
        namespace: dict[str, Any] = {
            "__file__": str(root / path_text),
            "__name__": "<frozen_binding_consumer>",
            "__package__": None,
        }
        exec(compile(source, str(root / path_text), "exec"), namespace)
        _verify_current_bytes(path_text, source, f"consumer source {path_text}", root=root)
        return namespace

    try:
        trace_generator = load_frozen(
            "scripts/generate_controlled_queue_prospective_trace.py"
        )
        trace_generator["validate_osf_binding"](raw, protocol_raw, root=root)

        trace_verifier = load_frozen(
            "scripts/verify_controlled_queue_prospective_trace.py"
        )
        trace_verifier["_verify_binding"](binding, protocol_raw)

        receipt_verifier = load_frozen(
            "scripts/verify_controlled_queue_prospective_receipt.py"
        )
        receipt_verifier["_validate_code_freeze_binding"](binding, protocol_raw)
    except RegistrationBindingError:
        raise
    except Exception as error:
        raise RegistrationBindingError(
            f"an existing binding consumer rejected the handoff: {error}"
        ) from error


def _validate_output_path(path: Path, *, root: Path = ROOT) -> Path:
    requested = path.expanduser().absolute()
    _reject_symlink_components(requested, "output")
    expected = (root / BINDING_PATH).resolve(strict=False)
    actual = requested.resolve(strict=False)
    if actual != expected:
        _fail(f"output path must be exactly {expected}")
    return actual


def _directory_matches_path(descriptor: int, path: Path) -> bool:
    opened = os.fstat(descriptor)
    try:
        current = os.stat(path, follow_symlinks=False)
    except FileNotFoundError:
        return False
    return opened.st_dev == current.st_dev and opened.st_ino == current.st_ino


def _has_output_alias_at(descriptor: int, target_name: str) -> bool:
    target_key = _path_identity(target_name)
    return any(_path_identity(name) == target_key for name in os.listdir(descriptor))


def _read_at(descriptor: int, name: str) -> bytes:
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    file_descriptor = os.open(name, flags, dir_fd=descriptor)
    try:
        metadata = os.fstat(file_descriptor)
        if not stat.S_ISREG(metadata.st_mode):
            _fail(f"created binding is not a regular file: {name}")
        with os.fdopen(file_descriptor, "rb") as handle:
            return handle.read()
    except Exception:
        try:
            os.close(file_descriptor)
        except OSError:
            pass
        raise


def _write_exclusive(path: Path, raw: bytes) -> None:
    _reject_symlink_components(path, "output")
    path.parent.mkdir(parents=True, exist_ok=True)
    _reject_symlink_components(path, "output")
    parent_flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    parent_flags |= getattr(os, "O_NOFOLLOW", 0)
    parent_descriptor = os.open(path.parent, parent_flags)
    temporary_name = f".{path.name}.{os.getpid()}.tmp"
    temporary_created = False
    final_created = False
    publication_verified = False
    try:
        if not _directory_matches_path(parent_descriptor, path.parent):
            _fail(f"output directory changed while opening binding path: {path.parent}")
        flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
        flags |= getattr(os, "O_NOFOLLOW", 0)
        descriptor = os.open(
            temporary_name,
            flags,
            0o644,
            dir_fd=parent_descriptor,
        )
        temporary_created = True
        with os.fdopen(descriptor, "wb") as handle:
            os.fchmod(handle.fileno(), 0o644)
            handle.write(raw)
            handle.flush()
            os.fsync(handle.fileno())
        if not _directory_matches_path(parent_descriptor, path.parent):
            _fail(f"output directory changed before binding publication: {path.parent}")
        if _has_output_alias_at(parent_descriptor, path.name):
            _fail(f"refusing to overwrite or alias an existing binding: {path}")
        try:
            os.link(
                temporary_name,
                path.name,
                src_dir_fd=parent_descriptor,
                dst_dir_fd=parent_descriptor,
                follow_symlinks=False,
            )
            final_created = True
        except FileExistsError as error:
            raise RegistrationBindingError(
                f"refusing to overwrite existing binding: {path}"
            ) from error
        os.fsync(parent_descriptor)
        if not _directory_matches_path(parent_descriptor, path.parent):
            _fail(f"output directory changed during binding publication: {path.parent}")
        if _read_at(parent_descriptor, path.name) != raw:
            _fail(f"created registration binding differs from expected bytes: {path}")
        if not _directory_matches_path(parent_descriptor, path.parent):
            _fail(f"output directory changed after binding publication: {path.parent}")
        publication_verified = True
    finally:
        if temporary_created:
            try:
                os.unlink(temporary_name, dir_fd=parent_descriptor)
            except FileNotFoundError:
                pass
        if final_created and (
            not publication_verified
            or not _directory_matches_path(parent_descriptor, path.parent)
        ):
            try:
                os.unlink(path.name, dir_fd=parent_descriptor)
            except FileNotFoundError:
                pass
        os.close(parent_descriptor)


def _path_identity(name: str) -> str:
    return unicodedata.normalize("NFC", name).casefold()


def check_binding(path: Path, expected: bytes) -> bool:
    try:
        actual = _read_regular(path, "registration binding")
    except RegistrationBindingError as error:
        print(str(error), file=sys.stderr)
        return False
    if actual != expected:
        print(f"stale registration binding: {path}", file=sys.stderr)
        return False
    return True


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true", help="write once without overwrite")
    mode.add_argument("--check", action="store_true", help="verify byte-identical binding output")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        output = _validate_output_path(args.output)
        expected = expected_binding_bytes()
        validate_existing_consumers(expected)
        _verify_fresh_outputs_absent(root=ROOT)
        if args.check:
            if not check_binding(output, expected):
                return 1
            _verify_fresh_outputs_absent(root=ROOT)
            print(
                "controlled-queue prospective registration binding is current: "
                f"{len(expected)} bytes, sha256={sha256_bytes(expected)}; "
                f"protocol={PROTOCOL_COMMIT}/{PROTOCOL_TREE}; "
                f"code_freeze={CODE_FREEZE_COMMIT}/{CODE_FREEZE_TREE}; "
                "registration_id=ABSENT; fresh_outputs=ABSENT; "
                "PRE-REGISTRATION ONLY"
            )
            return 0
        _write_exclusive(output, expected)
        _verify_fresh_outputs_absent(root=ROOT)
        if not check_binding(output, expected):
            _fail("created registration binding failed its byte-for-byte reread")
        print(
            "wrote controlled-queue prospective registration binding: "
            f"{output} ({len(expected)} bytes, sha256={sha256_bytes(expected)}); "
            f"protocol={PROTOCOL_COMMIT}/{PROTOCOL_TREE}; "
            f"code_freeze={CODE_FREEZE_COMMIT}/{CODE_FREEZE_TREE}; "
            "registration_id=ABSENT; fresh_outputs=ABSENT; "
            "PRE-REGISTRATION ONLY"
        )
        return 0
    except RegistrationBindingError as error:
        print(f"controlled-queue registration binding error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
