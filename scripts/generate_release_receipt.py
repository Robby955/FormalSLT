#!/usr/bin/env python3
"""Write a fail-closed receipt for an exact FormalSLT tag checkout.

The receipt certifies tag identity and records the source environment only. It
does not certify a CI result, a GitHub Release, a DOI, or a downstream build.
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import re
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Sequence


TAG_RE = re.compile(r"^v[0-9]+\.[0-9]+\.[0-9]+(?:[.-][0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*)?$")
SHA_RE = re.compile(r"^[0-9a-f]{40}$")
DEFAULT_REPOSITORY_URL = "https://github.com/Robby955/FormalSLT.git"


class ReceiptError(RuntimeError):
    """A condition that prevents an exact-tag receipt from being issued."""


def run(command: Sequence[str], *, cwd: Path | None = None) -> str:
    completed = subprocess.run(
        command,
        cwd=cwd,
        check=False,
        capture_output=True,
        text=True,
    )
    if completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip()
        suffix = f": {detail}" if detail else ""
        raise ReceiptError(f"command failed ({' '.join(command)}){suffix}")
    return completed.stdout.strip()


def validate_sha(value: str, description: str) -> str:
    if not SHA_RE.fullmatch(value):
        raise ReceiptError(f"{description} is not one full SHA-1 commit/object id: {value!r}")
    return value


def resolve_remote_tag(repository_url: str, tag: str) -> tuple[str, str]:
    tag_ref = f"refs/tags/{tag}"
    peeled_ref = f"{tag_ref}^{{}}"
    output = run(["git", "ls-remote", repository_url, tag_ref, peeled_ref])

    rows: dict[str, list[str]] = {}
    for line in output.splitlines():
        fields = line.split()
        if len(fields) != 2:
            raise ReceiptError(f"malformed remote-tag row: {line!r}")
        sha, ref = fields
        if ref not in {tag_ref, peeled_ref}:
            raise ReceiptError(f"unexpected remote-tag ref: {ref}")
        rows.setdefault(ref, []).append(validate_sha(sha, f"object for {ref}"))

    tag_objects = rows.get(tag_ref, [])
    if not tag_objects:
        raise ReceiptError(f"remote tag {tag} does not exist at {repository_url}")
    if len(tag_objects) != 1:
        raise ReceiptError(f"remote tag query for {tag} was ambiguous")

    peeled_objects = rows.get(peeled_ref, [])
    if len(peeled_objects) > 1:
        raise ReceiptError(f"peeled remote tag query for {tag} was ambiguous")
    resolved_commit = peeled_objects[0] if peeled_objects else tag_objects[0]
    return tag_objects[0], resolved_commit


def read_toolchain(checkout: Path) -> str:
    path = checkout / "lean-toolchain"
    try:
        lines = [line.strip() for line in path.read_text(encoding="utf-8").splitlines()]
    except OSError as exc:
        raise ReceiptError(f"unable to read {path}: {exc}") from exc
    if len(lines) != 1 or not lines[0]:
        raise ReceiptError(f"{path} must contain exactly one nonempty toolchain line")
    return lines[0]


def read_mathlib_pin(checkout: Path) -> tuple[str, str, str | None]:
    path = checkout / "lake-manifest.json"
    try:
        manifest = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ReceiptError(f"unable to read {path}: {exc}") from exc

    packages = manifest.get("packages")
    if not isinstance(packages, list):
        raise ReceiptError(f"{path} has no package list")
    matches = [
        package
        for package in packages
        if isinstance(package, dict) and package.get("name") == "mathlib"
    ]
    if len(matches) != 1:
        raise ReceiptError(f"{path} must contain exactly one mathlib package")

    package = matches[0]
    if package.get("type") != "git":
        raise ReceiptError("mathlib must be pinned as a git dependency")
    revision = validate_sha(str(package.get("rev", "")), "pinned Mathlib revision")
    url = package.get("url")
    if not isinstance(url, str) or not url:
        raise ReceiptError("the pinned Mathlib package has no repository URL")
    input_revision = package.get("inputRev")
    if input_revision is not None and not isinstance(input_revision, str):
        raise ReceiptError("the Mathlib input revision must be a string when present")
    return url, revision, input_revision


def infer_run_url(environment: dict[str, str]) -> str | None:
    explicit = environment.get("FORMALSLT_RUN_URL", "").strip()
    if explicit:
        return explicit
    server = environment.get("GITHUB_SERVER_URL", "").rstrip("/")
    repository = environment.get("GITHUB_REPOSITORY", "").strip("/")
    run_id = environment.get("GITHUB_RUN_ID", "").strip()
    if server and repository and run_id:
        return f"{server}/{repository}/actions/runs/{run_id}"
    return None


def utc_timestamp() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def build_receipt(
    *,
    checkout: Path,
    repository_url: str,
    tag: str,
    environment: dict[str, str],
) -> dict[str, Any]:
    if not TAG_RE.fullmatch(tag):
        raise ReceiptError(f"release tag is not exact semver-style syntax: {tag!r}")
    if not repository_url:
        raise ReceiptError("repository URL must not be empty")
    if not (checkout / ".git").exists():
        # Worktrees use a .git file; ordinary clones use a .git directory.
        raise ReceiptError(f"checkout is not a Git worktree: {checkout}")

    tag_object, resolved_commit = resolve_remote_tag(repository_url, tag)
    checkout_commit = validate_sha(
        run(["git", "rev-parse", "--verify", "HEAD^{commit}"], cwd=checkout),
        "checkout commit",
    )
    if checkout_commit != resolved_commit:
        raise ReceiptError(
            f"checkout mismatch: {tag} resolves to {resolved_commit}, but HEAD is {checkout_commit}"
        )

    tracked_changes = run(
        ["git", "status", "--porcelain=v1", "--untracked-files=no"], cwd=checkout
    )
    if tracked_changes:
        raise ReceiptError("checkout has tracked changes and is not the exact tagged source tree")

    checkout_tree = validate_sha(
        run(["git", "rev-parse", "--verify", "HEAD^{tree}"], cwd=checkout),
        "checkout tree",
    )
    toolchain = read_toolchain(checkout)
    mathlib_url, mathlib_revision, mathlib_input_revision = read_mathlib_pin(checkout)

    operating_system: dict[str, str] = {
        "system": platform.system(),
        "release": platform.release(),
        "machine": platform.machine(),
    }
    runner_os = environment.get("RUNNER_OS", "").strip()
    if runner_os:
        operating_system["runner_os"] = runner_os

    return {
        "schema": "formalslt.exact-tag-verification-receipt.v1",
        "verification_scope": "tag_identity_and_source_environment_only",
        "tag": tag,
        "repository_url": repository_url,
        "tag_object": tag_object,
        "resolved_commit": resolved_commit,
        "resolved_tree": checkout_tree,
        "lean_toolchain": toolchain,
        "mathlib": {
            "repository_url": mathlib_url,
            "revision": mathlib_revision,
            "input_revision": mathlib_input_revision,
        },
        "operating_system": operating_system,
        "generated_at_utc": utc_timestamp(),
        "run_url": infer_run_url(environment),
        "does_not_assert": [
            "continuous integration succeeded",
            "a downstream build succeeded",
            "a GitHub Release exists",
            "a DOI exists or resolves",
        ],
    }


def write_receipt(path: Path, receipt: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    with tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", dir=path.parent, prefix=f".{path.name}.", delete=False
    ) as temporary:
        temporary.write(encoded)
        temporary_path = Path(temporary.name)
    temporary_path.replace(path)


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True, help="existing exact release tag")
    parser.add_argument(
        "--repository-url",
        default=os.environ.get("FORMALSLT_REPOSITORY_URL", DEFAULT_REPOSITORY_URL),
        help="repository whose exact tag is authoritative",
    )
    parser.add_argument(
        "--checkout", type=Path, default=Path.cwd(), help="checkout expected at the tag commit"
    )
    parser.add_argument("--output", type=Path, required=True, help="JSON receipt path")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        receipt = build_receipt(
            checkout=args.checkout.resolve(),
            repository_url=args.repository_url,
            tag=args.tag,
            environment=dict(os.environ),
        )
        write_receipt(args.output, receipt)
    except ReceiptError as exc:
        print(f"ERROR: exact-tag receipt refused: {exc}", file=sys.stderr)
        return 1
    print(
        f"exact-tag identity receipt written: {args.tag} -> {receipt['resolved_commit']} "
        f"({args.output})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
