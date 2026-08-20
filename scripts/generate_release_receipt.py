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
import sys
import tempfile
from pathlib import Path
from typing import Any, Sequence

from release_tag_identity import (
    DEFAULT_REPOSITORY_URL,
    ReceiptError,
    run,
    utc_timestamp,
    validate_sha,
    verify_expected_remote,
)


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


def build_receipt(
    *,
    checkout: Path,
    repository_url: str,
    tag: str,
    expected_tag_object: str,
    expected_commit: str,
    environment: dict[str, str],
) -> dict[str, Any]:
    if not (checkout / ".git").exists():
        # Worktrees use a .git file; ordinary clones use a .git directory.
        raise ReceiptError(f"checkout is not a Git worktree: {checkout}")

    identity = verify_expected_remote(
        repository_url,
        tag,
        expected_tag_object,
        expected_commit,
    )
    checkout_commit = validate_sha(
        run(["git", "rev-parse", "--verify", "HEAD^{commit}"], cwd=checkout),
        "checkout commit",
    )
    if checkout_commit != expected_commit:
        raise ReceiptError(
            f"checkout mismatch: resolver fixed {expected_commit}, but HEAD is {checkout_commit}"
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
        "schema": "formalslt.exact-tag-verification-receipt.v2",
        "verification_scope": "resolver_bound_tag_identity_and_source_environment_only",
        "tag": tag,
        "repository_url": repository_url,
        "tag_object": identity.tag_object,
        "resolved_commit": identity.resolved_commit,
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
    parser.add_argument("--expected-tag-object", required=True)
    parser.add_argument("--expected-commit", required=True)
    parser.add_argument("--output", type=Path, required=True, help="JSON receipt path")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        receipt = build_receipt(
            checkout=args.checkout.resolve(),
            repository_url=args.repository_url,
            tag=args.tag,
            expected_tag_object=args.expected_tag_object,
            expected_commit=args.expected_commit,
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
