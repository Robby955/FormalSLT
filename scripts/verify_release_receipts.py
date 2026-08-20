#!/usr/bin/env python3
"""Aggregate the Linux/macOS exact-tag receipts and recheck remote identity."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Sequence

from release_tag_identity import (
    DEFAULT_REPOSITORY_URL,
    ReceiptError,
    run,
    validate_sha,
    verify_expected_remote,
)


SCHEMA = "formalslt.exact-tag-verification-receipt.v2"
TIMESTAMP_RE = re.compile(r"^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z$")
EXPECTED_RUNNERS = {"Linux", "macOS"}


def load_receipts(directory: Path) -> list[tuple[Path, dict[str, Any]]]:
    paths = sorted(directory.rglob("*.json"))
    if len(paths) != 2:
        raise ReceiptError(
            f"expected exactly two operating-system receipts, found {len(paths)}"
        )
    receipts: list[tuple[Path, dict[str, Any]]] = []
    for path in paths:
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise ReceiptError(f"unable to read receipt {path}: {exc}") from exc
        if not isinstance(value, dict):
            raise ReceiptError(f"receipt {path} is not a JSON object")
        receipts.append((path, value))
    return receipts


def require_equal(receipt: dict[str, Any], key: str, expected: object, path: Path) -> None:
    if receipt.get(key) != expected:
        raise ReceiptError(
            f"receipt {path} has {key}={receipt.get(key)!r}; expected {expected!r}"
        )


def verify_pair(
    *,
    directory: Path,
    checkout: Path,
    repository_url: str,
    tag: str,
    expected_tag_object: str,
    expected_commit: str,
) -> str:
    validate_sha(expected_tag_object, "expected tag object")
    validate_sha(expected_commit, "expected peeled commit")
    checkout_commit = validate_sha(
        run(["git", "rev-parse", "--verify", "HEAD^{commit}"], cwd=checkout),
        "aggregate checkout commit",
    )
    if checkout_commit != expected_commit:
        raise ReceiptError(
            f"aggregate checkout is {checkout_commit}, expected {expected_commit}"
        )
    expected_tree = validate_sha(
        run(["git", "rev-parse", "--verify", "HEAD^{tree}"], cwd=checkout),
        "aggregate checkout tree",
    )
    receipts = load_receipts(directory)

    shared_toolchain: str | None = None
    shared_mathlib: object | None = None
    shared_run_url: str | None = None
    runners: set[str] = set()
    required_nonclaims = {
        "continuous integration succeeded",
        "a downstream build succeeded",
        "a GitHub Release exists",
        "a DOI exists or resolves",
    }

    for path, receipt in receipts:
        require_equal(receipt, "schema", SCHEMA, path)
        require_equal(
            receipt,
            "verification_scope",
            "resolver_bound_tag_identity_and_source_environment_only",
            path,
        )
        require_equal(receipt, "tag", tag, path)
        require_equal(receipt, "repository_url", repository_url, path)
        require_equal(receipt, "tag_object", expected_tag_object, path)
        require_equal(receipt, "resolved_commit", expected_commit, path)

        tree = validate_sha(str(receipt.get("resolved_tree", "")), "resolved tree")
        if tree != expected_tree:
            raise ReceiptError(
                f"receipt {path} resolved_tree {tree} differs from checkout tree "
                f"{expected_tree}"
            )

        toolchain = receipt.get("lean_toolchain")
        if not isinstance(toolchain, str) or not toolchain:
            raise ReceiptError(f"receipt {path} has no Lean toolchain")
        if shared_toolchain is None:
            shared_toolchain = toolchain
        elif toolchain != shared_toolchain:
            raise ReceiptError(f"receipt {path} has a different Lean toolchain")

        mathlib = receipt.get("mathlib")
        if not isinstance(mathlib, dict):
            raise ReceiptError(f"receipt {path} has no Mathlib identity")
        validate_sha(str(mathlib.get("revision", "")), "pinned Mathlib revision")
        if shared_mathlib is None:
            shared_mathlib = mathlib
        elif mathlib != shared_mathlib:
            raise ReceiptError(f"receipt {path} has a different Mathlib identity")

        operating_system = receipt.get("operating_system")
        if not isinstance(operating_system, dict):
            raise ReceiptError(f"receipt {path} has no operating-system identity")
        runner = operating_system.get("runner_os")
        if runner not in EXPECTED_RUNNERS:
            raise ReceiptError(f"receipt {path} has unexpected runner_os={runner!r}")
        if runner in runners:
            raise ReceiptError(f"duplicate {runner} receipt")
        runners.add(runner)

        timestamp = receipt.get("generated_at_utc")
        if not isinstance(timestamp, str) or not TIMESTAMP_RE.fullmatch(timestamp):
            raise ReceiptError(f"receipt {path} has an invalid UTC timestamp")
        run_url = receipt.get("run_url")
        if not isinstance(run_url, str) or not run_url:
            raise ReceiptError(f"receipt {path} has no hosted run URL")
        if shared_run_url is None:
            shared_run_url = run_url
        elif run_url != shared_run_url:
            raise ReceiptError(f"receipt {path} belongs to a different hosted run")
        nonclaims = receipt.get("does_not_assert")
        if not isinstance(nonclaims, list) or not all(
            item in nonclaims for item in required_nonclaims
        ):
            raise ReceiptError(f"receipt {path} omits required nonclaims")

    if runners != EXPECTED_RUNNERS:
        raise ReceiptError(f"receipt runners are {sorted(runners)}, expected {sorted(EXPECTED_RUNNERS)}")

    # This is deliberately last: it detects a move after either OS receipt was
    # written instead of silently accepting a new resolution.
    verify_expected_remote(
        repository_url,
        tag,
        expected_tag_object,
        expected_commit,
    )
    return expected_tree


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt-dir", type=Path, required=True)
    parser.add_argument("--checkout", type=Path, default=Path.cwd())
    parser.add_argument("--repository-url", default=DEFAULT_REPOSITORY_URL)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--expected-tag-object", required=True)
    parser.add_argument("--expected-commit", required=True)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        tree = verify_pair(
            directory=args.receipt_dir,
            checkout=args.checkout.resolve(),
            repository_url=args.repository_url,
            tag=args.tag,
            expected_tag_object=args.expected_tag_object,
            expected_commit=args.expected_commit,
        )
    except ReceiptError as exc:
        print(f"ERROR: receipt aggregation refused: {exc}", file=sys.stderr)
        return 1
    print(
        f"matched Linux/macOS exact-tag receipts: {args.tag} -> "
        f"{args.expected_commit} (tree {tree})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
