#!/usr/bin/env python3
"""Classify a commit diff as prose/media-only or requiring full Lean checks."""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import PurePosixPath


SAFE_FILES = frozenset({"README.md", "LICENSE", "CITATION.cff"})
SAFE_PREFIXES = ("docs/", "media/")


def normalize_path(raw: str) -> str:
    """Return a repository-relative POSIX path or fail closed."""
    path = raw.strip().replace("\\", "/")
    if not path:
        raise ValueError("empty changed path")
    parsed = PurePosixPath(path)
    if parsed.is_absolute() or ".." in parsed.parts:
        raise ValueError(f"unsafe changed path: {raw!r}")
    return parsed.as_posix()


def requires_full_checks(paths: list[str]) -> bool:
    """Unknown and empty diffs require the full suite."""
    if not paths:
        return True
    for raw in paths:
        try:
            path = normalize_path(raw)
        except ValueError:
            return True
        if path in SAFE_FILES or path.startswith(SAFE_PREFIXES):
            continue
        return True
    return False


def self_test() -> None:
    assert not requires_full_checks(["README.md"])
    assert not requires_full_checks(["docs/site/index.html", "media/demo/render.py"])
    assert requires_full_checks([])
    assert requires_full_checks(["FormalSLT/PACBayes.lean"])
    assert requires_full_checks(["lean-toolchain"])
    assert requires_full_checks([".github/workflows/ci.yml"])
    assert requires_full_checks(["docs/guide.md", "scripts/stage_docs_site.py"])
    assert requires_full_checks(["../README.md"])
    print("CI scope classifier self-test passed")


def read_paths(stdin0: bool) -> list[str]:
    data = sys.stdin.buffer.read()
    if stdin0:
        return [part.decode("utf-8") for part in data.split(b"\0") if part]
    return [line for line in data.decode("utf-8").splitlines() if line]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--stdin0", action="store_true")
    parser.add_argument(
        "--github-output",
        action="store_true",
        help="append scope=docs|full to the path in GITHUB_OUTPUT",
    )
    args = parser.parse_args()

    if args.self_test:
        self_test()
        return 0

    paths = read_paths(args.stdin0)
    scope = "full" if requires_full_checks(paths) else "docs"
    print(f"CI scope: {scope}")
    for path in paths:
        print(f"  {path}")

    if args.github_output:
        output_path = os.environ.get("GITHUB_OUTPUT")
        if not output_path:
            raise RuntimeError("GITHUB_OUTPUT is not set")
        with open(output_path, "a", encoding="utf-8") as output:
            output.write(f"scope={scope}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
