#!/usr/bin/env python3
"""Check documented Lean source anchors in Markdown/MDX files.

The checker looks for anchors of the form `FormalSLT/...lean:NNN`, finds the
nearest backticked declaration name on the same line or immediately above it,
and verifies that the referenced source line contains that declaration.

It is intentionally small and conservative. If it cannot infer a declaration
name for an anchor, it reports that as a failure instead of guessing.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


ANCHOR_RE = re.compile(r"(FormalSLT/[^:`) ]+\.lean):(\d+)")
DECL_RE = re.compile(r"`([A-Za-z_][A-Za-z0-9_\.]*)`")


def declaration_before_anchor(line: str, anchor_start: int) -> str | None:
    matches = list(DECL_RE.finditer(line[:anchor_start]))
    if not matches:
        return None
    return matches[-1].group(1)


def nearby_declaration(lines: list[str], index: int) -> str | None:
    for j in range(index - 1, max(index - 8, -1), -1):
        matches = list(DECL_RE.finditer(lines[j]))
        if matches:
            return matches[-1].group(1)
    return None


def source_line_has_decl(source_line: str, decl: str) -> bool:
    if decl in source_line:
        return True
    if "." in decl and decl.rsplit(".", 1)[1] in source_line:
        return True
    return False


def check_file(path: Path) -> list[str]:
    failures: list[str] = []
    lines = path.read_text().splitlines()
    for i, line in enumerate(lines):
        for anchor in ANCHOR_RE.finditer(line):
            source = Path(anchor.group(1))
            line_no = int(anchor.group(2))
            decl = declaration_before_anchor(line, anchor.start()) or nearby_declaration(lines, i)
            if decl is None:
                failures.append(
                    f"{path}:{i + 1}: cannot infer declaration for {source}:{line_no}"
                )
                continue
            if not source.exists():
                failures.append(f"{path}:{i + 1}: missing source file {source}")
                continue
            source_lines = source.read_text().splitlines()
            if line_no < 1 or line_no > len(source_lines):
                failures.append(
                    f"{path}:{i + 1}: {source}:{line_no} is outside file length {len(source_lines)}"
                )
                continue
            source_line = source_lines[line_no - 1]
            if not source_line_has_decl(source_line, decl):
                failures.append(
                    f"{path}:{i + 1}: {decl} is not on {source}:{line_no}; "
                    f"line is: {source_line.strip()}"
                )
    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="+", type=Path)
    args = parser.parse_args()

    failures: list[str] = []
    for path in args.paths:
        failures.extend(check_file(path))

    if failures:
        for failure in failures:
            print(failure)
        return 1

    print("doc anchor check passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
