#!/usr/bin/env python3
"""Check documented Lean source anchors in Markdown/MDX files.

The checker looks for anchors of the form `FormalSLT/...lean:NNN`, finds the
backticked declaration name the anchor belongs to, and verifies that the
referenced source line contains that declaration.

Documents use three layouts, and the declaration can sit on either side of the
anchor:

    | description | `declName` | `File.lean:NNN` |    same line, name first
    - `declName`
      (`File.lean:NNN`)                                name above the anchor
    - `File.lean:NNN`
      `declName`                                       name below the anchor

The third layout is why a plain upward scan is not enough: it would pair each
anchor with the *previous* entry's name and report the whole list as stale.

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


LIST_ITEM_RE = re.compile(r"^\s*[-*+]\s")


def declaration_below_anchor(lines: list[str], index: int) -> str | None:
    """Name on the indented continuation line, for `- anchor` / `  name` entries.

    Only fires when the anchor opens a list item and carries no name of its own,
    and the next line is an indented continuation holding a name and no anchor.
    Both guards matter: without them this would swallow the `- name` /
    `  (anchor)` layout, pairing each anchor with the next entry's name.
    """
    line = lines[index]
    if not LIST_ITEM_RE.match(line) or DECL_RE.search(line):
        return None
    if index + 1 >= len(lines):
        return None
    below = lines[index + 1]
    if not below.strip() or LIST_ITEM_RE.match(below):
        return None
    if not below.startswith((" ", "\t")) or ANCHOR_RE.search(below):
        return None
    matches = list(DECL_RE.finditer(below))
    return matches[0].group(1) if matches else None


def nearby_declaration(lines: list[str], index: int) -> str | None:
    for j in range(index - 1, max(index - 8, -1), -1):
        matches = list(DECL_RE.finditer(lines[j]))
        if matches:
            return matches[-1].group(1)
    return None


def declaration_for_anchor(lines: list[str], index: int, anchor_start: int) -> str | None:
    """Association order: same line first, then below, then above."""
    return (
        declaration_before_anchor(lines[index], anchor_start)
        or declaration_below_anchor(lines, index)
        or nearby_declaration(lines, index)
    )


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
            decl = declaration_for_anchor(lines, i, anchor.start())
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


LAYOUT_FIXTURES: list[tuple[str, list[str], int, str]] = [
    (
        "same line, name before anchor",
        ["| desc | `alpha_thm` | `FormalSLT/A.lean:10` |"],
        0,
        "alpha_thm",
    ),
    (
        "name above the anchor",
        ["- `beta_thm`", "  (`FormalSLT/A.lean:20`)"],
        1,
        "beta_thm",
    ),
    (
        "name below the anchor",
        ["- `FormalSLT/A.lean:30`", "  `gamma_thm`"],
        0,
        "gamma_thm",
    ),
    (
        "name below, not fooled by the previous entry",
        [
            "- `FormalSLT/A.lean:30`",
            "  `gamma_thm`",
            "- `FormalSLT/A.lean:40`",
            "  `delta_thm`",
        ],
        2,
        "delta_thm",
    ),
]


def self_test() -> int:
    """Verify anchor-to-declaration association on each documented layout."""
    failures = 0
    print("== layout association fixtures ==")
    for name, lines, index, expected in LAYOUT_FIXTURES:
        anchor = ANCHOR_RE.search(lines[index])
        got = declaration_for_anchor(lines, index, anchor.start())
        if got == expected:
            print(f"  ok   {name}")
        else:
            print(f"  FAIL {name}: expected {expected!r}, got {got!r}")
            failures += 1
    if failures:
        print(f"doc-anchor self-test failed: {failures} layout(s) misassociated")
        return 1
    print("doc-anchor self-test passed: all layouts associate correctly")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", type=Path)
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="check the association logic against the known document layouts",
    )
    args = parser.parse_args()

    if args.self_test:
        return self_test()
    if not args.paths:
        parser.error("the following arguments are required: paths")

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
