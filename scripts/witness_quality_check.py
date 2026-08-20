#!/usr/bin/env python3
"""Classify a curated Lean witness file by its executable receipt surface.

This is a structural release gate, not a proof of mathematical non-vacuity.
It deliberately fails closed unless a comment-free top-level theorem, lemma,
example, or definition applies either a declaration audited by a real
``#check``/``#print axioms`` command in the same file or a distinctive imported
project declaration. Merely mentioning a declaration keyword in a comment, or
appending an unrelated ``1 + 1 = 2`` theorem to a check-only file, is not a
receipt.

Exit status is zero for a concrete receipt and one otherwise.  The final output
line is one of ``CONCRETE``, ``FAKE``, or ``NONE`` for the shell gate.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
IDENTIFIER = r"(?:«[^»]+»|[A-Za-z_Ͱ-Ͽ][A-Za-z0-9_'.₀-₉Ͱ-Ͽ]*)"
DECL_RE = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|nonrec|unsafe)\s+)*"
    r"(?P<kind>theorem|lemma|example|def)\b"
    r"(?:\s+(?P<name>" + IDENTIFIER + r"))?"
)
CHECK_RE = re.compile(
    r"(?m)^[ \t]*#(?:check|print\s+axioms)\s+@?(?P<name>" + IDENTIFIER + r")"
)
IMPORT_RE = re.compile(r"(?m)^[ \t]*import[ \t]+(?P<module>FormalSLT(?:\.[A-Za-z0-9_']+)*)")
TOKEN_RE = re.compile(IDENTIFIER)
COMMAND_RE = re.compile(
    r"(?m)^[ \t]*(?:#(?:check|print\s+axioms)\b|"
    r"(?:namespace|section|end|open|variable|universe)\b|"
    r"(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|unsafe)\s+)*"
    r"(?:theorem|lemma|example|def)\b)"
)


@dataclass(frozen=True)
class Declaration:
    kind: str
    name: str | None
    source: str
    line: int


def strip_lean_comments_and_strings(text: str) -> str:
    """Blank comments and strings while preserving positions and newlines."""

    result: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""

        if block_depth:
            if ch == "/" and nxt == "-":
                block_depth += 1
                result.extend("  ")
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                result.extend("  ")
                i += 2
                continue
            result.append("\n" if ch == "\n" else " ")
            i += 1
            continue

        if in_string:
            if ch == "\\":
                result.append(" ")
                if nxt:
                    result.append(" ")
                    i += 2
                else:
                    i += 1
                continue
            if ch == '"':
                in_string = False
            result.append("\n" if ch == "\n" else " ")
            i += 1
            continue

        if ch == "/" and nxt == "-":
            block_depth = 1
            result.extend("  ")
            i += 2
            continue
        if ch == "-" and nxt == "-":
            while i < len(text) and text[i] != "\n":
                result.append(" ")
                i += 1
            continue
        if ch == '"':
            in_string = True
            result.append(" ")
            i += 1
            continue
        result.append(ch)
        i += 1

    return "".join(result)


def declarations(clean: str) -> list[Declaration]:
    matches = list(DECL_RE.finditer(clean))
    result: list[Declaration] = []
    for match in matches:
        # Stop at the next top-level command, not at an arbitrary byte limit.
        next_command = COMMAND_RE.search(clean, match.end())
        end = next_command.start() if next_command else len(clean)
        result.append(
            Declaration(
                kind=match.group("kind"),
                name=match.group("name"),
                source=clean[match.start():end],
                line=clean.count("\n", 0, match.start()) + 1,
            )
        )
    return result


def short_name(name: str) -> str:
    return name.rsplit(".", 1)[-1].strip("«»")


def module_path(module: str) -> Path:
    if module == "FormalSLT":
        return ROOT / "FormalSLT.lean"
    return ROOT / Path(*module.split(".")).with_suffix(".lean")


@lru_cache(maxsize=None)
def imported_project_declarations(module: str) -> frozenset[str]:
    """Collect declaration short names from one FormalSLT import closure."""

    path = module_path(module)
    if not path.is_file():
        return frozenset()
    clean = strip_lean_comments_and_strings(path.read_text(encoding="utf-8"))
    names = {
        short_name(match.group("name"))
        for match in DECL_RE.finditer(clean)
        if match.group("name")
    }
    for imported in IMPORT_RE.finditer(clean):
        names.update(imported_project_declarations(imported.group("module")))
    return frozenset(names)


def is_receipt(
    declaration: Declaration,
    audited_names: set[str],
    imported_names: set[str],
    local_names: set[str],
) -> bool:
    """Require an executable declaration linked to the audited project surface."""

    if ":=" not in declaration.source:
        return False

    own_name = short_name(declaration.name) if declaration.name else None
    body = declaration.source
    for audited in audited_names:
        target = short_name(audited)
        if target == own_name:
            continue
        if re.search(rf"(?<![A-Za-z0-9_']){re.escape(target)}(?![A-Za-z0-9_'])", body):
            return True
    return any(
        short_name(token) in imported_names and short_name(token) not in local_names
        for token in TOKEN_RE.findall(body)
    )


def classify(path: Path) -> tuple[str, list[str]]:
    if not path.is_file():
        return "MISSING", [f"missing file: {path}"]

    clean = strip_lean_comments_and_strings(path.read_text(encoding="utf-8"))
    audited = {match.group("name") for match in CHECK_RE.finditer(clean)}
    imported_names: set[str] = set()
    for imported in IMPORT_RE.finditer(clean):
        imported_names.update(imported_project_declarations(imported.group("module")))
    decls = declarations(clean)
    local_names = {short_name(decl.name) for decl in decls if decl.name}
    receipts = [
        decl
        for decl in decls
        if is_receipt(decl, audited, imported_names, local_names)
    ]

    if receipts:
        details = [
            f"line {decl.line}: {decl.kind} {decl.name or '<anonymous>'} "
            "links a project declaration"
            for decl in receipts
        ]
        return "CONCRETE", details
    if audited:
        if decls:
            return "FAKE", [
                "top-level declarations exist, but none applies an audited or distinctive "
                "project declaration"
            ]
        return "FAKE", [
            "check commands exist, but no executable top-level receipt declaration exists"
        ]
    return "NONE", ["no #check/#print axioms target and no linked receipt declaration"]


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: witness_quality_check.py <file.lean>", file=sys.stderr)
        return 2
    verdict, details = classify(Path(sys.argv[1]))
    for detail in details:
        print(detail)
    print(verdict)
    return 0 if verdict == "CONCRETE" else 1


if __name__ == "__main__":
    raise SystemExit(main())
