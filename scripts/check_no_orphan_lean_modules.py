#!/usr/bin/env python3
"""Fail when tracked FormalSLT modules are not reachable from FormalSLT.lean."""

from __future__ import annotations

import re
import sys
from pathlib import Path


IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_'.]+)\s*$")


def module_to_path(root: Path, module: str) -> Path:
    parts = module.split(".")
    if parts == ["FormalSLT"]:
        return root / "FormalSLT.lean"
    return root.joinpath(*parts).with_suffix(".lean")


def path_to_module(root: Path, path: Path) -> str:
    rel = path.relative_to(root).with_suffix("")
    return ".".join(rel.parts)


def all_formalslt_modules(root: Path) -> set[str]:
    modules = {"FormalSLT"}
    for path in (root / "FormalSLT").rglob("*.lean"):
        modules.add(path_to_module(root, path))
    return modules


def imported_formalslt_modules(path: Path) -> list[str]:
    imports: list[str] = []
    if not path.exists():
        return imports
    for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        match = IMPORT_RE.match(line)
        if match and (match.group(1) == "FormalSLT" or match.group(1).startswith("FormalSLT.")):
            imports.append(match.group(1))
    return imports


def reachable_modules(root: Path) -> set[str]:
    seen: set[str] = set()
    stack = ["FormalSLT"]
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)
        for imported in imported_formalslt_modules(module_to_path(root, module)):
            if imported not in seen:
                stack.append(imported)
    return seen


def find_orphan_modules(root: Path) -> list[str]:
    modules = all_formalslt_modules(root)
    reachable = reachable_modules(root)
    return sorted(mod for mod in modules - reachable if mod != "FormalSLT")


def main() -> int:
    root = Path.cwd()
    orphans = find_orphan_modules(root)
    if not orphans:
        print("no orphaned FormalSLT modules")
        return 0
    print("orphaned FormalSLT modules:")
    for module in orphans:
        print(f"  {module} ({module_to_path(root, module).relative_to(root)})")
    return 1


if __name__ == "__main__":
    sys.exit(main())
