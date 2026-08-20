#!/usr/bin/env python3
"""Fail on orphaned FormalSLT modules or core-to-application import leaks.

The core umbrella is ``FormalSLT.lean``. If present, the separately imported
``FormalSLT/Applications.lean`` umbrella is a second reachability root. This
keeps worked applications covered by the orphan gate without making them part
of the default ``import FormalSLT`` surface.
"""

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


def umbrella_roots(root: Path) -> list[str]:
    roots = ["FormalSLT"]
    if module_to_path(root, "FormalSLT.Applications").is_file():
        roots.append("FormalSLT.Applications")
    return roots


def reachable_modules(root: Path, roots: list[str] | None = None) -> set[str]:
    seen: set[str] = set()
    stack = list(roots if roots is not None else umbrella_roots(root))
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


def find_core_application_imports(root: Path) -> list[str]:
    """Report application modules reachable from the default core umbrella."""

    return sorted(
        module
        for module in reachable_modules(root, ["FormalSLT"])
        if module == "FormalSLT.Applications"
        or module.startswith("FormalSLT.Applications.")
    )


def main() -> int:
    root = Path.cwd()
    application_imports = find_core_application_imports(root)
    orphans = find_orphan_modules(root)
    if not application_imports and not orphans:
        print("no orphaned FormalSLT modules; Applications remains opt-in")
        return 0
    if application_imports:
        print("FormalSLT.lean reaches opt-in application modules:")
        for module in application_imports:
            print(f"  {module} ({module_to_path(root, module).relative_to(root)})")
    if orphans:
        print("orphaned FormalSLT modules:")
        for module in orphans:
            print(f"  {module} ({module_to_path(root, module).relative_to(root)})")
    return 1


if __name__ == "__main__":
    sys.exit(main())
