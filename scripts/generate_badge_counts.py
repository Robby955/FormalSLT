#!/usr/bin/env python3
"""Generate shields.io badge data from the on-disk Lean surface.

For each metric (theorems, modules, lines) this writes a small JSON blob to
``docs/badges/<metric>.json`` that the shields.io endpoint badge consumes.
The README uses static shields.io badge URLs so pull-request previews do not
depend on files that have not landed on ``main`` yet. This script checks those
README badge values against the generated counts.

Run modes:

    python3 scripts/generate_badge_counts.py            # write the JSON files
    python3 scripts/generate_badge_counts.py --check    # CI gate: nonzero if drift

The ``--check`` mode mirrors ``scripts/generate_proof_frontier_manifest.py``.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from urllib.parse import quote

REPO_ROOT = Path(__file__).resolve().parent.parent
BADGE_DIR = REPO_ROOT / "docs" / "badges"
README = REPO_ROOT / "README.md"

THEOREM_RE = re.compile(r"^\s*(?:noncomputable\s+)?(?:theorem|lemma)\s+[A-Za-z_]")
README_BADGE_PATTERNS = {
    "theorems": re.compile(
        r"https://img\.shields\.io/badge/theorems%2Flemmas-[^-)\]]+-brightgreen\.svg"
    ),
    "modules": re.compile(
        r"https://img\.shields\.io/badge/FormalSLT%20modules-[^-)\]]+-blue\.svg"
    ),
    "lines": re.compile(
        r"https://img\.shields\.io/badge/Lean%20lines-[^-)\]]+-brightgreen\.svg"
    ),
}


def iter_lean_files(*roots: Path):
    for root in roots:
        if not root.exists():
            continue
        if root.is_file() and root.suffix == ".lean":
            yield root
            continue
        for path in sorted(root.rglob("*.lean")):
            yield path


def count_theorems(paths) -> int:
    count = 0
    for path in paths:
        for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
            if THEOREM_RE.match(line):
                count += 1
    return count


def count_lines(paths) -> int:
    return sum(
        sum(1 for _ in path.read_text(encoding="utf-8", errors="replace").splitlines())
        for path in paths
    )


def badge_payload(label: str, value: int) -> dict:
    return {
        "schemaVersion": 1,
        "label": label,
        "message": f"{value:,}",
        "color": "brightgreen",
    }


def static_badge_url(label: str, value: int, color: str = "brightgreen") -> str:
    return (
        "https://img.shields.io/badge/"
        f"{quote(label, safe='')}-{quote(f'{value:,}', safe='')}-{color}.svg"
    )


def write_or_check(path: Path, payload: dict, check: bool) -> bool:
    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if check:
        if not path.exists():
            print(f"[badge-counts] missing: {path.relative_to(REPO_ROOT)}", file=sys.stderr)
            return False
        actual = path.read_text(encoding="utf-8")
        if actual != text:
            print(
                f"[badge-counts] drift: {path.relative_to(REPO_ROOT)}\n"
                f"  expected: {text.strip()}\n"
                f"  actual:   {actual.strip()}",
                file=sys.stderr,
            )
            return False
        return True
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return True


def write_or_check_readme_badges(targets: dict[str, str], check: bool) -> bool:
    if not README.exists():
        print("[badge-counts] missing: README.md", file=sys.stderr)
        return False

    text = README.read_text(encoding="utf-8")
    updated = text
    ok = True

    for name, expected in targets.items():
        pattern = README_BADGE_PATTERNS[name]
        match = pattern.search(updated)
        if not match:
            print(f"[badge-counts] missing README badge: {name}", file=sys.stderr)
            ok = False
            continue
        if match.group(0) == expected:
            continue
        if check:
            print(
                f"[badge-counts] README badge drift: {name}\n"
                f"  expected: {expected}\n"
                f"  actual:   {match.group(0)}",
                file=sys.stderr,
            )
            ok = False
        else:
            updated = pattern.sub(expected, updated, count=1)

    if not check and updated != text:
        README.write_text(updated, encoding="utf-8")
    return ok


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="Fail with a nonzero exit if the on-disk JSON does not match the regenerated value.",
    )
    args = parser.parse_args()

    lib_root = REPO_ROOT / "FormalSLT"
    examples_root = REPO_ROOT / "examples"
    lib_files = list(iter_lean_files(lib_root))
    all_files = list(iter_lean_files(lib_root, examples_root))

    theorems = count_theorems(all_files)
    modules = len(lib_files)
    total_lines = count_lines(all_files)

    targets = [
        (BADGE_DIR / "theorems.json", badge_payload("theorems checked", theorems)),
        (BADGE_DIR / "modules.json", badge_payload("Lean modules", modules)),
        (BADGE_DIR / "lines.json", badge_payload("Lean lines", total_lines)),
    ]
    readme_badges = {
        "theorems": static_badge_url("theorems/lemmas", theorems),
        "modules": static_badge_url("FormalSLT modules", modules, "blue"),
        "lines": static_badge_url("Lean lines", total_lines),
    }

    ok = True
    for path, payload in targets:
        if not write_or_check(path, payload, args.check):
            ok = False
    if not write_or_check_readme_badges(readme_badges, args.check):
        ok = False

    if args.check and not ok:
        print(
            "[badge-counts] run 'python3 scripts/generate_badge_counts.py' to refresh.",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
