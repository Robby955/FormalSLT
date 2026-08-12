#!/usr/bin/env python3
"""Generate the FormalSLT proof-frontier manifest.

The manifest is intentionally conservative: it records the curated theorem map,
basic Lean source counts, proof-debt scan results, and a small set of documented
next lanes. It does not infer mathematical dependency structure from Lean.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
THEOREM_MAP = ROOT / "docs" / "theorem-map.md"
OUTPUT = ROOT / "docs" / "proof-frontier-manifest.json"

EXPECTED_PUBLIC_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]

FRONTIER_LANES: list[dict[str, str]] = [
    {
        "id": "finite-markov-prequential-risk",
        "status": "partially_closed",
        "scope": (
            "finite-state Markov paths with deterministic start, a fixed "
            "bounded observable, and a finite catalog of fixed predictors; "
            "the checked surface includes a sharp one-quarter variance proxy "
            "and fixed-tilt all-time posterior-uniform PAC-Bayes control"
        ),
        "difficulty": "medium",
        "source": "docs/roadmap.md#near-term",
        "next_step": (
            "Generalize the path law to a supplied initial distribution, "
            "support predictable or independently trained catalogs, and add "
            "declared finite or normalized countable tilt selection."
        ),
        "boundary": (
            "The checked certificate targets posterior-average one-step "
            "conditional risk at a fixed declared tilt. It does not cover "
            "same-trajectory fitting, arbitrary post-sample real-tilt "
            "optimization, stationarity, mixing, continuous state spaces, "
            "multistep prediction, or long-run risk."
        ),
    },
    {
        "id": "localized-rademacher-finite-concentration",
        "status": "partially_closed",
        "scope": "finite classes",
        "difficulty": "medium",
        "source": "docs/roadmap.md#near-term",
        "next_step": (
            "The finite Bernstein variance-localization route is now closed "
            "locally. The next deeper target is a whole-supremum "
            "random-threshold concentration bound for localized upper "
            "deviations."
        ),
        "boundary": (
            "The current finite Bernstein theorem is not an infinite-class, "
            "measurable-supremum, or full oracle-inequality theorem; it assumes "
            "bounded excess losses, a Bernstein condition, and 0 < c*r."
        ),
    },
    {
        "id": "continuous-dudley-entropy-integral",
        "status": "partially_closed",
        "scope": "unit-interval example plus total-bounded bridge; continuous integral remains open",
        "difficulty": "hard",
        "source": "docs/next-lane.md",
        "next_step": (
            "Package the unit-interval Dudley example and then generalize the "
            "endpoint-mesh terminal step beyond the exact half/quarter meshes. "
            "The full continuous entropy-integral theorem still needs analytic "
            "and measurability assumptions."
        ),
        "boundary": (
            "The unit-interval example exercises the non-finite metric index "
            "route, but it does not claim separability, measurable arbitrary "
            "suprema, or a continuous Dudley theorem."
        ),
    },
    {
        "id": "pac-bayes-all-real-lambda",
        "status": "partially_closed",
        "scope": (
            "finite hypotheses plus spherical-Gaussian continuous-hypothesis "
            "single-pair and finite fixed-catalog specializations"
        ),
        "difficulty": "medium-hard",
        "source": "docs/open-formalization-problems.md#near-term",
        "next_step": (
            "Extend the checked finite weighted indicator-Bernstein catalog toward "
            "a countable normalized-moment mixture or all-real lambda statement, "
            "then generalize the fixed spherical-Gaussian posterior lane."
        ),
        "boundary": (
            "The base continuous-hypothesis i.i.d. theorem is fixed-tilt, "
            "fixed-posterior, and spherical-Gaussian. Finite fixed catalogs "
            "of posterior/tilt pairs and a posterior-uniform finite weighted "
            "indicator-Bernstein tilt catalog support post-sample selection, "
            "but neither result is simultaneous over all continuous posteriors "
            "or all real tilts."
        ),
    },
    {
        "id": "pac-bayes-empirical-bernstein",
        "status": "partially_closed",
        "scope": (
            "finite per-hypothesis Bessel empirical loss variance, exact "
            "ordered-pair representation, finite-IID unbiasedness, "
            "random-matching source MGF, fixed-tilt posterior-uniform "
            "variance confidence, a standalone weighted finite variance-tilt "
            "catalog, fixed-parameter observable risk, and separately "
            "weighted finite eta/lambda catalogs, plus a fixed-sample "
            "per-hypothesis joint mean/Bessel-variance MGF core"
        ),
        "difficulty": "hard",
        "source": (
            "docs/open-formalization-problems.md#pac-bayes-empirical-sample-variance"
        ),
        "next_step": (
            "Lift the checked fixed-sample joint MGF through a finite prior "
            "mixture and one posterior-uniform confidence event; treat "
            "countable, all-real, and time-uniform adaptation separately."
        ),
        "boundary": (
            "The joint MGF core is per hypothesis and fixed sample: it has no "
            "prior mixture, posterior variational step, confidence event, or "
            "tilt catalog. The checked risk result still uses separate "
            "events, and neither lane gives all-real or time-uniform inference."
        ),
    },
    {
        "id": "sharp-mcdiarmid-product-kernel",
        "status": "blocked",
        "scope": "bounded-differences concentration",
        "difficulty": "hard",
        "source": "docs/roadmap.md#near-term",
        "next_step": (
            "Identify or build the product-kernel conditional-expectation "
            "decomposition needed for a range-based Hoeffding route."
        ),
        "boundary": (
            "The current high-probability bounds use the Azuma constant; sharp "
            "McDiarmid should wait for the required measure-theoretic layer."
        ),
    },
]


def tracked_lean_files(*roots: str) -> list[Path]:
    files: list[Path] = []
    for root in roots:
        base = ROOT / root
        if base.is_file() and base.suffix == ".lean":
            files.append(base)
        elif base.is_dir():
            files.extend(sorted(base.rglob("*.lean")))
    return sorted(files)


def count_lines(files: list[Path]) -> int:
    return sum(len(path.read_text(encoding="utf-8").splitlines()) for path in files)


def parse_mathlib_rev() -> str:
    lakefile = (ROOT / "lakefile.lean").read_text(encoding="utf-8")
    match = re.search(r'mathlib4\.git"\s*@\s*"([^"]+)"', lakefile)
    return match.group(1) if match else ""


def lean_toolchain() -> str:
    path = ROOT / "lean-toolchain"
    return path.read_text(encoding="utf-8").strip() if path.exists() else ""


def strip_lean_comments_and_strings(text: str) -> str:
    result: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""

        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
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
            if ch == "\"":
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
        if ch == "\"":
            in_string = True
            result.append(" ")
            i += 1
            continue
        result.append(ch)
        i += 1

    return "".join(result)


def audit_lean_files(files: list[Path]) -> dict[str, list[dict[str, Any]]]:
    proof_debt = re.compile(
        r"^\s*(?:by\s+)?(?:sorry|admit)\b|:=\s*(?:by\s+)?(?:sorry|admit)\b"
    )
    custom_axiom = re.compile(r"^\s*(?:axiom|constant)\s+[A-Za-z_]")
    debt_hits: list[dict[str, Any]] = []
    axiom_hits: list[dict[str, Any]] = []

    for path in files:
        clean = strip_lean_comments_and_strings(path.read_text(encoding="utf-8"))
        rel = path.relative_to(ROOT).as_posix()
        for line_no, line in enumerate(clean.splitlines(), start=1):
            if proof_debt.search(line):
                debt_hits.append({"file": rel, "line": line_no, "text": line.strip()})
            if custom_axiom.search(line):
                axiom_hits.append({"file": rel, "line": line_no, "text": line.strip()})

    return {
        "sorry_or_admit": debt_hits,
        "custom_axiom_or_constant": axiom_hits,
    }


def parse_theorem_map() -> list[dict[str, Any]]:
    lines = THEOREM_MAP.read_text(encoding="utf-8").splitlines()
    families: list[dict[str, Any]] = []
    current: dict[str, Any] | None = None
    header: list[str] | None = None

    for raw in lines:
        line = raw.strip()
        if line.startswith("## "):
            if current is not None:
                families.append(current)
            current = {"name": line.removeprefix("## ").strip(), "entries": []}
            header = None
            continue
        if current is None or not line.startswith("|"):
            if not line.startswith("|"):
                header = None
            continue

        cells = [cell.strip() for cell in line.strip("|").split("|")]
        if all(set(cell) <= {"-", ":"} for cell in cells):
            continue
        if header is None:
            header = cells
            continue
        if len(cells) != len(header):
            continue

        row = dict(zip(header, cells, strict=True))
        name = row.get("Declaration") or row.get("Theorem")
        module = row.get("Module")
        statement = row.get("Role") or row.get("Bound") or ""
        if not name or not module:
            continue

        current["entries"].append(
            {
                "name": name.strip("`"),
                "module": module.strip("`"),
                "kind": "definition" if "Declaration" in row else "theorem",
                "summary": statement.replace("`", ""),
            }
        )

    if current is not None:
        families.append(current)
    return [family for family in families if family["entries"]]


def build_manifest() -> dict[str, Any]:
    library_files = tracked_lean_files("FormalSLT")
    example_files = tracked_lean_files("examples")
    root_files = tracked_lean_files("FormalSLT.lean")
    audited_files = library_files + example_files + root_files
    theorem_families = parse_theorem_map()
    audit = audit_lean_files(audited_files)

    return {
        "schema": "FormalSLT.proof_frontier.v1",
        "repository": {
            "name": "Robby955/FormalSLT",
            "default_branch": "main",
        },
        "toolchain": {
            "lean": lean_toolchain(),
            "mathlib_revision": parse_mathlib_rev(),
        },
        "source_counts": {
            "library_modules": len(library_files),
            "library_lean_lines": count_lines(library_files),
            "example_lean_files": len(example_files),
            "library_and_example_lean_lines": count_lines(library_files + example_files),
            "theorem_map_entries": sum(len(family["entries"]) for family in theorem_families),
        },
        "audit": {
            "expected_public_axioms": EXPECTED_PUBLIC_AXIOMS,
            **audit,
        },
        "theorem_families": theorem_families,
        "frontier_lanes": FRONTIER_LANES,
        "generation": {
            "command": "python3 scripts/generate_proof_frontier_manifest.py",
            "output": "docs/proof-frontier-manifest.json",
            "sources": [
                "FormalSLT/**/*.lean",
                "FormalSLT.lean",
                "examples/*.lean",
                "docs/theorem-map.md",
                "docs/roadmap.md",
                "docs/next-lane.md",
                "docs/open-formalization-problems.md",
                "lakefile.lean",
                "lean-toolchain",
            ],
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="fail if the manifest is stale")
    args = parser.parse_args()

    encoded = json.dumps(build_manifest(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not OUTPUT.exists():
            print(f"{OUTPUT.relative_to(ROOT)} does not exist", file=sys.stderr)
            return 1
        current = OUTPUT.read_text(encoding="utf-8")
        if current != encoded:
            print(f"{OUTPUT.relative_to(ROOT)} is stale; regenerate it", file=sys.stderr)
            return 1
        return 0

    OUTPUT.write_text(encoded, encoding="utf-8")
    print(f"wrote {OUTPUT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
