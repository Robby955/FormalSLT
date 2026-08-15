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
from functools import lru_cache
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
THEOREM_MAP = ROOT / "docs" / "theorem-map.md"
OUTPUT = ROOT / "docs" / "proof-frontier-manifest.json"

EXPECTED_PUBLIC_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]

LEAN_DECLARATION_KINDS = {
    "theorem": "theorem",
    "lemma": "theorem",
    "def": "definition",
    "abbrev": "definition",
    "structure": "definition",
    "class": "definition",
    "instance": "definition",
    "inductive": "definition",
}
LEAN_DECLARATION_PATTERN = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:noncomputable|private|protected|nonrec|unsafe)\s+)*"
    r"(?P<keyword>" + "|".join(LEAN_DECLARATION_KINDS) + r")\s+"
    r"(?P<name>«[^»]+»|[^\s:({\[]+)"
)

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
            "variance confidence over all posteriors on a finite hypothesis "
            "type, a standalone weighted finite variance-tilt "
            "catalog, fixed-parameter observable risk, and separately "
            "weighted finite eta/lambda catalogs, plus a fixed-sample "
            "per-hypothesis joint mean/Bessel-variance MGF core and a "
            "one-event weighted joint-pair posterior catalog with selector, "
            "including its explicit zero-residual branch and exact attained "
            "three-piece residual penalty, plus a support-aware Nat-indexed "
            "countable master mixture and per-entry prior-moment extraction"
        ),
        "difficulty": "hard",
        "source": (
            "docs/open-formalization-problems.md#pac-bayes-empirical-sample-variance"
        ),
        "next_step": (
            "Lift the checked support-aware countable weighted joint (t, eta) "
            "master event to posterior and exact-xi selector endpoints; treat "
            "all-real and time-uniform adaptation as separate process problems."
        ),
        "boundary": (
            "The posterior and exact-xi endpoints are fixed-sample, finite, "
            "and declared in advance: one master-mixture confidence event and "
            "one KL term per selected pair. The countable foundation is also "
            "fixed-sample and stops at per-entry prior moments; its posterior "
            "and xi selector lift is open. The separately budgeted rational "
            "risk theorem remains a distinct two-event result. No lane gives "
            "all-real or time-uniform inference."
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


def parse_lean_declarations(text: str) -> list[dict[str, Any]]:
    """Return named public-source declarations with namespace-qualified names.

    Comment and string contents are blanked before matching, while newlines are
    preserved so the reported source lines remain exact.
    """
    clean = strip_lean_comments_and_strings(text)
    lines = clean.splitlines()
    namespace_at_line: list[str] = []
    scopes: list[tuple[str, str]] = []

    for line in lines:
        namespace_at_line.append(
            ".".join(name for scope_kind, name in scopes if scope_kind == "namespace")
        )
        stripped = line.strip()
        namespace_match = re.fullmatch(r"namespace\s+(\S+)", stripped)
        if namespace_match:
            scopes.append(("namespace", namespace_match.group(1)))
            continue
        section_match = re.fullmatch(r"section(?:\s+(\S+))?", stripped)
        if section_match:
            scopes.append(("section", section_match.group(1) or ""))
            continue
        if re.fullmatch(r"end(?:\s+\S+)?", stripped) and scopes:
            scopes.pop()

    declarations: list[dict[str, Any]] = []
    for match in LEAN_DECLARATION_PATTERN.finditer(clean):
        keyword = match.group("keyword")
        raw_name = match.group("name")
        line = clean.count("\n", 0, match.start("keyword")) + 1
        namespace = namespace_at_line[line - 1] if line <= len(namespace_at_line) else ""
        qualified_name = f"{namespace}.{raw_name}" if namespace else raw_name
        declarations.append(
            {
                "keyword": keyword,
                "kind": LEAN_DECLARATION_KINDS[keyword],
                "raw_name": raw_name,
                "qualified_name": qualified_name,
                "line": line,
            }
        )
    return declarations


def resolve_declaration_from_text(
    text: str, name: str, source: str = "Lean source"
) -> dict[str, Any]:
    """Resolve a mapped declaration exactly/full-name first, then by short name.

    Resolution is deliberately fail-closed: missing and ambiguous declarations
    are errors, never silently treated as theorems or omitted from generated data.
    """
    declarations = parse_lean_declarations(text)
    exact = [
        decl
        for decl in declarations
        if decl["raw_name"] == name
        or decl["qualified_name"] == name
        or decl["qualified_name"].endswith(f".{name}")
    ]
    if len(exact) == 1:
        return exact[0]
    if len(exact) > 1:
        matches = ", ".join(
            f"{decl['keyword']} {decl['qualified_name']}:{decl['line']}" for decl in exact
        )
        raise ValueError(
            f"{source}: ambiguous exact/full declaration {name!r}: {matches}"
        )

    short_name = name.rsplit(".", 1)[-1]
    short = [
        decl
        for decl in declarations
        if decl["raw_name"].rsplit(".", 1)[-1] == short_name
    ]
    if len(short) == 1:
        return short[0]
    if len(short) > 1:
        matches = ", ".join(
            f"{decl['keyword']} {decl['qualified_name']}:{decl['line']}" for decl in short
        )
        raise ValueError(f"{source}: ambiguous short declaration {name!r}: {matches}")
    raise ValueError(f"{source}: declaration {name!r} was not found")


@lru_cache(maxsize=None)
def _source_declarations(path: Path) -> tuple[dict[str, Any], ...]:
    if not path.exists():
        raise ValueError(f"Lean source does not exist: {path.relative_to(ROOT)}")
    return tuple(parse_lean_declarations(path.read_text(encoding="utf-8")))


def resolve_source_declaration(path: Path, name: str) -> dict[str, Any]:
    """Resolve `name` in `path` without accepting missing/ambiguous matches."""
    declarations = _source_declarations(path)
    exact = [
        decl
        for decl in declarations
        if decl["raw_name"] == name
        or decl["qualified_name"] == name
        or decl["qualified_name"].endswith(f".{name}")
    ]
    source = path.relative_to(ROOT).as_posix()
    if len(exact) == 1:
        return exact[0]
    if len(exact) > 1:
        matches = ", ".join(
            f"{decl['keyword']} {decl['qualified_name']}:{decl['line']}" for decl in exact
        )
        raise ValueError(
            f"{source}: ambiguous exact/full declaration {name!r}: {matches}"
        )

    short_name = name.rsplit(".", 1)[-1]
    short = [
        decl
        for decl in declarations
        if decl["raw_name"].rsplit(".", 1)[-1] == short_name
    ]
    if len(short) == 1:
        return short[0]
    if len(short) > 1:
        matches = ", ".join(
            f"{decl['keyword']} {decl['qualified_name']}:{decl['line']}" for decl in short
        )
        raise ValueError(f"{source}: ambiguous short declaration {name!r}: {matches}")
    raise ValueError(f"{source}: declaration {name!r} was not found")


def source_resolution_self_test() -> None:
    sample = '''
namespace Outer
-- theorem commented : True := by trivial
theorem same : True := by trivial
namespace Inner
/-- def documented : Nat := 0 -/
def same : Nat := 0
def quoted : String := "lemma fake : True := by trivial"
end Inner
lemma unique : True := by trivial
end Outer
'''
    outer = resolve_declaration_from_text(sample, "Outer.same", "self-test")
    inner = resolve_declaration_from_text(sample, "Outer.Inner.same", "self-test")
    unique = resolve_declaration_from_text(sample, "unique", "self-test")
    assert (outer["kind"], outer["line"]) == ("theorem", 4)
    assert (inner["kind"], inner["line"]) == ("definition", 7)
    assert unique["kind"] == "theorem"
    try:
        resolve_declaration_from_text(sample, "same", "self-test")
    except ValueError as error:
        assert "ambiguous" in str(error)
    else:
        raise AssertionError("ambiguous short names must fail closed")
    try:
        resolve_declaration_from_text(sample, "missing", "self-test")
    except ValueError as error:
        assert "not found" in str(error)
    else:
        raise AssertionError("missing declarations must fail closed")

    offset_sample = """theorem commented /- outer /- nested -/ comment -/ : True := by
  trivial
"""
    stripped = strip_lean_comments_and_strings(offset_sample)
    assert len(stripped) == len(offset_sample)
    assert [i for i, ch in enumerate(stripped) if ch == "\n"] == [
        i for i, ch in enumerate(offset_sample) if ch == "\n"
    ]
    commented = resolve_declaration_from_text(
        offset_sample, "commented", "offset self-test"
    )
    assert (commented["line"], commented["kind"]) == (1, "theorem")


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
                "kind": resolve_source_declaration(
                    ROOT
                    / "FormalSLT"
                    / Path(module.strip("`").replace(".", "/") + ".lean"),
                    name.strip("`"),
                )["kind"],
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
    parser.add_argument(
        "--self-test", action="store_true", help="test fail-closed Lean declaration resolution"
    )
    args = parser.parse_args()

    if args.self_test:
        source_resolution_self_test()
        print("source resolution self-test passed")
        return 0

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
