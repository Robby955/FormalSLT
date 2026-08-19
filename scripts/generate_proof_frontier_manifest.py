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
            "finite-state trajectories with deterministic start and arbitrary "
            "fixed prefix-dependent probability kernels and bounded prefix/"
            "next-state scores; the semantic layer derives exact conditional "
            "risk, centering, and a sharp one-quarter variance proxy. A fixed "
            "score functional may encode an online update rule whose current "
            "prediction is chosen before the next state arrives. A finite "
            "trajectory adapter gives all-positive-time, all-posterior, "
            "all-atom PAC-Bayes control for a predeclared catalog of such "
            "scores. The Markov squared-loss theorem is a specialization"
        ),
        "difficulty": "medium",
        "source": "docs/roadmap.md#near-term",
        "next_step": (
            "Add a supplied initial distribution, controlled kernels, and an "
            "interface for catalogs constructed from auxiliary random data. "
            "Continue empirical-variance and normalized countable or "
            "predictable tilt work in the concentration layer."
        ),
        "boundary": (
            "TrajectoryRisk alone is a path-semantics and conditional-"
            "expectation bridge. TrajectoryPACBayes adds one measurable "
            "confidence event for finite predeclared catalogs, including "
            "fixed-in-advance online update rules; the posterior and one "
            "finite tilt atom may be selected after the path. The theorem "
            "does not validate creating catalog members after observing their "
            "scored outcomes, and it does not cover random initial laws, "
            "controlled kernels, arbitrary joint predictor--tilt posteriors, "
            "countable or all-real tilt control, empirical variance, "
            "continuous state spaces, multistep prediction, optional stopping, "
            "or stationary long-run risk."
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
        "scope": (
            "finite-outcome continuous entropy-integral endpoints under explicit "
            "total-boundedness, separable-terminal, modulus, and boundary "
            "certificates, plus concrete selected-cover capstones"
        ),
        "difficulty": "hard",
        "source": "docs/next-lane.md",
        "next_step": (
            "Construct the measurable-supremum and separable-process bridge on "
            "a general probability space, beyond the checked finite-outcome "
            "and supplied-boundary interfaces."
        ),
        "boundary": (
            "The entropy-integral algebra and finite-outcome endpoint are "
            "checked. The library does not yet construct arbitrary measurable "
            "suprema or discharge a general measure-side chaining budget."
        ),
    },
    {
        "id": "anytime-boundary-lower-bounds",
        "status": "partially_closed",
        "scope": (
            "deterministic one-sided boundaries for the infinite fair-"
            "Rademacher walk; an unconditional fixed-Gaussian-tail sqrt-n "
            "floor from the CLT and Portmanteau theorem; and an unconditional "
            "unbounded sqrt-n floor from disjoint blocks and the second "
            "Borel--Cantelli lemma"
        ),
        "difficulty": "hard",
        "source": (
            "docs/assumptions-and-nonclaims.md#universal-fair-sign-anytime-boundary-lower-bound"
        ),
        "next_step": (
            "Prove the fair-sign upper law of the iterated logarithm needed by "
            "the checked constant-one reduction, then study structured tilt-"
            "family and two-sided minimax lower bounds."
        ),
        "boundary": (
            "The unconditional result is specific to deterministic one-sided "
            "boundaries under the fair-sign product law. It proves divergence "
            "after sqrt-n normalization, not the sqrt(2 n log log n) rate. "
            "The sharp limsup theorem explicitly assumes the still-unproved "
            "FairSignUpperLIL proposition and a boundedness side condition; it "
            "does not close a full LIL theorem."
        ),
    },
    {
        "id": "pac-bayes-all-real-lambda",
        "status": "partially_closed",
        "scope": (
            "finite hypotheses plus spherical-Gaussian continuous-hypothesis "
            "single-pair and finite fixed-catalog specializations; a generic "
            "finite normalized hypothesis--tilt e-process with one Ville "
            "event and selected-atom weight penalty; a finite adaptive-"
            "selection guardrail with exact predeclared-weight/Kraft upper "
            "bounds and diagonal-witness cardinality necessity; a countable-"
            "allocation guardrail with a blockwise reciprocal-weight obstruction "
            "and geometric-epoch log-log subsequence cost; a forward finite-"
            "hypothesis predictable-residual e-process with a hybrid Bessel "
            "lower envelope and finite weighted PAC-Bayes tilt catalog; and "
            "an offline reverse all-sample-size empirical-Bernstein endpoint "
            "over arbitrary measurable hypothesis spaces"
        ),
        "difficulty": "medium-hard",
        "source": "docs/open-formalization-problems.md#near-term",
        "next_step": (
            "Extend the forward finite normalized hypothesis--tilt master to "
            "a countable vanishing-width mixture and measurable hypothesis "
            "priors, then pursue honest all-real localization using continuous "
            "score control or a supremum-to-integral argument. Keep that "
            "forward-process target distinct from the checked offline reverse "
            "continuous-posterior endpoint."
        ),
        "boundary": (
            "The process-level continuous-hypothesis i.i.d. theorem is fixed-"
            "tilt, fixed-posterior, and spherical-Gaussian. The reverse "
            "stitched theorem is instead uniform over finite-KL posteriors on "
            "an arbitrary measurable hypothesis space, but it is an offline "
            "reverse-exchangeability result with declared finite tilts, not a "
            "forward e-process. The new forward hybrid-Bessel PAC-Bayes master "
            "is a genuine finite hypothesis--tilt mixture of predictable-"
            "residual e-processes; its hybrid Bessel expression is only a "
            "pointwise lower envelope and its catalog is finite. Its "
            "informative biased-Boolean receipt has Bessel variance 1/32, "
            "KL = log 2, a theorem-produced good path with risk below "
            "343/1000, and a same-prefix boundary comparison of approximately "
            "0.312 versus 0.760. "
            "A separate fixed-sample countable joint "
            "master has a finite-posterior selector over its predeclared "
            "natural-index catalog, but it is not a process-level or all-real "
            "result. The countable-allocation result is specific to union/"
            "confidence allocation and does not prove a universal LIL or "
            "minimax boundary lower bound. No forward result is simultaneous over arbitrary "
            "continuous posteriors or all real tilts."
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
            "three-piece residual penalty, a closed-form clog-depth dyadic "
            "square-root-plus-linear endpoint, plus a support-aware Nat-indexed "
            "countable master mixture, per-entry prior-moment extraction, "
            "finite-posterior bound, and exact-xi selector; plus a proved "
            "reverse Bessel martingale, reverse joint mean/variance epoch "
            "process, reverse finite catalog, closed-form epoch endpoint, "
            "finite-prefix infinite-product bridge, and one stitched "
            "all-sample-size finite-IID event; plus a continuous-prior "
            "reverse mixture, finite tilt catalog, closed-form epoch bound, "
            "and stitched all-sample-size endpoint over arbitrary measurable "
            "hypothesis spaces; plus a known predictable-residual forward "
            "empirical-Bernstein e-process, exact Welford/Abel identities, a "
            "hybrid Bessel lower envelope, a finite hypothesis--tilt PAC-Bayes "
            "master, and its finite-IID adapter"
        ),
        "difficulty": "hard",
        "source": (
            "docs/open-formalization-problems.md#pac-bayes-empirical-sample-variance"
        ),
        "next_step": (
            "Derive a countable or stitched vanishing-width forward tilt "
            "mixture and extend its PAC-Bayes master to measurable hypothesis "
            "priors. Continue matched-boundary evidence and external review."
        ),
        "boundary": (
            "The stitched reverse-epoch endpoint gives one measurable "
            "infinite-IID event shared by every n >= 2. The continuous-prior "
            "version is uniform over every posterior probability measure on "
            "an arbitrary measurable hypothesis space that is absolutely "
            "continuous with respect to the fixed prior and has an integrable "
            "log-likelihood ratio. It retains finite-valued observations and "
            "is an offline reverse-exchangeability theorem, not a forward "
            "e-process or optional-stopping API. The tilt catalogs are "
            "declared in advance, so there is no all-real optimization. The "
            "continuous product-Gaussian/fair-Boolean receipt gives every "
            "finite set posterior mass zero, has KL = 1/32, and uses an "
            "unscaled zero-one sign-flip mismatch loss that depends on both "
            "hypothesis coordinates and attains both endpoints. Every "
            "nonempty-sample posterior empirical risk is 1/2; at n = 2^20 "
            "and delta = 1/2, the correction is below 1/2 and the theorem-"
            "produced right-hand side is below 1. A checked corollary gives "
            "a path outside the exceptional event. The receipt fixes the "
            "posterior and does not exercise data-dependent continuous-"
            "posterior selection. "
            "Separately, the forward lane packages the actual predictable-"
            "residual process as an e-process and bounds it below by a hybrid "
            "per-hypothesis Bessel penalty. The hybrid expression is not "
            "itself an e-process. Its PAC-Bayes master currently has finite "
            "hypotheses and a declared finite tilt catalog. Its informative "
            "Boolean receipt has Bessel variance 1/32, KL = log 2, a theorem-"
            "produced good path with risk below 343/1000, and a same-prefix "
            "boundary comparison of approximately 0.312 versus 0.760. "
            "The separately budgeted rational risk theorem remains a distinct "
            "two-event result."
        ),
    },
    {
        "id": "sharp-mcdiarmid-product-kernel",
        "status": "closed",
        "scope": (
            "sharp one-sided, lower-tail, and two-sided bounded-differences "
            "concentration for independent finite product coordinates, including "
            "heterogeneous marginal laws and downstream learning wrappers"
        ),
        "difficulty": "hard",
        "source": "docs/roadmap.md#near-term",
        "next_step": (
            "No immediate closure work: reuse the checked sharp kernel in "
            "downstream theorems, or separately study dependent-coordinate "
            "extensions."
        ),
        "boundary": (
            "The sharp product-kernel route assumes independent finite product "
            "coordinates and explicit bounded differences; it is not a dependent-"
            "data concentration theorem."
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


def split_markdown_table_row(line: str) -> list[str]:
    """Split a Markdown table row without treating escaped pipes as columns."""
    return [
        cell.replace(r"\|", "|").strip()
        for cell in re.split(r"(?<!\\)\|", line.strip("|"))
    ]


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

        cells = split_markdown_table_row(line)
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
        assert split_markdown_table_row(
            r"| Declaration | Module | Role with \|escaped\| delimiters |"
        ) == ["Declaration", "Module", "Role with |escaped| delimiters"]
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
