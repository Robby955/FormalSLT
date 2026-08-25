#!/usr/bin/env python3
"""Extract the stitched-confidence-sequence film facts from one Git commit."""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


DEFAULT_BOUND_SHA = "e01f857d1604788be35fdc2f3dc7108851471a88"
DEFAULT_BOUND_TAG = "v0.2.0"
SOURCE_COMMIT_ENV = "FORMALSLT_FILM_SOURCE_COMMIT"
ROOT = Path(__file__).resolve().parents[2]
CONFIG = Path(__file__).with_name("film_config.json")
OUTPUT = Path(__file__).with_name("facts.json")
CLAIM_OUTPUT = Path(__file__).with_name("claim-receipt.json")
TRANSCRIPT_TEMPLATE = Path(__file__).with_name("TRANSCRIPT.template.md")
TRANSCRIPT_OUTPUT = Path(__file__).with_name("TRANSCRIPT.md")
SOCIAL_TRANSCRIPT_TEMPLATE = Path(__file__).with_name(
    "TRANSCRIPT-SOCIAL.template.md"
)
SOCIAL_TRANSCRIPT_OUTPUT = Path(__file__).with_name("TRANSCRIPT-SOCIAL.md")

POLYNOMIAL_FILE = "FormalSLT/AnytimeValid/PolynomialStitchedLIL.lean"
ALLOCATION_FILE = "FormalSLT/AnytimeValid/AllocationLogLog.lean"
MIXTURE_FILE = "FormalSLT/AnytimeValid/MixtureCS.lean"
SUBGAUSSIAN_FILE = "FormalSLT/AnytimeValid/SubGaussianCS.lean"
CHECKER_FILE = "examples/CheckPolynomialStitchedLIL.lean"
MEASURABLE_CHECKER_FILE = "examples/CheckPolynomialStitchedLILMeasurableEvent.lean"
FRONTIER_FILE = "docs/proof-frontier.md"
NONCLAIMS_FILE = "docs/assumptions-and-nonclaims.md"
RELATED_WORK_FILE = "docs/related-work.md"

BASE_PINNED_FILES = (
    POLYNOMIAL_FILE,
    ALLOCATION_FILE,
    MIXTURE_FILE,
    SUBGAUSSIAN_FILE,
    CHECKER_FILE,
    FRONTIER_FILE,
    NONCLAIMS_FILE,
    RELATED_WORK_FILE,
)

MEASURABLE_THEOREM = "polynomialStitchedLIL_explicit_measurable_event"
SOURCE_COMMIT_PATTERN = re.compile(r"[0-9a-f]{40}")


def git(*args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(ROOT), *args],
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    ).stdout


def source_at(source_commit: str, file_name: str) -> str:
    return git("show", f"{source_commit}:{file_name}")


def configured_source_commit() -> str:
    try:
        config = json.loads(CONFIG.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise SystemExit(f"cannot read source commit from {CONFIG}: {error}") from error
    source_commit = config.get("source_commit")
    if not isinstance(source_commit, str):
        raise SystemExit(f"missing string source_commit in {CONFIG}")
    return source_commit


def resolve_source_commit(requested: str) -> str:
    if SOURCE_COMMIT_PATTERN.fullmatch(requested) is None:
        raise SystemExit(
            "source commit must be an exact lowercase 40-character Git SHA"
        )
    try:
        resolved = git("rev-parse", f"{requested}^{{commit}}").strip()
    except subprocess.CalledProcessError as error:
        raise SystemExit(f"source commit does not resolve: {requested}") from error
    if resolved != requested:
        raise SystemExit(
            f"source commit did not resolve exactly: requested {requested}, got {resolved}"
        )
    return resolved


def require_public_main_commit(source_commit: str) -> None:
    """Reject an explicit film binding until the exact commit is on origin/main."""
    completed = subprocess.run(
        [
            "git",
            "-C",
            str(ROOT),
            "merge-base",
            "--is-ancestor",
            source_commit,
            "origin/main",
        ],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if completed.returncode != 0:
        raise SystemExit(
            f"refusing film binding: {source_commit} is not reachable from "
            "the fetched origin/main; fetch after the theorem PR merges"
        )


def require(
    pattern: str,
    source: str,
    description: str,
    *,
    flags: int = re.MULTILINE | re.DOTALL,
) -> re.Match[str]:
    match = re.search(pattern, source, flags=flags)
    if match is None:
        raise SystemExit(f"missing pinned fact: {description}")
    return match


def line_number(source: str, offset: int) -> int:
    return source.count("\n", 0, offset) + 1


def declaration_statement(
    source: str,
    kind: str,
    name: str,
) -> tuple[str, int]:
    match = require(
        rf"^{kind}\s+{re.escape(name)}\b(?P<statement>[\s\S]*?)\s*:=\s*by",
        source,
        f"complete {kind} statement {name}",
    )
    return match.group("statement"), line_number(source, match.start())


def anchor(
    source: str,
    file_name: str,
    name: str,
    pattern: str,
    description: str,
) -> dict[str, Any]:
    match = require(pattern, source, description)
    return {
        "file": file_name,
        "line": line_number(source, match.start()),
        "name": name,
    }


def canonical_json(data: dict[str, Any]) -> str:
    return json.dumps(data, indent=2, ensure_ascii=False) + "\n"


def rendered_transcripts(facts: dict[str, Any]) -> dict[Path, str]:
    theorem_fqn = f"{facts['result']['module']}.{facts['result']['theorem']}"
    if facts["result"]["event_measurable"]:
        values = {
            "MAIN_CONFIDENCE_PARAGRAPH": (
                "The theorem's canonical measurable event `G` satisfies "
                "`mu.real(G) >= 1 - delta`. For every\n"
                "`omega` in `G` and every sample size `n >= 4`,\n"
                "`|(1/n) sum_(k<n) X_k(omega)| < W_n`."
            ),
            "SOCIAL_CONFIDENCE_PARAGRAPH": (
                "The theorem's measurable event `G` has\n"
                "`mu.real(G) >= 1 - delta`, and on `G` the running-mean bound "
                "holds for every\n"
                "`n >= 4`."
            ),
            "MEASURABILITY_SENTENCE": (
                "The theorem proves that `G` is measurable, so the displayed\n"
                "mass bound is an ordinary probability-at-least statement."
            ),
            "SOURCE_DESCRIPTION": f"FormalSLT main commit\n`{facts['commit']}`",
        }
    else:
        values = {
            "MAIN_CONFIDENCE_PARAGRAPH": (
                "The theorem produces a set `G` satisfying "
                "`mu.real(G^c) <= delta`. For every\n"
                "`omega` in `G` and every sample size `n >= 4`,\n"
                "`|(1/n) sum_(k<n) X_k(omega)| < W_n`."
            ),
            "SOCIAL_CONFIDENCE_PARAGRAPH": (
                "The theorem produces a set\n"
                "`G` with `mu.real(G^c) <= delta`, and on `G` the running-mean "
                "bound holds for\n"
                "every `n >= 4`."
            ),
            "MEASURABILITY_SENTENCE": (
                "The theorem does not assert that `G` is measurable, so the\n"
                "mass statement is not paraphrased as a probability-at-least\n"
                "statement."
            ),
            "SOURCE_DESCRIPTION": (
                f"FormalSLT {DEFAULT_BOUND_TAG} commit\n`{facts['commit']}`"
            ),
        }
    values["THEOREM_FQN"] = theorem_fqn

    rendered: dict[Path, str] = {}
    for template, output in (
        (TRANSCRIPT_TEMPLATE, TRANSCRIPT_OUTPUT),
        (SOCIAL_TRANSCRIPT_TEMPLATE, SOCIAL_TRANSCRIPT_OUTPUT),
    ):
        text = template.read_text(encoding="utf-8")
        for key, value in values.items():
            text = text.replace(f"{{{{{key}}}}}", value)
        unresolved = re.findall(r"\{\{[A-Z_]+\}\}", text)
        if unresolved:
            raise SystemExit(
                f"unresolved transcript placeholders in {template.name}: "
                f"{', '.join(sorted(set(unresolved)))}"
            )
        rendered[output] = text
    return rendered


def build_claim_receipt(facts: dict[str, Any]) -> dict[str, Any]:
    """Return the exact public claim surface displayed by both compositions."""
    return {
        "schema": "formalslt-stitched-lil-claim-receipt-v2",
        "source_ref": facts["source_ref"],
        "release_tag": facts["release_tag"],
        "source_profile": facts["source_profile"],
        "theorem_source_commit": facts["commit"],
        "theorem_blob_oid": facts["blob_oids"][POLYNOMIAL_FILE],
        "theorem_module": facts["result"]["module"],
        "theorem": facts["result"]["theorem"],
        "classification": facts["classification"],
        "public_claim": facts["public_claim"],
        "assumptions": facts["process_model"],
        "display_math": {
            "selector": r"j=j(n),\qquad 4^{j+1}\le n<4^{j+2}",
            "budget": r"B_j=\log\frac{2}{\delta}+\log(j+1)+\log(j+2)",
            "width": r"W_n=2\sqrt{\frac{2\sigma^2B_j}{n}}+\frac{4bB_j}{3n}",
            "width_first_line": r"W_n=2\sqrt{\frac{2\sigma^2B_j}{n}}",
            "width_second_line": r"\phantom{W_n={}}+\frac{4bB_j}{3n}",
            "confidence_mass": facts["result"]["confidence_tex"],
            "event_condition": r"\omega\in G\Longrightarrow\forall n\ge4:",
            "event_bound": r"\left|\frac1n\sum_{k<n}X_k(\omega)\right|<W_n",
            "event_conclusion": (
                r"\omega\in G\Longrightarrow\forall n\ge4:\ "
                r"\left|\frac1n\sum_{k<n}X_k(\omega)\right|<W_n"
            ),
        },
        "nonclaims": facts["nonclaims"],
        "anchors": facts["anchors"],
    }


def extract(source_commit: str) -> dict[str, Any]:
    measurable_profile = source_commit != DEFAULT_BOUND_SHA
    if not measurable_profile:
        tagged = git("rev-parse", f"{DEFAULT_BOUND_TAG}^{{commit}}").strip()
        if tagged != source_commit:
            raise SystemExit(
                f"{DEFAULT_BOUND_TAG} resolves to {tagged}, expected theorem "
                f"commit {source_commit}"
            )

    polynomial = source_at(source_commit, POLYNOMIAL_FILE)
    allocation = source_at(source_commit, ALLOCATION_FILE)
    mixture = source_at(source_commit, MIXTURE_FILE)
    subgaussian = source_at(source_commit, SUBGAUSSIAN_FILE)
    checker = source_at(source_commit, CHECKER_FILE)
    measurable_checker = (
        source_at(source_commit, MEASURABLE_CHECKER_FILE)
        if measurable_profile
        else ""
    )
    frontier = source_at(source_commit, FRONTIER_FILE)
    nonclaims = source_at(source_commit, NONCLAIMS_FILE)
    related = source_at(source_commit, RELATED_WORK_FILE)

    require(
        r"Epoch `j` receives confidence weight\s+"
        r"`1 / \(\(j\+1\)\(j\+2\)\)`",
        polynomial,
        "module-level polynomial confidence allocation",
    )
    require(
        r"The exact epoch budget is\s+\n\s*"
        r"`log \(2 / delta\) \+ log \(j\+1\) \+ log \(j\+2\)`",
        polynomial,
        "module-level exact epoch budget",
    )
    require(
        r"This is an allocated fixed-tilt stitch; it does not\s+"
        r"claim that the countable union is itself an e-process",
        polynomial,
        "module-level countable-e-process nonclaim",
    )

    require(
        r"def\s+IncrementAdapted\b[\s\S]*?"
        r"\(X\s*:\s*ℕ\s*→\s*Ω\s*→\s*ℝ\)\s*:\s*Prop\s*:=\s*\n\s*"
        r"∀\s+k,\s*StronglyMeasurable\[ℱ\s*\(k\s*\+\s*1\)\]\s*\(X\s+k\)",
        mixture,
        "increment X_k is revealed at filtration time k+1",
    )

    require(
        r"def\s+polynomialGeometricEpochIndex\s+\(n\s*:\s*ℕ\)\s*:\s*ℕ\s*:=\s*"
        r"\(Nat\.log\s+4\s+n\)\.pred",
        polynomial,
        "exact selected epoch index",
    )
    require(
        r"def\s+polynomialGeometricEpochFloor\s+\(j\s*:\s*ℕ\)\s*:\s*ℕ\s*:=\s*"
        r"4\s*\^\s*\(j\s*\+\s*1\)",
        polynomial,
        "factor-four epoch floor",
    )
    require(
        r"def\s+polynomialGeometricEpochHorizon\s+\(j\s*:\s*ℕ\)\s*:\s*ℕ\s*:=\s*"
        r"4\s*\^\s*\(j\s*\+\s*2\)",
        polynomial,
        "factor-four epoch horizon",
    )

    epoch_spec, epoch_spec_line = declaration_statement(
        polynomial,
        "theorem",
        "polynomialGeometricEpochIndex_spec",
    )
    for shape, description in (
        (r"4\s*<=\s*n", "epoch selector lower sample-size premise"),
        (
            r"polynomialGeometricEpochFloor\s*"
            r"\(polynomialGeometricEpochIndex\s+n\)\s*<=\s*n",
            "selected epoch floor bound",
        ),
        (
            r"n\s*<\s*polynomialGeometricEpochHorizon\s*"
            r"\(polynomialGeometricEpochIndex\s+n\)",
            "selected epoch horizon bound",
        ),
    ):
        require(shape, epoch_spec, description)

    budget_statement, budget_line = declaration_statement(
        polynomial,
        "theorem",
        "polynomialGeometricEpochBudget_eq",
    )
    for shape, description in (
        (r"Real\.log\s*\(2\s*/\s*delta\)", "two-sided confidence cost"),
        (r"Real\.log\s*\(\(j\s*:\s*ℝ\)\s*\+\s*1\)", "first epoch-index cost"),
        (r"Real\.log\s*\(\(j\s*:\s*ℝ\)\s*\+\s*2\)", "second epoch-index cost"),
    ):
        require(shape, budget_statement, description)

    failure_statement, failure_line = declaration_statement(
        polynomial,
        "theorem",
        "polynomialStitchedLILFailure_mass_le",
    )
    require(
        r"μ\.real\s*\(polynomialStitchedLILFailure\s+X\s+sigma2\s+b\s+delta\)\s*"
        r"<=\s*delta",
        failure_statement,
        "countable union failure mass",
    )

    result_statement, result_line = declaration_statement(
        polynomial,
        "theorem",
        "exists_polynomialStitchedLIL_explicit_event",
    )
    result_shapes = (
        (r"\[IsProbabilityMeasure\s+μ\]", "probability-measure model"),
        (r"hδ\s*:\s*0\s*<\s*delta", "positive failure budget"),
        (r"hδ_one\s*:\s*delta\s*<=\s*1", "failure budget at most one"),
        (r"hb\s*:\s*0\s*<\s*b", "positive increment bound"),
        (r"hσ\s*:\s*0\s*<\s*sigma2", "positive variance proxy"),
        (r"hX_meas\s*:\s*∀\s+k,\s*Measurable\s*\(X\s+k\)", "measurable increments"),
        (r"hX_int\s*:\s*∀\s+k,\s*Integrable\s*\(X\s+k\)\s+μ", "integrable increments"),
        (r"hX_adapted\s*:\s*IncrementAdapted\s+ℱ\s+X", "adapted increments"),
        (
            r"hbound\s*:\s*∀\s+k,\s*∀ᵐ\s+omega\s+∂μ,\s*\|X\s+k\s+omega\|\s*<=\s*b",
            "almost-everywhere bounded increments",
        ),
        (
            r"hcenter\s*:\s*∀\s+k,\s*μ\[X\s+k\s*\|\s*ℱ\s+k\]\s*=ᵐ\[μ\]\s*0",
            "almost-everywhere conditional centering",
        ),
        (
            r"hvar\s*:\s*∀\s+k,\s*μ\[fun\s+omega\s*=>\s*\(X\s+k\s+omega\)\s*\^\s*2\s*\|\s*ℱ\s+k\]\s*≤ᵐ\[μ\]\s*fun\s+_\s*=>\s*sigma2",
            "full almost-everywhere conditional second-moment relation",
        ),
        (r"∃\s+goodEvent\s*:\s*Set\s+Ω", "single good event"),
        (r"μ\.real\s+goodEventᶜ\s*<=\s*delta", "failure mass at most delta"),
        (r"∀\s+omega\s+∈\s+goodEvent,\s*∀\s+n\s*:\s*ℕ,\s*4\s*<=\s*n", "all n at least four"),
        (r"\|runningMean\s+X\s+n\s+omega\|\s*<", "two-sided running mean"),
        (r"2\s*\*\s*Real\.sqrt", "square-root constant"),
        (r"4\s*\*\s*b", "linear constant"),
        (r"3\s*\*\s*\(n\s*:\s*ℝ\)", "linear denominator"),
    )
    for shape, description in result_shapes:
        require(shape, result_statement, description)
    exact_result_shape = (
        r"∀\s+omega\s+∈\s+goodEvent,\s*∀\s+n\s*:\s*ℕ,\s*4\s*<=\s*n\s*->\s*"
        r"\|runningMean\s+X\s+n\s+omega\|\s*<\s*"
        r"2\s*\*\s*Real\.sqrt\s*\(\s*2\s*\*\s*sigma2\s*\*\s*"
        r"polynomialGeometricEpochBudget\s+delta\s*"
        r"\(polynomialGeometricEpochIndex\s+n\)\s*/\s*\(n\s*:\s*ℝ\)\s*\)\s*\+\s*"
        r"4\s*\*\s*b\s*\*\s*polynomialGeometricEpochBudget\s+delta\s*"
        r"\(polynomialGeometricEpochIndex\s+n\)\s*/\s*"
        r"\(3\s*\*\s*\(n\s*:\s*ℝ\)\)"
    )
    require(
        exact_result_shape,
        result_statement,
        "complete explicit width and all-sample-size quantifier order",
    )
    measurable_result_line: int | None = None
    if measurable_profile:
        measurable_result, measurable_result_line = declaration_statement(
            polynomial,
            "theorem",
            MEASURABLE_THEOREM,
        )
        for shape, description in result_shapes[:11]:
            require(shape, measurable_result, f"measurable endpoint {description}")
        for shape, description in (
            (
                r"MeasurableSet\s*\(polynomialStitchedLILGoodEvent\s+"
                r"X\s+sigma2\s+b\s+delta\)",
                "measurable canonical event",
            ),
            (
                r"1\s*-\s*delta\s*<=\s*μ\.real\s*"
                r"\(polynomialStitchedLILGoodEvent\s+X\s+sigma2\s+b\s+delta\)",
                "ordinary probability at least one minus delta",
            ),
            (
                r"∀\s+omega\s+∈\s+polynomialStitchedLILGoodEvent\s+"
                r"X\s+sigma2\s+b\s+delta,\s*∀\s+n\s*:\s*ℕ,\s*4\s*<=\s*n",
                "single canonical event controls every n at least four",
            ),
            (r"\|runningMean\s+X\s+n\s+omega\|\s*<", "two-sided running mean"),
            (r"2\s*\*\s*Real\.sqrt", "square-root constant"),
            (r"4\s*\*\s*b", "linear constant"),
            (r"3\s*\*\s*\(n\s*:\s*ℝ\)", "linear denominator"),
        ):
            require(shape, measurable_result, f"measurable endpoint {description}")
        require(
            rf"#check\s+{MEASURABLE_THEOREM}",
            measurable_checker,
            "measurable endpoint public check",
        )
        require(
            rf"#print\s+axioms\s+{MEASURABLE_THEOREM}",
            measurable_checker,
            "measurable endpoint public axiom query",
        )
    require(
        r"def\s+runningMean[\s\S]*?\s*:=\s*\n\s*runningSum\s+X\s+n\s+ω\s*/\s*\(n\s*:\s*ℝ\)",
        subgaussian,
        "running mean is the first-n sum divided by n",
    )

    require(
        r"def\s+polynomialEpochWeight\s+\(k\s*:\s*ℕ\)\s*:\s*ℝ\s*:=\s*"
        r"1\s*/\s*\(\(\(k\s*:\s*ℝ\)\s*\+\s*1\)\s*\*\s*"
        r"\(\(k\s*:\s*ℝ\)\s*\+\s*2\)\)",
        allocation,
        "polynomial epoch weight formula",
    )
    has_sum_statement, has_sum_line = declaration_statement(
        allocation,
        "theorem",
        "polynomialEpochWeight_hasSum",
    )
    require(
        r"HasSum\s+polynomialEpochWeight\s+1",
        has_sum_statement,
        "polynomial weights sum exactly to one",
    )

    checker_receipts = (
        (
            r"theorem\s+first_epoch_index\s*:\s*"
            r"polynomialGeometricEpochIndex\s+4\s*=\s*0",
            "first epoch index",
        ),
        (
            r"theorem\s+first_epoch_floor\s*:\s*"
            r"polynomialGeometricEpochFloor\s+0\s*=\s*4",
            "first epoch floor",
        ),
        (
            r"theorem\s+first_epoch_budget\s*:\s*"
            r"polynomialGeometricEpochBudget\s*\(1\s*/\s*2\)\s+0\s*=\s*Real\.log\s+8",
            "first epoch budget",
        ),
        (
            r"#check\s+exists_polynomialStitchedLIL_explicit_event",
            "public endpoint check",
        ),
        (
            r"#print\s+axioms\s+exists_polynomialStitchedLIL_explicit_event",
            "public endpoint axiom query",
        ),
    )
    for pattern, description in checker_receipts:
        require(pattern, checker, description)

    require(
        r"no full LIL is claimed",
        frontier,
        "proof-frontier LIL nonclaim",
        flags=re.IGNORECASE,
    )
    require(
        r"The library does not prove `FairSignUpperLIL`, a general\s+"
        r"process-level LIL",
        nonclaims,
        "general process-level LIL remains open",
    )
    require(
        r"This is a source-level audit, not an exhaustive prior-art search",
        related,
        "bounded prior-art audit scope",
    )
    require(
        r"FormalSLT makes no broad priority claim",
        related,
        "no broad priority claim",
    )
    anchors = [
        anchor(
            mixture,
            MIXTURE_FILE,
            "IncrementAdapted",
            r"^def\s+IncrementAdapted\b",
            "predictable-increment adaptedness definition",
        ),
        anchor(
            polynomial,
            POLYNOMIAL_FILE,
            "polynomialGeometricEpochIndex_spec",
            r"^theorem\s+polynomialGeometricEpochIndex_spec\b",
            "epoch-index theorem anchor",
        ),
        {
            "file": POLYNOMIAL_FILE,
            "line": budget_line,
            "name": "polynomialGeometricEpochBudget_eq",
        },
        {
            "file": POLYNOMIAL_FILE,
            "line": failure_line,
            "name": "polynomialStitchedLILFailure_mass_le",
        },
        {
            "file": POLYNOMIAL_FILE,
            "line": result_line,
            "name": "exists_polynomialStitchedLIL_explicit_event",
        },
        {
            "file": ALLOCATION_FILE,
            "line": has_sum_line,
            "name": "polynomialEpochWeight_hasSum",
        },
        anchor(
            checker,
            CHECKER_FILE,
            "first_epoch_budget",
            r"^theorem\s+first_epoch_budget\b",
            "checker first-epoch budget anchor",
        ),
        anchor(
            checker,
            CHECKER_FILE,
            "axioms:exists_polynomialStitchedLIL_explicit_event",
            r"^#print\s+axioms\s+exists_polynomialStitchedLIL_explicit_event\s*$",
            "checker axiom-query anchor",
        ),
    ]
    if measurable_profile:
        if measurable_result_line is None:
            raise AssertionError("measurable result line was not recorded")
        anchors.extend(
            [
                {
                    "file": POLYNOMIAL_FILE,
                    "line": measurable_result_line,
                    "name": MEASURABLE_THEOREM,
                },
                anchor(
                    measurable_checker,
                    MEASURABLE_CHECKER_FILE,
                    f"axioms:{MEASURABLE_THEOREM}",
                    rf"^#print\s+axioms\s+{MEASURABLE_THEOREM}\s*$",
                    "measurable checker axiom-query anchor",
                ),
            ]
        )

    pinned_files = BASE_PINNED_FILES + (
        (MEASURABLE_CHECKER_FILE,) if measurable_profile else ()
    )
    blob_oids = {
        file_name: git("rev-parse", f"{source_commit}:{file_name}").strip()
        for file_name in pinned_files
    }

    source_profile = (
        "measurable-probability-event-v1"
        if measurable_profile
        else "v0.2-outer-mass-event-v1"
    )
    result_theorem = (
        MEASURABLE_THEOREM
        if measurable_profile
        else "exists_polynomialStitchedLIL_explicit_event"
    )
    public_claim = (
        "An explicit two-sided confidence sequence for bounded increments "
        "revealed at time k+1 and centered given F_k; one measurable event "
        "of probability at least 1 - delta controls every n >= 4 with an "
        "exact iterated-logarithm-order budget."
        if measurable_profile
        else
        "An explicit two-sided confidence sequence for bounded increments "
        "revealed at time k+1 and centered given F_k; one failure set of mass "
        "at most delta controls every n >= 4 with an exact "
        "iterated-logarithm-order budget."
    )
    confidence_statement = (
        "1 - delta <= mu.real goodEvent"
        if measurable_profile
        else "mu.real goodEvent^c <= delta"
    )
    confidence_tex = (
        r"\mu_{\mathbb R}(G)\ge 1-\delta"
        if measurable_profile
        else r"\mu_{\mathbb R}(G^{\mathsf c})\le\delta"
    )
    result_nonclaims = [
        "not the law of the iterated logarithm",
        "not a sharp-constant or optimality result",
        "the countable confidence allocation is not itself an e-process",
        "not an optional-stopping theorem",
        "not a predictable or data-selected tilt construction",
    ]
    if not measurable_profile:
        result_nonclaims.append(
            "goodEvent is a Set; its measurability is not asserted by the theorem"
        )
    result_nonclaims.append("no first-formalization or priority claim")

    return {
        "schema": "formalslt-stitched-lil-facts-v2",
        "commit": source_commit,
        "short_commit": source_commit[:7],
        "source_ref": (
            DEFAULT_BOUND_TAG
            if source_commit == DEFAULT_BOUND_SHA
            else f"origin/main@{source_commit}"
        ),
        "release_tag": (
            DEFAULT_BOUND_TAG if source_commit == DEFAULT_BOUND_SHA else None
        ),
        "source_profile": source_profile,
        "blob_oids": blob_oids,
        "public_claim": public_claim,
        "classification": "FORMALIZED COMPOSITION; NO PRIORITY CLAIM",
        "process_model": [
            "mu is a probability measure",
            "X_k is measurable and integrable",
            "X_k is revealed at time k+1 (strongly measurable with respect to F_(k+1))",
            "|X_k| <= b almost everywhere",
            "E[X_k | F_k] = 0 almost everywhere",
            "E[X_k^2 | F_k] <= sigma^2 almost everywhere",
            "0 < delta <= 1, b > 0, sigma^2 > 0",
        ],
        "epochs": {
            "floor": "4^(j+1)",
            "exclusive_horizon": "4^(j+2)",
            "selected_index": "(Nat.log 4 n).pred",
            "examples": ["[4,16)", "[16,64)", "[64,256)", "[256,1024)"],
        },
        "allocation": {
            "weight": "1 / ((j+1)(j+2))",
            "telescoping_form": "1/(j+1) - 1/(j+2)",
            "total_mass": "sum_j w_j = 1",
            "two_sided_epoch_budget": (
                "log(2/delta) + log(j+1) + log(j+2)"
            ),
        },
        "result": {
            "module": "FormalSLT.AnytimeValid.PolynomialStitchedLIL",
            "theorem": result_theorem,
            "minimum_n": 4,
            "failure_mass": "mu.real goodEvent^c <= delta",
            "confidence_statement": confidence_statement,
            "confidence_tex": confidence_tex,
            "event_measurable": measurable_profile,
            "budget_symbol": "B_j",
            "budget": "log(2/delta) + log(j+1) + log(j+2)",
            "width_symbol": "W_n",
            "width": (
                "2 sqrt(2 sigma^2 B_j / n) + 4 b B_j / (3n)"
            ),
            "conclusion": "|runningMean X n| < W_n for every n >= 4",
        },
        "checker": {
            "file": (
                MEASURABLE_CHECKER_FILE if measurable_profile else CHECKER_FILE
            ),
            "first_epoch_index": "j(4) = 0",
            "first_epoch_floor": "N_0 = 4",
            "first_epoch_budget": "delta = 1/2, j = 0: B_0 = log 8",
            "queries_public_axioms": True,
        },
        "nonclaims": result_nonclaims,
        "anchors": anchors,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source-commit",
        metavar="SHA",
        help=(
            "exact 40-character commit to bind; non-v0.2 commits must be "
            "reachable from the fetched origin/main and expose the measurable endpoint"
        ),
    )
    action = parser.add_mutually_exclusive_group()
    action.add_argument(
        "--write",
        action="store_true",
        help=(
            "replace fact receipts; with an explicit source override, also bind "
            "film_config.json to that commit"
        ),
    )
    action.add_argument(
        "--print",
        dest="print_only",
        action="store_true",
        help="print extracted facts without reading or writing facts.json",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    environment_commit = os.environ.get(SOURCE_COMMIT_ENV)
    if args.source_commit and environment_commit:
        raise SystemExit(
            f"set the source commit with either --source-commit or {SOURCE_COMMIT_ENV}, not both"
        )
    source_override = args.source_commit or environment_commit
    requested = source_override or configured_source_commit()
    source_commit = resolve_source_commit(requested)
    if source_commit != DEFAULT_BOUND_SHA:
        require_public_main_commit(source_commit)
    facts = extract(source_commit)
    rendered = canonical_json(facts)
    claim_rendered = canonical_json(build_claim_receipt(facts))
    transcript_outputs = rendered_transcripts(facts)
    if args.print_only:
        sys.stdout.write(rendered)
        return
    if args.write:
        OUTPUT.write_text(rendered, encoding="utf-8")
        CLAIM_OUTPUT.write_text(claim_rendered, encoding="utf-8")
        for path, transcript in transcript_outputs.items():
            path.write_text(transcript, encoding="utf-8")
        if source_override is not None:
            config = json.loads(CONFIG.read_text(encoding="utf-8"))
            config["source_commit"] = source_commit
            config["source_profile"] = facts["source_profile"]
            CONFIG.write_text(canonical_json(config), encoding="utf-8")
        print(
            f"wrote {OUTPUT.relative_to(ROOT)} and "
            f"{CLAIM_OUTPUT.relative_to(ROOT)} from {facts['source_ref']} "
            f"({source_commit})"
        )
        return
    expected_outputs = {
        OUTPUT: rendered,
        CLAIM_OUTPUT: claim_rendered,
        **transcript_outputs,
    }
    for path, expected in expected_outputs.items():
        if not path.is_file():
            raise SystemExit(f"missing committed receipt: {path.relative_to(ROOT)}")
        committed = path.read_text(encoding="utf-8")
        if committed != expected:
            raise SystemExit(
                f"{path.name} does not match the pinned sources; run "
                "extract_facts.py --write and review the diff"
            )
    print(
        f"checked {OUTPUT.relative_to(ROOT)} and {CLAIM_OUTPUT.relative_to(ROOT)} "
        f"against {facts['source_ref']} ({source_commit})"
    )


if __name__ == "__main__":
    main()
