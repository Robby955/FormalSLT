#!/usr/bin/env python3
"""Generate the FormalSLT concept-keyed searchable theorem index.

The proof-frontier manifest already records the curated theorem spine
(concept family -> declaration -> module -> one-line role). This script projects
that data into a *human-searchable* index: it resolves each declaration to a
`file:line`, tags it with the mathematical concepts it touches (Bernstein,
Hoeffding, PAC-Bayes, ...), and emits

  * docs/INDEX.html  -- a self-contained page with a live filter box, so a user
                        searches by "Bernstein" instead of guessing a long name;
  * docs/INDEX.md    -- a grep-friendly markdown table, one row per declaration.

It reads:
  * docs/proof-frontier-manifest.json  (the family -> declaration data)
  * the FormalSLT/*.lean sources         (to resolve file:line)

Run with --check to verify the generated files are up to date (non-blocking in
CI, like the manifest checker).
"""

from __future__ import annotations

import argparse
import html
import json
import re
import sys
from pathlib import Path
from typing import Any

if __package__:
    from .generate_proof_frontier_manifest import (
        resolve_source_declaration,
        source_resolution_self_test,
    )
else:
    from generate_proof_frontier_manifest import (  # type: ignore[no-redef]
        resolve_source_declaration,
        source_resolution_self_test,
    )

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "docs" / "proof-frontier-manifest.json"
OUT_HTML = ROOT / "docs" / "INDEX.html"
OUT_MD = ROOT / "docs" / "INDEX.md"
SITE_CSS = ROOT / "docs" / "site" / "assets" / "site.css"
REPO_URL = "https://github.com/Robby955/FormalSLT/blob/main"

# Concept keywords: a declaration is tagged with every concept whose trigger
# patterns appear (case-insensitively) in its name or declaration-level summary.
# The broader theorem-map family is deliberately excluded: family prose often
# spans several neighboring ideas and otherwise leaks unrelated tags into every
# declaration in the table.
CONCEPT_TRIGGERS: dict[str, list[str]] = {
    "Markov": ["markov"],
    "adaptive trajectory": [
        "trajectory",
        "prequential",
        "full-prefix",
        "full prefix",
        "prefix-dependent",
        "prefix dependent",
        "controlledtrajectory",
        "controlled trajectory",
        "controlledobserved",
        "controlledimportance",
        "controlledtarget",
        "controlledcontinuation",
        "controlledfinite",
        "prefixcontrolled",
        "targetpolicy",
        "target policy",
        "dynamictargetpolicy",
    ],
    "stationary / invariant law": [
        "stationaryrisk",
        "stationary risk",
        "stationary-risk",
        "stationarymarkov",
        "stationary markov",
        "empiricalstationary",
        "empirical stationary",
        "stationarypoisson",
        "stationary poisson",
        "stationarytarget",
        "stationary target",
        "invariantpmf",
        "invariant pmf",
        "invariant law",
        "invariant distribution",
        "dobrushin",
    ],
    "Poisson equation": [
        "empiricalstationary",
        "empirical stationary",
        "stationarypoisson",
        "stationary_poisson",
        "poissonpotential",
        "poisson_potential",
        "poisson potential",
        "poissonresidual",
        "poisson_residual",
        "poisson residual",
        "poissoncorrect",
        "poisson_correct",
        "poisson-correct",
        "poisson equation",
        "poissondrift",
        "poisson_drift",
        "poisson drift",
        "poisson_depth",
        "poisson depth",
        "exactpoisson",
        "exact_poisson",
        "finitedepthpoisson",
        "finite-depth poisson",
        "finite depth poisson",
    ],
    "transition kernel": [
        "empiricalstationary",
        "empirical stationary",
        "empiricaltransition",
        "empirical transition",
        "stationarypoisson",
        "stationary poisson",
        "transitioncoordinate",
        "transition coordinate",
        "transitionfrequency",
        "transition frequency",
        "transitionrow",
        "transition row",
        "transitionedge",
        "transition edge",
        "transitionvisit",
        "transition visit",
        "transitionkernel",
        "transition_kernel",
        "transition kernel",
        "candidatekernel",
        "candidate kernel",
        "markov kernel",
        "environment kernel",
        "transition pmf",
        "transition matrix",
        "kernelpush",
        "kernel push",
        "finitekernel",
        "finite kernel",
        "prefixkernel",
        "prefix kernel",
        "inducedkernel",
        "induced kernel",
        "candidaterow",
        "candidate row",
        "rowtotalvariation",
        "row total variation",
        "row-tv",
        "rowtv",
        "dobrushin",
    ],
    "Chebyshev": ["chebyshev"],
    "Hoeffding": ["hoeffding"],
    "Bernstein": ["bernstein"],
    "Bennett": ["bennett"],
    "Chernoff": ["chernoff"],
    "sub-Gaussian": ["subgaussian", "sub-gaussian", "subgauss"],
    "sub-Gamma": ["subgamma", "sub-gamma"],
    "Azuma": ["azuma"],
    "McDiarmid": ["mcdiarmid", "bounded difference", "boundeddiff"],
    "union bound": ["unionbound", "union bound"],
    "tail bound": ["_tail", "tail ", "tail-", "tail_", "tailbound"],
    "MGF": ["mgf", "moment generating", "moment-generating"],
    "confidence sequence": [
        "confidence sequence",
        "confidence-sequence",
        "confidence_sequence",
        "confidencesequence",
        "time-uniform",
        "time uniform",
        "timeuniform",
        "anytime",
        "all-time",
        "all time",
        "ville",
        "subgammacs",
        "mixturecs",
        "eprocess",
        "e-process",
        "subgaussiancs",
        "attopcs",
    ],
    "PAC-Bayes": ["pacbayes", "pac-bayes", "kldiv", "mcallester", "seeger", "maurer", "catoni"],
    "KL divergence": ["kldiv", "kl ", "kl-", "divergence", "donsker", "variational"],
    "Rademacher": [
        "rademacher",
        "massart",
        "symmetriz",
        "one_step_contraction",
        "contraction_1lip",
    ],
    "VC dimension": [
        ".vc.",
        "vc_",
        "_vc",
        "vcdimension",
        "vc dimension",
        "vc-dimension",
        "sauer",
        "shelah",
        "shatter",
    ],
    "covering / chaining": [
        "covering",
        "dudley",
        "chaining",
        "entropy",
        "finitenet",
        "projectednet",
        "dyadicnet",
        "meshnet",
        " finite net",
        " projected net",
        " dyadic net",
        " net ",
        "net_",
    ],
    "ERM": [
        "iserm",
        "_erm_",
        "rademachererm",
        " erm ",
        "empirical risk minimizer",
        "empirical-risk minimizer",
    ],
    "stability": ["stability", " stable ", "stable_", "_stable"],
    "sample statistics": [
        "samplemean",
        "samplevariance",
        "empiricalvariance",
        "weightedexpectation",
        "weightedvariance",
        "weightedcovariance",
        "sample mean",
        "sample variance",
        "empirical variance",
        "empirical-variance",
        "estimator",
    ],
    "Glivenko-Cantelli": ["glivenko", "cantelli", "empiricalcdf", "empirical cdf", "lowerray", "lower ray", "lower-ray", "uniformdeviation", "bracketing"],
    "Bernoulli": ["bernoulli"],
    "risk": ["risk"],
    "exponential tilting": [
        "exponentialtilt",
        "exponential tilt",
        "tiltpmf",
        "tilted",
        "change of measure",
        "changeofmeasure",
    ],
    "likelihood / MLE": ["likelihood", "_mle", " mle", "argmax"],
    "unbiasedness": ["unbiased"],
    "Fisher information": ["fisherinformation", "fisher information"],
    "Cramér-Rao": ["cramerrao", "cramer-rao", "cramér-rao"],
    "survey sampling": ["horvitz", "survey sampling", "design-unbiased", "inclusion probability"],
    "bootstrap": ["bootstrap"],
    "exponential family": [
        "exponentialfamily",
        "exponential family",
        "finiteexponentialpmf",
        "finitepartition",
        "finitemean_hasderiv",
        "finitemean_deriv",
        "bernoullinatural",
        "logpartition",
        "log-partition",
    ],
}

# Concepts that are mathematically present but not reliably recoverable from a
# declaration's name, summary, or family. Keep this list narrow: broad keyword
# triggers such as "indicator" would incorrectly tag CDF indicator families as
# Bernoulli results.
DECLARATION_CONCEPTS: dict[str, list[str]] = {
    "FormalSLT.Applications.ControlledQueue.refreshTargetPolicyKernel_dobrushin_le_gamma": [
        "stationary / invariant law",
        "transition kernel",
    ],
    "FormalSLT.Applications.ControlledQueue.refreshTargetPolicyKernel_existsUnique_invariantPMF": [
        "stationary / invariant law",
        "transition kernel",
    ],
    "FormalSLT.Applications.ControlledQueue.queueHypothesisStationary_unique_of_refresh": [
        "stationary / invariant law",
        "transition kernel",
    ],
    "FormalSLT.Applications.ControlledQueue.refreshEnvironment_apply_toReal": [
        "transition kernel"
    ],
    "FormalSLT.Applications.ControlledQueue.candidateEnvironment_eq_refreshEnvironment": [
        "transition kernel"
    ],
    "FormalSLT.Applications.ControlledQueue.persistenceDestinationHit_rowRisk": [
        "adaptive trajectory", "transition kernel"
    ],
    "FormalSLT.Applications.ControlledQueue.exists_persistenceHitConfidence_event": [
        "adaptive trajectory", "transition kernel", "confidence sequence"
    ],
    "FormalSLT.Applications.ControlledQueue.refreshEnvironment_candidate_rowTV_eq_hitDiscrepancy": [
        "transition kernel"
    ],
    "FormalSLT.Applications.ControlledQueue.exists_structuredCandidateTVConfidence_event": [
        "adaptive trajectory", "transition kernel", "confidence sequence"
    ],
    "FormalSLT.StochasticDynamics.candidateTargetPolicyFiniteDepthPotential": [
        "adaptive trajectory", "Poisson equation", "transition kernel"
    ],
    "FormalSLT.StochasticDynamics.finiteOscillation_targetPolicyPoissonDrift_finiteDepth_le": [
        "adaptive trajectory", "stationary / invariant law", "Poisson equation", "transition kernel"
    ],
    "FormalSLT.StochasticDynamics.exists_stationaryRobustCandidateFiniteDepthTargetPolicyOPE_event": [
        "adaptive trajectory", "stationary / invariant law", "Poisson equation", "PAC-Bayes", "transition kernel"
    ],
    "FormalSLT.PACBayes.IndicatorVariance.indicatorPopulationRisk_mem_Icc": ["Bernoulli"],
    "FormalSLT.PACBayes.IndicatorVariance.indicatorDeviation_centered": ["Bernoulli"],
    "FormalSLT.PACBayes.IndicatorVariance.indicatorDeviation_secondMoment_eq": ["Bernoulli"],
    "FormalSLT.PACBayes.FiniteProductBernstein.indicator_oneCoordinateDeviationMGF_le": ["Bernoulli"],
    "FormalSLT.PACBayes.FiniteProductBernstein.indicator_product_mgf_le": ["Bernoulli"],
    "FormalSLT.PACBayes.FiniteProductBernstein.indicator_product_normalizedMGF_le_one": ["Bernoulli"],
    "FormalSLT.PACBayes.IndicatorBernsteinMoment.indicatorBernstein_normalization_eq_budget": ["Bernoulli"],
    "FormalSLT.PACBayes.IndicatorBernsteinMoment.indicator_expectedPriorBernsteinExpMoment_le_one": ["Bernoulli", "MGF"],
    "FormalSLT.PACBayes.IndicatorBernsteinConfidence.indicatorFinitePACBayesBernsteinBadSamples": ["Bernoulli"],
    "FormalSLT.PACBayes.IndicatorBernsteinConfidence.indicator_posteriorGeneralizationGap_le_of_not_mem": ["Bernoulli"],
    "FormalSLT.PACBayes.IndicatorBernsteinConfidence.indicator_finitePACBayesBernstein_fixedLambda_badEventMass_le_delta": ["Bernoulli"],
    "FormalSLT.PACBayes.IndicatorBernsteinTiltCatalog.indicatorFinitePACBayesBernsteinWeightedCatalogBadSamples": ["Bernoulli"],
    "FormalSLT.PACBayes.IndicatorBernsteinTiltCatalog.indicator_mem_weightedCatalog_iff": ["Bernoulli"],
    "FormalSLT.PACBayes.IndicatorBernsteinTiltCatalog.indicator_not_mem_weightedCatalog_iff": ["Bernoulli"],
    "FormalSLT.PACBayes.IndicatorBernsteinTiltCatalog.indicatorFixedTiltBadSamples_subset_weightedCatalog": ["Bernoulli"],
    "FormalSLT.PACBayes.IndicatorBernsteinTiltCatalog.indicator_posteriorGeneralizationGap_le_weightedCatalog_of_not_mem": ["Bernoulli"],
    "FormalSLT.PACBayes.IndicatorBernsteinTiltCatalog.indicator_finitePACBayesBernstein_weightedCatalog_badEventMass_le_delta": ["Bernoulli"],
    "FormalSLT.PACBayes.IndicatorBernsteinTiltCatalog.indicator_posteriorRisk_le_weightedLowRiskCatalog_of_not_mem": ["Bernoulli"],
    "FormalSLT.PACBayes.IndicatorBernsteinTiltCatalog.indicator_posteriorRisk_le_weightedLowRiskCatalog_selected_of_not_mem": ["Bernoulli"],
    "FormalSLT.Statistics.FisherInformation.scoreFunction": ["Fisher information"],
    "FormalSLT.Statistics.FisherInformation.score_mean_zero_of_finite_regular": ["Fisher information"],
    "FormalSLT.Statistics.FisherInformation.covariance_score_eq_deriv_mean": ["Fisher information"],
    "FormalSLT.Statistics.FisherInformation.covariance_cauchy_schwarz": ["Fisher information"],
    "FormalSLT.Statistics.CramerRao.cramerRao_unbiased": ["Fisher information"],
    "FormalSLT.Statistics.CramerRao.bernoulliHalfCramerRaoWitness": ["Fisher information"],
}

def module_to_file(module: str) -> Path:
    return ROOT / "FormalSLT" / Path(module.replace(".", "/") + ".lean")


def resolve_decl(module: str, name: str) -> dict[str, Any]:
    """Resolve source line and kind, rejecting missing or ambiguous names."""
    return resolve_source_declaration(module_to_file(module), name)


def concepts_for(name: str, summary: str, _family: str) -> list[str]:
    """Return declaration-local concept tags.

    ``_family`` remains in the public helper signature for generator callers,
    but is intentionally not part of the tagging haystack.
    """
    haystack = f" {name} {summary} ".lower()
    found = [
        concept
        for concept, triggers in CONCEPT_TRIGGERS.items()
        if any(t in haystack for t in triggers)
    ]
    for concept in DECLARATION_CONCEPTS.get(name, []):
        if concept not in found:
            found.append(concept)
    return found


def build_rows() -> list[dict[str, Any]]:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    rows: list[dict[str, Any]] = []
    for family in manifest["theorem_families"]:
        fam_name = family["name"]
        for entry in family["entries"]:
            name = entry["name"]
            module = entry["module"]
            summary = entry.get("summary", "")
            declaration = resolve_decl(module, name)
            rel = module_to_file(module).relative_to(ROOT).as_posix()
            rows.append(
                {
                    "name": name,
                    "module": module,
                    "kind": declaration["kind"],
                    "summary": summary,
                    "family": fam_name,
                    "file": rel,
                    "line": declaration["line"],
                    "concepts": concepts_for(
                        declaration["qualified_name"], summary, fam_name
                    ),
                }
            )
    rows.sort(key=lambda r: (r["family"], r["name"]))
    return rows


def render_md(rows: list[dict[str, Any]]) -> str:
    n_resolved = sum(1 for r in rows if r["line"] is not None)
    lines = [
        "# FormalSLT theorem index (concept-keyed)",
        "",
        "Search by mathematical concept, not by declaration name. Generated from",
        "`docs/proof-frontier-manifest.json` plus the Lean sources by",
        "`scripts/generate_theorem_index.py`. For a searchable version with a live",
        "filter box, open `docs/INDEX.html`.",
        "This is a discovery index, not an API compatibility promise.",
        "",
        f"{len(rows)} declarations, {n_resolved} resolved to a `file:line`.",
        "",
        "## By concept",
        "",
    ]
    by_concept: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        for concept in row["concepts"] or ["(untagged)"]:
            by_concept.setdefault(concept, []).append(row)
    for concept in sorted(by_concept):
        members = sorted({r["name"] for r in by_concept[concept]})
        lines.append(f"- **{concept}** ({len(members)}): " + ", ".join(f"`{m}`" for m in members))
    lines += ["", "## All declarations", "", "| Concept(s) | Declaration | Kind | Location | Role |", "|---|---|---|---|---|"]
    for row in rows:
        loc = f"`{row['file']}:{row['line']}`" if row["line"] else f"`{row['file']}`"
        concepts = ", ".join(row["concepts"]) if row["concepts"] else ""
        summary = row["summary"].replace("|", "\\|")
        lines.append(
            f"| {concepts} | `{row['name']}` | {row['kind']} | {loc} | {summary} |"
        )
    lines.append("")
    return "\n".join(lines)


def render_html(rows: list[dict[str, Any]]) -> str:
    n_resolved = sum(1 for r in rows if r["line"] is not None)
    all_concepts = sorted({c for r in rows for c in r["concepts"]})
    shared_site_css = SITE_CSS.read_text(encoding="utf-8")

    def esc(s: str) -> str:
        return html.escape(s, quote=True)

    cards: list[str] = []
    for row in rows:
        if row["line"]:
            loc = f"{esc(row['file'])}:{row['line']}"
            href = f"{REPO_URL}/{row['file']}#L{row['line']}"
            loc_html = f'<a class="loc" href="{href}">{loc}</a>'
        else:
            loc_html = f'<span class="loc">{esc(row["file"])}</span>'
        chips = "".join(f'<span class="chip">{esc(c)}</span>' for c in row["concepts"])
        concept_data = esc(json.dumps(row["concepts"], ensure_ascii=False))
        haystack = esc(
            " ".join(
                [row["name"], row["module"], row["summary"], row["family"]]
                + row["concepts"]
            ).lower()
        )
        cards.append(
            f'<div class="row" data-search="{haystack}" data-concepts="{concept_data}">'
            f'<div class="decl"><code>{esc(row["name"])}</code>'
            f'<span class="kind">{esc(row["kind"])}</span></div>'
            f'<div class="meta">{chips}</div>'
            f'<div class="summary">{esc(row["summary"])}</div>'
            f'<div class="locline">{loc_html} '
            f'<span class="fam">{esc(row["family"])}</span></div>'
            f"</div>"
        )

    concept_buttons = "".join(
        f'<button type="button" class="cbtn" data-concept="{esc(c)}" '
        f'aria-pressed="false">{esc(c)}</button>'
        for c in all_concepts
    )

    return f"""<!doctype html>
<html lang="en" data-formalslt-site="theorem-index">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="description" content="Search the checked FormalSLT theorem surface by mathematical concept, declaration, module, or role.">
<meta name="theme-color" content="#0b172b">
<title>FormalSLT theorem index</title>
<link rel="canonical" href="https://robby955.github.io/FormalSLT/theorems/">
<link rel="icon" href="../assets/favicon.svg" type="image/svg+xml">
<style>
{shared_site_css}
input:focus-visible, summary:focus-visible {{ outline: 3px solid var(--accent-light); outline-offset: 4px; }}
.index-header {{ background: var(--ink-deep); color: var(--paper-bright); }}
.index-header-inner, .search-inner, main {{ width: min(calc(100% - 2.5rem), var(--measure)); margin-inline: auto; }}
.index-header-inner {{ padding: 2rem 0 clamp(3rem, 7vw, 6rem); }}
.index-nav {{ display: flex; align-items: center; justify-content: space-between; gap: 1rem; margin-bottom: clamp(3rem, 7vw, 6rem); }}
.index-header .wordmark {{ color: var(--paper-bright); }}
.index-nav-links {{ display: flex; flex-wrap: wrap; justify-content: flex-end; gap: .6rem 1.25rem; }}
.index-nav-links a {{ color: #d8dfeb; font-size: .78rem; font-weight: 700; letter-spacing: .05em; text-decoration: none; text-transform: uppercase; }}
.eyebrow {{ margin: 0 0 1rem; color: var(--accent-light); font-size: .76rem; font-weight: 750; letter-spacing: .13em; text-transform: uppercase; }}
h1 {{ max-width: 14ch; margin: 0 0 1.25rem; font: 600 clamp(2.6rem, 7vw, 5.8rem)/1.02 var(--serif); letter-spacing: -.045em; text-wrap: balance; }}
.sub {{ max-width: 50rem; margin: 0; color: #d8dfeb; font-size: 1.02rem; }}
.search-shell {{ position: sticky; top: 0; z-index: 8; border-bottom: 1px solid var(--line); background: color-mix(in srgb, var(--paper-bright) 96%, transparent); backdrop-filter: blur(12px); }}
.search-inner {{ display: grid; grid-template-columns: minmax(0, 1fr) auto; gap: .75rem; align-items: end; padding-block: .9rem; }}
.search-field {{ display: grid; gap: .35rem; }}
.search-field label {{ color: var(--muted); font-size: .76rem; font-weight: 750; letter-spacing: .08em; text-transform: uppercase; }}
#q {{ width: 100%; min-height: 3rem; padding: .7rem .85rem; border: 1px solid var(--line-dark); border-radius: 0; background: var(--paper-bright); color: var(--ink); font: 1rem var(--sans); }}
.clear {{ min-height: 3rem; padding: .65rem 1rem; border: 1px solid var(--ink); background: transparent; color: var(--ink); font-weight: 720; cursor: pointer; }}
.clear:disabled {{ border-color: var(--line); color: var(--muted); cursor: default; }}
main {{ padding-block: clamp(2.5rem, 6vw, 5rem) 6rem; }}
.concept-filter {{ margin-bottom: 2rem; border-block: 1px solid var(--line); }}
.concept-filter summary {{ display: flex; min-height: 3.25rem; align-items: center; justify-content: space-between; gap: 1rem; cursor: pointer; font-weight: 720; }}
.filter-state {{ color: var(--muted); font-size: .78rem; font-weight: 500; }}
.concepts {{ display: flex; flex-wrap: wrap; gap: .45rem; padding: 0 0 1.1rem; }}
.cbtn {{ min-height: 2.15rem; padding: .3rem .7rem; border: 1px solid var(--line-dark); border-radius: 999px; background: transparent; color: var(--ink); font-size: .76rem; cursor: pointer; }}
.cbtn.active, .cbtn[aria-pressed="true"] {{ border-color: var(--accent); background: var(--accent); color: var(--paper-bright); }}
.count {{ display: block; margin: 0 0 1rem; color: var(--muted); font-size: .84rem; }}
.row {{ display: grid; grid-template-columns: minmax(16rem, .8fr) minmax(0, 1.2fr); gap: .65rem clamp(1.5rem, 4vw, 4rem); padding: 1.5rem 0; border-top: 1px solid var(--line); }}
.row > * {{ min-width: 0; }}
.row:last-child {{ border-bottom: 1px solid var(--line); }}
.decl {{ min-width: 0; }}
.decl code {{ color: var(--accent); font: 650 .9rem/1.45 var(--mono); overflow-wrap: anywhere; }}
.kind {{ margin-left: .55rem; color: var(--muted); font-size: .66rem; letter-spacing: .06em; text-transform: uppercase; }}
.meta {{ display: flex; flex-wrap: wrap; gap: .35rem; margin-top: .65rem; }}
.chip {{ padding: .05rem .45rem; border: 1px solid var(--line); border-radius: 999px; color: var(--muted); font-size: .67rem; }}
.summary {{ align-self: start; color: var(--ink); font-size: .92rem; overflow-wrap: anywhere; }}
.locline {{ grid-column: 2; color: var(--muted); font-size: .72rem; }}
.loc {{ color: var(--muted); font-family: var(--mono); overflow-wrap: anywhere; text-decoration: none; }}
.loc:hover {{ color: var(--accent); text-decoration: underline; }}
.fam {{ margin-left: .7rem; font-style: italic; }}
.index-footer {{ width: min(calc(100% - 2.5rem), var(--measure)); margin-inline: auto; padding: 2rem 0 3rem; border-top: 1px solid var(--line); color: var(--muted); font-size: .78rem; }}
.index-footer p {{ margin: 0; }}
.hidden {{ display: none; }}
@media (max-width: 720px) {{
  .index-nav {{ align-items: flex-start; }}
  .index-nav-links {{ display: grid; gap: .25rem; text-align: right; }}
  .search-inner {{ grid-template-columns: 1fr; }}
  .clear {{ width: 100%; }}
  .concepts {{ max-height: 14rem; overflow: auto; padding-right: .25rem; }}
  .row {{ grid-template-columns: minmax(0, 1fr); }}
  .locline {{ grid-column: 1; }}
  .fam {{ display: block; margin: .25rem 0 0; }}
}}
@media (prefers-reduced-motion: reduce) {{
  html {{ scroll-behavior: auto; }}
  *, *::before, *::after {{ transition-duration: .01ms !important; }}
}}
</style>
</head>
<body>
<a class="skip-link" href="#results">Skip to results</a>
<header class="index-header">
  <div class="index-header-inner">
    <nav class="index-nav" aria-label="Theorem index navigation">
      <a class="wordmark" href="../">FormalSLT</a>
      <div class="index-nav-links">
        <a href="../">Research overview</a>
        <a href="../api.html">Lean docs</a>
      </div>
    </nav>
    <p class="eyebrow">Concept-keyed discovery</p>
    <h1>Find the theorem before the declaration name.</h1>
    <p class="sub">{len(rows)} indexed declarations &middot; {n_resolved} linked to source &middot; discovery surface, not an API compatibility promise</p>
  </div>
</header>
<div class="search-shell">
  <div class="search-inner">
    <div class="search-field">
      <label for="q">Search declarations</label>
      <input id="q" type="search" autocomplete="off" spellcheck="false" aria-controls="results" placeholder="Empirical Bernstein, adaptive trajectory, Poisson equation, transition kernel">
    </div>
    <button class="clear" id="clear" type="button" disabled>Clear filters</button>
  </div>
</div>
<main id="results">
  <details class="concept-filter" id="concept-filter">
    <summary>Filter by concept <span class="filter-state" id="filter-state">No concept selected</span></summary>
    <div class="concepts" aria-label="Theorem concepts">{concept_buttons}</div>
  </details>
  <output class="count" id="count" role="status" aria-live="polite" aria-atomic="true"></output>
  {"".join(cards)}
</main>
<footer class="index-footer">
  <p>Built from <a href="https://github.com/Robby955/FormalSLT/tree/__FORMALSLT_SOURCE_REF__"><code>__FORMALSLT_SOURCE_REF__</code></a>. Source links are pinned to the same documentation commit during staging.</p>
</footer>
<script>
const rows = Array.from(document.querySelectorAll('.row'));
const q = document.getElementById('q');
const count = document.getElementById('count');
const cbtns = Array.from(document.querySelectorAll('.cbtn'));
const clear = document.getElementById('clear');
const filterState = document.getElementById('filter-state');
const conceptFilter = document.getElementById('concept-filter');
let activeConcept = null;
if (!window.matchMedia('(max-width: 720px)').matches) conceptFilter.open = true;
function normalize(value) {{
  return value.toLowerCase().replace(/[-\u2010-\u2015]/g, '');
}}
function selectConcept(concept) {{
  activeConcept = concept;
  for (const b of cbtns) {{
    const active = b.dataset.concept === activeConcept;
    b.classList.toggle('active', active);
    b.setAttribute('aria-pressed', String(active));
  }}
  filterState.textContent = activeConcept || 'No concept selected';
}}
function apply() {{
  const term = normalize(q.value.trim());
  let shown = 0;
  for (const r of rows) {{
    const hay = normalize(r.dataset.search);
    const concepts = JSON.parse(r.dataset.concepts);
    const okTerm = !term || hay.includes(term);
    const okConcept = !activeConcept || concepts.includes(activeConcept);
    const show = okTerm && okConcept;
    r.classList.toggle('hidden', !show);
    if (show) shown++;
  }}
  count.textContent = shown + ' of ' + rows.length + ' declarations shown';
  clear.disabled = !term && !activeConcept;
}}
q.addEventListener('input', apply);
for (const b of cbtns) {{
  b.addEventListener('click', () => {{
    selectConcept(activeConcept === b.dataset.concept ? null : b.dataset.concept);
    apply();
  }});
}}
clear.addEventListener('click', () => {{
  q.value = '';
  selectConcept(null);
  apply();
  q.focus();
}});
apply();
</script>
</body>
</html>
"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="fail if the index is stale")
    parser.add_argument(
        "--self-test", action="store_true", help="test declaration resolution and concepts"
    )
    args = parser.parse_args()

    if args.self_test:
        source_resolution_self_test()
        assert "confidence sequence" not in concepts_for(
            "fixedHighConfidenceBound", "fixed-sample high-confidence theorem", ""
        )
        assert "confidence sequence" in concepts_for(
            "timeUniformBound", "all-time Ville crossing theorem", ""
        )
        assert "ERM" not in concepts_for(
            "finiteJointMeanVarianceMasterMixture", "master mixture", ""
        )
        assert "ERM" not in concepts_for(
            "finiteSupremumBound", "terminal supremum theorem", ""
        )
        assert "ERM" not in concepts_for("pac_bayes_generalization", "", "")
        assert "ERM" not in concepts_for("genGap", "generalization gap", "")
        assert "ERM" in concepts_for("IsERM", "empirical risk minimizer", "")
        assert "ERM" in concepts_for("vc_erm_sample_complexity", "", "")
        structured_tags = concepts_for(
            "FormalSLT.Applications.ControlledQueue."
            "exists_structuredCandidateTVConfidence_event",
            "Simultaneous physical-row TV budgets for the generated candidates",
            "",
        )
        assert "VC dimension" not in structured_tags
        assert {
            "adaptive trajectory", "transition kernel", "confidence sequence"
        }.issubset(structured_tags)
        assert "covering / chaining" not in concepts_for("bennett_mgf", "Bennett MGF", "")
        assert "Rademacher" in concepts_for(
            "one_step_contraction", "One coordinate replacement step", ""
        )
        assert "Rademacher" in concepts_for(
            "contraction_1lip", "Finite-sample scalar contraction", ""
        )
        assert "Rademacher" not in concepts_for(
            "queueHypothesis_nominal_isOscillationContraction",
            "Target-policy Dobrushin kernel-contraction certificate",
            "",
        )
        assert "Rademacher" not in concepts_for(
            "finiteDobrushinCoefficient_isOscillationContraction",
            "Finite-state Markov-kernel oscillation contraction",
            "",
        )
        assert "stability" not in concepts_for(
            "candidateKernelTable_eq_massTable",
            "Exact generated transition-kernel table identity",
            "",
        )
        assert "stability" in concepts_for(
            "expectedGeneralizationGap_le_uniformStability",
            "Uniform stability generalization theorem",
            "",
        )
        assert "risk" not in concepts_for(
            "finiteWeightedUnionBound_sum_le_of_exists_mem",
            "Plain-sum finite weighted union bound",
            "Empirical risk and sample statistics",
        )
        sharp_tags = concepts_for(
            "boundedDifferences_tail_sharp",
            "Sharp McDiarmid tail theorem",
            "Rademacher and VC generalization",
        )
        assert "McDiarmid" in sharp_tags
        assert "Rademacher" not in sharp_tags and "VC dimension" not in sharp_tags
        assert "exponential tilting" in concepts_for(
            "finiteExponentialTilt_changeOfMeasure",
            "Exact finite change of measure",
            "",
        )
        assert "KL divergence" not in concepts_for(
            "finiteExponentialTilt_changeOfMeasure",
            "Exact finite change of measure",
            "",
        )
        assert "unbiasedness" in concepts_for("sampleMean_unbiased_finite", "", "")
        assert "Fisher information" in concepts_for("bernoulliFisherInformation", "", "")
        cramer_tags = concepts_for(
            "FormalSLT.Statistics.CramerRao.cramerRao_unbiased", "", ""
        )
        assert {"Cramér-Rao", "Fisher information", "unbiasedness"}.issubset(cramer_tags)
        assert "survey sampling" in concepts_for("horvitzThompson_design_unbiased", "", "")
        assert "bootstrap" in concepts_for("bootstrapMean_eq_sampleMean", "", "")
        assert "exponential family" in concepts_for("finiteLogPartition_hasDerivAt", "", "")
        assert {"Bernstein", "MGF", "Bernoulli"}.issubset(
            concepts_for(
                "FormalSLT.PACBayes.IndicatorBernsteinMoment."
                "indicator_expectedPriorBernsteinExpMoment_le_one",
                "",
                "",
            )
        )
        assert "adaptive trajectory" in concepts_for(
            "exists_trajectoryCountableEmpiricalBernsteinPACBayes_event", "", ""
        )
        assert "adaptive trajectory" in concepts_for(
            "markovPACBayes_prequentialRisk_certificate", "", ""
        )
        assert "adaptive trajectory" in concepts_for(
            "controlledObservedImportanceScore_condExp", "", ""
        )
        assert {
            "Poisson equation", "stationary / invariant law", "transition kernel"
        }.issubset(
            concepts_for(
                "exists_selectedCanonicalEmpiricalStationaryCatalog_event", "", ""
            )
        )
        assert "stationary / invariant law" in concepts_for(
            "finiteInvariantPMF_isInvariant", "", ""
        )
        assert "Poisson equation" in concepts_for(
            "finiteDepthPoisson_residual_identity", "", ""
        )
        assert "Poisson equation" in concepts_for(
            "finiteDepthPoissonSpanBound_closed", "", ""
        )
        assert "transition kernel" in concepts_for(
            "exists_empiricalCandidateKernelTV_event", "", ""
        )
        assert "transition kernel" in concepts_for(
            "finiteDobrushinCoefficient",
            "Maximum row distance for a finite transition kernel",
            "",
        )
        assert {
            "stationary / invariant law", "transition kernel"
        }.issubset(concepts_for("finiteDobrushinCoefficient", "", ""))
        assert "stationary / invariant law" not in concepts_for(
            "finiteJointMeanVarianceXi_eq_interior_of_lt",
            "The interior stationary point is the maximizer",
            "",
        )
        assert "Poisson equation" not in concepts_for(
            "poissonDistribution_pmf", "Poisson count distribution", ""
        )
        assert "transition kernel" not in concepts_for(
            "kernelizedLoss", "RKHS kernel risk bound", ""
        )
        assert "adaptive trajectory" not in concepts_for(
            "boundedRisk", "Risk is controlled by a deterministic bound", ""
        )
        family_only_tags = concepts_for(
            "plainBound",
            "A declaration-local summary",
            "Adaptive trajectory, stationary Poisson, and transition kernels",
        )
        assert not {
            "adaptive trajectory",
            "stationary / invariant law",
            "Poisson equation",
            "transition kernel",
        }.intersection(family_only_tags)
        filter_fixture = render_html([
            {
                "name": "notCramerRao",
                "module": "Statistics.CramerRao",
                "kind": "theorem",
                "summary": "A neighboring result",
                "family": "Cramér-Rao information lower bounds",
                "file": "FormalSLT/Statistics/CramerRao.lean",
                "line": 1,
                "concepts": ["Fisher information"],
            }
        ])
        assert 'data-concepts="[&quot;Fisher information&quot;]"' in filter_fixture
        assert "concepts.includes(activeConcept)" in filter_fixture
        assert "1 indexed declarations" in filter_fixture
        assert "discovery surface, not an API compatibility promise" in filter_fixture
        assert "public declarations" not in filter_fixture
        assert 'href="../">FormalSLT</a>' in filter_fixture
        assert 'rel="canonical" href="https://robby955.github.io/FormalSLT/theorems/"' in filter_fixture
        assert 'rel="icon" href="../assets/favicon.svg"' in filter_fixture
        assert 'aria-pressed="false"' in filter_fixture
        assert 'role="status" aria-live="polite" aria-atomic="true"' in filter_fixture
        assert '<details class="concept-filter" id="concept-filter">' in filter_fixture
        assert "setAttribute('aria-pressed', String(active))" in filter_fixture
        assert filter_fixture.count("__FORMALSLT_SOURCE_REF__") == 2
        print("theorem-index self-test passed")
        return 0

    rows = build_rows()
    md = render_md(rows)
    html_doc = render_html(rows)

    if args.check:
        stale = []
        for path, content in ((OUT_MD, md), (OUT_HTML, html_doc)):
            if not path.exists() or path.read_text(encoding="utf-8") != content:
                stale.append(path.relative_to(ROOT).as_posix())
        if stale:
            print("stale index files: " + ", ".join(stale), file=sys.stderr)
            return 1
        return 0

    OUT_MD.write_text(md, encoding="utf-8")
    OUT_HTML.write_text(html_doc, encoding="utf-8")
    unresolved = [r["name"] for r in rows if r["line"] is None]
    print(f"wrote {OUT_MD.relative_to(ROOT)} and {OUT_HTML.relative_to(ROOT)} "
          f"({len(rows)} declarations, {len(unresolved)} unresolved)")
    if unresolved:
        print("  unresolved (no file:line found): " + ", ".join(unresolved[:20]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
