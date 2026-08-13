#!/usr/bin/env python3
"""Generate the FormalSLT concept-keyed searchable theorem index.

The proof-frontier manifest already records the public theorem spine
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
REPO_URL = "https://github.com/Robby955/FormalSLT/blob/main"

# Concept keywords: a declaration is tagged with every concept whose trigger
# patterns appear (case-insensitively) in its name or declaration-level summary.
# The broader theorem-map family is deliberately excluded: family prose often
# spans several neighboring ideas and otherwise leaks unrelated tags into every
# declaration in the table.
CONCEPT_TRIGGERS: dict[str, list[str]] = {
    "Markov": ["markov"],
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
    "Rademacher": ["rademacher", "massart", "symmetriz", "contraction"],
    "VC dimension": ["vc", "sauer", "shelah", "shatter"],
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
    "stability": ["stability", "stable"],
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
        f'<button type="button" class="cbtn" data-concept="{esc(c)}">{esc(c)}</button>'
        for c in all_concepts
    )

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>FormalSLT theorem index</title>
<style>
:root {{ --bg:#0f1115; --fg:#e6e6e6; --muted:#9aa4b2; --card:#1a1d24; --accent:#7aa2f7; --chip:#283041; }}
* {{ box-sizing:border-box; }}
body {{ margin:0; font:15px/1.5 -apple-system,Segoe UI,Roboto,Helvetica,Arial,sans-serif; background:var(--bg); color:var(--fg); }}
header {{ position:sticky; top:0; background:var(--bg); padding:18px 20px 12px; border-bottom:1px solid #232733; z-index:5; }}
h1 {{ margin:0 0 4px; font-size:20px; }}
.sub {{ color:var(--muted); font-size:13px; margin-bottom:10px; }}
#q {{ width:100%; padding:10px 12px; font-size:15px; border-radius:8px; border:1px solid #2c3340; background:#11141a; color:var(--fg); }}
.concepts {{ margin-top:10px; display:flex; flex-wrap:wrap; gap:6px; }}
.cbtn {{ background:var(--chip); color:var(--fg); border:1px solid #313a4d; border-radius:14px; padding:3px 10px; font-size:12px; cursor:pointer; }}
.cbtn.active {{ background:var(--accent); color:#0f1115; border-color:var(--accent); }}
main {{ padding:14px 20px 60px; }}
.count {{ color:var(--muted); font-size:13px; margin:8px 0 14px; }}
.row {{ background:var(--card); border:1px solid #232733; border-radius:10px; padding:12px 14px; margin-bottom:10px; }}
.decl code {{ font-size:15px; color:var(--accent); word-break:break-all; }}
.kind {{ color:var(--muted); font-size:11px; margin-left:8px; text-transform:uppercase; letter-spacing:.04em; }}
.meta {{ margin:6px 0; display:flex; flex-wrap:wrap; gap:5px; }}
.chip {{ background:var(--chip); color:#cdd6e4; border-radius:10px; padding:1px 8px; font-size:11px; }}
.summary {{ color:#d3d8e0; font-size:14px; }}
.locline {{ margin-top:6px; font-size:12px; }}
.loc {{ color:var(--muted); text-decoration:none; font-family:ui-monospace,Menlo,monospace; }}
.loc:hover {{ color:var(--accent); text-decoration:underline; }}
.fam {{ color:var(--muted); margin-left:10px; font-style:italic; }}
.hidden {{ display:none; }}
</style>
</head>
<body>
<header>
  <h1>FormalSLT theorem index</h1>
  <div class="sub">{len(rows)} public declarations &middot; {n_resolved} linked to source &middot; search by concept or name</div>
  <input id="q" type="search" aria-label="Search the theorem index" placeholder="Search: Bernstein, sample mean, PAC-Bayes, confidence sequence, ...">
  <div class="concepts">{concept_buttons}</div>
</header>
<main>
  <div class="count" id="count"></div>
  {"".join(cards)}
</main>
<script>
const rows = Array.from(document.querySelectorAll('.row'));
const q = document.getElementById('q');
const count = document.getElementById('count');
const cbtns = Array.from(document.querySelectorAll('.cbtn'));
let activeConcept = null;
function normalize(value) {{
  return value.toLowerCase().replace(/[-\u2010-\u2015]/g, '');
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
  count.textContent = shown + ' / ' + rows.length + ' shown';
}}
q.addEventListener('input', apply);
for (const b of cbtns) {{
  b.addEventListener('click', () => {{
    if (activeConcept === b.dataset.concept) {{ activeConcept = null; b.classList.remove('active'); }}
    else {{ cbtns.forEach(x => x.classList.remove('active')); activeConcept = b.dataset.concept; b.classList.add('active'); }}
    apply();
  }});
}}
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
        assert "covering / chaining" not in concepts_for("bennett_mgf", "Bennett MGF", "")
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
