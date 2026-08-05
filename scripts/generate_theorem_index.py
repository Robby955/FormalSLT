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

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "docs" / "proof-frontier-manifest.json"
OUT_HTML = ROOT / "docs" / "INDEX.html"
OUT_MD = ROOT / "docs" / "INDEX.md"
REPO_URL = "https://github.com/Robby955/FormalSLT/blob/main"

# Concept keywords: a declaration is tagged with every concept whose trigger
# patterns appear (case-insensitively) in its name, summary, or family name.
# This is the search vocabulary a user actually types.
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
    "confidence sequence": ["confidence", "anytime", "ville", "subgammacs", "mixturecs", "eprocess", "e-process", "subgaussiancs", "attopcs"],
    "PAC-Bayes": ["pacbayes", "pac-bayes", "kldiv", "mcallester", "seeger", "maurer", "catoni"],
    "KL divergence": ["kldiv", "kl ", "kl-", "divergence", "change of measure", "changeofmeasure"],
    "Rademacher": ["rademacher", "massart", "symmetriz", "contraction"],
    "VC dimension": ["vc", "sauer", "shelah", "shatter"],
    "covering / chaining": ["covering", "dudley", "chaining", "entropy", "net"],
    "ERM": ["erm", "empiricalrisk", "excessrisk", "gengap", "generalization"],
    "stability": ["stability", "stable"],
    "sample statistics": ["samplemean", "samplevariance", "sample mean", "sample variance", "estimator"],
    "Glivenko-Cantelli": ["glivenko", "cantelli", "empiricalcdf", "empirical cdf", "lowerray", "lower ray", "lower-ray", "uniformdeviation", "bracketing"],
    "Bernoulli": ["bernoulli"],
    "risk": ["risk"],
}

KIND_PATTERN = (
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:private\s+)?(?:protected\s+)?"
    r"(?:theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+"
)


def module_to_file(module: str) -> Path:
    return ROOT / "FormalSLT" / Path(module.replace(".", "/") + ".lean")


def resolve_line(module: str, name: str) -> int | None:
    """Find the 1-based line where `name` is declared in its module file.

    Tries the fully written name first, then the last dotted component (handles
    declarations written as `def Foo` inside a `namespace Bar`, recorded as
    `Bar.Foo` in the theorem map)."""
    path = module_to_file(module)
    if not path.exists():
        return None
    text = path.read_text(encoding="utf-8").splitlines()
    candidates = [name]
    if "." in name:
        candidates.append(name.rsplit(".", 1)[1])
    for cand in candidates:
        pat = re.compile(KIND_PATTERN + re.escape(cand) + r"\b")
        for idx, line in enumerate(text, start=1):
            if pat.search(line):
                return idx
    return None


def concepts_for(name: str, summary: str, family: str) -> list[str]:
    haystack = f" {name} {summary} {family} ".lower()
    found = [
        concept
        for concept, triggers in CONCEPT_TRIGGERS.items()
        if any(t in haystack for t in triggers)
    ]
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
            line = resolve_line(module, name)
            rel = module_to_file(module).relative_to(ROOT).as_posix()
            rows.append(
                {
                    "name": name,
                    "module": module,
                    "kind": entry.get("kind", "theorem"),
                    "summary": summary,
                    "family": fam_name,
                    "file": rel,
                    "line": line,
                    "concepts": concepts_for(name, summary, fam_name),
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
        haystack = esc(
            " ".join(
                [row["name"], row["module"], row["summary"], row["family"]]
                + row["concepts"]
            ).lower()
        )
        cards.append(
            f'<div class="row" data-search="{haystack}">'
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
    const okTerm = !term || hay.includes(term);
    const okConcept = !activeConcept || hay.includes(normalize(activeConcept));
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
    args = parser.parse_args()

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
