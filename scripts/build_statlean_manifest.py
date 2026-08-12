#!/usr/bin/env python3
"""Harvest the FormalSLT theorem spine into the StatLean-v0.1 benchmark manifest.

StatLean is a Lean-4 benchmark of *statistics* concentration / learning-theory
tasks. v0.1 is a HARVEST: it does no new proving. It projects the already-verified
public spine (recorded in docs/proof-frontier-manifest.json plus the Lean sources)
into one self-describing task record per theorem, suitable for a retrieval / proof-
repair baseline.

Read-only over the .lean sources: this script never edits a proof file. It emits

  docs/statlean/statlean-v0.1.jsonl   one JSON record per selected task
  docs/statlean/statlean-v0.1.full.jsonl  every resolved decl (the harvest pool)

Each selected record:
  id                 stable slug (family-shortmodule-name)
  source             "FormalSLT" + repo + commit
  concept_family     the manifest family this decl sits in
  concept_tags       the 24-concept tags (Markov, Hoeffding, PAC-Bayes, ...)
  informal_statement seeded from the Lean docstring (/-- ... -/)
  lean_statement     verbatim signature (decl head through the `:=`)
  lean_proof_pointer file:line of the declaration
  dependency_edges   {imports: [...], lemma_uses: [...]}  (parsed, intra-corpus)
  axiom_profile      live `#print axioms` result, or "not-audited" if --no-axioms
  difficulty         heuristic tier from proof length + dependency fan-in
  fidelity           statement_fidelity_check.py result + sign-off field

Reuses:
  docs/proof-frontier-manifest.json   (family -> decl -> module -> role)
  scripts/generate_theorem_index.py   (the 24-concept CONCEPT_TRIGGERS vocabulary)
  scripts/statement_fidelity_check.py (the non-vacuity lint)
  scripts/check_axioms.sh             (the axiom-profile convention)

Usage:
  build_statlean_manifest.py            full harvest + curate + fidelity + axioms
  build_statlean_manifest.py --no-axioms  skip the live #print axioms pass (fast)
  build_statlean_manifest.py --limit N    cap selected tasks at N
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "docs" / "proof-frontier-manifest.json"
SRC_ROOT = ROOT / "FormalSLT"
OUT_DIR = ROOT / "docs" / "statlean"
OUT_SELECTED = OUT_DIR / "statlean-v0.1.jsonl"
OUT_FULL = OUT_DIR / "statlean-v0.1.full.jsonl"
OUT_STATS = OUT_DIR / "statlean-v0.1.stats.json"
def _find_fidelity() -> Path:
    """The non-vacuity gate. Prefer the vendored copy in FormalSLT/scripts; fall
    back to the project-level copy one directory up."""
    local = ROOT / "scripts" / "statement_fidelity_check.py"
    if local.exists():
        return local
    parent = ROOT.parent / "scripts" / "statement_fidelity_check.py"
    return parent if parent.exists() else local


FIDELITY = _find_fidelity()
LAKE = os.path.expanduser("~/.elan/bin/lake")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# The 24-concept search vocabulary, kept in sync with generate_theorem_index.py.
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
    "sample statistics": ["samplemean", "samplevariance", "empiricalvariance", "sample mean", "sample variance", "empirical variance", "empirical-variance", "estimator"],
    "Glivenko-Cantelli": ["glivenko", "cantelli", "empiricalcdf", "empirical cdf", "lowerray", "lower ray", "lower-ray", "uniformdeviation", "bracketing"],
    "Bernoulli": ["bernoulli"],
    "risk": ["risk"],
}

# The 24 statistics concept families the harvest must span (the curation budget is
# spread across these so no family is dropped).
TARGET_CONCEPTS = list(CONCEPT_TRIGGERS.keys())

KIND_PATTERN = (
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:private\s+)?(?:protected\s+)?"
    r"(?:theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+"
)


# --------------------------------------------------------------------------- #
# source resolution
# --------------------------------------------------------------------------- #
def module_to_file(module: str) -> Path:
    return SRC_ROOT / Path(module.replace(".", "/") + ".lean")


_FILE_CACHE: dict[str, list[str]] = {}


def file_lines(module: str) -> list[str] | None:
    if module in _FILE_CACHE:
        return _FILE_CACHE[module]
    path = module_to_file(module)
    if not path.exists():
        _FILE_CACHE[module] = None
        return None
    lines = path.read_text(encoding="utf-8").splitlines()
    _FILE_CACHE[module] = lines
    return lines


def resolve_decl(module: str, name: str) -> tuple[int, int] | None:
    """Return (1-based decl line, 0-based index) for `name` in its module."""
    lines = file_lines(module)
    if lines is None:
        return None
    candidates = [name]
    if "." in name:
        candidates.append(name.rsplit(".", 1)[1])
    for cand in candidates:
        pat = re.compile(KIND_PATTERN + re.escape(cand) + r"\b")
        for idx, line in enumerate(lines):
            if pat.search(line):
                return idx + 1, idx
    return None


def active_namespace(lines: list[str], idx0: int) -> str:
    """The namespace stack active at line idx0, walking `namespace`/`end`.
    Returns the dotted namespace prefix (e.g. FormalSLT.Concentration.SubGamma)."""
    stack: list[str] = []
    for i in range(idx0):
        m = re.match(r"^\s*namespace\s+(\S+)", lines[i])
        if m:
            stack.append(m.group(1))
            continue
        e = re.match(r"^\s*end\s+(\S+)\s*$", lines[i])
        if e and stack and stack[-1].split(".")[-1] == e.group(1).split(".")[-1]:
            stack.pop()
        elif re.match(r"^\s*end\s*$", lines[i]) and stack:
            stack.pop()
    return ".".join(stack)


def extract_signature(lines: list[str], idx0: int) -> str:
    """Verbatim signature: from the decl head down to (not including) the `:=`/`by`
    that starts the proof, capped to keep records bounded."""
    out: list[str] = []
    for i in range(idx0, min(idx0 + 60, len(lines))):
        line = lines[i]
        # stop once the proof body begins
        m = re.search(r":=\s*by\b|:=\s*$|:=\s*\S", line)
        if m and i > idx0 - 1:
            # keep the part of this line up to the `:=`
            cut = line[: m.start()].rstrip()
            if cut:
                out.append(cut)
            # include a trailing `:= by` marker truncation only if the colon-type
            # of the statement already closed; the signature is the part before `:=`.
            break
        out.append(line.rstrip())
    sig = "\n".join(out).rstrip()
    return sig


def extract_docstring(lines: list[str], idx0: int) -> str:
    """The `/-- ... -/` block immediately above the declaration, flattened."""
    j = idx0 - 1
    # skip attribute lines / blank lines directly above
    while j >= 0 and (lines[j].strip() == "" or lines[j].lstrip().startswith("@[")):
        j -= 1
    if j < 0 or not lines[j].rstrip().endswith("-/"):
        return ""
    end = j
    start = end
    while start >= 0 and "/--" not in lines[start]:
        start -= 1
    if start < 0:
        return ""
    block = lines[start : end + 1]
    text = "\n".join(block)
    text = text.replace("/--", "").replace("-/", "")
    text = re.sub(r"\s+", " ", text).strip()
    return text


def proof_body(lines: list[str], idx0: int) -> tuple[str, int]:
    """Best-effort proof body (from `:=` to the next top-level decl) + its line count."""
    body: list[str] = []
    started = False
    for i in range(idx0, len(lines)):
        line = lines[i]
        if i > idx0 and re.match(KIND_PATTERN, line):
            break
        if not started:
            if ":=" in line:
                started = True
                body.append(line[line.index(":=") :])
            continue
        body.append(line)
    return "\n".join(body), len([b for b in body if b.strip()])


# --------------------------------------------------------------------------- #
# tagging + dependency edges
# --------------------------------------------------------------------------- #
def concepts_for(name: str, summary: str, family: str) -> list[str]:
    hay = f" {name} {summary} {family} ".lower()
    return [c for c, trig in CONCEPT_TRIGGERS.items() if any(t in hay for t in trig)]


def module_imports(module: str) -> list[str]:
    lines = file_lines(module)
    if lines is None:
        return []
    imps = []
    for line in lines:
        m = re.match(r"^\s*import\s+(FormalSLT\S*)", line)
        if m:
            imps.append(m.group(1))
    return imps


def lemma_uses(body: str, all_short_names: set[str], self_name: str) -> list[str]:
    """Intra-corpus lemma calls: other harvested decls whose (short) name appears in
    the proof body as an identifier."""
    if not body:
        return []
    self_short = self_name.rsplit(".", 1)[-1]
    found = set()
    for short in all_short_names:
        if short == self_short:
            continue
        if re.search(r"(?<![A-Za-z0-9_.'])" + re.escape(short) + r"(?![A-Za-z0-9_'])", body):
            found.add(short)
    return sorted(found)


# --------------------------------------------------------------------------- #
# harvest
# --------------------------------------------------------------------------- #
def harvest() -> list[dict[str, Any]]:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    families = manifest["theorem_families"]
    # collect short names across the whole corpus for lemma-use parsing
    all_short = {e["name"].rsplit(".", 1)[-1] for f in families for e in f["entries"]}

    records: list[dict[str, Any]] = []
    for family in families:
        fam = family["name"]
        for entry in family["entries"]:
            name = entry["name"]
            module = entry["module"]
            summary = entry.get("summary", "")
            kind = entry.get("kind", "theorem")
            res = resolve_decl(module, name)
            if res is None:
                continue
            line1, idx0 = res
            lines = file_lines(module)
            sig = extract_signature(lines, idx0)
            doc = extract_docstring(lines, idx0)
            body, body_lines = proof_body(lines, idx0)
            ns = active_namespace(lines, idx0)
            rel = module_to_file(module).relative_to(ROOT).as_posix()
            short = name.rsplit(".", 1)[-1]
            mod_tail = module.split(".")[-1]
            slug = re.sub(r"[^A-Za-z0-9]+", "-", f"{mod_tail}-{short}").strip("-").lower()
            uses = lemma_uses(body, all_short, name) if kind in ("theorem", "lemma") else []
            rec = {
                "id": slug,
                "qualified_name": name,
                "short_name": short,
                "kind": kind,
                "source": {
                    "library": "FormalSLT",
                    "repo": manifest["repository"]["name"],
                    "module": module,
                },
                "concept_family": fam,
                "concept_tags": concepts_for(name, summary, fam),
                "informal_statement": doc or summary,
                "role": summary,
                "lean_statement": sig,
                "lean_proof_pointer": f"{rel}:{line1}",
                "dependency_edges": {
                    "imports": module_imports(module),
                    "lemma_uses": uses,
                },
                "_proof_lines": body_lines,  # internal, stripped before write
                "_file": rel,
                "_line": line1,
                "_namespace": ns,
                "_import": "FormalSLT." + module,
            }
            records.append(rec)
    return records


def difficulty(rec: dict[str, Any]) -> str:
    """Heuristic tier from proof length + intra-corpus fan-in."""
    pl = rec["_proof_lines"]
    fan = len(rec["dependency_edges"]["lemma_uses"])
    score = pl + 2 * fan
    if rec["kind"] not in ("theorem", "lemma"):
        return "definition"
    if score <= 4:
        return "easy"
    if score <= 20:
        return "medium"
    return "hard"


# --------------------------------------------------------------------------- #
# curation: cleanest ~120-150 named theorems spread across concept families
# --------------------------------------------------------------------------- #
def cleanliness(rec: dict[str, Any]) -> tuple:
    """Sort key for "cleanest": named theorem (not def), has a docstring, statement
    not absurdly long, prefers a primary named result over a plumbing wrapper."""
    has_doc = bool(rec["informal_statement"]) and rec["informal_statement"] != rec["role"]
    has_any_informal = bool(rec["informal_statement"])
    sig_len = len(rec["lean_statement"])
    name = rec["short_name"].lower()
    # de-prioritise obvious plumbing / helper suffixes
    plumbing = any(name.endswith(s) for s in ("_aux", "_helper", "_of_eq", "_eq", "_def"))
    primary = any(k in name for k in ("inequality", "bound", "tail", "theorem", "lemma", "complexity", "valid", "decomposition"))
    # lower tuple sorts first
    return (
        0 if has_any_informal else 1,
        0 if has_doc else 1,
        0 if not plumbing else 1,
        0 if primary else 1,
        sig_len,
    )


def curate(records: list[dict[str, Any]], target_lo: int, target_hi: int) -> list[dict[str, Any]]:
    """Select the cleanest named theorems, spread across the 24 concept families.
    Definitions are kept only as dependency context, never as benchmark tasks."""
    theorems = [r for r in records if r["kind"] in ("theorem", "lemma")]
    # bucket by primary concept tag (first tag), fall back to concept_family
    by_concept: dict[str, list[dict[str, Any]]] = {c: [] for c in TARGET_CONCEPTS}
    untagged: list[dict[str, Any]] = []
    for r in theorems:
        tags = r["concept_tags"]
        if not tags:
            untagged.append(r)
            continue
        for t in tags:
            by_concept.setdefault(t, []).append(r)
    for c in by_concept:
        by_concept[c].sort(key=cleanliness)

    selected: dict[str, dict[str, Any]] = {}  # id -> rec, dedup across concepts
    # round-robin: take the cleanest from each concept until budget reached
    per_round_idx = 0
    progressed = True
    while len(selected) < target_hi and progressed:
        progressed = False
        for c in TARGET_CONCEPTS:
            pool = by_concept.get(c, [])
            if per_round_idx < len(pool):
                r = pool[per_round_idx]
                if r["id"] not in selected:
                    selected[r["id"]] = r
                progressed = True
                if len(selected) >= target_hi:
                    break
        per_round_idx += 1
    # ensure floor: if a concept contributed nothing, force its single cleanest in
    for c in TARGET_CONCEPTS:
        if len(selected) >= target_hi:
            break
        pool = by_concept.get(c, [])
        if pool and not any(c in selected[i]["concept_tags"] for i in selected):
            r = pool[0]
            selected[r["id"]] = r
    out = list(selected.values())
    out.sort(key=lambda r: (r["concept_family"], r["short_name"]))
    return out[:target_hi] if len(out) > target_hi else out


# --------------------------------------------------------------------------- #
# fidelity + axioms
# --------------------------------------------------------------------------- #
def run_fidelity(rec: dict[str, Any]) -> dict[str, Any]:
    if not FIDELITY.exists():
        return {"checked": False, "flagged": False, "signed_off": False,
                "lint": f"error: fidelity gate not found at {FIDELITY}"}
    path = ROOT / rec["_file"]
    try:
        r = subprocess.run(
            [sys.executable, str(FIDELITY), str(path), rec["short_name"]],
            capture_output=True, text=True, timeout=60,
        )
        out = (r.stdout + r.stderr).strip()
        # The gate prints a "--- checked N decl(s), M flag(s)" trailer on success.
        # If that trailer is absent, the gate did not actually run (e.g. file open
        # error): record checked=False so a missing run is never a silent pass.
        ran = "--- checked" in out
        flagged = " FLAG " in (" " + out + " ")
        signed = "ok(signed)" in out
        return {
            "checked": ran,
            "flagged": bool(flagged and not signed),
            "signed_off": signed,
            "lint": out.splitlines()[-1] if out else "checked 0 decl(s), 0 flag(s)",
        }
    except Exception as e:  # noqa: BLE001
        return {"checked": False, "flagged": False, "signed_off": False, "lint": f"error: {e}"}


def _classify_axioms(kind: str, raw: str) -> str:
    if kind == "does not":
        return "axiom-free"
    axset = {a.strip() for a in raw.replace("\n", " ").split(",") if a.strip()}
    extra = axset - ALLOWED_AXIOMS
    if extra:
        return "NONSTANDARD:" + ",".join(sorted(extra))
    return "clean{propext,Classical.choice,Quot.sound}"


def axiom_profiles(records: list[dict[str, Any]]) -> dict[str, str]:
    """One batched `#print axioms` over all selected decls.

    Manifest names are short / partially-qualified, so the scratch resolves each
    via `open <active-namespace> in #print axioms <short>` (the namespace is read
    from the source file's namespace stack). Results are keyed by the record id.

    Manifest modules are recorded library-relative (e.g. `AlgorithmicStability`);
    the lake target and Lean import are the fully-qualified `FormalSLT.<module>`."""
    modules = sorted({r["_import"] for r in records})
    # build the modules first (cached -> fast)
    build = subprocess.run(
        [LAKE, "build", *modules], cwd=str(ROOT),
        capture_output=True, text=True, timeout=3600,
    )
    if build.returncode != 0:
        sys.stderr.write("axiom-profile build failed; tail:\n" + build.stderr[-1500:] + "\n")
        return {r["id"]: "unknown(build-failed)" for r in records}

    body = "".join(f"import {m}\n" for m in modules)
    # marker each query so we can map output blocks back to the record id reliably
    for r in records:
        ns = r["_namespace"]
        short = r["short_name"]
        body += f'#check "STATLEAN_ID::{r["id"]}"\n'
        if ns:
            body += f"open {ns} in\n#print axioms {short}\n"
        else:
            body += f"#print axioms {short}\n"
    fd, scratch = tempfile.mkstemp(suffix=".lean", dir=str(ROOT))
    os.write(fd, body.encode()); os.close(fd)
    try:
        r = subprocess.run([LAKE, "env", "lean", scratch], cwd=str(ROOT),
                           capture_output=True, text=True, timeout=3600)
    finally:
        os.unlink(scratch)
    text = r.stdout + "\n" + r.stderr

    # Split the stream on the id markers; each segment holds that id's axiom report.
    profiles: dict[str, str] = {}
    parts = re.split(r'"STATLEAN_ID::([^"]+)"', text)
    # parts: [pre, id1, seg1, id2, seg2, ...]
    for i in range(1, len(parts) - 1, 2):
        rid = parts[i]
        seg = parts[i + 1]
        m = re.search(r"(does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",
                      seg, re.DOTALL)
        if m:
            profiles[rid] = _classify_axioms(
                "does not" if m.group(1).startswith("does not") else "depends",
                m.group(2) or "")
    for r in records:
        profiles.setdefault(r["id"], "unknown")
    return profiles


# --------------------------------------------------------------------------- #
def write_jsonl(path: Path, records: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as fh:
        for r in records:
            clean = {k: v for k, v in r.items() if not k.startswith("_")}
            fh.write(json.dumps(clean, ensure_ascii=False) + "\n")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-axioms", action="store_true", help="skip the live #print axioms pass")
    ap.add_argument("--no-fidelity", action="store_true", help="skip the per-task fidelity lint")
    ap.add_argument("--limit", type=int, default=150, help="max selected tasks (default 150)")
    ap.add_argument("--floor", type=int, default=120, help="target floor for selection")
    a = ap.parse_args()

    print("harvesting from", MANIFEST.relative_to(ROOT))
    pool = harvest()
    n_def = sum(1 for r in pool if r["kind"] not in ("theorem", "lemma"))
    print(f"  resolved {len(pool)} declarations ({len(pool)-n_def} theorems/lemmas, {n_def} defs)")

    for r in pool:
        r["difficulty"] = difficulty(r)

    selected = curate(pool, a.floor, a.limit)
    print(f"  curated {len(selected)} tasks across "
          f"{len({c for r in selected for c in r['concept_tags']})} concept tags")

    if not a.no_fidelity:
        print("running statement_fidelity_check per selected task ...")
        flagged = 0
        for r in selected:
            r["fidelity"] = run_fidelity(r)
            if r["fidelity"]["flagged"]:
                flagged += 1
        print(f"  fidelity: {len(selected)} audited, {flagged} flagged")
    else:
        for r in selected:
            r["fidelity"] = {"checked": False, "flagged": False, "signed_off": False, "lint": "skipped"}

    if not a.no_axioms:
        print("running batched #print axioms for the axiom profile ...")
        prof = axiom_profiles(selected)
        for r in selected:
            r["axiom_profile"] = prof.get(r["id"], "unknown")
        nonstd = sum(1 for r in selected if r["axiom_profile"].startswith("NONSTANDARD"))
        print(f"  axioms: {sum(1 for r in selected if r['axiom_profile'].startswith(('clean','axiom-free')))} clean, "
              f"{nonstd} nonstandard")
    else:
        for r in selected:
            r["axiom_profile"] = "not-audited"

    # final per-task field ordering for the selected manifest
    ordered = []
    for r in selected:
        ordered.append({
            "id": r["id"],
            "source": r["source"],
            "concept_family": r["concept_family"],
            "concept_tags": r["concept_tags"],
            "informal_statement": r["informal_statement"],
            "lean_statement": r["lean_statement"],
            "lean_proof_pointer": r["lean_proof_pointer"],
            "dependency_edges": r["dependency_edges"],
            "axiom_profile": r["axiom_profile"],
            "difficulty": r["difficulty"],
            "fidelity": r["fidelity"],
            "qualified_name": r["qualified_name"],
            "kind": r["kind"],
            "role": r["role"],
        })

    write_jsonl(OUT_SELECTED, ordered)
    write_jsonl(OUT_FULL, pool)

    from collections import Counter
    tag_counts = Counter(t for r in ordered for t in r["concept_tags"])
    diff_counts = Counter(r["difficulty"] for r in ordered)
    stats = {
        "release": "StatLean-v0.1",
        "source_repo": json.loads(MANIFEST.read_text())["repository"]["name"],
        "harvested_declarations": len(pool),
        "harvested_theorems": len(pool) - n_def,
        "harvested_definitions": n_def,
        "curated_tasks": len(ordered),
        "concept_tags_covered": len(tag_counts),
        "tasks_per_concept_tag": dict(sorted(tag_counts.items())),
        "tasks_per_difficulty": dict(diff_counts),
        "fidelity_audited": sum(1 for r in ordered if r["fidelity"]["checked"]),
        "fidelity_flagged": sum(1 for r in ordered if r["fidelity"]["flagged"]),
        "axiom_clean": sum(1 for r in ordered
                           if r["axiom_profile"].startswith(("clean", "axiom-free"))),
        "axiom_nonstandard": sum(1 for r in ordered
                                 if r["axiom_profile"].startswith("NONSTANDARD")),
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
    }
    OUT_STATS.write_text(json.dumps(stats, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    print(f"wrote {OUT_SELECTED.relative_to(ROOT)} ({len(ordered)} tasks)")
    print(f"wrote {OUT_FULL.relative_to(ROOT)} ({len(pool)} harvested decls)")
    print(f"wrote {OUT_STATS.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
