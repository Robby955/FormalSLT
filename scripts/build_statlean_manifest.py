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
  source             "FormalSLT" + repo + module + immutable source-tree hash
  concept_family     the manifest family this decl sits in
  concept_tags       the shared statistics tags (Markov, MLE, PAC-Bayes, ...)
  informal_statement seeded from the Lean docstring (/-- ... -/)
  lean_statement     verbatim signature (declaration head before the proof body)
  lean_proof_pointer file:line of the declaration
  dependency_edges   {imports: [...], lexical_declaration_mentions: [...]}
  axiom_profile      live `#print axioms` result, or "not-audited" if --no-axioms
  difficulty         heuristic tier from proof length + dependency fan-in
  fidelity           statement_fidelity_check.py result + sign-off field

Reuses:
  docs/proof-frontier-manifest.json   (family -> decl -> module -> role)
  scripts/generate_theorem_index.py   (the canonical concept-tag vocabulary)
  scripts/statement_fidelity_check.py (the non-vacuity lint)
  scripts/check_axioms.sh             (the axiom-profile convention)

Usage:
  build_statlean_manifest.py            full harvest + curate + fidelity + axioms
  build_statlean_manifest.py --no-axioms  skip the live #print axioms pass (fast)
  build_statlean_manifest.py --limit N    cap selected tasks at N
"""
from __future__ import annotations

import argparse
import copy
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

if __package__:
    from .generate_proof_frontier_manifest import (
        parse_lean_declarations,
        resolve_source_declaration,
        source_resolution_self_test,
        strip_lean_comments_and_strings,
    )
    from .generate_theorem_index import CONCEPT_TRIGGERS, concepts_for
else:
    from generate_proof_frontier_manifest import (  # type: ignore[no-redef]
        parse_lean_declarations,
        resolve_source_declaration,
        source_resolution_self_test,
        strip_lean_comments_and_strings,
    )
    from generate_theorem_index import (  # type: ignore[no-redef]
        CONCEPT_TRIGGERS,
        concepts_for,
    )

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "docs" / "proof-frontier-manifest.json"
SRC_ROOT = ROOT / "FormalSLT"
OUT_DIR = ROOT / "docs" / "statlean"
OUT_SELECTED = OUT_DIR / "statlean-v0.1.jsonl"
OUT_FULL = OUT_DIR / "statlean-v0.1.full.jsonl"
OUT_STATS = OUT_DIR / "statlean-v0.1.stats.json"
OUT_SELECTION = OUT_DIR / "statlean-v0.1.selection.json"


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
SCHEMA_VERSION = "statlean-v0.1"

# The canonical statistics vocabulary. Curation spreads its budget across every
# tag represented in the current harvest.
TARGET_CONCEPTS = list(CONCEPT_TRIGGERS.keys())

# --------------------------------------------------------------------------- #
# source resolution
# --------------------------------------------------------------------------- #
def module_to_file(module: str) -> Path:
    return SRC_ROOT / Path(module.replace(".", "/") + ".lean")


_FILE_CACHE: dict[str, list[str] | None] = {}
_DECLARATION_CACHE: dict[str, list[dict[str, Any]]] = {}


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


def file_declarations(module: str) -> list[dict[str, Any]]:
    if module in _DECLARATION_CACHE:
        return _DECLARATION_CACHE[module]
    path = module_to_file(module)
    declarations = parse_lean_declarations(path.read_text(encoding="utf-8"))
    _DECLARATION_CACHE[module] = declarations
    return declarations


def resolve_decl(module: str, name: str) -> dict[str, Any]:
    """Return the exact source-derived declaration metadata."""
    return resolve_source_declaration(module_to_file(module), name)


TOP_LEVEL_BOUNDARY = re.compile(
    r"^(?:namespace\b|section\b|end\b|open\b|export\b|variable\b|"
    r"include\b|omit\b|attribute\b|local\b|scoped\b|set_option\b|"
    r"noncomputable\s+section\b|mutual\b|#|@\[)"
)
STRUCTURAL_DECLARATIONS = {"structure", "class", "inductive"}


def _declaration_end(lines: list[str], idx0: int, next_idx0: int) -> int:
    """Return the first line after this declaration's source span.

    Parsed declarations provide the hard upper bound. Namespace/section commands
    can occur between declarations and are excluded from the preceding proof.
    """
    raw = "\n".join(lines[idx0:next_idx0])
    clean_lines = strip_lean_comments_and_strings(raw).splitlines()
    for offset, clean_line in enumerate(clean_lines[1:], start=1):
        if clean_line and not clean_line[0].isspace() and TOP_LEVEL_BOUNDARY.match(clean_line):
            return idx0 + offset
    return next_idx0


def _top_level_marker(clean: str, keyword: str) -> tuple[int, int] | None:
    """Find the declaration-level body marker outside all bracketed arguments."""
    stack: list[str] = []
    closing = {")": "(", "]": "[", "}": "{"}
    assignment: tuple[int, int] | None = None
    where_marker: tuple[int, int] | None = None
    i = 0
    while i < len(clean):
        ch = clean[i]
        if ch in "([{":
            stack.append(ch)
        elif ch in closing:
            if stack and stack[-1] == closing[ch]:
                stack.pop()
        elif not stack:
            if assignment is None and clean.startswith(":=", i):
                prefix = clean[:i]
                # A theorem proposition may itself begin with a top-level
                # `let x := ...`; that local binding is not the declaration's
                # proof assignment.
                local_binding = re.search(
                    r"(?:^|[;\n:])\s*(?:let|have|set)\s+"
                    r"[^;\n:=]+(?:\s*:\s*[^;\n:=]+)?\s*$",
                    prefix,
                )
                if local_binding is None:
                    assignment = (i, i + 2)
            if (
                where_marker is None
                and keyword not in STRUCTURAL_DECLARATIONS
                and clean.startswith("where", i)
                and (i == 0 or not (clean[i - 1].isalnum() or clean[i - 1] in "_'"))
                and (
                    i + 5 == len(clean)
                    or not (clean[i + 5].isalnum() or clean[i + 5] in "_'")
                )
            ):
                where_marker = (i, i + 5)
        i += 1
    markers = [marker for marker in (assignment, where_marker) if marker is not None]
    return min(markers, key=lambda marker: marker[0]) if markers else None


def _balanced_brackets(clean: str) -> bool:
    stack: list[str] = []
    closing = {")": "(", "]": "[", "}": "{"}
    for ch in clean:
        if ch in "([{":
            stack.append(ch)
        elif ch in closing:
            if not stack or stack[-1] != closing[ch]:
                return False
            stack.pop()
    return not stack


def declaration_source_parts(
    lines: list[str], idx0: int, end_idx0: int, declaration: dict[str, Any]
) -> tuple[str, str, int]:
    """Return verbatim signature, cleaned body, and nonblank proof-line count."""
    raw = "\n".join(lines[idx0:end_idx0]).rstrip()
    clean = strip_lean_comments_and_strings(raw)
    marker = _top_level_marker(clean, declaration["keyword"])

    if declaration["keyword"] in STRUCTURAL_DECLARATIONS:
        # Structures/classes/inductives have no proof assignment. Keep their
        # fields, but omit trailing documentation for the following command.
        last = max((i for i, ch in enumerate(clean) if not ch.isspace()), default=-1)
        signature = raw[: last + 1].rstrip()
        clean_body = ""
    else:
        if marker is None:
            raise ValueError(
                f"{declaration['qualified_name']}:{declaration['line']}: "
                "no top-level declaration body marker"
            )
        start, body_start = marker
        signature = raw[:start].rstrip()
        clean_body = clean[body_start:]

    clean_signature = strip_lean_comments_and_strings(signature)
    if not _balanced_brackets(clean_signature):
        raise ValueError(
            f"{declaration['qualified_name']}:{declaration['line']}: "
            "unbalanced extracted signature"
        )
    expected = re.compile(
        rf"^\s*(?:@\[[^\]]*\]\s*)*"
        rf"(?:(?:noncomputable|private|protected|nonrec|unsafe)\s+)*"
        rf"{re.escape(declaration['keyword'])}\s+{re.escape(declaration['raw_name'])}"
    )
    if not expected.search(clean_signature):
        raise ValueError(
            f"{declaration['qualified_name']}:{declaration['line']}: "
            "signature does not begin at the resolved declaration"
        )
    proof_lines = sum(1 for line in clean_body.splitlines() if line.strip())
    return signature, clean_body, proof_lines


def resolved_declaration_parts(
    module: str, name: str
) -> tuple[dict[str, Any], str, str, int]:
    """Resolve one mapped declaration and extract its exact bounded source span."""
    lines = file_lines(module)
    if lines is None:
        raise ValueError(f"Lean source does not exist: {module_to_file(module)}")
    declaration = resolve_decl(module, name)
    idx0 = declaration["line"] - 1
    declarations = file_declarations(module)
    next_idx0 = min(
        (decl["line"] - 1 for decl in declarations if decl["line"] - 1 > idx0),
        default=len(lines),
    )
    end_idx0 = _declaration_end(lines, idx0, next_idx0)
    signature, body, proof_lines = declaration_source_parts(
        lines, idx0, end_idx0, declaration
    )
    return declaration, signature, body, proof_lines


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


def extract_fidelity_comment(lines: list[str], idx0: int) -> str:
    """Return the contiguous `--` comment block immediately above a declaration."""
    j = idx0 - 1
    if j >= 0 and not lines[j].strip():
        j -= 1
    end = j
    while j >= 0 and lines[j].lstrip().startswith("--"):
        j -= 1
    return "\n".join(lines[j + 1 : end + 1]) if end >= j + 1 else ""


def source_tree_hash() -> str:
    """Return the immutable Git tree containing the harvested Lean source."""
    try:
        dirty = subprocess.check_output(
            ["git", "status", "--porcelain=v1", "--", "FormalSLT"],
            cwd=ROOT,
            text=True,
        ).strip()
        if dirty:
            raise RuntimeError(
                "FormalSLT source has uncommitted changes; refusing to attach a stale tree hash"
            )
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD:FormalSLT"], cwd=ROOT, text=True
        ).strip()
    except (OSError, subprocess.CalledProcessError) as error:
        raise RuntimeError("could not resolve the FormalSLT source tree hash") from error


# --------------------------------------------------------------------------- #
# dependency edges
# --------------------------------------------------------------------------- #
def module_imports(module: str) -> list[str]:
    lines = file_lines(module)
    if lines is None:
        return []
    imps = []
    for line in lines:
        m = re.match(r"^\s*import\s+(FormalSLT\S*)", line)
        if m:
            imps.append(m.group(1))
    return sorted(set(imps))


IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def lexical_declaration_mentions(
    body: str,
    current: dict[str, Any],
    records: list[dict[str, Any]],
) -> list[dict[str, str]]:
    """Resolve unambiguous harvested declaration names mentioned in cleaned source.

    This is deliberately described as a lexical relation, not an elaborated Lean
    dependency graph. Qualified mentions and unique same-namespace short mentions
    are retained; unresolved ambiguity is omitted.
    """
    if not body:
        return []
    by_short: dict[str, list[dict[str, Any]]] = {}
    for record in records:
        by_short.setdefault(record["short_name"], []).append(record)
    current_ns = current["qualified_name"].rsplit(".", 1)[0]
    found: dict[str, dict[str, str]] = {}
    for token in set(IDENTIFIER.findall(body)):
        candidates: list[dict[str, Any]]
        if "." in token:
            candidates = [
                record for record in records
                if record["qualified_name"] == token
                or record["qualified_name"].endswith(f".{token}")
            ]
        else:
            candidates = list(by_short.get(token, []))
            same_ns = [
                record for record in candidates
                if record["qualified_name"].rsplit(".", 1)[0] == current_ns
            ]
            candidates = same_ns if len(same_ns) == 1 else []
        if len(candidates) != 1 or candidates[0]["id"] == current["id"]:
            continue
        target = candidates[0]
        found[target["id"]] = {
            "id": target["id"],
            "qualified_name": target["qualified_name"],
        }
    return [found[key] for key in sorted(found)]


# --------------------------------------------------------------------------- #
# harvest
# --------------------------------------------------------------------------- #
def harvest() -> list[dict[str, Any]]:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    families = manifest["theorem_families"]
    tree_hash = source_tree_hash()

    records: list[dict[str, Any]] = []
    for family in families:
        fam = family["name"]
        for entry in family["entries"]:
            name = entry["name"]
            module = entry["module"]
            summary = entry.get("summary", "")
            declaration, sig, body, body_lines = resolved_declaration_parts(module, name)
            line1 = declaration["line"]
            idx0 = line1 - 1
            lines = file_lines(module)
            if lines is None:
                raise ValueError(f"Lean source does not exist: {module_to_file(module)}")
            doc = extract_docstring(lines, idx0)
            fidelity_comment = extract_fidelity_comment(lines, idx0)
            rel = module_to_file(module).relative_to(ROOT).as_posix()
            qualified = declaration["qualified_name"]
            short = declaration["raw_name"].rsplit(".", 1)[-1]
            mod_tail = module.split(".")[-1]
            slug = re.sub(r"[^A-Za-z0-9]+", "-", f"{mod_tail}-{short}").strip("-").lower()
            rec = {
                "schema_version": SCHEMA_VERSION,
                "id": slug,
                "qualified_name": qualified,
                "short_name": short,
                "kind": declaration["kind"],
                "source": {
                    "library": "FormalSLT",
                    "repo": manifest["repository"]["name"],
                    "module": module,
                    "tree": tree_hash,
                },
                "concept_family": fam,
                "concept_tags": concepts_for(qualified, summary, fam),
                "informal_statement": doc or summary,
                "role": summary,
                "lean_statement": sig,
                "lean_proof_pointer": f"{rel}:{line1}",
                "dependency_edges": {
                    "imports": module_imports(module),
                    "lexical_declaration_mentions": [],
                },
                "_proof_lines": body_lines,  # internal, stripped before write
                "_proof_body": body,
                "_fidelity_comment": fidelity_comment,
                "_file": rel,
                "_line": line1,
                "_import": "FormalSLT." + module,
            }
            records.append(rec)

    ids = [record["id"] for record in records]
    if len(ids) != len(set(ids)):
        duplicates = sorted({rid for rid in ids if ids.count(rid) > 1})
        raise ValueError(f"duplicate StatLean record ids: {', '.join(duplicates)}")
    qualified_names = [record["qualified_name"] for record in records]
    if len(qualified_names) != len(set(qualified_names)):
        duplicates = sorted(
            {name for name in qualified_names if qualified_names.count(name) > 1}
        )
        raise ValueError(f"duplicate qualified declaration names: {', '.join(duplicates)}")
    for record in records:
        if record["kind"] in ("theorem", "lemma"):
            record["dependency_edges"]["lexical_declaration_mentions"] = (
                lexical_declaration_mentions(record["_proof_body"], record, records)
            )
    by_id = {record["id"]: record for record in records}
    vocabulary = set(TARGET_CONCEPTS)
    for record in records:
        tags = record["concept_tags"]
        if len(tags) != len(set(tags)) or not set(tags) <= vocabulary:
            raise ValueError(f"invalid concept tags on {record['qualified_name']}")
        mentions = record["dependency_edges"]["lexical_declaration_mentions"]
        if mentions != sorted(mentions, key=lambda edge: edge["id"]):
            raise ValueError(f"unsorted lexical mentions on {record['qualified_name']}")
        for edge in mentions:
            target = by_id.get(edge["id"])
            if (
                target is None
                or target["id"] == record["id"]
                or target["qualified_name"] != edge["qualified_name"]
            ):
                raise ValueError(f"invalid lexical mention on {record['qualified_name']}")
    return records


def difficulty(rec: dict[str, Any]) -> str:
    """Heuristic tier from proof length + intra-corpus fan-in."""
    pl = rec["_proof_lines"]
    fan = len(rec["dependency_edges"]["lexical_declaration_mentions"])
    score = pl + 2 * fan
    if rec["kind"] not in ("theorem", "lemma"):
        return "definition"
    if score <= 4:
        return "easy"
    if score <= 20:
        return "medium"
    return "hard"


# --------------------------------------------------------------------------- #
# curation: cleanest named theorems spread across declaration-local concept tags
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
    """Select clean named theorems across every represented vocabulary tag.
    Definitions are kept only as dependency context, never as benchmark tasks."""
    theorems = [r for r in records if r["kind"] in ("theorem", "lemma")]
    # Bucket each theorem under every declaration-local concept tag.
    by_concept: dict[str, list[dict[str, Any]]] = {c: [] for c in TARGET_CONCEPTS}
    for r in theorems:
        tags = r["concept_tags"]
        if not tags:
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


def select_tasks(
    records: list[dict[str, Any]],
    target_lo: int,
    target_hi: int,
    refresh_selection: bool,
) -> list[dict[str, Any]]:
    """Load the source-tree-pinned v0.1 selection or explicitly refresh it."""
    tree = source_tree_hash()
    if refresh_selection:
        selected = curate(records, target_lo, target_hi)
        if len(selected) < min(target_lo, target_hi):
            raise RuntimeError("refreshed selection does not meet the requested floor")
        return selected

    if not OUT_SELECTION.exists():
        raise RuntimeError(
            f"missing pinned selection {OUT_SELECTION.relative_to(ROOT)}; "
            "run once with --refresh-selection"
        )
    selection = json.loads(OUT_SELECTION.read_text(encoding="utf-8"))
    if selection.get("schema_version") != SCHEMA_VERSION:
        raise RuntimeError("selection schema version does not match the generator")
    if selection.get("source_tree") != tree:
        raise RuntimeError(
            "the pinned StatLean-v0.1 selection targets a different FormalSLT source tree"
        )
    ids = selection.get("task_ids")
    if not isinstance(ids, list) or len(ids) != len(set(ids)):
        raise RuntimeError("pinned selection task_ids must be a unique list")
    by_id = {record["id"]: record for record in records}
    missing = [rid for rid in ids if rid not in by_id]
    if missing:
        raise RuntimeError("pinned selection has missing ids: " + ", ".join(missing))
    selected = [by_id[rid] for rid in ids[:target_hi]]
    if target_hi >= len(ids) and len(selected) < min(target_lo, target_hi):
        raise RuntimeError("pinned selection does not meet the requested floor")
    return selected


# --------------------------------------------------------------------------- #
# fidelity + axioms
# --------------------------------------------------------------------------- #
def run_fidelity(rec: dict[str, Any]) -> dict[str, Any]:
    if not FIDELITY.exists():
        return {"checked": False, "flagged": False, "signed_off": False,
                "lint": f"error: fidelity gate not found at {FIDELITY}"}
    scratch_text = ""
    if rec["_fidelity_comment"]:
        scratch_text += rec["_fidelity_comment"] + "\n"
    scratch_text += rec["lean_statement"] + "\n"
    fd, scratch = tempfile.mkstemp(suffix=".lean")
    os.write(fd, scratch_text.encode())
    os.close(fd)
    try:
        r = subprocess.run(
            [sys.executable, str(FIDELITY), scratch],
            capture_output=True, text=True, timeout=60,
        )
        out = (r.stdout + r.stderr).strip()
        trailer = re.search(r"--- checked (\d+) decl\(s\), (\d+) flag\(s\)$", out)
        checked_count = int(trailer.group(1)) if trailer else 0
        flag_count = int(trailer.group(2)) if trailer else 0
        ran = checked_count == 1 and r.returncode == 0
        signed = "ok(signed)" in out
        return {
            "checked": ran,
            "flagged": bool(flag_count),
            "signed_off": signed,
            "lint": out.splitlines()[-1] if out else "error: no fidelity output",
        }
    except Exception as e:  # noqa: BLE001
        return {"checked": False, "flagged": False, "signed_off": False, "lint": f"error: {e}"}
    finally:
        os.unlink(scratch)


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

    Source-resolved fully qualified names make every query exact, including the
    two distinct `bernstein_tail` declarations. Results are keyed by record id.

    Manifest modules are recorded library-relative (e.g. `AlgorithmicStability`);
    the lake target and Lean import are the fully-qualified `FormalSLT.<module>`."""
    modules = sorted({r["_import"] for r in records})
    # build the modules first (cached -> fast)
    build = subprocess.run(
        [LAKE, "build", *modules], cwd=str(ROOT),
        capture_output=True, text=True, timeout=3600,
    )
    if build.returncode != 0:
        raise RuntimeError(
            "axiom-profile build failed; tail:\n" + (build.stdout + build.stderr)[-1500:]
        )

    body = "".join(f"import {m}\n" for m in modules)
    # marker each query so we can map output blocks back to the record id reliably
    for r in records:
        body += f'#check "STATLEAN_ID::{r["id"]}"\n'
        body += f'#print axioms {r["qualified_name"]}\n'
    fd, scratch = tempfile.mkstemp(suffix=".lean", dir=str(ROOT))
    os.write(fd, body.encode()); os.close(fd)
    try:
        r = subprocess.run([LAKE, "env", "lean", scratch], cwd=str(ROOT),
                           capture_output=True, text=True, timeout=3600)
    finally:
        os.unlink(scratch)
    text = r.stdout + "\n" + r.stderr
    if r.returncode != 0:
        raise RuntimeError("axiom-profile Lean run failed; tail:\n" + text[-1500:])

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
    ap.add_argument(
        "--refresh-selection",
        action="store_true",
        help="explicitly replace the source-tree-pinned v0.1 task selection",
    )
    ap.add_argument(
        "--self-test", action="store_true", help="test declaration resolution and concepts"
    )
    a = ap.parse_args()

    if a.self_test:
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
        assert "covering / chaining" not in concepts_for("internet", "", "")
        assert {"Bernstein", "MGF", "Bernoulli"}.issubset(
            concepts_for(
                "FormalSLT.PACBayes.IndicatorBernsteinMoment."
                "indicator_expectedPriorBernsteinExpMoment_le_one",
                "",
                "",
            )
        )
        declaration = resolve_decl(
            "PACBayes.FiniteExponentialTilt", "finiteExponentialTiltNormalizer_pos"
        )
        assert declaration["line"] > 1 and declaration["kind"] == "theorem"
        assert declaration["qualified_name"] == (
            "FormalSLT.PACBayes.FiniteExponentialTilt."
            "finiteExponentialTiltNormalizer_pos"
        )
        _, named_signature, _, _ = resolved_declaration_parts(
            "Covering.TotalBoundedDudleyCovering",
            "totalBoundedCoveringNumberAtRadius_dyadic",
        )
        assert "(T := T)" in named_signature
        assert named_signature.rstrip().endswith("hT hradiusScale j")
        _, net_signature, _, _ = resolved_declaration_parts(
            "Covering.FiniteSubGaussianChaining", "FiniteNet"
        )
        assert net_signature.rstrip().endswith(
            "covers : ∀ t : T, dist t (center (project t)) ≤ radius"
        )
        assert "namespace FiniteNet" not in net_signature
        _, cfg_signature, _, _ = resolved_declaration_parts(
            "UniformConvergence", "FiniteClassConfidenceSequence"
        )
        assert cfg_signature.rstrip().endswith("delta_pos : 0 < δ_real")
        assert "theorem anytime" not in cfg_signature
        synthetic = [
            "theorem named (f : Nat → Nat) : f (n := 1) = f (n := 1) := by",
            "  rfl",
        ]
        synthetic_decl = {
            "keyword": "theorem",
            "raw_name": "named",
            "qualified_name": "SelfTest.named",
            "line": 1,
        }
        signature, body, count = declaration_source_parts(
            synthetic, 0, len(synthetic), synthetic_decl
        )
        assert "(n := 1)" in signature and ":= by" not in signature
        assert body.strip().startswith("by") and count == 2
        block_comment = [
            "theorem commented /- outer /- nested -/ comment -/ : True := by",
            "  trivial",
        ]
        commented_decl = {
            "keyword": "theorem",
            "raw_name": "commented",
            "qualified_name": "SelfTest.commented",
            "line": 1,
        }
        commented_sig, commented_body, _ = declaration_source_parts(
            block_comment, 0, len(block_comment), commented_decl
        )
        assert commented_sig.endswith(": True")
        assert commented_body.strip().startswith("by")
        string_comment = [
            'def literal : String := "theorem fake : True := by trivial"',
        ]
        literal_decl = {
            "keyword": "def",
            "raw_name": "literal",
            "qualified_name": "SelfTest.literal",
            "line": 1,
        }
        literal_sig, literal_body, _ = declaration_source_parts(
            string_comment, 0, 1, literal_decl
        )
        assert literal_sig == "def literal : String"
        assert "theorem fake" not in literal_body
        let_statement = [
            "theorem letInType : let x := 1; x = 1 := by",
            "  rfl",
        ]
        let_decl = {
            "keyword": "theorem",
            "raw_name": "letInType",
            "qualified_name": "SelfTest.letInType",
            "line": 1,
        }
        let_sig, let_body, _ = declaration_source_parts(
            let_statement, 0, len(let_statement), let_decl
        )
        assert "let x := 1" in let_sig and let_body.strip().startswith("by")
        fqn_tags = concepts_for(
            "finiteExponentialTilt_changeOfMeasure", "Exact finite change of measure", ""
        )
        assert "exponential tilting" in fqn_tags and "KL divergence" not in fqn_tags
        test_pool = harvest()
        by_qualified = {record["qualified_name"]: record for record in test_pool}
        assert len(by_qualified) == len(test_pool)
        named_tail_mentions = by_qualified[
            "FormalSLT.Concentration.NamedTails.bernstein_tail"
        ]["dependency_edges"]["lexical_declaration_mentions"]
        assert named_tail_mentions == [{
            "id": "bernsteinmgf-bernstein-tail",
            "qualified_name": "FormalSLT.Probability.BernsteinMGF.bernstein_tail",
        }]
        assert not by_qualified[
            "FormalSLT.Probability.BernsteinMGF.bernstein_tail"
        ]["dependency_edges"]["lexical_declaration_mentions"]
        uniform_mentions = by_qualified[
            "FormalSLT.UniformConvergence."
            "finiteTimeClassEmpiricalAverageDeviationFromHoeffding_dyadicBudget"
        ]["dependency_edges"]["lexical_declaration_mentions"]
        assert {edge["qualified_name"] for edge in uniform_mentions} == {
            "FormalSLT.UniformConvergence.empiricalAverageLowerHoeffdingTail",
            "FormalSLT.UniformConvergence.empiricalAverageUpperHoeffdingTail",
            "FormalSLT.UniformConvergence."
            "finiteTimeClassTwoSidedUnionBoundFromOneSidedTails_dyadicBudget",
        }
        print("StatLean manifest self-test passed")
        return 0

    if a.limit < 0 or a.floor < 0:
        ap.error("require nonnegative floor and limit")

    print("harvesting from", MANIFEST.relative_to(ROOT))
    pool = harvest()
    n_def = sum(1 for r in pool if r["kind"] not in ("theorem", "lemma"))
    print(f"  resolved {len(pool)} declarations ({len(pool)-n_def} theorems/lemmas, {n_def} defs)")

    for r in pool:
        r["difficulty"] = difficulty(r)

    selected = copy.deepcopy(
        select_tasks(pool, a.floor, a.limit, a.refresh_selection)
    )
    print(f"  curated {len(selected)} tasks across "
          f"{len({c for r in selected for c in r['concept_tags']})} concept tags")

    if not a.no_fidelity:
        print("running statement_fidelity_check per selected task ...")
        flagged = 0
        for r in selected:
            r["fidelity"] = run_fidelity(r)
            if r["fidelity"]["flagged"]:
                flagged += 1
        incomplete = [r["id"] for r in selected if not r["fidelity"]["checked"]]
        if incomplete:
            raise RuntimeError(
                "fidelity did not audit exactly one declaration for: " + ", ".join(incomplete)
            )
        if flagged:
            raise RuntimeError(
                "unsigned statement-fidelity flags for: "
                + ", ".join(r["id"] for r in selected if r["fidelity"]["flagged"])
            )
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
        unknown = [r["id"] for r in selected if r["axiom_profile"] == "unknown"]
        if unknown or nonstd:
            raise RuntimeError(
                "invalid axiom profiles: "
                + ", ".join(unknown + [r["id"] for r in selected if r["axiom_profile"].startswith("NONSTANDARD")])
            )
        print(f"  axioms: {sum(1 for r in selected if r['axiom_profile'].startswith(('clean','axiom-free')))} clean, "
              f"{nonstd} nonstandard")
    else:
        for r in selected:
            r["axiom_profile"] = "not-audited"

    # final per-task field ordering for the selected manifest
    ordered = []
    for r in selected:
        ordered.append({
            "schema_version": r["schema_version"],
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
            "short_name": r["short_name"],
            "kind": r["kind"],
            "role": r["role"],
        })

    full_public = [
        {key: value for key, value in r.items() if not key.startswith("_")}
        for r in pool
    ]
    expected_full_keys = set(full_public[0]) if full_public else set()
    if any(set(record) != expected_full_keys for record in full_public):
        raise RuntimeError("full harvest schema is not uniform")
    full_by_id = {record["id"]: record for record in full_public}
    selected_only = {"axiom_profile", "fidelity"}
    for record in ordered:
        base = {key: value for key, value in record.items() if key not in selected_only}
        if base != full_by_id[record["id"]]:
            raise RuntimeError(f"selected/full base record mismatch: {record['id']}")

    if a.refresh_selection:
        selection = {
            "schema_version": SCHEMA_VERSION,
            "source_tree": source_tree_hash(),
            "task_ids": [record["id"] for record in selected],
        }
        OUT_SELECTION.write_text(
            json.dumps(selection, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )

    write_jsonl(OUT_SELECTED, ordered)
    write_jsonl(OUT_FULL, full_public)

    from collections import Counter
    tag_counts = Counter(t for r in ordered for t in r["concept_tags"])
    diff_counts = Counter(r["difficulty"] for r in ordered)
    stats = {
        "release": "StatLean-v0.1",
        "schema_version": SCHEMA_VERSION,
        "source_repo": json.loads(MANIFEST.read_text())["repository"]["name"],
        "source_tree": source_tree_hash(),
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
