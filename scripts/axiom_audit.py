#!/usr/bin/env python3
"""axiom_audit.py — reusable axiom-clean gate for FormalSLT (Lean 4 + mathlib).

Standing check: "is it really axiom-clean / where does any sorryAx come from?"

Given a Lean module (its import path, e.g. ``FormalSLT.PACBayesKL``) and either
an explicit list of theorem names or auto-discovered top-level theorems/lemmas,
this runs ``#print axioms <name>`` through ``lake env lean`` and classifies each:

  PASS  if its axiom set ⊆ the trusted allowlist
          {propext, Classical.choice, Quot.sound,
           native_decide / ofReduceBool / ofReduceNat compiler families}
        (a decl that "does not depend on any axioms" also PASSes).
  FAIL  if ``sorryAx`` appears (an incomplete / `sorry`-backed proof) OR any
        axiom outside the allowlist appears. The offending theorem and the
        unexpected axioms are printed.

Exit code is nonzero if ANY theorem FAILs (so this drops straight into a
pre-push / CI gate). Stdlib-only, no external deps.

Usage
-----
    python3 scripts/axiom_audit.py MODULE [name ...] [options]

    # auto-discover every top-level theorem/lemma in a module's source file
    python3 scripts/axiom_audit.py FormalSLT.PACBayesKL

    # audit specific fully-qualified names
    python3 scripts/axiom_audit.py FormalSLT.PACBayesKL \
        FormalSLT.PACBayesKL.klDiv_nonneg FormalSLT.PACBayesKL.donsker_varadhan

Options
-------
    --source FILE   Lean source file used for auto-discovery
                    (default: MODULE with dots -> '/', '.lean' appended,
                     resolved against the project root).
    --root DIR      Project root (default: parent dir of this script's dir).
    --lake PATH     lake binary (default: $LAKE or ~/.elan/bin/lake or 'lake').
    --timeout SEC   lean invocation timeout in seconds (default: 600).
    --quiet         only print FAILs and the final summary.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys

# Bare axiom names that are always trusted (the standard mathlib trio).
ALLOWED_EXACT = {"propext", "Classical.choice", "Quot.sound"}

# Substrings marking a trusted compiler-reflection axiom family. In recent Lean
# `native_decide` emits a per-declaration axiom like
# `<decl>._native.native_decide.ax_1_1`; older / `decide`-via-reduction paths
# emit `Lean.ofReduceBool` / `Lean.ofReduceNat` / `Lean.trustCompiler`.
ALLOWED_SUBSTRINGS = (
    "native_decide",
    "ofReduceBool",
    "ofReduceNat",
    "trustCompiler",
)

# The one axiom that is always a hard FAIL: an unfinished / `sorry`-backed proof.
SORRY_AXIOM = "sorryAx"


def axiom_is_allowed(axiom: str) -> bool:
    if axiom in ALLOWED_EXACT:
        return True
    return any(sub in axiom for sub in ALLOWED_SUBSTRINGS)


def default_lake() -> str:
    env = os.environ.get("LAKE")
    if env:
        return env
    elan = os.path.expanduser("~/.elan/bin/lake")
    if os.path.exists(elan):
        return elan
    return "lake"


_DECL_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+([A-Za-z_][\w']*)")
_NS_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][\w'.]*)")
_END_RE = re.compile(r"^\s*end\s+([A-Za-z_][\w'.]*)\s*$")


def discover_theorems(source_path: str) -> list[str]:
    """Parse a Lean source file for top-level theorem/lemma names, qualifying
    each with the enclosing ``namespace`` stack. Lightweight line scanner — good
    enough for FormalSLT's one-namespace-per-file convention; it does not parse
    comments/strings, which is acceptable for discovery (a stray match just
    yields an unknown-constant skip, not a false FAIL)."""
    names: list[str] = []
    ns_stack: list[str] = []
    with open(source_path, "r", encoding="utf-8") as fh:
        for line in fh:
            m_ns = _NS_RE.match(line)
            if m_ns:
                ns_stack.append(m_ns.group(1))
                continue
            m_end = _END_RE.match(line)
            if m_end and ns_stack and ns_stack[-1].endswith(m_end.group(1)):
                ns_stack.pop()
                continue
            m_decl = _DECL_RE.match(line)
            if m_decl:
                prefix = ".".join(ns_stack)
                short = m_decl.group(1)
                names.append(f"{prefix}.{short}" if prefix else short)
    return names


def run_print_axioms(
    lake: str, root: str, module: str, names: list[str], timeout: int
) -> str:
    """Build one Lean file that imports MODULE and `#print axioms` every name,
    then run it once through `lake env lean` (one process for the whole batch)."""
    lines = [f"import {module}", ""]
    for n in names:
        lines.append(f"#print axioms {n}")
    src = "\n".join(lines) + "\n"

    tmp = os.path.join(
        os.environ.get("TMPDIR", "/tmp"), f"axiom_audit_probe_{os.getpid()}.lean"
    )
    with open(tmp, "w", encoding="utf-8") as fh:
        fh.write(src)
    try:
        proc = subprocess.run(
            [lake, "env", "lean", tmp],
            cwd=root,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    finally:
        try:
            os.remove(tmp)
        except OSError:
            pass
    return proc.stdout + "\n" + proc.stderr


# A `#print axioms` report for one decl, possibly wrapped across several lines:
#   'NAME' depends on axioms: [a,
#    b,
#    c]
# or 'NAME' does not depend on any axioms
_REPORT_START = re.compile(r"^'([^']+)' (depends on axioms: \[|does not depend on any axioms)")


def parse_reports(output: str) -> dict[str, list[str]]:
    """Return {decl_name: [axioms...]} from `#print axioms` output, re-joining
    the pretty-printer's line-wrapped axiom lists."""
    # Collapse wrapped axiom lists: join lines until the closing ']' is seen.
    logical: list[str] = []
    buf: str | None = None
    for raw in output.splitlines():
        line = raw.rstrip()
        if buf is None:
            if _REPORT_START.match(line):
                if "depends on axioms: [" in line and "]" not in line:
                    buf = line  # start of a multi-line list
                else:
                    logical.append(line)
            # else: noise (errors, warnings, blank) — ignored here
        else:
            buf += " " + line.strip()
            if "]" in line:
                logical.append(buf)
                buf = None
    if buf is not None:
        logical.append(buf)

    reports: dict[str, list[str]] = {}
    for entry in logical:
        m = _REPORT_START.match(entry)
        if not m:
            continue
        name = m.group(1)
        if "does not depend on any axioms" in entry:
            reports[name] = []
            continue
        inside = entry[entry.index("[") + 1 : entry.rindex("]")]
        axioms = [a.strip() for a in inside.split(",") if a.strip()]
        reports[name] = axioms
    return reports


def collect_errors(output: str) -> list[str]:
    """Surface unknown-constant errors so a typo'd / mis-namespaced name is not
    silently treated as a pass."""
    errs = []
    for line in output.splitlines():
        if "unknownIdentifier" in line or "unknown constant" in line.lower():
            errs.append(line.strip())
    return errs


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description="Axiom-clean gate for Lean modules.")
    ap.add_argument("module", help="Lean import path, e.g. FormalSLT.PACBayesKL")
    ap.add_argument("names", nargs="*", help="Fully-qualified theorem names (optional)")
    ap.add_argument("--source", help="Lean source file for auto-discovery")
    ap.add_argument("--root", help="Project root")
    ap.add_argument("--lake", default=default_lake(), help="lake binary")
    ap.add_argument("--timeout", type=int, default=600, help="lean timeout (s)")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args(argv)

    script_dir = os.path.dirname(os.path.abspath(__file__))
    root = os.path.abspath(args.root) if args.root else os.path.dirname(script_dir)

    names = list(args.names)
    if not names:
        source = args.source or os.path.join(
            root, args.module.replace(".", os.sep) + ".lean"
        )
        if not os.path.exists(source):
            print(f"ERROR: source file not found for auto-discovery: {source}",
                  file=sys.stderr)
            return 2
        names = discover_theorems(source)
        if not names:
            print(f"ERROR: no theorems/lemmas discovered in {source}", file=sys.stderr)
            return 2
        if not args.quiet:
            print(f"Auto-discovered {len(names)} decl(s) in {os.path.relpath(source, root)}")

    if not args.quiet:
        print(f"Auditing module {args.module} via {args.lake} (root={root})\n")

    output = run_print_axioms(args.lake, root, args.module, names, args.timeout)
    reports = parse_reports(output)
    errors = collect_errors(output)

    passes: list[str] = []
    fails: list[tuple[str, list[str], bool]] = []  # (name, bad_axioms, has_sorry)
    missing: list[str] = []

    for name in names:
        if name not in reports:
            missing.append(name)
            continue
        axioms = reports[name]
        bad = [a for a in axioms if not axiom_is_allowed(a)]
        has_sorry = any(SORRY_AXIOM in a for a in axioms)
        if bad:
            fails.append((name, bad, has_sorry))
        else:
            passes.append(name)

    if not args.quiet:
        for name in passes:
            ax = reports[name]
            shown = "no axioms" if not ax else ", ".join(ax)
            print(f"  PASS  {name}  [{shown}]")

    for name, bad, has_sorry in fails:
        tag = "FAIL (sorryAx!)" if has_sorry else "FAIL"
        print(f"  {tag}  {name}  unexpected axioms: [{', '.join(bad)}]")

    for name in missing:
        print(f"  ERROR  {name}  not found in `#print axioms` output (unknown constant?)")

    if errors and not args.quiet:
        print("\nLean reported identifier errors:")
        for e in errors:
            print(f"    {e}")

    n_total = len(names)
    n_pass = len(passes)
    n_fail = len(fails)
    n_miss = len(missing)
    print(
        f"\nSummary: {n_pass}/{n_total} PASS, {n_fail} FAIL, {n_miss} missing"
        f" — module {args.module}"
    )

    # Nonzero exit on any FAIL or any missing/unknown decl.
    return 1 if (n_fail or n_miss) else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
