#!/usr/bin/env python3
"""seal_statements.py - statement-anchor gate (adversarial-verification Defense 2).

check_axioms.sh proves the proofs are axiom-clean; this proves the SIGNATURES still
say what the paper claims. It guards the failure class that has actually bitten us
(vacuous bound / weakened hypothesis / inert component / junk semantics): a valid
proof of a quietly-changed statement. The whole "non-vacuous flagship" story is
downstream of these signatures being faithful, so this is the highest-leverage gate.

Governed theorems are listed in anchors/manifest.txt (fully-qualified, one per line).

  --seal   (re)generate every signature snapshot into anchors/<thm>.sig
           run once at baseline, and only on an INTENTIONAL signature change (review the diff).
  --check  regenerate + exact-diff against the snapshots; nonzero on ANY drift, a missing
           snapshot, or a theorem lean can't find. Fail-closed. Wire this into CI.

NOT seal_prediction.py: that seals submission OUTCOMES for calibration. This seals
theorem SIGNATURES for soundness. Different concern; do not merge them.
"""
from __future__ import annotations
import argparse, os, re, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent          # FormalSLT repo root
ANCHORS = ROOT / "anchors"
MANIFEST = ANCHORS / "manifest.txt"
LAKE = os.path.expanduser("~/.elan/bin/lake")


def _governed():
    if not MANIFEST.exists():
        return []
    out = []
    for line in MANIFEST.read_text().splitlines():
        line = line.split("#", 1)[0].strip()
        if line:
            out.append(line)
    return out


def _signatures(names):
    """{name: normalized signature} via one `lake env lean` scratch of `#check @name` lines."""
    body = "import FormalSLT\n" + "".join(f"#check @{n}\n" for n in names)
    fd, scratch = tempfile.mkstemp(suffix=".lean", dir=str(ROOT))
    os.write(fd, body.encode()); os.close(fd)
    try:
        r = subprocess.run([LAKE, "env", "lean", scratch], cwd=str(ROOT),
                           capture_output=True, text=True, timeout=1800)
    finally:
        os.unlink(scratch)
    sigs, cur = {}, None
    nameset = set(names)
    for raw in r.stdout.splitlines():
        m = re.match(r'^@(\S+)\s*:\s*(.*)$', raw)
        if m and m.group(1) in nameset:
            cur = m.group(1); sigs[cur] = m.group(2)
        elif cur is not None:
            sigs[cur] += " " + raw.strip()
    for n in list(sigs):
        sigs[n] = re.sub(r'\s+', ' ', sigs[n]).strip()
    return sigs, r


def main():
    ap = argparse.ArgumentParser()
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--seal", action="store_true", help="capture/refresh signature snapshots")
    g.add_argument("--check", action="store_true", help="CI gate: diff signatures vs snapshots")
    a = ap.parse_args()

    names = _governed()
    if not names:
        print("FAIL (fail-closed): anchors/manifest.txt missing or empty"); return 1
    ANCHORS.mkdir(exist_ok=True)
    sigs, r = _signatures(names)

    not_found = [n for n in names if n not in sigs]
    if not_found:
        print(f"FAIL: lean emitted no signature for {not_found} (renamed/removed, or build error)")
        if r.stderr.strip():
            print(r.stderr.strip()[:600])
        return 1

    if a.seal:
        for n in names:
            (ANCHORS / (n.replace('.', '_') + ".sig")).write_text(sigs[n] + "\n")
        print(f"sealed {len(names)} statement anchors -> {ANCHORS.relative_to(ROOT)}/")
        return 0

    drift, missing = [], []
    for n in names:
        snap = ANCHORS / (n.replace('.', '_') + ".sig")
        if not snap.exists():
            missing.append(n); continue
        if sigs[n] != snap.read_text().strip():
            drift.append((n, snap.read_text().strip(), sigs[n]))
    if missing:
        print(f"FAIL (fail-closed): no sealed anchor for {missing} - run --seal"); return 1
    if drift:
        for n, want, got in drift:
            print(f"FAIL statement drift: {n}\n  sealed: {want}\n  now:    {got}")
        return 1
    print(f"statement-anchor gate PASS: {len(names)} signatures match their seals")
    return 0


if __name__ == "__main__":
    sys.exit(main())
