#!/usr/bin/env python3
"""Statement-fidelity / non-vacuity gate for Lean theorems (NON-NEGOTIABLE).

Vacuity is undecidable in general, so this does the two things that ARE mechanizable and forces the
rest to an explicit human/adversarial sign-off:

  1. LINT the common near-vacuity shapes (static, regex over theorem statements):
     - quantifier inversion: a theorem with a free variable param (e.g. {t : ℝ}) whose conclusion is
       `∃ c ..., ‖f t ...‖ ≤ c * (...)` — i.e. ∀t ∃c, near-vacuous (the constant is chosen AFTER the
       variable, so the bound is trivially satisfiable). The genuine form is ∃c, ∀t. (This is the
       INC-2026-06-22 lemma-3 catch.)
     - trivial conclusion: `: True`, `↔ True`, or a hypothesis that is literally `False`.
  2. REQUIRE a fidelity sign-off for every load-bearing theorem: a `-- fidelity:` line stating why the
     statement is non-vacuous (the witness / why the constant is uniform / the adversarial-falsify result),
     OR the theorem is flagged.

It does NOT replace the adversarial-falsify reasoning pass — it forces it. Run on a Lean file; exit 1 on flags.
Usage: statement_fidelity_check.py <file.lean> [theorem_name ...]
"""
import re, sys

NORM = r'(?:‖|\bnorm\b|abs |\|)'  # a magnitude on the LHS of a bound

def theorems(src):
    # crude: split on top-level `theorem`/`lemma` keywords, keep name + the statement up to `:= by`/`:=`.
    # The vacuity lint runs on `stmt` (the statement only). The `-- fidelity:` sign-off, however, may sit
    # on the comment line(s) immediately ABOVE the keyword or anywhere inside the proof body, so we also
    # yield a `signoff` window that spans from the preceding comment block through the body up to the next
    # top-level decl. Without this, a legitimate `-- fidelity:` override never registers (the sign-off line
    # is outside `stmt`), and the gate would block genuine ∃c-∀var theorems with no working escape hatch.
    starts = [m.start() for m in re.finditer(r'(?m)^\s*(?:noncomputable\s+)?(?:theorem|lemma)\s+[A-Za-z0-9_\']+', src)]
    for i, m in enumerate(re.finditer(r'(?m)^\s*(?:noncomputable\s+)?(?:theorem|lemma)\s+([A-Za-z0-9_\']+)', src)):
        name = m.group(1)
        start = m.start()
        nxt = starts[i + 1] if i + 1 < len(starts) else len(src)
        # bound the body to THIS declaration (next top-level decl, capped) so a statement that ends with
        # `:= term` (no newline after `:=`) does not bleed into the following theorem and mis-attribute flags.
        body = src[start:min(nxt, start + 1600)]
        stmt = re.split(r':=\s*by|:=\s*$|:=\n|:=\s', body)[0]
        # signoff window: preceding contiguous comment lines + the decl body up to the next top-level decl.
        pre = src[:start]
        lines = pre.split('\n')
        j = len(lines) - 1
        if j >= 0 and lines[j].strip() == '':
            j -= 1
        k = j
        while k >= 0 and lines[k].lstrip().startswith('--'):
            k -= 1
        comment_block = '\n'.join(lines[k + 1:j + 1])
        signoff = comment_block + '\n' + src[start:nxt]
        yield name, stmt, signoff

def flags_for(name, stmt):
    out = []
    # Lean identifiers: letters, digits, _, ', unicode subscripts ₀-₉ and Greek/primes
    ID = r"[A-Za-z0-9_\'₀-₉Ͱ-Ͽ]+"
    # param vars declared in {..}/(..) of a numeric/complex sort
    params = re.findall(r'[\{\(]\s*((?:' + ID + r'\s+)*' + ID + r')\s*:\s*(?:ℝ|ℂ|ℕ|ℤ|ℚ)', stmt)
    pvars = set()
    for p in params:
        pvars.update(p.split())
    pvars = {v for v in pvars if not v.isdigit()}  # drop numeric tokens like "1" from `(1 : ℝ)`
    # quantifier inversion = BAD (∀var ∃const): a theorem-PARAM var appears in a `≤ c * ...` bound where the
    # constant c is ∃-bound, and NO inner `∀` re-binds the var between the ∃ and the bound. The GOOD form
    # (∃c, ∀var, bound) has an inner ∀ after the ∃ and must NOT be flagged.
    concl = stmt.split(':', 1)[-1]
    ex = re.search(r'∃\s*(' + ID + r')', concl)
    if ex:
        c = ex.group(1)
        after = concl[ex.end():]
        le = after.find('≤')
        seg = after[:le] if le != -1 else after
        inner_forall = '∀' in seg                      # ∃c ... ∀var ... ≤  => uniform => GOOD, skip
        bound = re.search(NORM + r'[\s\S]*?≤\s*' + re.escape(c) + r'\s*\*', concl)
        mentions_param = any(re.search(re.escape(v), concl) for v in pvars)
        if bound and mentions_param and pvars and not inner_forall:
            out.append(f"QUANTIFIER-INVERSION: '{name}' is ∀{{{','.join(sorted(pvars))}}} ∃{c} (constant after "
                       f"variable) — near-vacuous; the genuine form is ∃{c} ∀var. Hoist the ∃ outside the params, "
                       f"or add a `-- fidelity:` line proving the constant is uniform.")
    if re.search(r':\s*True\b', stmt) or re.search(r'↔\s*True\b', stmt):
        out.append(f"TRIVIAL-CONCLUSION: '{name}' concludes `True` — vacuous.")
    if re.search(r'\(\s*[A-Za-z0-9_\' ]+\s*:\s*False\s*\)', stmt):
        out.append(f"FALSE-HYPOTHESIS: '{name}' has a `: False` hypothesis — vacuously true.")
    return out

def main():
    if len(sys.argv) < 2:
        print("usage: statement_fidelity_check.py <file.lean> [theorem ...]"); return 2
    src = open(sys.argv[1], encoding='utf-8', errors='ignore').read()
    only = set(sys.argv[2:])
    flagged = 0; checked = 0
    for name, stmt, signoff in theorems(src):
        if only and name not in only: continue
        checked += 1
        fl = flags_for(name, stmt)
        signed = bool(re.search(r'--\s*fidelity:', signoff))
        for f in fl:
            if signed:
                print(f"  ok(signed) {f.split(':',1)[0]} on {name} — has -- fidelity: sign-off")
            else:
                print(f"  FLAG {f}"); flagged += 1
    print(f"--- checked {checked} decl(s), {flagged} flag(s)")
    return 1 if flagged else 0

if __name__ == "__main__":
    sys.exit(main())
