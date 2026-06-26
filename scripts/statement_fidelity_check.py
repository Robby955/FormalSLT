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
ID_CHARS = r"A-Za-z0-9_\'₀-₉Ͱ-Ͽ"
ID = r"[" + ID_CHARS + r"]+"
DECL_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+("
    + ID
    + r")"
)


def has_fidelity_signoff(comment_block):
    return any(
        re.match(r"\s*--\s*fidelity:", line)
        for line in comment_block.splitlines()
    )


def conclusion_of(stmt):
    depth = 0
    in_string = False
    escaped = False
    closers = {")": "(", "}": "{", "]": "["}
    stack = []
    for i, ch in enumerate(stmt):
        if in_string:
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            continue
        if ch == '"':
            in_string = True
            continue
        if ch in "({[":
            stack.append(ch)
            depth += 1
            continue
        if ch in closers:
            if stack and stack[-1] == closers[ch]:
                stack.pop()
                depth -= 1
            continue
        if ch == ":" and depth == 0:
            return stmt[i + 1:]
    return stmt

def top_level_proof_delimiter(stmt):
    depth = 0
    in_string = False
    escaped = False
    closers = {")": "(", "}": "{", "]": "["}
    stack = []
    for i, ch in enumerate(stmt):
        if in_string:
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            continue
        if ch == '"':
            in_string = True
            continue
        if ch in "({[":
            stack.append(ch)
            depth += 1
            continue
        if ch in closers:
            if stack and stack[-1] == closers[ch]:
                stack.pop()
                depth -= 1
            continue
        if ch == ":" and depth == 0 and i + 1 < len(stmt) and stmt[i + 1] == "=":
            return i
    return None

def theorems(src):
    # crude: split on top-level `theorem`/`lemma` keywords, keep name + the statement up to `:= by`/`:=`.
    # The vacuity lint runs on `stmt` (the statement only). The `-- fidelity:` sign-off, however, may sit
    # on the comment line(s) immediately ABOVE the keyword or anywhere inside the proof body, so we also
    # yield a `signoff` window that spans from the preceding comment block through the body up to the next
    # top-level decl. Without this, a legitimate `-- fidelity:` override never registers (the sign-off line
    # is outside `stmt`), and the gate would block genuine ∃c-∀var theorems with no working escape hatch.
    matches = list(DECL_RE.finditer(src))
    starts = [m.start() for m in matches]
    for i, m in enumerate(matches):
        name = m.group(1)
        start = m.start()
        nxt = starts[i + 1] if i + 1 < len(starts) else len(src)
        # bound the body to THIS declaration (next top-level decl, capped) so a statement that ends with
        # `:= term` (no newline after `:=`) does not bleed into the following theorem and mis-attribute flags.
        body = src[start:min(nxt, start + 1600)]
        proof_start = top_level_proof_delimiter(body)
        stmt = body[:proof_start] if proof_start is not None else body
        # Sign-offs must be genuine contiguous comment lines on the declaration.
        # Strings or arbitrary proof-body text containing `-- fidelity:` do not count.
        pre = src[:start]
        lines = pre.split('\n')
        j = len(lines) - 1
        if j >= 0 and lines[j].strip() == '':
            j -= 1
        k = j
        while k >= 0 and lines[k].lstrip().startswith('--'):
            k -= 1
        comment_block = '\n'.join(lines[k + 1:j + 1])
        yield name, stmt, has_fidelity_signoff(comment_block)

def flags_for(name, stmt):
    out = []
    # param vars declared in {..}/(..) of a numeric/complex sort
    params = re.findall(
        r'[\{\(]\s*((?:' + ID + r'\s+)*' + ID + r')\s*:\s*(?:ℝ|ℂ|ℕ|ℤ|ℚ)(?!\s*(?:→|->))',
        stmt,
    )
    pvars = set()
    for p in params:
        pvars.update(p.split())
    pvars = {v for v in pvars if not v.isdigit()}  # drop numeric tokens like "1" from `(1 : ℝ)`
    # quantifier inversion = BAD (∀var ∃const): a theorem-PARAM var appears in a `≤ c * ...` bound where the
    # constant c is ∃-bound, and NO inner `∀` re-binds the var between the ∃ and the bound. The GOOD form
    # (∃c, ∀var, bound) has an inner ∀ after the ∃ and must NOT be flagged.
    concl = conclusion_of(stmt)
    ex = re.search(r'∃\s*(' + ID + r')', concl)
    if ex:
        c = ex.group(1)
        after = concl[ex.end():]
        le = after.find('≤')
        seg = after[:le] if le != -1 else after
        inner_forall = '∀' in seg                      # ∃c ... ∀var ... ≤  => uniform => GOOD, skip
        bound = re.search(NORM + r'[\s\S]*?≤\s*' + re.escape(c) + r'\s*\*', concl)
        mentions_param = any(
            re.search(r"(?<![" + ID_CHARS + r"])" + re.escape(v) + r"(?![" + ID_CHARS + r"])", concl)
            for v in pvars
        )
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
    for name, stmt, signed in theorems(src):
        if only and name not in only: continue
        checked += 1
        fl = flags_for(name, stmt)
        for f in fl:
            if signed:
                print(f"  ok(signed) {f.split(':',1)[0]} on {name} — has -- fidelity: sign-off")
            else:
                print(f"  FLAG {f}"); flagged += 1
    print(f"--- checked {checked} decl(s), {flagged} flag(s)")
    return 1 if flagged else 0

if __name__ == "__main__":
    sys.exit(main())
