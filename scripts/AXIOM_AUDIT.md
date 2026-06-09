# Axiom-audit gate (`axiom_audit.py`)

`scripts/axiom_audit.py` is the standing **"is it really axiom-clean / where does
any `sorryAx` come from"** check. Given a Lean import path (e.g.
`FormalSLT.PACBayesKL`) plus either explicit fully-qualified theorem names or
auto-discovered top-level `theorem`/`lemma`s from the module source, it runs
`#print axioms <name>` once through `lake env lean` and classifies each decl:
it **PASSes** when the axiom set is a subset of the trusted allowlist
(`propext`, `Classical.choice`, `Quot.sound`, and the `native_decide` /
`ofReduceBool` / `ofReduceNat` / `trustCompiler` compiler-reflection families, or
"does not depend on any axioms"), and **FAILs** — naming the offending theorem
and the unexpected axioms — when `sorryAx` (an unfinished `sorry`-backed proof)
or any other off-allowlist axiom appears; a missing/unknown constant also fails.
The process exits nonzero on any FAIL, so it drops straight into a pre-push /
CI gate. It is stdlib-only Python (no external deps) and re-joins Lean's
line-wrapped axiom lists so long axiom sets parse correctly.

```sh
# auto-discover every top-level theorem/lemma in a module and audit them all
python3 scripts/axiom_audit.py FormalSLT.PACBayesKL

# audit specific names (skip discovery)
python3 scripts/axiom_audit.py FormalSLT.PACBayesKL \
    FormalSLT.PACBayesKL.klDiv_nonneg FormalSLT.PACBayesKL.donsker_varadhan

# quiet mode (FAILs + summary only), custom lake / timeout
python3 scripts/axiom_audit.py FormalSLT.PACBayesMcAllester --quiet --timeout 600
```

Options: `--source FILE` (override the discovery source file), `--root DIR`
(project root, default = parent of `scripts/`), `--lake PATH`
(default `$LAKE`, else `~/.elan/bin/lake`, else `lake`), `--timeout SEC`
(default 600), `--quiet`. The module must be built (`lake build`) first so its
oleans are importable.
