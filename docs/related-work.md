# Related Work

Existing Lean 4 and Isabelle formalizations of statistical learning theory
and concentration inequalities. FormalSLT is intended to be complementary
to these projects, not a replacement.

A side-by-side feature comparison is in
[`comparison-table.md`](./comparison-table.md).

## Adjacent Lean projects

| Project | Scope | Relation to FormalSLT |
|---|---|---|
| [YuanheZ/lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory) / [arXiv:2602.02285](https://arxiv.org/abs/2602.02285) | Empirical-process formalization: Gaussian Lipschitz concentration, Dudley's entropy integral for sub-Gaussian processes, localized Gaussian complexity, critical radii, and least-squares rates. | Strong adjacent prior art for localized SLT formalization. FormalSLT's finite Bernstein/localization route is a different bounded-excess-loss path. |
| [auto-res/lean-rademacher](https://github.com/auto-res/lean-rademacher) / [arXiv:2503.19605](https://arxiv.org/abs/2503.19605) | Rademacher-complexity generalization bounds, symmetrization, McDiarmid/Hoeffding-style concentration, and Dudley/Rademacher infrastructure. Sonoda, Kasaura, Mizuno, Tsukamoto, Onda (RIKEN AIP / OMRON SINIC X / U. Tokyo / UCD). | Prior Lean infrastructure for Rademacher and Dudley-style generalization, including a sharp McDiarmid in Lean 4 / Mathlib via the direct Hoeffding-lemma route. FormalSLT's sharp McDiarmid is a different proof architecture (exposure martingale into Mathlib's conditional sub-Gaussian engine), and FormalSLT adds a tight PAC-Bayes track that lean-rademacher does not. |
| [formal-learning-theory-kernel](https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel) | PAC/VC characterization, compression, PAC-Bayes, learning paradigms, measurability, and finite-support machinery. | Adjacent finite learning-theory formalization. Has a PAC-Bayes module, but the tight change-of-measure form is left as a TODO in source. FormalSLT supplies that tight version. |

## Adjacent Isabelle / HOL projects

| Project | Scope | Relation to FormalSLT |
|---|---|---|
| [Karayel-Tan AFP, Concentration_Inequalities](https://isa-afp.org/entries/Concentration_Inequalities.html) (November 2023) | Isabelle/HOL formalization of Bennett, Bernstein, Efron-Stein, Paley-Zygmund, and McDiarmid bounded-differences inequality. Sharp form via direct Hoeffding-lemma route. | Different proof assistant; covers the concentration toolkit but not a learning-theory spine. Blocks any "first sharp McDiarmid in a proof assistant" claim for FormalSLT, which this project does not make. |

## Mathlib upstream

Mathlib4's `Probability.Moments.SubGaussian` (R. Degenne, 2025) provides
Hoeffding's lemma, the conditional Azuma-Hoeffding engine, and sharp
sub-Gaussian sum inequalities, but does not expose a theorem named McDiarmid
or PAC-Bayes by name. FormalSLT's sharp McDiarmid imports and uses
`measure_sum_ge_le_of_hasCondSubgaussianMGF` from this module.

## Scope

FormalSLT makes no priority claim on sharp McDiarmid. The defensible
positioning is scope-by-scope:

```text
finite-class ERM, Rademacher symmetrization, VC capacity, finite Dudley
chaining, algorithmic stability, and a tight change-of-measure PAC-Bayes
layer, all in one axiom-clean Lean 4 / Mathlib library.
```

## Complementary, not competitive

- YuanheZ / lean-stat-learning-theory develops deeper Gaussian / Dudley
  and critical-radius machinery.
- lean-rademacher develops a sharp McDiarmid + Rademacher-generalization
  route via the direct Hoeffding-lemma argument.
- formal-learning-theory-kernel develops PAC / VC / PAC-Bayes and
  measurability infrastructure, with the tight PAC-Bayes form deferred.
- Karayel-Tan develops the broader Isabelle/HOL concentration toolkit.
- FormalSLT routes the exposure martingale into Mathlib's conditional
  sub-Gaussian engine, then pairs the resulting sharp McDiarmid with a
  tight change-of-measure PAC-Bayes track in one axiom-clean library.

Public wording avoids priority claims, broad novelty claims, and any
suggestion that the project solves localized Rademacher theory.
