# Comparison with adjacent formalizations

This table compares FormalSLT against the two closest peer libraries that
formalize sharp McDiarmid and adjacent concentration / generalization
machinery, plus a Mathlib4 baseline. The point is scope honesty, not a
ranking.

For full prior-art notes see [related-work.md](./related-work.md).

| Property | FormalSLT | lean-rademacher (Sonoda et al., 2025) | Karayel-Tan AFP (2023) | mathlib4 (upstream) |
|---|---|---|---|---|
| Proof assistant | Lean 4 + Mathlib4 | Lean 4 + Mathlib4 | Isabelle / HOL | Lean 4 |
| Sharp McDiarmid (constant 2) | yes, upper + lower + two-sided | yes, one-sided + negated form | yes, McDiarmid 1989 Lemma 1.2 form | no theorem named McDiarmid; sharp Hoeffding building blocks present |
| Sharp McDiarmid proof route | exposure martingale into Mathlib `measure_sum_ge_le_of_hasCondSubgaussianMGF` | direct Hoeffding-lemma argument, Hoeffding rebuilt in-tree | direct Hoeffding-lemma route (AFP `Hoeffdings_lemma_bochner` imports) | sub-Gaussian MGF API only (`Probability.Moments.SubGaussian`, R. Degenne 2025) |
| McDiarmid hypothesis | per-coordinate bounded differences, homogeneous iid product, `StandardBorelSpace Z` | per-coordinate bounded differences, finite independent coordinate maps | bounded differences over finite index, independent variables | not applicable |
| Tight PAC-Bayes (change of measure) | yes: Donsker-Varadhan, Catoni, McAllester grid peeling on bounded loss | no PAC-Bayes layer | no PAC-Bayes layer | no PAC-Bayes layer |
| Generalization spine | finite-class ERM through VC and PAC-Bayes confidence bounds | Rademacher-complexity uniform deviation pipeline | concentration toolkit, no learning spine | probability primitives only |
| Public axioms | `[propext, Classical.choice, Quot.sound]` (axiom transcript published in README) | source-level scan shows no `sorry` / `admit` / custom axiom across 11 `FoML/*.lean` files | standard Isabelle / HOL kernel | standard Lean / Mathlib axioms |
| Scope of library | finite-class SLT spine: ERM, Rademacher, VC, PAC-Bayes, stability, finite Dudley | Rademacher and Dudley infrastructure for generalization error | concentration inequalities collection (Bennett, Bernstein, McDiarmid, Efron-Stein, Paley-Zygmund) | foundational probability and measure theory, not learning-theory |

## What FormalSLT adds on top of these

- A tight change-of-measure PAC-Bayes track (Donsker-Varadhan into Catoni
  and into a finite-grid McAllester peeling wrapper). Neither lean-rademacher
  nor Karayel-Tan provides this. The one other Lean PAC-Bayes library that
  exists (`formal-learning-theory-kernel`) leaves the tight change-of-measure
  form as a TODO in source.
- A different proof architecture for the sharp McDiarmid bound: the exposure
  martingale feeds Mathlib's conditional sub-Gaussian engine
  (`Probability.Moments.SubGaussian.measure_sum_ge_le_of_hasCondSubgaussianMGF`).
  lean-rademacher takes the direct Hoeffding-lemma route and rebuilds
  Hoeffding's lemma in-tree.
- Upper, lower, and two-sided forms of the sharp bounded-differences theorem
  packaged in one module, plus the textbook
  `P(|f(S) - E[f]| >= eps) <= 2 exp(-2 eps^2 / sum c_k^2)` form.

## Honest caveats

- FormalSLT does not claim to be a first sharp McDiarmid in any proof
  assistant. Karayel-Tan published sharp McDiarmid in AFP in November 2023;
  lean-rademacher published the same bound in Lean 4 / Mathlib in
  [arXiv:2503.19605](https://arxiv.org/abs/2503.19605) (March-April 2025).
- The contribution is the verified mechanization and the integrated
  spine (concentration + symmetrization + VC + PAC-Bayes in one library),
  not new mathematics.
- The McDiarmid theorem in this library is for a homogeneous iid product
  measure. Heterogeneous-product extensions are a separate target; see
  [`assumptions-and-nonclaims.md`](./assumptions-and-nonclaims.md).

## Sources

- lean-rademacher: <https://github.com/auto-res/lean-rademacher>; paper [arXiv:2503.19605v2](https://arxiv.org/abs/2503.19605), Sonoda, Kasaura, Mizuno, Tsukamoto, Onda (RIKEN AIP, OMRON SINIC X, U. Tokyo, UCD).
- Karayel-Tan AFP: [Concentration_Inequalities](https://isa-afp.org/entries/Concentration_Inequalities.html), submitted November 2023.
- Mathlib4 sub-Gaussian: [`Mathlib/Probability/Moments/SubGaussian.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Probability/Moments/SubGaussian.lean), R. Degenne 2025.
- FormalSLT sharp McDiarmid: [`FormalSLT/Concentration/SharpMcDiarmid.lean`](../FormalSLT/Concentration/SharpMcDiarmid.lean).
