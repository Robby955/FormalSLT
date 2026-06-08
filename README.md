# Formal Statistical Learning Theory in Lean 4

[![Lean 4](https://img.shields.io/badge/Lean-4.30.0--rc2-blue.svg)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-25b7ac7-blueviolet.svg)](https://github.com/leanprover-community/mathlib4)
[![Zero sorry](https://img.shields.io/badge/sorry-0-brightgreen.svg)](#reproducing-the-build-and-axiom-audit)
[![Axioms](https://img.shields.io/badge/axioms-propext%2C%20Classical.choice%2C%20Quot.sound-brightgreen.svg)](#reproducing-the-build-and-axiom-audit)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](./LICENSE)

**A machine-checked statistical learning theory library in Lean 4 / mathlib: one axiom-clean spine from empirical risk minimization through VC, Rademacher, and a tight change-of-measure PAC-Bayes layer. Among the Lean SLT libraries we surveyed, FormalSLT is the only one with a tight (change-of-measure) PAC-Bayes track — a machine-checked Donsker–Varadhan variational inequality wired into McAllester grid-peeling and Catoni posterior-risk bounds.**

Every public theorem is checked with no `sorry`, no `admit`, no custom axiom; the full dependency chain closes against only the standard mathlib axioms `[propext, Classical.choice, Quot.sound]`.

## What is the contribution

The distinctive, verified result is the **tight change-of-measure PAC-Bayes track**:

- `PACBayesKL.donsker_varadhan` — the Donsker–Varadhan variational inequality (real proof, not a stub).
- `PACBayesMcAllester.pacbayes_changeOfMeasure` and `PACBayesBoundedLoss.finiteMcAllesterGridPeeling_badEventMass_le_delta` — McAllester-style bounds with grid λ-peeling.
- `PACBayesBoundedLoss.finiteCatoni_badEventMass_le_delta` — Catoni posterior-risk bound.

Prior art for context (so the claim is precise): among Lean SLT libraries we surveyed, [lean-rademacher](https://github.com/auto-res/lean-rademacher) and [YuanheZ/lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory) have no PAC-Bayes; the one with any PAC-Bayes ([formal-learning-theory-kernel](https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel)) has only the loose union-bound form and explicitly defers the tight change-of-measure version (`PACBayes.lean`: "TODO: Prove the tight version via change of measure (Catoni 2007)"). FormalSLT supplies that tight version, inside an end-to-end SLT development.

## What's inside

### 1. The generalization pipeline: ERM → Rademacher → VC → PAC-Bayes

| Stage | Representative theorem |
|---|---|
| ERM excess risk | `ERM.erm_excessRisk_le_two_uniformDeviation` |
| Symmetrization | `Rademacher.Symmetrization.expected_genGap_le_two_expected_empiricalRademacherComplexity` |
| Massart finite-class bound | `Rademacher.Massart.massart_finite_class` |
| High-probability Rademacher | `Rademacher.HighProbability.genGap_highProb_rademacher` |
| Sauer–Shelah | `VC.SauerShelah.sauerShelah_polynomial_bound` |
| VC ERM tail + sample complexity | `VC.SampleComplexity.vc_erm_excessRisk_tail`, `vc_erm_sample_complexity` |
| Tight PAC-Bayes | `PACBayesKL.pacbayes_changeOfMeasure`, `PACBayesBoundedLoss.finiteCatoni_badEventMass_le_delta` |

### 2. Concentration backbone (`Azuma.*`, `Concentration.SharpMcDiarmid`)

A sharp (constant-2) McDiarmid bounded-differences inequality is included as a verified component and wired to the generalization gap:

| Theorem | What it gives |
|---|---|
| `Azuma.HasBoundedDifferences` | the textbook per-coordinate predicate `∀ S k z', \|f S − f (update S k z')\| ≤ c k` |
| `Concentration.mcdiarmid_of_hasBoundedDifferences_sharp` | general product-measure upper tail `≤ exp(-2 ε² / Σ c_k²)` |
| `Concentration.mcdiarmid_twoSided_of_hasBoundedDifferences_sharp` | two-sided `≤ 2·exp(-2 ε² / Σ c_k²)` |
| `Azuma.ExposureMartingale.genGap_tail_bound_sharp` | the sharp inequality applied to the SLT generalization gap |

The sharp constant is earned via the exposure-martingale increment's conditional fiber range (proxy `(c_k/2)²`, vs the Azuma `c_k²` route, which co-exists in the same files). **McDiarmid is classical and already formalized elsewhere in Lean and Isabelle — this is a verified re-formalization, not a first; see [Scope and boundaries](#scope-and-honest-boundaries).**

### 3. The finite Dudley chaining layer (`Covering.*`)

Discrete/finite chaining: two-scale peeling (`Covering.DudleyChaining`), the total-bounded discrete entropy sum (`Covering.TotalBoundedDudley`), finite two-point and unit-interval instances (`Covering.TwoPointDudley`, `Covering.UnitIntervalDudley`), and the finite sub-Gaussian chaining foundation (`Covering.FiniteSubGaussianChaining`). This layer is **finite/discrete throughout**; the continuous Dudley entropy integral is not part of this library.

### Module map

| Layer | Modules |
|---|---|
| Core | `Risk`, `ERM`, `UniformConvergence`, `GhostSample` |
| Probability | `Probability.{Concentration, FiniteUnionBound, FiniteExpectation, BernsteinMGF}` |
| Rademacher | `Rademacher.{FiniteSample, Symmetrization, Massart, HighProbability, UniformDeviation, ERMGeneralization, Contraction, LinearPredictor, …}` |
| Concentration / McDiarmid | `Azuma.{HasBoundedDifferences, ExposureMartingale, ExposureIncrementCondMGF, GenGapTail}`, `Concentration.SharpMcDiarmid`, `Concentration.SubGamma.*` |
| VC | `VC.{Dimension, SauerShelah, Rademacher, SampleComplexity, BinaryVCBridge}` |
| Covering (finite) | `Covering.{Rademacher, DudleyChaining, FiniteDiscreteDudley, FiniteSubGaussianChaining, TotalBoundedDudley, TwoPointDudley, UnitIntervalDudley}` |
| Stability / PAC-Bayes | `AlgorithmicStability`, `Stability.BousquetElisseeff`, `PACBayesKL`, `PACBayesMcAllester`, `PACBayesFiniteProductMGF`, `PACBayesBoundedLoss` |

The library is **60 modules / ≈31,500 lines** of Lean (mathlib excluded).

## Reproducing the build and axiom audit

Install [elan](https://github.com/leanprover/elan); it reads [`lean-toolchain`](./lean-toolchain) and fetches the pinned Lean automatically.

```bash
git clone https://github.com/Robby955/FormalSLT.git
cd FormalSLT
lake exe cache get      # download the pinned Mathlib oleans
lake build FormalSLT    # builds the whole library (2951 jobs)
```

### Axiom transcript (captured on `origin/main`)

```
'FormalSLT.PACBayesBoundedLoss.finiteCatoni_badEventMass_le_delta'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSLT.PACBayesBoundedLoss.posteriorRisk_bound_of_priorDeviationMGF_le'         depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSLT.Concentration.mcdiarmid_of_hasBoundedDifferences_sharp'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSLT.Concentration.mcdiarmid_twoSided_of_hasBoundedDifferences_sharp'         depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSLT.Rademacher.Massart.massart_finite_class'                                 depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSLT.VC.SampleComplexity.vc_erm_sample_complexity'                            depends on axioms: [propext, Classical.choice, Quot.sound]
```

`propext`, `Classical.choice`, and `Quot.sound` are the three axioms underlying ordinary classical mathematics in mathlib; there is no project-specific axiom and no `sorry`.

## Scope and honest boundaries

The contribution is the **verified formalization and integration**, not new mathematics.

- **The tight PAC-Bayes track is the distinctive piece.** Scoped precisely: among the Lean SLT libraries surveyed, FormalSLT is the only one with the tight change-of-measure form; the one other Lean PAC-Bayes library leaves it as a TODO. This is a survey-scoped claim, not an absolute "first."
- **McDiarmid is not a first in any proof assistant.** Karayel–Tan (AFP 2023, Isabelle/HOL) and [lean-rademacher](https://github.com/auto-res/lean-rademacher) (Sonoda et al., [arXiv:2503.19605](https://arxiv.org/abs/2503.19605)) both have a McDiarmid; FormalSLT's is a verified re-formalization wired into the spine, not a priority claim.
- **The general sharp McDiarmid theorem is the one-sided upper tail**; lower-tail and two-sided are separate proven siblings.
- **`StandardBorelSpace Z` is required** (from mathlib's `condExpKernel`); covers ℝ, Bool, and all Polish spaces.
- **Homogeneous iid product** for the general theorem; independent-non-identical coordinates are a separate sibling.
- **Finite/discrete-first throughout** — finite hypothesis classes, finite grids, discrete Dudley. No continuous Dudley integral, no continuous-posterior PAC-Bayes (those are in-progress work, not in this library).

## How to cite

```bibtex
@software{formal_slt,
  title  = {FormalSLT: Formal Statistical Learning Theory in Lean 4},
  author = {Sneiderman, Robert},
  year   = {2026},
  url    = {https://github.com/Robby955/FormalSLT}
}
```

## License

Released under the [MIT License](./LICENSE).
