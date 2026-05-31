/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Integrability of `exp(λ X)` for bounded `X`

Supporting lemma for `Extractor.lean`. The proof uses `Integrable.mono'`
against the constant bound `exp(|λ| b)`.
-/

open MeasureTheory ProbabilityTheory

namespace FormalSLT.Concentration.SubGamma

/--
**Exponential of a bounded random variable is integrable.**

If `|X| ≤ b` almost surely on a probability space, then `exp(λ X)` is
integrable for every `λ`.
-/
theorem integrable_exp_mul_of_bounded
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {b lam : ℝ}
    (hX_meas : Measurable X)
    (h_bounded : ∀ᵐ ω ∂μ, |X ω| ≤ b) :
    Integrable (fun ω => Real.exp (lam * X ω)) μ := by
  -- Strategy: dominate `exp(λ X)` by the constant `exp(|λ| · b)`.
  -- `|λ X| ≤ |λ| · b` on the a.s. set `|X| ≤ b`, and `exp` is monotone,
  -- so `exp(λ X) ≤ exp(|λ| · b)`. Then `Integrable.mono'` against the
  -- constant integrable bound finishes.
  refine MeasureTheory.Integrable.mono'
    (MeasureTheory.integrable_const (Real.exp (|lam| * b))) ?_ ?_
  · exact Real.continuous_exp.comp_aestronglyMeasurable
      (hX_meas.aestronglyMeasurable.const_mul _)
  · filter_upwards [h_bounded] with ω hω
    simpa using Real.exp_le_exp.2
      (by cases abs_cases lam <;> nlinarith [abs_le.mp hω])

end FormalSLT.Concentration.SubGamma
