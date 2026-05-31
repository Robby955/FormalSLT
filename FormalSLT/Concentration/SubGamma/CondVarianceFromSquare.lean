/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Conditional variance from conditional `E[X²]`

When `X` is conditionally centered (`μ[X | m] = 0`), the conditional
variance reduces to the conditional second moment:

    Var(X | m) = μ[X² | m] − (μ[X | m])²  = μ[X² | m]  a.s.

This is the bridge between the bound `μ[X² | m] ≤ σ²` provided to the
extractor and the textbook sub-gamma bound which is usually stated in
terms of conditional variance.

This file records the centered identity in the form used by the
conditional sub-gamma extractor.
-/

open MeasureTheory ProbabilityTheory

namespace FormalSLT.Concentration.SubGamma

/--
**Centered conditional second moment dominates square of conditional
mean (trivially equal under centering).**

When `μ[X | m] =ᵐ[μ] 0`, the conditional second moment `μ[X² | m]`
*is* the conditional variance, and the sub-gamma bound's `σ²` hypothesis
bounds it directly.

Stated as the explicit identity so downstream proofs can rewrite freely.
-/
theorem condExp_sq_eq_condVar_of_centered
    {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω}
    {X : Ω → ℝ}
    (_hX_meas : Measurable X)
    (_hX_sq_int : Integrable (fun ω => X ω ^ 2) μ)
    (hcenter : μ[X | m] =ᵐ[μ] 0) :
    μ[fun ω => (X ω - (μ[X | m]) ω) ^ 2 | m] =ᵐ[μ] μ[fun ω => X ω ^ 2 | m] := by
  -- Strategy: avoid expanding the square. Since `μ[X | m] =ᵐ 0`, on a co-null
  -- set `X ω - μ[X | m] ω = X ω`, hence their squares agree pointwise a.s.
  -- `condExp_congr_ae` then lifts the integrand-level a.s. equality to the
  -- conditional-expectation level.
  refine condExp_congr_ae ?_
  filter_upwards [hcenter] with ω hω
  simp [hω]

end FormalSLT.Concentration.SubGamma
