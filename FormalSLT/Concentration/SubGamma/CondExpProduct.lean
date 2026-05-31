/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Conditional expectation of a product with a bounded `m`-measurable factor

**Pull-out property.** If `Z` is `m`-strongly-measurable and bounded,
and `Y` is integrable, then

    μ[Z · Y | m] =ᵐ[μ] Z · μ[Y | m].

This packages the specific form used by the extractor, including the
integrability bookkeeping for a bounded left factor.
-/

open MeasureTheory ProbabilityTheory

namespace FormalSLT.Concentration.SubGamma

/--
**Pull-out: bounded `m`-measurable factor.**

For `Z` strongly `m`-measurable and (almost surely) bounded, and `Y`
integrable, the conditional expectation pulls the bounded factor out.
-/
theorem condExp_mul_bounded_left
    {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {Z Y : Ω → ℝ} {C : ℝ}
    (hZ_meas : StronglyMeasurable[m] Z)
    (hZ_bdd : ∀ᵐ ω ∂μ, |Z ω| ≤ C)
    (hY_int : Integrable Y μ) :
    μ[fun ω => Z ω * Y ω | m] =ᵐ[μ] fun ω => Z ω * (μ[Y | m]) ω := by
  -- Strategy: apply mathlib's `condExp_mul_of_stronglyMeasurable_left`. The
  -- only nontrivial hypothesis to discharge is integrability of `Z · Y`,
  -- which follows from `Integrable.bdd_mul` (bounded × integrable). Letting
  -- Lean infer the underlying σ-algebra avoids `m` vs `m₀` resolution noise.
  have hZY_int : Integrable (fun ω => Z ω * Y ω) μ := by
    refine hY_int.bdd_mul (c := C) ((hZ_meas.mono hm).aestronglyMeasurable) ?_
    filter_upwards [hZ_bdd] with ω hω using by
      simpa [Real.norm_eq_abs] using hω
  exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left hZ_meas hZY_int hY_int

end FormalSLT.Concentration.SubGamma
