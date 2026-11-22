/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Concentration.SharpMcDiarmid
import FormalSLT.Azuma.GenGapTail
import FormalSLT.Azuma.SharpMcDiarmid
import FormalSLT.Azuma.BoundedIncrementBound
import FormalSLT.Azuma.ExposureIncrementCondMGF

/-!
Axiom audit for the sharp (constant-2) McDiarmid bounded-differences theorems
and their generalization-gap specialization. Each prints the standard mathlib
classical axiom set `[propext, Classical.choice, Quot.sound]`, with no `sorry`,
no `admit`, and no project-specific axiom.
-/

#print axioms FormalSLT.Concentration.mcdiarmid_of_hasBoundedDifferences_sharp
#print axioms FormalSLT.Concentration.mcdiarmid_of_hasBoundedDifferences_sharp_lower
#print axioms FormalSLT.Concentration.mcdiarmid_twoSided_of_hasBoundedDifferences_sharp
#print axioms FormalSLT.Azuma.ExposureMartingale.genGap_tail_bound_sharp

open FormalSLT.Azuma.ExposureMartingale

#print axioms sharp_mcdiarmid_increment_subGaussian_mgf
#print axioms sharp_mcdiarmid_inequality_iid_const_width

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace FormalSLT.Concentration.Test

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

#check FormalSLT.Azuma.ExposureMartingale.abs_partialIntegral_succ_sub_succ_le_of_agree_prefix
#check FormalSLT.Azuma.ExposureMartingale.abs_partialIntegral_step_sub_step_le_of_agree_prefix
#check FormalSLT.Azuma.ExposureMartingale.exposureIncrement_condRange_width
#check FormalSLT.Azuma.ExposureMartingale.exposureIncrement_hasCondSubgaussianMGF_sharp
#check FormalSLT.Azuma.ExposureMartingale.hasBoundedDifferences_tail_sharp
#check FormalSLT.Azuma.ExposureMartingale.genGap_tail_bound_sharp_explicit
#check FormalSLT.Concentration.mcdiarmid_of_hasBoundedDifferences_sharp
#check FormalSLT.Concentration.mcdiarmid_of_hasBoundedDifferences_sharp_lower
#check FormalSLT.Concentration.mcdiarmid_twoSided_of_hasBoundedDifferences_sharp

/-- **Unit-range bounded summands (`c_i = 1`).**
The centered sum of independent `[0,1]`-valued variables obeys
`exp (-2 t^2 / n)`, with `n = s.card`. -/
example [IsProbabilityMeasure μ] {ι : Type*} {X : ι → Ω → ℝ}
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (hX : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    {s : Finset ι} {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ s, (X i ω - ∫ x, X i x ∂μ)}
      ≤ Real.exp (-2 * t ^ 2 / (s.card : ℝ)) := by
  have h := mcdiarmid_additive_independent (a := fun _ => 0) (b := fun _ => 1)
    hmeas hindep (fun _ => zero_le_one) hX (s := s) ht
  simpa using h

/-- **Sample-mean scaling (`c_i = 1 / n`).**
With each summand in `[0, 1/n]` the centered sum obeys the standard
`exp (-2 n t^2)` bound. -/
example [IsProbabilityMeasure μ] {ι : Type*} {X : ι → Ω → ℝ}
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    {s : Finset ι} (hs : s.Nonempty)
    (hX : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) (1 / (s.card : ℝ)))
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ s, (X i ω - ∫ x, X i x ∂μ)}
      ≤ Real.exp (-2 * (s.card : ℝ) * t ^ 2) := by
  have hne : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have h := mcdiarmid_additive_independent (a := fun _ => 0) (b := fun _ => 1 / (s.card : ℝ))
    hmeas hindep (fun _ => by positivity) hX (s := s) ht
  have hden : (∑ _i ∈ s, ((1 / (s.card : ℝ)) - 0) ^ 2) = 1 / (s.card : ℝ) := by
    simp only [sub_zero, Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [hden] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  field_simp

end FormalSLT.Concentration.Test
