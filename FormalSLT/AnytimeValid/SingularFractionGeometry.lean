/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.AnytimeValid.ContinuumPredictableBettingMixture
import FormalSLT.AnytimeValid.ForwardBesselProcess
import FormalSLT.AnytimeValid.MixtureCS

/-!
# Singular fraction geometry for multiscale betting mixtures

This file isolates the scalar geometry behind a continuous multiscale prior.
The map

`u ↦ exp (-1 / u)` for `u > 0`, extended by zero for `u ≤ 0`,

turns a uniform parameter near zero into a distribution over arbitrarily
small betting fractions.  For `L = -log λ`, the parameter interval
`[1 / (L + 1), 1 / L]` maps into `[λ / exp 1, λ]` and has exact uniform
prior mass `1 / (L * (L + 1))`.

These are deterministic measure and order facts.  They do not by themselves
prove an e-process, a confidence sequence, or an iterated-logarithm boundary.
-/

open MeasureTheory ProbabilityTheory

namespace FormalSLT.AnytimeValid

noncomputable section

/-- A flat-at-zero reparameterization that reaches every fraction in `(0, exp (-1)]`
from a unit-interval parameter. -/
def singularFraction (u : Real) : Real :=
  if 0 < u then Real.exp (-1 / u) else 0

/-- Logarithmic scale associated with a positive target fraction. -/
def singularFractionLogScale (lam : Real) : Real :=
  -Real.log lam

/-- The unit-parameter window whose singular fractions are within one factor
of `exp 1` of `lam`. -/
def singularFractionWindow (lam : Real) : Set Real :=
  Set.Icc
    (1 / (singularFractionLogScale lam + 1))
    (1 / singularFractionLogScale lam)

/-- The logarithmic parameter window is measurable. -/
theorem measurableSet_singularFractionWindow (lam : Real) :
    MeasurableSet (singularFractionWindow lam) := by
  exact measurableSet_Icc

@[simp]
theorem singularFraction_of_pos {u : Real} (hu : 0 < u) :
    singularFraction u = Real.exp (-1 / u) := by
  simp [singularFraction, hu]

@[simp]
theorem singularFraction_of_nonpos {u : Real} (hu : u <= 0) :
    singularFraction u = 0 := by
  simp [singularFraction, not_lt.mpr hu]

/-- The singular reparameterization is Borel measurable, including at its
piecewise extension point. -/
theorem measurable_singularFraction : Measurable singularFraction := by
  have hquotient : Measurable (fun u : Real => (-1 : Real) / u) :=
    measurable_const.div measurable_id
  exact Measurable.ite measurableSet_Ioi
    (Real.measurable_exp.comp hquotient) measurable_const

/-- Every singular fraction is nonnegative. -/
theorem singularFraction_nonneg (u : Real) : 0 <= singularFraction u := by
  by_cases hu : 0 < u
  · rw [singularFraction_of_pos hu]
    exact (Real.exp_pos _).le
  · rw [singularFraction_of_nonpos (not_lt.mp hu)]

/-- The singular reparameterization is monotone on the whole real line. -/
theorem singularFraction_monotone : Monotone singularFraction := by
  intro u v huv
  by_cases hu : 0 < u
  · have hv : 0 < v := hu.trans_le huv
    rw [singularFraction_of_pos hu, singularFraction_of_pos hv]
    apply Real.exp_le_exp.mpr
    have hinv : 1 / v <= 1 / u :=
      one_div_le_one_div_of_le hu huv
    calc
      -1 / u = -(1 / u) := by ring
      _ <= -(1 / v) := neg_le_neg hinv
      _ = -1 / v := by ring
  · rw [singularFraction_of_nonpos (not_lt.mp hu)]
    exact singularFraction_nonneg v

/-- Fractions at most `exp (-1)` have logarithmic scale at least one. -/
theorem one_le_singularFractionLogScale
    {lam : Real} (hlam_pos : 0 < lam) (hlam : lam <= Real.exp (-1)) :
    1 <= singularFractionLogScale lam := by
  have hlog : Real.log lam <= -1 :=
    (Real.log_le_iff_le_exp hlam_pos).2 hlam
  unfold singularFractionLogScale
  linarith

/-- The singular-fraction window lies inside `[0,1]`. -/
theorem singularFractionWindow_subset_unit
    {lam : Real} (hlam_pos : 0 < lam) (hlam : lam <= Real.exp (-1)) :
    singularFractionWindow lam ⊆ Set.Icc (0 : Real) 1 := by
  let L := singularFractionLogScale lam
  have hL : 1 <= L := by
    simpa [L] using one_le_singularFractionLogScale hlam_pos hlam
  have hL_pos : 0 < L := zero_lt_one.trans_le hL
  have hL1_pos : 0 < L + 1 := by linarith
  have hupper : 1 / L <= (1 : Real) := by
    apply (div_le_iff₀ hL_pos).2
    simpa using hL
  intro u hu
  have hu' : 1 / (L + 1) <= u ∧ u <= 1 / L := by
    simpa [singularFractionWindow, L] using hu
  constructor
  · exact (one_div_pos.mpr hL1_pos).le.trans hu'.1
  · exact hu'.2.trans hupper

/-- Under the admissible fraction range, the logarithmic parameter window is
nonempty. -/
theorem singularFractionWindow_nonempty
    {lam : Real} (hlam_pos : 0 < lam) (hlam : lam <= Real.exp (-1)) :
    (singularFractionWindow lam).Nonempty := by
  let L := singularFractionLogScale lam
  have hL : 1 <= L := by
    simpa [L] using one_le_singularFractionLogScale hlam_pos hlam
  have hL_pos : 0 < L := zero_lt_one.trans_le hL
  have horder : 1 / (L + 1) <= 1 / L :=
    one_div_le_one_div_of_le hL_pos (by linarith)
  refine ⟨1 / L, ?_⟩
  change 1 / (L + 1) <= 1 / L ∧ 1 / L <= 1 / L
  exact ⟨horder, le_rfl⟩

/-- The logarithmic parameter window maps into a constant-factor neighborhood
of the requested fraction. -/
theorem singularFractionWindow_maps
    {lam u : Real} (hlam_pos : 0 < lam) (hlam : lam <= Real.exp (-1))
    (hu : u ∈ singularFractionWindow lam) :
    lam / Real.exp 1 <= singularFraction u ∧ singularFraction u <= lam := by
  let L := singularFractionLogScale lam
  have hL : 1 <= L := by
    simpa [L] using one_le_singularFractionLogScale hlam_pos hlam
  have hL_pos : 0 < L := zero_lt_one.trans_le hL
  have hL1_pos : 0 < L + 1 := by linarith
  have hu' : 1 / (L + 1) <= u ∧ u <= 1 / L := by
    simpa [singularFractionWindow, L] using hu
  have hu_pos : 0 < u := (one_div_pos.mpr hL1_pos).trans_le hu'.1
  have hscale_upper : 1 / u <= L + 1 := by
    apply (div_le_iff₀ hu_pos).2
    have h := (div_le_iff₀ hL1_pos).1 hu'.1
    nlinarith
  have hscale_lower : L <= 1 / u := by
    apply (le_div_iff₀ hu_pos).2
    have h := (le_div_iff₀ hL_pos).1 hu'.2
    nlinarith
  have hexp_scale : Real.exp (-L) = lam := by
    have harg : -L = Real.log lam := by
      simp [L, singularFractionLogScale]
    rw [harg, Real.exp_log hlam_pos]
  have hlower_identity : Real.exp (-(L + 1)) = lam / Real.exp 1 := by
    calc
      Real.exp (-(L + 1)) = Real.exp (-L - 1) := by
        congr 1
        ring
      _ = Real.exp (-L) / Real.exp 1 := Real.exp_sub (-L) 1
      _ = lam / Real.exp 1 := by rw [hexp_scale]
  rw [singularFraction_of_pos hu_pos]
  constructor
  · rw [← hlower_identity]
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hscale_upper
  · rw [← hexp_scale]
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hscale_lower

/-- The logarithmic window has exact mass `1 / (L * (L + 1))` under the
uniform probability measure on `[0,1]`. -/
theorem singularFractionWindow_uniformTiltPrior_real
    {lam : Real} (hlam_pos : 0 < lam) (hlam : lam <= Real.exp (-1)) :
    (uniformTiltPrior 0 1).real (singularFractionWindow lam) =
      1 / (singularFractionLogScale lam *
        (singularFractionLogScale lam + 1)) := by
  let L := singularFractionLogScale lam
  have hL : 1 <= L := by
    simpa [L] using one_le_singularFractionLogScale hlam_pos hlam
  have hL_pos : 0 < L := zero_lt_one.trans_le hL
  have hL1_pos : 0 < L + 1 := by linarith
  have hwindow_order : 1 / (L + 1) <= 1 / L :=
    one_div_le_one_div_of_le hL_pos (by linarith)
  have hsubset : singularFractionWindow lam ⊆ Set.Icc (0 : Real) 1 :=
    singularFractionWindow_subset_unit hlam_pos hlam
  have hinter : Set.Icc (0 : Real) 1 ∩ singularFractionWindow lam =
      singularFractionWindow lam := Set.inter_eq_right.mpr hsubset
  have hdiff : 1 / L - 1 / (L + 1) = 1 / (L * (L + 1)) := by
    field_simp [hL_pos.ne', hL1_pos.ne']
    ring
  unfold uniformTiltPrior Measure.real
  rw [ProbabilityTheory.cond_apply measurableSet_Icc, hinter,
    Real.volume_Icc]
  simp only [singularFractionWindow, Real.volume_Icc]
  simp only [sub_zero, ENNReal.ofReal_one, inv_one, one_mul]
  rw [show 1 / singularFractionLogScale lam = 1 / L by rfl,
    show 1 / (singularFractionLogScale lam + 1) = 1 / (L + 1) by rfl,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hwindow_order), hdiff]

/-- The logarithmic window has strictly positive uniform prior mass. -/
theorem singularFractionWindow_uniformTiltPrior_real_pos
    {lam : Real} (hlam_pos : 0 < lam) (hlam : lam <= Real.exp (-1)) :
    0 < (uniformTiltPrior 0 1).real (singularFractionWindow lam) := by
  rw [singularFractionWindow_uniformTiltPrior_real hlam_pos hlam]
  have hL : 1 <= singularFractionLogScale lam :=
    one_le_singularFractionLogScale hlam_pos hlam
  exact one_div_pos.mpr
    (mul_pos (zero_lt_one.trans_le hL) (by linarith))

end

end FormalSLT.AnytimeValid
