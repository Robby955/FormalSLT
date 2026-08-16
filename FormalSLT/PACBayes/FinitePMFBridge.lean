/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayesKL
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Finite PAC-Bayes interoperability with mathlib probability measures

This module connects FormalSLT's finite real-valued probability mass functions,
posterior averages, and KL divergence to mathlib's `PMF`, `Measure`, and
`InformationTheory.klDiv` APIs.

The KL bridge requires the posterior support to be contained in the prior
support. This is exactly the finite absolute-continuity condition. Without it,
FormalSLT's totalized real-valued finite sum is not the same object as mathlib's
extended-real KL divergence, which is infinite when absolute continuity fails.
-/

namespace FormalSLT.PACBayesKL

open Finset BigOperators MeasureTheory
open scoped ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι]

/-! ### Real-valued PMFs as mathlib PMFs -/

/-- Convert a finite nonnegative real-valued PMF into mathlib's `PMF` type. -/
noncomputable def IsPMF.toPMF {ρ : ι → ℝ} (hρ : IsPMF ρ) : PMF ι :=
  PMF.ofFintype (fun i => ENNReal.ofReal (ρ i)) (by
    rw [← ENNReal.ofReal_one, ← hρ.sum_one]
    exact Eq.symm (ENNReal.ofReal_sum_of_nonneg
      (s := Finset.univ) (f := ρ) (fun i _hi => hρ.nonneg i)))

@[simp]
theorem IsPMF.toPMF_apply {ρ : ι → ℝ} (hρ : IsPMF ρ) (i : ι) :
    hρ.toPMF i = ENNReal.ofReal (ρ i) :=
  rfl

@[simp]
theorem IsPMF.toPMF_apply_toReal {ρ : ι → ℝ} (hρ : IsPMF ρ) (i : ι) :
    (hρ.toPMF i).toReal = ρ i := by
  simp [hρ.nonneg i]

/-! ### Posterior averages as Bochner integrals -/

/-- Integration against the mathlib PMF associated to a FormalSLT finite PMF
is the corresponding finite weighted sum. -/
theorem IsPMF.integral_toPMF_eq_sum
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {ρ : ι → ℝ} (hρ : IsPMF ρ) (g : ι → ℝ) :
    (∫ i, g i ∂hρ.toPMF.toMeasure) = ∑ i, ρ i * g i := by
  rw [PMF.integral_eq_sum]
  simp [ENNReal.toReal_ofReal, hρ.nonneg, smul_eq_mul]

/-- A FormalSLT finite posterior average is the Bochner integral against the
corresponding mathlib probability measure. -/
theorem integral_toPMF_eq_posteriorAverage
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {ρ : ι → ℝ} (hρ : IsPMF ρ) (g : ι → ℝ) :
    (∫ i, g i ∂hρ.toPMF.toMeasure) = posteriorAverage ρ g := by
  simpa [posteriorAverage] using hρ.integral_toPMF_eq_sum g

/-! ### Support-aware measure and KL bridges -/

/-- The pointwise density of the posterior PMF with respect to the prior PMF. -/
private noncomputable def pmfDensityRatio
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsPMF π) (i : ι) : ℝ≥0∞ :=
  hρ.toPMF i / hπ.toPMF i

/-- Under support inclusion, the posterior measure is the prior measure with
the finite PMF density ratio. -/
private theorem toPMF_toMeasure_eq_withDensity_of_support
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsPMF π)
    (hsupport : Function.support ρ ⊆ Function.support π) :
    hρ.toPMF.toMeasure =
      hπ.toPMF.toMeasure.withDensity (pmfDensityRatio hρ hπ) := by
  apply Measure.ext_of_singleton
  intro i
  rw [PMF.toMeasure_apply_singleton hρ.toPMF i (MeasurableSet.singleton i)]
  rw [withDensity_apply _ (MeasurableSet.singleton i)]
  rw [lintegral_singleton]
  rw [PMF.toMeasure_apply_singleton hπ.toPMF i (MeasurableSet.singleton i)]
  unfold pmfDensityRatio
  symm
  apply ENNReal.div_mul_cancel'
  · intro hπ_zero
    have hπi : π i = 0 := by
      apply le_antisymm
      · exact ENNReal.ofReal_eq_zero.mp (by simpa using hπ_zero)
      · exact hπ.nonneg i
    have hρi : ρ i = 0 := by
      by_contra hρi
      exact (hsupport hρi) hπi
    simp [hρi]
  · intro hπ_top
    exact (hπ.toPMF.apply_ne_top i hπ_top).elim

/-- Finite support inclusion induces absolute continuity between the associated
mathlib probability measures. -/
theorem toPMF_toMeasure_absolutelyContinuous_of_support
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsPMF π)
    (hsupport : Function.support ρ ⊆ Function.support π) :
    hρ.toPMF.toMeasure ≪ hπ.toPMF.toMeasure := by
  rw [toPMF_toMeasure_eq_withDensity_of_support hρ hπ hsupport]
  exact withDensity_absolutelyContinuous _ _

/-- A full-support prior dominates every finite posterior PMF. -/
theorem toPMF_toMeasure_absolutelyContinuous_of_fullSupport
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsFullSupportPMF π) :
    hρ.toPMF.toMeasure ≪ hπ.toIsPMF.toPMF.toMeasure := by
  apply toPMF_toMeasure_absolutelyContinuous_of_support hρ hπ.toIsPMF
  intro i _hi
  exact (hπ.pos i).ne'

/-- On the posterior measure, mathlib's log-likelihood ratio is the finite
pointwise log mass ratio. -/
private theorem llr_toPMF_ae_eq_log_ratio_of_support
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsPMF π)
    (hsupport : Function.support ρ ⊆ Function.support π) :
    llr hρ.toPMF.toMeasure hπ.toPMF.toMeasure =ᵐ[hρ.toPMF.toMeasure]
      fun i => Real.log (ρ i / π i) := by
  have hratio_measurable : Measurable (pmfDensityRatio hρ hπ) :=
    measurable_of_finite _
  have hrn_prior :
      hρ.toPMF.toMeasure.rnDeriv hπ.toPMF.toMeasure
          =ᵐ[hπ.toPMF.toMeasure] pmfDensityRatio hρ hπ := by
    rw [toPMF_toMeasure_eq_withDensity_of_support hρ hπ hsupport]
    exact Measure.rnDeriv_withDensity _ hratio_measurable
  have hac := toPMF_toMeasure_absolutelyContinuous_of_support hρ hπ hsupport
  filter_upwards [hac.ae_le hrn_prior] with i hi
  simp [llr, hi, pmfDensityRatio, ENNReal.toReal_ofReal, hρ.nonneg, hπ.nonneg]

/-- The integral of mathlib's log-likelihood ratio is FormalSLT's finite KL
sum whenever the posterior support is contained in the prior support. -/
private theorem integral_llr_toPMF_eq_klDiv_of_support
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsPMF π)
    (hsupport : Function.support ρ ⊆ Function.support π) :
    (∫ i, llr hρ.toPMF.toMeasure hπ.toPMF.toMeasure i ∂hρ.toPMF.toMeasure) =
      klDiv ρ π := by
  rw [integral_congr_ae (llr_toPMF_ae_eq_log_ratio_of_support hρ hπ hsupport)]
  rw [PMF.integral_eq_sum]
  simp [klDiv, ENNReal.toReal_ofReal, hρ.nonneg, smul_eq_mul]

/-- FormalSLT's finite KL sum is nonnegative under the minimal finite
absolute-continuity assumption. -/
theorem klDiv_nonneg_of_support
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsPMF π)
    (hsupport : Function.support ρ ⊆ Function.support π) :
    0 ≤ klDiv ρ π := by
  have hac := toPMF_toMeasure_absolutelyContinuous_of_support hρ hπ hsupport
  have hint :
      Integrable (llr hρ.toPMF.toMeasure hπ.toPMF.toMeasure) hρ.toPMF.toMeasure :=
    Integrable.of_finite
  have hnonneg := InformationTheory.integral_llr_add_sub_measure_univ_nonneg hac hint
  simpa [integral_llr_toPMF_eq_klDiv_of_support hρ hπ hsupport, measureReal_def] using hnonneg

/-- Under finite support inclusion, mathlib's extended-real KL divergence is
exactly `ENNReal.ofReal` of FormalSLT's finite KL sum. -/
theorem informationTheory_klDiv_toPMF_eq_of_support
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsPMF π)
    (hsupport : Function.support ρ ⊆ Function.support π) :
    InformationTheory.klDiv hρ.toPMF.toMeasure hπ.toPMF.toMeasure =
      ENNReal.ofReal (klDiv ρ π) := by
  have hac := toPMF_toMeasure_absolutelyContinuous_of_support hρ hπ hsupport
  have hint :
      Integrable (llr hρ.toPMF.toMeasure hπ.toPMF.toMeasure) hρ.toPMF.toMeasure :=
    Integrable.of_finite
  rw [InformationTheory.klDiv_of_ac_of_integrable hac hint]
  rw [integral_llr_toPMF_eq_klDiv_of_support hρ hπ hsupport]
  simp [measureReal_def]

/-- Real-valued form of the support-aware finite KL interoperability theorem. -/
theorem toReal_informationTheory_klDiv_toPMF_eq_of_support
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsPMF π)
    (hsupport : Function.support ρ ⊆ Function.support π) :
    (InformationTheory.klDiv hρ.toPMF.toMeasure hπ.toPMF.toMeasure).toReal =
      klDiv ρ π := by
  rw [informationTheory_klDiv_toPMF_eq_of_support hρ hπ hsupport]
  exact ENNReal.toReal_ofReal (klDiv_nonneg_of_support hρ hπ hsupport)

/-- Full-support specialization of the extended-real finite KL bridge used by
FormalSLT's finite PAC-Bayes theorems. -/
theorem informationTheory_klDiv_toPMF_eq_of_fullSupport
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsFullSupportPMF π) :
    InformationTheory.klDiv hρ.toPMF.toMeasure hπ.toIsPMF.toPMF.toMeasure =
      ENNReal.ofReal (klDiv ρ π) := by
  apply informationTheory_klDiv_toPMF_eq_of_support hρ hπ.toIsPMF
  intro i _hi
  exact (hπ.pos i).ne'

/-- Full-support specialization of the real-valued finite KL bridge used by
FormalSLT's finite PAC-Bayes theorems. -/
theorem toReal_informationTheory_klDiv_toPMF_eq_of_fullSupport
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsFullSupportPMF π) :
    (InformationTheory.klDiv hρ.toPMF.toMeasure
        hπ.toIsPMF.toPMF.toMeasure).toReal = klDiv ρ π := by
  apply toReal_informationTheory_klDiv_toPMF_eq_of_support hρ hπ.toIsPMF
  intro i _hi
  exact (hπ.pos i).ne'

end

end FormalSLT.PACBayesKL
