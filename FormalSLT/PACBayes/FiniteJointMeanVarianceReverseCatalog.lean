/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteJointMeanVarianceReversePACBayes

/-!
# Finite weighted tilt catalogs for joint reverse PAC-Bayes epochs

This module mixes a predeclared finite catalog of joint `(t, eta)` reverse
processes before applying Doob's maximal inequality.  One finite-horizon event
then controls every prefix, every finite posterior, and every catalog atom;
an atom may be chosen after the horizon path and posterior are observed.  The
selected boundary pays `log (1 / (delta * w c))` and one hypothesis KL term.

The catalog is finite and fixed before the data.  This is not countable or
all-real tilt optimization, and it remains an offline finite-horizon theorem.
-/

namespace FormalSLT.PACBayes.FiniteJointMeanVarianceReverse

open Finset BigOperators MeasureTheory
open scoped NNReal ENNReal
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse
open FormalSLT.PACBayes.FiniteJointMeanVarianceMGF

noncomputable section

variable {kappa ι Z : Type*} [MeasurableSpace Z]

/-- Weighted mixture over a finite predeclared joint-tilt catalog. -/
def reverseJointMeanVarianceEpochCatalogMixture
    [Fintype kappa] [Fintype Z] [Fintype ι]
    (w : kappa → ℝ) (prior : ι → ℝ)
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : ι → Z → ℝ)
    (t eta : kappa → ℝ) : ℕ → (Fin N → Z) → ℝ :=
  fun k x ↦ ∑ c : kappa, w c *
    reverseJointMeanVarianceEpochPriorMixture
      prior N hN m p ell (t c) (eta c) k x

omit [MeasurableSpace Z] in
theorem reverseJointMeanVarianceEpochCatalogMixture_nonneg
    [Fintype kappa] [Fintype Z] [Fintype ι]
    {w : kappa → ℝ} (hw : IsPMF w)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : ι → Z → ℝ) (t eta : kappa → ℝ) :
    0 ≤ reverseJointMeanVarianceEpochCatalogMixture
      w prior N hN m p ell t eta := by
  intro k x
  exact Finset.sum_nonneg fun c _ ↦ mul_nonneg (hw.nonneg c)
    (reverseJointMeanVarianceEpochPriorMixture_nonneg
      hprior N hN m p ell (t c) (eta c) k x)

private theorem submartingale_finset_sum
    {Omega alpha : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {filt : Filtration ℕ (inferInstance : MeasurableSpace Omega)}
    (s : Finset alpha) (M : alpha → ℕ → Omega → ℝ)
    (hM : ∀ i ∈ s, Submartingale (M i) filt mu) :
    Submartingale (fun k x ↦ ∑ i ∈ s, M i k x) filt mu := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa only [Finset.sum_empty] using
        (martingale_const filt mu (0 : ℝ)).submartingale
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hM a (Finset.mem_insert_self a s)).add
        (ih (fun i hi ↦ hM i (Finset.mem_insert_of_mem hi)))

/-- The finite catalog mixture is a nonnegative submartingale. -/
theorem reverseJointMeanVarianceEpochCatalogMixture_submartingale
    [Fintype kappa] [Fintype Z] [MeasurableSingletonClass Z] [Fintype ι]
    (p : Z → ℝ) (hp : IsPMF p)
    {w : kappa → ℝ} (hw : IsPMF w)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (ell : ι → Z → ℝ) (t eta : kappa → ℝ) :
    Submartingale
      (reverseJointMeanVarianceEpochCatalogMixture
        w prior N hN m p ell t eta)
      (reverseBesselFiltration (Z := Z) N)
      (Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) := by
  classical
  let muN := Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
  let filt := reverseBesselFiltration (Z := Z) N
  have hfixed : ∀ c : kappa,
      Submartingale
        (fun k x ↦ w c * reverseJointMeanVarianceEpochPriorMixture
          prior N hN m p ell (t c) (eta c) k x)
        filt muN := by
    intro c
    have hsub := reverseJointMeanVarianceEpochPriorMixture_submartingale
      p hp hprior N hN m ell (t c) (eta c)
    have hscaled := hsub.smul_nonneg (c := w c) (hw.nonneg c)
    change Submartingale
      (w c • reverseJointMeanVarianceEpochPriorMixture
        prior N hN m p ell (t c) (eta c)) filt muN
    exact hscaled
  have hsum := submartingale_finset_sum
    (Finset.univ : Finset kappa)
    (fun c k x ↦ w c * reverseJointMeanVarianceEpochPriorMixture
      prior N hN m p ell (t c) (eta c) k x)
    (fun c _ ↦ hfixed c)
  change Submartingale
    (fun k x ↦ ∑ c : kappa, w c *
      reverseJointMeanVarianceEpochPriorMixture
        prior N hN m p ell (t c) (eta c) k x) filt muN
  exact hsum

/-- The catalog-mixture endpoint expectation is at most one. -/
theorem reverseJointMeanVarianceEpochCatalogMixture_endpoint_integral_le_one
    [Fintype kappa] [Fintype Z] [DecidableEq Z]
    [MeasurableSingletonClass Z] [Fintype ι]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    {w : kappa → ℝ} (hw : IsPMF w)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    (t eta : kappa → ℝ)
    (ht : ∀ c, 0 ≤ t c) (heta : ∀ c, 0 ≤ eta c)
    (hkappa : ∀ c, 0 ≤ finiteJointMeanVarianceKappa m (eta c)) :
    (∫ x, reverseJointMeanVarianceEpochCatalogMixture
        w prior N hN m p ell t eta (N - m) x
      ∂Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) ≤ 1 := by
  have hcomponent (c : kappa) :
      (∫ x, reverseJointMeanVarianceEpochPriorMixture
          prior N hN m p ell (t c) (eta c) (N - m) x
        ∂Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) ≤ 1 :=
    reverseJointMeanVarianceEpochPriorMixture_endpoint_integral_le_one
      N m hN hm p hp hprior ell hell (ht c) (heta c) (hkappa c)
  unfold reverseJointMeanVarianceEpochCatalogMixture
  rw [integral_finsetSum Finset.univ]
  · calc
      (∑ c : kappa, ∫ x, w c *
          reverseJointMeanVarianceEpochPriorMixture
            prior N hN m p ell (t c) (eta c) (N - m) x
          ∂Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) =
        ∑ c : kappa, w c *
          (∫ x, reverseJointMeanVarianceEpochPriorMixture
            prior N hN m p ell (t c) (eta c) (N - m) x
            ∂Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) := by
          apply Finset.sum_congr rfl
          intro c _
          rw [integral_const_mul]
      _ ≤ ∑ c : kappa, w c * 1 := by
        exact Finset.sum_le_sum fun c _ ↦
          mul_le_mul_of_nonneg_left (hcomponent c) (hw.nonneg c)
      _ = 1 := by simpa using hw.sum_one
  · intro c _
    exact Integrable.of_finite.const_mul (w c)

/-- Exact catalog-wide joint-score failure event. -/
def reverseJointMeanVarianceEpochCatalogAnyPosteriorFailure
    [Fintype kappa] [Fintype Z] [Fintype ι]
    (w : kappa → ℝ) (prior : ι → ℝ)
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : ι → Z → ℝ)
    (t eta : kappa → ℝ) (delta : ℝ) : Set (Fin N → Z) :=
  {x | ∃ c : kappa, ∃ k : ℕ, k ≤ N - m ∧ ∃ rho : ι → ℝ,
    IsPMF rho ∧
      klDiv rho prior + Real.log (1 / (delta * w c)) ≤
        posteriorAverage rho (fun i ↦
          reverseJointMeanVarianceEpochScore
            N hN m p ell (t c) (eta c) i k x)}

/-- Catalog master crossing set. -/
def reverseJointMeanVarianceEpochCatalogBadPaths
    [Fintype kappa] [Fintype Z] [Fintype ι]
    (w : kappa → ℝ) (prior : ι → ℝ)
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : ι → Z → ℝ)
    (t eta : kappa → ℝ) (delta : ℝ) : Set (Fin N → Z) :=
  {x | delta⁻¹ ≤
    (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
      (fun k ↦ reverseJointMeanVarianceEpochCatalogMixture
        w prior N hN m p ell t eta k x)}

omit [MeasurableSpace Z] in
/-- Every catalog posterior-score violation forces the one master mixture to
cross.  The selected atom contributes `log (1 / w c)` but no second KL. -/
theorem reverseJointMeanVarianceEpochCatalogAnyPosteriorFailure_subset_badPaths
    [Fintype kappa] [Fintype Z] [Fintype ι] [Nonempty ι]
    (N m : ℕ) (hN : 2 ≤ N) (p : Z → ℝ)
    {w : kappa → ℝ} (hw : IsFullSupportPMF w)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ) (t eta : kappa → ℝ)
    {delta : ℝ} (hdelta : 0 < delta) :
    reverseJointMeanVarianceEpochCatalogAnyPosteriorFailure
        w prior N hN m p ell t eta delta ⊆
      reverseJointMeanVarianceEpochCatalogBadPaths
        w prior N hN m p ell t eta delta := by
  classical
  intro x hx
  rcases hx with ⟨c, k, hk, rho, hrho, hfail⟩
  let Mc := reverseJointMeanVarianceEpochPriorMixture
    prior N hN m p ell (t c) (eta c)
  let M := reverseJointMeanVarianceEpochCatalogMixture
    w prior N hN m p ell t eta
  have hdv :
      posteriorAverage rho (fun i ↦ reverseJointMeanVarianceEpochScore
          N hN m p ell (t c) (eta c) i k x) ≤
        klDiv rho prior + Real.log (Mc k x) := by
    simpa only [posteriorAverage, Mc,
      reverseJointMeanVarianceEpochPriorMixture,
      reverseJointMeanVarianceEpochExponentialProcess] using
      donsker_varadhan hrho hprior
        (fun i ↦ reverseJointMeanVarianceEpochScore
          N hN m p ell (t c) (eta c) i k x)
  have hlog_le : Real.log (1 / (delta * w c)) ≤ Real.log (Mc k x) := by
    linarith
  have hMc_pos : 0 < Mc k x := by
    unfold Mc reverseJointMeanVarianceEpochPriorMixture
    apply Finset.sum_pos
    · intro i _
      exact mul_pos (hprior.pos i) (Real.exp_pos _)
    · exact Finset.univ_nonempty
  have hshare_pos : 0 < (1 : ℝ) / (delta * w c) := by
    exact one_div_pos.mpr (mul_pos hdelta (hw.pos c))
  have hMc_threshold : (1 : ℝ) / (delta * w c) ≤ Mc k x :=
    (Real.log_le_log_iff hshare_pos hMc_pos).mp hlog_le
  have hscaled : (1 : ℝ) / delta ≤ w c * Mc k x := by
    calc
      (1 : ℝ) / delta = w c * (1 / (delta * w c)) := by
        field_simp [(hw.pos c).ne', hdelta.ne']
      _ ≤ w c * Mc k x :=
        mul_le_mul_of_nonneg_left hMc_threshold (hw.pos c).le
  have hcomponent : w c * Mc k x ≤ M k x := by
    unfold M reverseJointMeanVarianceEpochCatalogMixture
    exact Finset.single_le_sum
      (fun d _ ↦ mul_nonneg (hw.nonneg d)
        (reverseJointMeanVarianceEpochPriorMixture_nonneg
          hprior.toIsPMF N hN m p ell (t d) (eta d) k x))
      (Finset.mem_univ c)
  have hk_mem : k ∈ Finset.range (N - m + 1) := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
  change delta⁻¹ ≤
    (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
      (fun j ↦ M j x)
  simpa only [one_div] using
    hscaled.trans (hcomponent.trans (Finset.le_sup' (fun j ↦ M j x) hk_mem))

/-- Doob and the normalized catalog endpoint give a unit maximal bound. -/
theorem reverseJointMeanVarianceEpochCatalogMixture_maximal_le_one
    [Fintype kappa] [Fintype Z] [DecidableEq Z]
    [MeasurableSingletonClass Z] [Fintype ι]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    {w : kappa → ℝ} (hw : IsPMF w)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    (t eta : kappa → ℝ)
    (ht : ∀ c, 0 ≤ t c) (heta : ∀ c, 0 ≤ eta c)
    (hkappa : ∀ c, 0 ≤ finiteJointMeanVarianceKappa m (eta c))
    (epsilon : ℝ≥0) :
    epsilon * Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        {x | (epsilon : ℝ) ≤
          (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
            (fun k ↦ reverseJointMeanVarianceEpochCatalogMixture
              w prior N hN m p ell t eta k x)} ≤ 1 := by
  let muN := Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
  let M := reverseJointMeanVarianceEpochCatalogMixture
    w prior N hN m p ell t eta
  have hsub : Submartingale M (reverseBesselFiltration (Z := Z) N) muN :=
    reverseJointMeanVarianceEpochCatalogMixture_submartingale
      p hp hw hprior N hN m ell t eta
  have hnonneg : 0 ≤ M :=
    reverseJointMeanVarianceEpochCatalogMixture_nonneg
      hw hprior N hN m p ell t eta
  have hdoob := MeasureTheory.maximal_ineq hsub hnonneg
    (ε := epsilon) (N - m)
  have hsetIntegral :
      ∫ x in {x | (epsilon : ℝ) ≤
          (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
            (fun k ↦ M k x)}, M (N - m) x ∂muN ≤
        ∫ x, M (N - m) x ∂muN :=
    setIntegral_le_integral (hsub.integrable (N - m))
      (Filter.Eventually.of_forall (fun x ↦ hnonneg (N - m) x))
  have hend : (∫ x, M (N - m) x ∂muN) ≤ 1 :=
    reverseJointMeanVarianceEpochCatalogMixture_endpoint_integral_le_one
      N m hN hm p hp hw hprior ell hell t eta ht heta hkappa
  calc
    epsilon * muN {x | (epsilon : ℝ) ≤
        (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
          (fun k ↦ M k x)} ≤
      ENNReal.ofReal
        (∫ x in {x | (epsilon : ℝ) ≤
            (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
              (fun k ↦ M k x)}, M (N - m) x ∂muN) := hdoob
    _ ≤ ENNReal.ofReal (∫ x, M (N - m) x ∂muN) :=
      ENNReal.ofReal_le_ofReal hsetIntegral
    _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hend
    _ = 1 := by norm_num

/-- One catalog-wide event controls all atoms, prefixes, and finite
posteriors. -/
theorem reverseJointMeanVarianceEpochCatalogAnyPosteriorFailure_mass_le_delta
    [Fintype kappa] [Fintype Z] [DecidableEq Z]
    [MeasurableSingletonClass Z] [Fintype ι] [Nonempty ι]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    {w : kappa → ℝ} (hw : IsFullSupportPMF w)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    (t eta : kappa → ℝ)
    (ht : ∀ c, 0 ≤ t c) (heta : ∀ c, 0 ≤ eta c)
    (hkappa : ∀ c, 0 ≤ finiteJointMeanVarianceKappa m (eta c))
    {delta : ℝ} (hdelta : 0 < delta) :
    Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        (reverseJointMeanVarianceEpochCatalogAnyPosteriorFailure
          w prior N hN m p ell t eta delta) ≤ ENNReal.ofReal delta := by
  let epsilon : ℝ≥0 := ⟨delta⁻¹, inv_nonneg.mpr hdelta.le⟩
  let d : ℝ≥0∞ := ENNReal.ofReal delta
  have hscaled := reverseJointMeanVarianceEpochCatalogMixture_maximal_le_one
    N m hN hm p hp hw.toIsPMF hprior.toIsPMF ell hell t eta
      ht heta hkappa epsilon
  have hepsilonReal : (epsilon : ℝ) = delta⁻¹ := rfl
  have hepsilon : (epsilon : ℝ≥0∞) = d⁻¹ := by
    calc
      (epsilon : ℝ≥0∞) = ENNReal.ofReal delta⁻¹ := by
        symm
        exact ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr hdelta.le)
      _ = d⁻¹ := by rw [ENNReal.ofReal_inv_of_pos hdelta]
  have hscaled' : d⁻¹ *
      Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        (reverseJointMeanVarianceEpochCatalogBadPaths
          w prior N hN m p ell t eta delta) ≤ 1 := by
    rw [hepsilon] at hscaled
    rw [hepsilonReal] at hscaled
    exact hscaled
  have hd0 : d ≠ 0 := by
    simpa [d] using ENNReal.ofReal_ne_zero_iff.mpr hdelta
  have hdtop : d ≠ ∞ := ENNReal.ofReal_ne_top
  have hbad : Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
      (reverseJointMeanVarianceEpochCatalogBadPaths
        w prior N hN m p ell t eta delta) ≤ d := by
    calc
      Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
          (reverseJointMeanVarianceEpochCatalogBadPaths
            w prior N hN m p ell t eta delta) =
        d * (d⁻¹ * Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
          (reverseJointMeanVarianceEpochCatalogBadPaths
            w prior N hN m p ell t eta delta)) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hd0 hdtop, one_mul]
      _ ≤ d * 1 := mul_le_mul_right hscaled' d
      _ = d := mul_one d
  exact (measure_mono
    (reverseJointMeanVarianceEpochCatalogAnyPosteriorFailure_subset_badPaths
      N m hN p hw hprior ell t eta hdelta)).trans hbad

omit [MeasurableSpace Z] in
/-- Outside the catalog event, any one declared atom inherits the fixed-pair
prefix-uniform risk theorem with its explicit weight penalty. -/
theorem reverseJointMeanVarianceEpochCatalog_posteriorRisk_prefix_lt_of_not_mem
    [Fintype kappa] [Fintype Z] [Fintype ι]
    (N m s : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m)
    (hms : m ≤ s) (hsN : s ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (w : kappa → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (t eta : kappa → ℝ) {delta : ℝ}
    (x : Fin N → Z)
    (hx : x ∉ reverseJointMeanVarianceEpochCatalogAnyPosteriorFailure
      w prior N hN m p ell t eta delta)
    (c : kappa) (htc : 0 < t c)
    (hbalance :
      (m : ℝ) * (Real.exp (t c) - 1 - t c) ≤
        Real.exp (-t c) * finiteJointMeanVarianceKappa m (eta c))
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationRisk p ell) <
      posteriorAverage rho
          (fun i ↦ finiteEmpiricalRisk ell i (samplePrefix hsN x)) +
        (klDiv rho prior + Real.log (1 / (delta * w c))) /
          (t c * (m : ℝ)) +
        (eta c / t c) * posteriorAverage rho
          (fun i ↦ finiteEmpiricalVariance ell i (samplePrefix hsN x)) := by
  have hfixed : x ∉ reverseJointMeanVarianceEpochAnyPosteriorFailure
      prior N hN m p ell (t c) (eta c) (delta * w c) := by
    intro hfail
    rcases hfail with ⟨k, hk, rho', hrho', hviolation⟩
    exact hx ⟨c, k, hk, rho', hrho', hviolation⟩
  exact reverseJointMeanVarianceEpoch_posteriorRisk_prefix_lt_of_not_mem
    N m s hN hm hms hsN p hp prior ell htc hbalance x hfixed hrho

omit [MeasurableSpace Z] in
/-- A catalog atom may be selected pointwise from the observed horizon path
and posterior because the common event already controls every atom and every
posterior.  This selector adds no measurability or optional-stopping claim. -/
theorem reverseJointMeanVarianceEpochCatalog_posteriorRisk_prefix_lt_selected_of_not_mem
    [Fintype kappa] [Fintype Z] [Fintype ι]
    (N m s : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m)
    (hms : m ≤ s) (hsN : s ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (w : kappa → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (t eta : kappa → ℝ) {delta : ℝ}
    (select : (Fin N → Z) → (ι → ℝ) → kappa)
    (ht : ∀ c, 0 < t c)
    (hbalance : ∀ c,
      (m : ℝ) * (Real.exp (t c) - 1 - t c) ≤
        Real.exp (-t c) * finiteJointMeanVarianceKappa m (eta c))
    (x : Fin N → Z)
    (hx : x ∉ reverseJointMeanVarianceEpochCatalogAnyPosteriorFailure
      w prior N hN m p ell t eta delta)
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationRisk p ell) <
      posteriorAverage rho
          (fun i ↦ finiteEmpiricalRisk ell i (samplePrefix hsN x)) +
        (klDiv rho prior +
            Real.log (1 / (delta * w (select x rho)))) /
          (t (select x rho) * (m : ℝ)) +
        (eta (select x rho) / t (select x rho)) *
          posteriorAverage rho
            (fun i ↦ finiteEmpiricalVariance ell i (samplePrefix hsN x)) := by
  exact reverseJointMeanVarianceEpochCatalog_posteriorRisk_prefix_lt_of_not_mem
    N m s hN hm hms hsN p hp w prior ell t eta x hx (select x rho)
      (ht _) (hbalance _) hrho

end

end FormalSLT.PACBayes.FiniteJointMeanVarianceReverse
