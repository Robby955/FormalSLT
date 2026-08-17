/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteJointMeanVarianceReverse
import Mathlib.Probability.Martingale.OptionalStopping

/-!
# One-event PAC-Bayes control for a joint reverse mean--Bessel epoch

This module mixes the derived joint reverse mean/Bessel exponential processes
over a fixed finite hypothesis prior before applying Doob's maximal
inequality.  One finite-horizon event controls every prefix size in the epoch
and every posterior selected after the horizon sample, with one
`KL(posterior || prior)` term.

The mean and Bessel conditional-expectation identities, joint submartingale,
endpoint product-law bridge, and fixed-sample joint MGF are all checked
upstream.  This is an offline fixed-horizon, fixed-`(t, eta)` epoch theorem;
it is not yet a stitched infinite-time confidence sequence or a selectable
tilt catalog.
-/

namespace FormalSLT.PACBayes.FiniteJointMeanVarianceReverse

open Finset BigOperators MeasureTheory
open scoped NNReal ENNReal
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse
open FormalSLT.PACBayes.FiniteJointMeanVarianceMGF
open FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes

noncomputable section

variable {ι Z : Type*} [MeasurableSpace Z]

/-- Finite prior mixture of the joint reverse-epoch exponentials. -/
def reverseJointMeanVarianceEpochPriorMixture [Fintype Z] [Fintype ι]
    (prior : ι → ℝ) (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : ι → Z → ℝ) (t eta : ℝ) :
    ℕ → (Fin N → Z) → ℝ :=
  fun k x ↦ ∑ i : ι, prior i *
    reverseJointMeanVarianceEpochExponentialProcess
      N hN m p ell t eta i k x

omit [MeasurableSpace Z] in
theorem reverseJointMeanVarianceEpochPriorMixture_nonneg
    [Fintype Z] [Fintype ι]
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : ι → Z → ℝ) (t eta : ℝ) :
    0 ≤ reverseJointMeanVarianceEpochPriorMixture
      prior N hN m p ell t eta := by
  intro k x
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg
    (hprior.nonneg i)
    (reverseJointMeanVarianceEpochExponentialProcess_nonneg
      N hN m p ell t eta i k x)

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

/-- The finite prior mixture is a nonnegative submartingale. -/
theorem reverseJointMeanVarianceEpochPriorMixture_submartingale
    [Fintype Z] [MeasurableSingletonClass Z] [Fintype ι]
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (ell : ι → Z → ℝ) (t eta : ℝ) :
    Submartingale
      (reverseJointMeanVarianceEpochPriorMixture
        prior N hN m p ell t eta)
      (reverseBesselFiltration (Z := Z) N)
      (Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) := by
  classical
  let mu := hp.toPMF.toMeasure
  let filt := reverseBesselFiltration (Z := Z) N
  have hfixed : ∀ i : ι,
      Submartingale
        (fun k x ↦ prior i *
          reverseJointMeanVarianceEpochExponentialProcess
            N hN m p ell t eta i k x)
        filt (Measure.pi (fun _ : Fin N ↦ mu)) := by
    intro i
    have hsub :=
      reverseJointMeanVarianceEpochExponentialProcess_submartingale
        mu N hN m p ell t eta i
    have hscaled := hsub.smul_nonneg (c := prior i) (hprior.nonneg i)
    change Submartingale
      (prior i • reverseJointMeanVarianceEpochExponentialProcess
        N hN m p ell t eta i)
      filt (Measure.pi (fun _ : Fin N ↦ mu))
    exact hscaled
  have hsum := submartingale_finset_sum
    (Finset.univ : Finset ι)
    (fun i k x ↦ prior i *
      reverseJointMeanVarianceEpochExponentialProcess
        N hN m p ell t eta i k x)
    (fun i _ ↦ hfixed i)
  change Submartingale
    (fun k x ↦ ∑ i : ι, prior i *
      reverseJointMeanVarianceEpochExponentialProcess
        N hN m p ell t eta i k x)
    filt (Measure.pi (fun _ : Fin N ↦ mu))
  exact hsum

/-- The endpoint expectation of the prior mixture is at most one. -/
theorem reverseJointMeanVarianceEpochPriorMixture_endpoint_integral_le_one
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z] [Fintype ι]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {t eta : ℝ} (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa m eta) :
    (∫ x, reverseJointMeanVarianceEpochPriorMixture
        prior N hN m p ell t eta (N - m) x
      ∂Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) ≤ 1 := by
  have hcomponent (i : ι) :
      (∫ x, reverseJointMeanVarianceEpochExponentialProcess
          N hN m p ell t eta i (N - m) x
        ∂Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) ≤ 1 :=
    reverseJointMeanVarianceEpoch_endpoint_integral_le_one
      hN hm p hp ell i (hell i) ht heta hkappa
  unfold reverseJointMeanVarianceEpochPriorMixture
  rw [integral_finsetSum Finset.univ]
  · calc
      (∑ i : ι, ∫ x, prior i *
          reverseJointMeanVarianceEpochExponentialProcess
            N hN m p ell t eta i (N - m) x
          ∂Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) =
        ∑ i : ι, prior i *
          (∫ x, reverseJointMeanVarianceEpochExponentialProcess
            N hN m p ell t eta i (N - m) x
            ∂Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [integral_const_mul]
      _ ≤ ∑ i : ι, prior i * 1 := by
        exact Finset.sum_le_sum fun i _ ↦
          mul_le_mul_of_nonneg_left (hcomponent i) (hprior.nonneg i)
      _ = 1 := by simpa using hprior.sum_one
  · intro i _
    exact (Integrable.of_finite.const_mul (prior i))

/-- One prior-mixture crossing set for a fixed joint reverse epoch. -/
def reverseJointMeanVarianceEpochBadPaths [Fintype Z] [Fintype ι]
    (prior : ι → ℝ) (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : ι → Z → ℝ) (t eta delta : ℝ) :
    Set (Fin N → Z) :=
  {x | delta⁻¹ ≤
    (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
      (fun k ↦ reverseJointMeanVarianceEpochPriorMixture
        prior N hN m p ell t eta k x)}

/-- Exact event that some epoch time and some finite posterior violate the
joint score boundary. -/
def reverseJointMeanVarianceEpochAnyPosteriorFailure
    [Fintype Z] [Fintype ι]
    (prior : ι → ℝ) (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : ι → Z → ℝ) (t eta delta : ℝ) :
    Set (Fin N → Z) :=
  {x | ∃ k : ℕ, k ≤ N - m ∧ ∃ rho : ι → ℝ,
    IsPMF rho ∧
      klDiv rho prior + Real.log (1 / delta) ≤
        posteriorAverage rho
          (fun i ↦ reverseJointMeanVarianceEpochScore
            N hN m p ell t eta i k x)}

omit [MeasurableSpace Z] in
/-- Every exact posterior-score violation forces the prior mixture to cross. -/
theorem reverseJointMeanVarianceEpochAnyPosteriorFailure_subset_badPaths
    [Fintype Z] [Fintype ι] [Nonempty ι]
    (N m : ℕ) (hN : 2 ≤ N) (p : Z → ℝ)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ) {t eta delta : ℝ} (hdelta : 0 < delta) :
    reverseJointMeanVarianceEpochAnyPosteriorFailure
        prior N hN m p ell t eta delta ⊆
      reverseJointMeanVarianceEpochBadPaths
        prior N hN m p ell t eta delta := by
  classical
  intro x hx
  rcases hx with ⟨k, hk, rho, hrho, hfail⟩
  let M := reverseJointMeanVarianceEpochPriorMixture
    prior N hN m p ell t eta
  have hdv :
      posteriorAverage rho
          (fun i ↦ reverseJointMeanVarianceEpochScore
            N hN m p ell t eta i k x) ≤
        klDiv rho prior + Real.log (M k x) := by
    simpa only [posteriorAverage, M,
      reverseJointMeanVarianceEpochPriorMixture,
      reverseJointMeanVarianceEpochExponentialProcess] using
      donsker_varadhan hrho hprior
        (fun i ↦ reverseJointMeanVarianceEpochScore
          N hN m p ell t eta i k x)
  have hlog_le : Real.log (1 / delta) ≤ Real.log (M k x) := by
    linarith
  have hM_pos : 0 < M k x := by
    unfold M reverseJointMeanVarianceEpochPriorMixture
    apply Finset.sum_pos
    · intro i _
      exact mul_pos (hprior.pos i) (Real.exp_pos _)
    · exact Finset.univ_nonempty
  have hinv_pos : 0 < (1 : ℝ) / delta := one_div_pos.mpr hdelta
  have hthreshold : (1 : ℝ) / delta ≤ M k x :=
    (Real.log_le_log_iff hinv_pos hM_pos).mp hlog_le
  have hk_mem : k ∈ Finset.range (N - m + 1) := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
  change delta⁻¹ ≤
    (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
      (fun j ↦ M j x)
  simpa only [one_div] using
    hthreshold.trans (Finset.le_sup' (fun j ↦ M j x) hk_mem)

/-- Doob's maximal inequality and the endpoint joint MGF give a unit bound on
threshold times crossing mass for the prior mixture. -/
theorem reverseJointMeanVarianceEpochPriorMixture_maximal_le_one
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z] [Fintype ι]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {t eta : ℝ} (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa m eta)
    (epsilon : ℝ≥0) :
    epsilon * Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        {x | (epsilon : ℝ) ≤
          (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
            (fun k ↦ reverseJointMeanVarianceEpochPriorMixture
              prior N hN m p ell t eta k x)} ≤ 1 := by
  let muN := Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
  let M := reverseJointMeanVarianceEpochPriorMixture
    prior N hN m p ell t eta
  have hsub : Submartingale M (reverseBesselFiltration (Z := Z) N) muN :=
    reverseJointMeanVarianceEpochPriorMixture_submartingale
      p hp hprior N hN m ell t eta
  have hnonneg : 0 ≤ M :=
    reverseJointMeanVarianceEpochPriorMixture_nonneg
      hprior N hN m p ell t eta
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
    reverseJointMeanVarianceEpochPriorMixture_endpoint_integral_le_one
      N m hN hm p hp hprior ell hell ht heta hkappa
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

/-- The exact all-posterior joint-score violation event has mass at most
`delta`. -/
theorem reverseJointMeanVarianceEpochAnyPosteriorFailure_mass_le_delta
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {t eta delta : ℝ} (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa m eta)
    (hdelta : 0 < delta) :
    Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        (reverseJointMeanVarianceEpochAnyPosteriorFailure
          prior N hN m p ell t eta delta) ≤ ENNReal.ofReal delta := by
  let epsilon : ℝ≥0 := ⟨delta⁻¹, inv_nonneg.mpr hdelta.le⟩
  let d : ℝ≥0∞ := ENNReal.ofReal delta
  have hscaled := reverseJointMeanVarianceEpochPriorMixture_maximal_le_one
    N m hN hm p hp hprior.toIsPMF ell hell ht heta hkappa epsilon
  have hepsilonReal : (epsilon : ℝ) = delta⁻¹ := rfl
  have hepsilon : (epsilon : ℝ≥0∞) = d⁻¹ := by
    calc
      (epsilon : ℝ≥0∞) = ENNReal.ofReal delta⁻¹ := by
        symm
        exact ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr hdelta.le)
      _ = d⁻¹ := by rw [ENNReal.ofReal_inv_of_pos hdelta]
  have hscaled' : d⁻¹ *
      Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        (reverseJointMeanVarianceEpochBadPaths
          prior N hN m p ell t eta delta) ≤ 1 := by
    rw [hepsilon] at hscaled
    rw [hepsilonReal] at hscaled
    exact hscaled
  have hd0 : d ≠ 0 := by
    simpa [d] using ENNReal.ofReal_ne_zero_iff.mpr hdelta
  have hdtop : d ≠ ∞ := ENNReal.ofReal_ne_top
  have hbad : Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
      (reverseJointMeanVarianceEpochBadPaths
        prior N hN m p ell t eta delta) ≤ d := by
    calc
      Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
          (reverseJointMeanVarianceEpochBadPaths
            prior N hN m p ell t eta delta) =
        d * (d⁻¹ * Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
          (reverseJointMeanVarianceEpochBadPaths
            prior N hN m p ell t eta delta)) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hd0 hdtop, one_mul]
      _ ≤ d * 1 := mul_le_mul_right hscaled' d
      _ = d := mul_one d
  exact (measure_mono
    (reverseJointMeanVarianceEpochAnyPosteriorFailure_subset_badPaths
      N m hN p hprior ell hdelta)).trans hbad

omit [MeasurableSpace Z] in
/-- Outside the exact failure event, every reverse time and every finite
posterior satisfy the joint score bound with one KL/confidence term. -/
theorem reverseJointMeanVarianceEpoch_posteriorScore_lt_of_not_mem
    [Fintype Z] [Fintype ι]
    (N m : ℕ) (hN : 2 ≤ N) (p : Z → ℝ)
    (prior : ι → ℝ) (ell : ι → Z → ℝ) {t eta delta : ℝ}
    (x : Fin N → Z)
    (hx : x ∉ reverseJointMeanVarianceEpochAnyPosteriorFailure
      prior N hN m p ell t eta delta)
    (k : ℕ) (hk : k ≤ N - m)
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho
        (fun i ↦ reverseJointMeanVarianceEpochScore
          N hN m p ell t eta i k x) <
      klDiv rho prior + Real.log (1 / delta) := by
  by_contra hnot
  exact hx ⟨k, hk, rho, hrho, le_of_not_gt hnot⟩

omit [MeasurableSpace Z] in
/-- **One-event prefix-uniform empirical-Bernstein PAC-Bayes bound.**

On the complement of the exact joint-score violation event, every prefix size
`s` in `[m, N]` and every finite posterior selected after observing the full
horizon sample satisfy a population-risk bound with empirical risk, posterior
average per-hypothesis Bessel variance, and exactly one KL/confidence term.
The balance condition is the zero-residual branch of the fixed-sample joint
MGF; it is imposed on the fixed epoch endpoint parameters, not on the moving
prefix size. -/
theorem reverseJointMeanVarianceEpoch_posteriorRisk_prefix_lt_of_not_mem
    [Fintype Z] [Fintype ι]
    (N m s : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m)
    (hms : m ≤ s) (hsN : s ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (prior : ι → ℝ) (ell : ι → Z → ℝ)
    {t eta delta : ℝ} (ht : 0 < t)
    (hbalance :
      (m : ℝ) * (Real.exp t - 1 - t) ≤
        Real.exp (-t) * finiteJointMeanVarianceKappa m eta)
    (x : Fin N → Z)
    (hx : x ∉ reverseJointMeanVarianceEpochAnyPosteriorFailure
      prior N hN m p ell t eta delta)
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationRisk p ell) <
      posteriorAverage rho
          (fun i ↦ finiteEmpiricalRisk ell i (samplePrefix hsN x)) +
        (klDiv rho prior + Real.log (1 / delta)) / (t * (m : ℝ)) +
        (eta / t) * posteriorAverage rho
          (fun i ↦ finiteEmpiricalVariance ell i (samplePrefix hsN x)) := by
  classical
  have hs_two : 2 ≤ s := hm.trans hms
  have hk : N - s ≤ N - m := Nat.sub_le_sub_left hms N
  have hscore := reverseJointMeanVarianceEpoch_posteriorScore_lt_of_not_mem
    N m hN p prior ell x hx (N - s) hk hrho
  have hresidual (i : ι) :
      (m : ℝ) * Real.log
          (1 + (Real.exp t - 1 - t) * finitePopulationVariance p ell i) -
        Real.exp (-t) * finiteJointMeanVarianceKappa m eta *
          finitePopulationVariance p ell i ≤ 0 :=
    finiteJointMeanVariance_logResidual_nonpos_of_balance
      (finitePopulationVariance_nonneg p hp ell i) hbalance
  let base : ι → ℝ := fun i ↦
    t * (m : ℝ) *
        (finitePopulationRisk p ell i -
          finiteEmpiricalRisk ell i (samplePrefix hsN x)) -
      eta * (m : ℝ) *
        finiteEmpiricalVariance ell i (samplePrefix hsN x)
  have hpoint (i : ι) :
      base i ≤ reverseJointMeanVarianceEpochScore
        N hN m p ell t eta i (N - s) x := by
    rw [reverseJointMeanVarianceEpochScore_sub_eq_prefix
      hN hs_two hsN m p ell t eta i x]
    dsimp only [base]
    linarith [hresidual i]
  have hbase_le : posteriorAverage rho base ≤
      posteriorAverage rho (fun i ↦ reverseJointMeanVarianceEpochScore
        N hN m p ell t eta i (N - s) x) := by
    unfold posteriorAverage
    exact Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_left (hpoint i) (hrho.nonneg i)
  have hbase_lt : posteriorAverage rho base <
      klDiv rho prior + Real.log (1 / delta) := hbase_le.trans_lt hscore
  have hbase_identity :
      posteriorAverage rho base =
        t * (m : ℝ) *
            (posteriorAverage rho (finitePopulationRisk p ell) -
              posteriorAverage rho
                (fun i ↦ finiteEmpiricalRisk ell i (samplePrefix hsN x))) -
          eta * (m : ℝ) * posteriorAverage rho
            (fun i ↦ finiteEmpiricalVariance ell i (samplePrefix hsN x)) := by
    unfold posteriorAverage base
    calc
      (∑ i, rho i *
          (t * (m : ℝ) *
              (finitePopulationRisk p ell i -
                finiteEmpiricalRisk ell i (samplePrefix hsN x)) -
            eta * (m : ℝ) *
              finiteEmpiricalVariance ell i (samplePrefix hsN x))) =
        ∑ i,
          (t * (m : ℝ) * (rho i * finitePopulationRisk p ell i) -
            t * (m : ℝ) *
              (rho i * finiteEmpiricalRisk ell i (samplePrefix hsN x)) -
            eta * (m : ℝ) *
              (rho i * finiteEmpiricalVariance ell i (samplePrefix hsN x))) := by
          refine Finset.sum_congr rfl (fun i _ ↦ ?_)
          ring
      _ = t * (m : ℝ) *
            ((∑ i, rho i * finitePopulationRisk p ell i) -
              ∑ i, rho i * finiteEmpiricalRisk ell i (samplePrefix hsN x)) -
          eta * (m : ℝ) *
            ∑ i, rho i * finiteEmpiricalVariance ell i (samplePrefix hsN x) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
          ring
  rw [hbase_identity] at hbase_lt
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
  have hden : 0 < t * (m : ℝ) := mul_pos ht hmR
  have hgap :
      posteriorAverage rho (finitePopulationRisk p ell) -
          posteriorAverage rho
            (fun i ↦ finiteEmpiricalRisk ell i (samplePrefix hsN x)) <
        (klDiv rho prior + Real.log (1 / delta) +
          eta * (m : ℝ) * posteriorAverage rho
            (fun i ↦ finiteEmpiricalVariance ell i (samplePrefix hsN x))) /
          (t * (m : ℝ)) := by
    rw [lt_div_iff₀ hden]
    linarith
  calc
    posteriorAverage rho (finitePopulationRisk p ell) <
        posteriorAverage rho
            (fun i ↦ finiteEmpiricalRisk ell i (samplePrefix hsN x)) +
          (klDiv rho prior + Real.log (1 / delta) +
            eta * (m : ℝ) * posteriorAverage rho
              (fun i ↦ finiteEmpiricalVariance ell i (samplePrefix hsN x))) /
            (t * (m : ℝ)) := by linarith
    _ = posteriorAverage rho
          (fun i ↦ finiteEmpiricalRisk ell i (samplePrefix hsN x)) +
        (klDiv rho prior + Real.log (1 / delta)) / (t * (m : ℝ)) +
        (eta / t) * posteriorAverage rho
          (fun i ↦ finiteEmpiricalVariance ell i (samplePrefix hsN x)) := by
      field_simp [ht.ne', hmR.ne']
      ring

/-- **End-to-end finite-horizon joint empirical-Bernstein PAC-Bayes event.**

There exists one measurable exceptional set of iid horizon paths with mass at
most `delta` such that, off that set, the zero-residual empirical-Bernstein
bound holds simultaneously for every prefix size in `[m, N]` and every finite
posterior, including post-sample posterior choices.  The theorem derives the
reverse martingales, Doob crossing control, endpoint joint MGF, prior mixture,
and Donsker--Varadhan step; none is supplied as a caller hypothesis. -/
theorem exists_reverseJointMeanVarianceEpoch_event
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {t eta delta : ℝ} (ht : 0 < t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa m eta)
    (hbalance :
      (m : ℝ) * (Real.exp t - 1 - t) ≤
        Real.exp (-t) * finiteJointMeanVarianceKappa m eta)
    (hdelta : 0 < delta) :
    ∃ E : Set (Fin N → Z),
      MeasurableSet E ∧
      Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure) E ≤
        ENNReal.ofReal delta ∧
      ∀ x, x ∉ E → ∀ s : ℕ, (hms : m ≤ s) → (hsN : s ≤ N) →
        ∀ rho : ι → ℝ, IsPMF rho →
          posteriorAverage rho (finitePopulationRisk p ell) <
            posteriorAverage rho
                (fun i ↦ finiteEmpiricalRisk ell i (samplePrefix hsN x)) +
              (klDiv rho prior + Real.log (1 / delta)) / (t * (m : ℝ)) +
              (eta / t) * posteriorAverage rho
                (fun i ↦ finiteEmpiricalVariance ell i
                  (samplePrefix hsN x)) := by
  let E := reverseJointMeanVarianceEpochAnyPosteriorFailure
    prior N hN m p ell t eta delta
  refine ⟨E, (Set.toFinite E).measurableSet, ?_, ?_⟩
  · exact reverseJointMeanVarianceEpochAnyPosteriorFailure_mass_le_delta
      N m hN hm p hp hprior ell hell ht.le heta hkappa hdelta
  · intro x hx s hms hsN rho hrho
    exact reverseJointMeanVarianceEpoch_posteriorRisk_prefix_lt_of_not_mem
      N m s hN hm.1 hms hsN p hp prior ell ht hbalance x hx hrho

end

end FormalSLT.PACBayes.FiniteJointMeanVarianceReverse
