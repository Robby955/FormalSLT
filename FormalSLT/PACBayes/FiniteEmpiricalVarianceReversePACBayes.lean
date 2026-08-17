/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteEmpiricalVarianceReverseEpoch

/-!
# Finite-hypothesis PAC-Bayes control on a reverse Bessel epoch

This module mixes the reverse-time Bessel exponential submartingales over a
fixed finite hypothesis prior before applying Doob's maximal inequality.  One
finite-horizon event then controls every prefix size in the epoch and every
posterior selected after observing the sample, with exactly one finite
`KL(posterior || prior)` term.

The event is built from the actual prior mixture; there is no hypothesis union
bound and no caller-supplied MGF or martingale assumption.  This remains an
offline finite-horizon result for a fixed endpoint `m` and fixed `eta`.  It is
not yet a stitched all-horizon theorem, a tilt catalog, or a risk bound.
-/

namespace FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse

open Finset BigOperators MeasureTheory
open scoped NNReal ENNReal
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.FiniteEmpiricalVariance

noncomputable section

variable {ι Z : Type*} [MeasurableSpace Z]

/-- Per-hypothesis endpoint-normalized score along a reverse Bessel epoch. -/
def reverseBesselEpochScore [Fintype Z] (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : ι → Z → ℝ) (eta : ℝ)
    (i : ι) (k : ℕ) (x : Fin N → Z) : ℝ :=
  eta * (m : ℝ) *
      (finitePopulationVariance p ell i -
        reverseBesselProcess N hN (ell i) k x) -
    reverseBesselEpochPenalty m eta (finitePopulationVariance p ell i)

/-- Finite prior mixture of the reverse-epoch hypothesis exponentials. -/
def reverseBesselEpochPriorMixture [Fintype Z] [Fintype ι]
    (prior : ι → ℝ) (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : ι → Z → ℝ) (eta : ℝ) :
    ℕ → (Fin N → Z) → ℝ :=
  fun k x ↦ ∑ i : ι, prior i *
    Real.exp (reverseBesselEpochScore N hN m p ell eta i k x)

omit [MeasurableSpace Z] in
theorem reverseBesselEpochPriorMixture_nonneg [Fintype Z] [Fintype ι]
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : ι → Z → ℝ) (eta : ℝ) :
    0 ≤ reverseBesselEpochPriorMixture prior N hN m p ell eta := by
  intro k x
  exact Finset.sum_nonneg fun i _ ↦
    mul_nonneg (hprior.nonneg i) (Real.exp_pos _).le

private theorem submartingale_finset_sum
    {Ω α : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} [IsFiniteMeasure mu]
    {filt : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    (s : Finset α) (M : α → ℕ → Ω → ℝ)
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

/-- The finite prior mixture is itself a nonnegative submartingale. -/
theorem reverseBesselEpochPriorMixture_submartingale
    [Fintype Z] [MeasurableSingletonClass Z] [Fintype ι]
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (ell : ι → Z → ℝ) (eta : ℝ) :
    Submartingale
      (reverseBesselEpochPriorMixture prior N hN m p ell eta)
      (reverseBesselFiltration (Z := Z) N)
      (Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) := by
  classical
  let mu := hp.toPMF.toMeasure
  let filt := reverseBesselFiltration (Z := Z) N
  have hfixed : ∀ i : ι,
      Submartingale
        (fun k x ↦ prior i *
          Real.exp (reverseBesselEpochScore N hN m p ell eta i k x))
        filt (Measure.pi (fun _ : Fin N ↦ mu)) := by
    intro i
    have hsub := reverseBesselExponentialProcess_submartingale
      mu N hN (ell i) (finitePopulationVariance p ell i)
        (eta * (m : ℝ))
        (reverseBesselEpochPenalty m eta (finitePopulationVariance p ell i))
    have hscaled := hsub.smul_nonneg (c := prior i) (hprior.nonneg i)
    change Submartingale
      (prior i • reverseBesselExponentialProcess N hN (ell i)
        (finitePopulationVariance p ell i) (eta * (m : ℝ))
        (reverseBesselEpochPenalty m eta (finitePopulationVariance p ell i)))
      filt (Measure.pi (fun _ : Fin N ↦ mu))
    exact hscaled
  have hsum := submartingale_finset_sum
    (Finset.univ : Finset ι)
    (fun i k x ↦ prior i *
      Real.exp (reverseBesselEpochScore N hN m p ell eta i k x))
    (fun i _ ↦ hfixed i)
  change Submartingale
    (fun k x ↦ ∑ i : ι, prior i *
      Real.exp (reverseBesselEpochScore N hN m p ell eta i k x))
    filt (Measure.pi (fun _ : Fin N ↦ mu))
  exact hsum

/-- At the endpoint `N - m`, the integral of the prior mixture is at most one.
Every hypothesis uses the same fixed `eta` and endpoint `m`, while its
normalizer retains its own population variance. -/
theorem reverseBesselEpochPriorMixture_endpoint_integral_le_one
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z] [Fintype ι]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {eta : ℝ} (heta : 0 ≤ eta) :
    (∫ x, reverseBesselEpochPriorMixture prior N hN m p ell eta (N - m) x
      ∂Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) ≤ 1 := by
  classical
  have hcomponent (i : ι) :
      (∫ x, Real.exp (reverseBesselEpochScore N hN m p ell eta i (N - m) x)
        ∂Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) ≤ 1 := by
    have hend := reverseBesselEpoch_endpoint_integral_le_one
      hm p hp ell i (hell i) heta
    simpa only [reverseBesselEpochScore,
      reverseBesselProcess_sub_eq_prefix hN hm.1 hm.2] using hend
  rw [show reverseBesselEpochPriorMixture prior N hN m p ell eta (N - m) =
      fun x ↦ ∑ i : ι, prior i *
        Real.exp (reverseBesselEpochScore N hN m p ell eta i (N - m) x) by
    rfl]
  rw [integral_finsetSum (Finset.univ : Finset ι)
    (fun _ _ ↦ Integrable.of_finite)]
  calc
    (∑ i : ι, ∫ x, prior i *
        Real.exp (reverseBesselEpochScore N hN m p ell eta i (N - m) x)
        ∂Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) =
      ∑ i : ι, prior i *
        (∫ x, Real.exp
          (reverseBesselEpochScore N hN m p ell eta i (N - m) x)
          ∂Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_const_mul]
    _ ≤ ∑ i : ι, prior i * 1 := by
      exact Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_left (hcomponent i) (hprior.nonneg i)
    _ = 1 := by simpa using hprior.sum_one

/-- The single exceptional set for one reverse Bessel epoch.  A path is bad
when the prior mixture crosses `1 / delta` at some reverse time through
`N - m`. -/
def reverseBesselEpochPACBayesBadPaths [Fintype Z] [Fintype ι]
    (prior : ι → ℝ) (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : ι → Z → ℝ) (eta delta : ℝ) :
    Set (Fin N → Z) :=
  {x | delta⁻¹ ≤
    (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
      (fun k ↦ reverseBesselEpochPriorMixture
        prior N hN m p ell eta k x)}

/-- The exact all-posterior score-violation event on one reverse epoch. -/
def reverseBesselEpochAnyPosteriorFailure [Fintype Z] [Fintype ι]
    (prior : ι → ℝ) (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : ι → Z → ℝ) (eta delta : ℝ) :
    Set (Fin N → Z) :=
  {x | ∃ k : ℕ, k ≤ N - m ∧ ∃ rho : ι → ℝ,
    IsPMF rho ∧
      klDiv rho prior + Real.log (1 / delta) ≤
        posteriorAverage rho
          (fun i ↦ reverseBesselEpochScore N hN m p ell eta i k x)}

omit [MeasurableSpace Z] in
/-- A posterior score violation forces the common prior mixture to cross. -/
theorem reverseBesselEpochAnyPosteriorFailure_subset_badPaths
    [Fintype Z] [Fintype ι] [Nonempty ι]
    (N m : ℕ) (hN : 2 ≤ N) (p : Z → ℝ)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ) {eta delta : ℝ} (hdelta : 0 < delta) :
    reverseBesselEpochAnyPosteriorFailure
        prior N hN m p ell eta delta ⊆
      reverseBesselEpochPACBayesBadPaths
        prior N hN m p ell eta delta := by
  classical
  intro x hx
  rcases hx with ⟨k, hk, rho, hrho, hfail⟩
  let M := reverseBesselEpochPriorMixture prior N hN m p ell eta
  have hdv :
      posteriorAverage rho
          (fun i ↦ reverseBesselEpochScore N hN m p ell eta i k x) ≤
        klDiv rho prior + Real.log (M k x) := by
    simpa only [posteriorAverage, M, reverseBesselEpochPriorMixture] using
      donsker_varadhan hrho hprior
        (fun i ↦ reverseBesselEpochScore N hN m p ell eta i k x)
  have hlog_le : Real.log (1 / delta) ≤ Real.log (M k x) := by
    linarith
  have hM_pos : 0 < M k x := by
    unfold M reverseBesselEpochPriorMixture
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

/-- Doob's inequality and the normalized component MGFs give a unit bound on
threshold times crossing mass for the prior mixture. -/
theorem reverseBesselEpochPriorMixture_maximal_le_one
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z] [Fintype ι]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {eta : ℝ} (heta : 0 ≤ eta) (ε : ℝ≥0) :
    ε * Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        {x | (ε : ℝ) ≤
          (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
            (fun k ↦ reverseBesselEpochPriorMixture
              prior N hN m p ell eta k x)} ≤ 1 := by
  let muN := Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
  let M := reverseBesselEpochPriorMixture prior N hN m p ell eta
  have hsub : Submartingale M (reverseBesselFiltration (Z := Z) N) muN :=
    reverseBesselEpochPriorMixture_submartingale
      p hp hprior N hN m ell eta
  have hnonneg : 0 ≤ M :=
    reverseBesselEpochPriorMixture_nonneg hprior N hN m p ell eta
  have hdoob := MeasureTheory.maximal_ineq hsub hnonneg
    (ε := ε) (N - m)
  have hsetIntegral :
      ∫ x in {x | (ε : ℝ) ≤
          (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
            (fun k ↦ M k x)}, M (N - m) x ∂muN ≤
        ∫ x, M (N - m) x ∂muN :=
    setIntegral_le_integral (hsub.integrable (N - m))
      (Filter.Eventually.of_forall (fun x ↦ hnonneg (N - m) x))
  have hend : (∫ x, M (N - m) x ∂muN) ≤ 1 :=
    reverseBesselEpochPriorMixture_endpoint_integral_le_one
      N m hN hm p hp hprior ell hell heta
  calc
    ε * muN {x | (ε : ℝ) ≤
        (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
          (fun k ↦ M k x)} ≤
      ENNReal.ofReal
        (∫ x in {x | (ε : ℝ) ≤
            (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
              (fun k ↦ M k x)}, M (N - m) x ∂muN) := hdoob
    _ ≤ ENNReal.ofReal (∫ x, M (N - m) x ∂muN) :=
      ENNReal.ofReal_le_ofReal hsetIntegral
    _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hend
    _ = 1 := by norm_num

/-- The one prior-mixture epoch event has probability at most `delta`. -/
theorem reverseBesselEpochPACBayesBadPaths_mass_le_delta
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z] [Fintype ι]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {eta delta : ℝ} (heta : 0 ≤ eta) (hdelta : 0 < delta) :
    Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        (reverseBesselEpochPACBayesBadPaths
          prior N hN m p ell eta delta) ≤ ENNReal.ofReal delta := by
  let ε : ℝ≥0 := ⟨delta⁻¹, inv_nonneg.mpr hdelta.le⟩
  let d : ℝ≥0∞ := ENNReal.ofReal delta
  have hscaled := reverseBesselEpochPriorMixture_maximal_le_one
    N m hN hm p hp hprior ell hell heta ε
  have hεReal : (ε : ℝ) = delta⁻¹ := rfl
  have hε : (ε : ℝ≥0∞) = d⁻¹ := by
    calc
      (ε : ℝ≥0∞) = ENNReal.ofReal delta⁻¹ := by
        symm
        exact ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr hdelta.le)
      _ = d⁻¹ := by rw [ENNReal.ofReal_inv_of_pos hdelta]
  have hscaled' : d⁻¹ * Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
      (reverseBesselEpochPACBayesBadPaths
        prior N hN m p ell eta delta) ≤ 1 := by
    rw [hε] at hscaled
    rw [hεReal] at hscaled
    exact hscaled
  have hd0 : d ≠ 0 := by
    simpa [d] using (ENNReal.ofReal_ne_zero_iff.mpr hdelta)
  have hdtop : d ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        (reverseBesselEpochPACBayesBadPaths
          prior N hN m p ell eta delta) =
      d * (d⁻¹ * Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        (reverseBesselEpochPACBayesBadPaths
          prior N hN m p ell eta delta)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hd0 hdtop, one_mul]
    _ ≤ d * 1 := mul_le_mul_right hscaled' d
    _ = ENNReal.ofReal delta := by simp [d]

/-- The exact all-posterior violation event has mass at most `delta`.  The
proof uses one prior-mixture crossing event, not a union over hypotheses or
posteriors. -/
theorem reverseBesselEpochAnyPosteriorFailure_mass_le_delta
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {eta delta : ℝ} (heta : 0 ≤ eta) (hdelta : 0 < delta) :
    Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        (reverseBesselEpochAnyPosteriorFailure
          prior N hN m p ell eta delta) ≤ ENNReal.ofReal delta := by
  apply le_trans (measure_mono
    (reverseBesselEpochAnyPosteriorFailure_subset_badPaths
      N m hN p hprior ell hdelta))
  exact reverseBesselEpochPACBayesBadPaths_mass_le_delta
    N m hN hm p hp hprior.toIsPMF ell hell heta hdelta

/-- Outside the one epoch event, every reverse time in the epoch and every
finite posterior satisfy the Donsker--Varadhan score bound with one KL term. -/
theorem reverseBesselEpoch_posteriorScore_lt_of_not_mem
    [Fintype Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι]
    (N m : ℕ) (hN : 2 ≤ N)
    (p : Z → ℝ)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ) {eta delta : ℝ}
    (x : Fin N → Z)
    (hx : x ∉ reverseBesselEpochPACBayesBadPaths
      prior N hN m p ell eta delta)
    (k : ℕ) (hk : k ≤ N - m)
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho
        (fun i ↦ reverseBesselEpochScore N hN m p ell eta i k x) <
      klDiv rho prior + Real.log (1 / delta) := by
  classical
  let M := reverseBesselEpochPriorMixture prior N hN m p ell eta
  have hk_mem : k ∈ Finset.range (N - m + 1) := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
  have hk_le_sup : M k x ≤
      (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
        (fun j ↦ M j x) :=
    Finset.le_sup' (fun j ↦ M j x) hk_mem
  have hsup_lt :
      (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
          (fun j ↦ M j x) < delta⁻¹ := by
    exact lt_of_not_ge hx
  have hM_lt : M k x < 1 / delta := by
    simpa only [one_div] using hk_le_sup.trans_lt hsup_lt
  have hM_pos : 0 < M k x := by
    unfold M reverseBesselEpochPriorMixture
    apply Finset.sum_pos
    · intro i _
      exact mul_pos (hprior.pos i) (Real.exp_pos _)
    · exact Finset.univ_nonempty
  have hdv :
      posteriorAverage rho
          (fun i ↦ reverseBesselEpochScore N hN m p ell eta i k x) ≤
        klDiv rho prior + Real.log (M k x) := by
    simpa only [posteriorAverage, M, reverseBesselEpochPriorMixture] using
      donsker_varadhan hrho hprior
        (fun i ↦ reverseBesselEpochScore N hN m p ell eta i k x)
  have hlog : Real.log (M k x) < Real.log (1 / delta) :=
    Real.log_lt_log hM_pos hM_lt
  linarith

omit [MeasurableSpace Z] in
/-- Complement form for the exact violation event. -/
theorem reverseBesselEpoch_posteriorScore_lt_of_not_mem_failure
    [Fintype Z] [Fintype ι]
    (N m : ℕ) (hN : 2 ≤ N) (p : Z → ℝ)
    (prior : ι → ℝ) (ell : ι → Z → ℝ) {eta delta : ℝ}
    (x : Fin N → Z)
    (hx : x ∉ reverseBesselEpochAnyPosteriorFailure
      prior N hN m p ell eta delta)
    (k : ℕ) (hk : k ≤ N - m)
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho
        (fun i ↦ reverseBesselEpochScore N hN m p ell eta i k x) <
      klDiv rho prior + Real.log (1 / delta) := by
  by_contra hnot
  exact hx ⟨k, hk, rho, hrho, le_of_not_gt hnot⟩

/-- Posterior-averaged population variance is controlled by its reverse-prefix
empirical counterpart, one KL/confidence term, and the retained quadratic
variance correction.  Both variance terms average the per-hypothesis Bessel
quantities; this is not the variance of a posterior-averaged loss. -/
theorem reverseBesselEpoch_posteriorVarianceGap_lt_of_not_mem
    [Fintype Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m)
    (p : Z → ℝ)
    (prior : ι → ℝ)
    (ell : ι → Z → ℝ) {eta delta : ℝ} (heta : 0 < eta)
    (x : Fin N → Z)
    (hx : x ∉ reverseBesselEpochAnyPosteriorFailure
      prior N hN m p ell eta delta)
    (k : ℕ) (hk : k ≤ N - m)
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho (fun i ↦ finitePopulationVariance p ell i) -
        posteriorAverage rho
          (fun i ↦ reverseBesselProcess N hN (ell i) k x) <
      (klDiv rho prior + Real.log (1 / delta)) / (eta * (m : ℝ)) +
        (eta * (m : ℝ)) / (2 * ((m : ℝ) - 1)) *
          posteriorAverage rho (fun i ↦ finitePopulationVariance p ell i) := by
  have hscore := reverseBesselEpoch_posteriorScore_lt_of_not_mem_failure
    N m hN p prior ell x hx k hk hrho
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
  have hscale : 0 < eta * (m : ℝ) := mul_pos heta hmR
  have hidentity :
      posteriorAverage rho
          (fun i ↦ reverseBesselEpochScore N hN m p ell eta i k x) =
        (eta * (m : ℝ)) *
            (posteriorAverage rho (fun i ↦ finitePopulationVariance p ell i) -
              posteriorAverage rho
                (fun i ↦ reverseBesselProcess N hN (ell i) k x)) -
          reverseBesselEpochPenalty m eta 1 *
            posteriorAverage rho (fun i ↦ finitePopulationVariance p ell i) := by
    unfold posteriorAverage reverseBesselEpochScore reverseBesselEpochPenalty
    calc
      (∑ i, rho i *
          (eta * (m : ℝ) *
              (finitePopulationVariance p ell i -
                reverseBesselProcess N hN (ell i) k x) -
            eta ^ (2 : Nat) * (m : ℝ) ^ (2 : Nat) *
                finitePopulationVariance p ell i /
              (2 * ((m : ℝ) - 1)))) =
        ∑ i, ((eta * (m : ℝ)) *
              (rho i * finitePopulationVariance p ell i) -
            (eta * (m : ℝ)) *
              (rho i * reverseBesselProcess N hN (ell i) k x) -
            (eta ^ (2 : Nat) * (m : ℝ) ^ (2 : Nat) /
              (2 * ((m : ℝ) - 1))) *
              (rho i * finitePopulationVariance p ell i)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = (eta * (m : ℝ)) *
            ((∑ i, rho i * finitePopulationVariance p ell i) -
              ∑ i, rho i * reverseBesselProcess N hN (ell i) k x) -
          (eta ^ (2 : Nat) * (m : ℝ) ^ (2 : Nat) /
            (2 * ((m : ℝ) - 1))) *
            ∑ i, rho i * finitePopulationVariance p ell i := by
          simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
      _ = _ := by ring
  rw [hidentity] at hscore
  have hscore' :
      (eta * (m : ℝ)) *
          (posteriorAverage rho (fun i ↦ finitePopulationVariance p ell i) -
            posteriorAverage rho
              (fun i ↦ reverseBesselProcess N hN (ell i) k x)) -
        eta ^ (2 : Nat) * (m : ℝ) ^ (2 : Nat) *
            posteriorAverage rho (fun i ↦ finitePopulationVariance p ell i) /
          (2 * ((m : ℝ) - 1)) <
        klDiv rho prior + Real.log (1 / delta) := by
    calc
      _ = (eta * (m : ℝ)) *
            (posteriorAverage rho (fun i ↦ finitePopulationVariance p ell i) -
              posteriorAverage rho
                (fun i ↦ reverseBesselProcess N hN (ell i) k x)) -
          reverseBesselEpochPenalty m eta 1 *
            posteriorAverage rho (fun i ↦ finitePopulationVariance p ell i) := by
              unfold reverseBesselEpochPenalty
              ring
      _ < _ := hscore
  rw [← sub_lt_iff_lt_add]
  apply (lt_div_iff₀ hscale).2
  calc
    _ = (eta * (m : ℝ)) *
          (posteriorAverage rho (fun i ↦ finitePopulationVariance p ell i) -
            posteriorAverage rho
              (fun i ↦ reverseBesselProcess N hN (ell i) k x)) -
        eta ^ (2 : Nat) * (m : ℝ) ^ (2 : Nat) *
            posteriorAverage rho (fun i ↦ finitePopulationVariance p ell i) /
          (2 * ((m : ℝ) - 1)) := by ring
    _ < _ := hscore'

/-- Rearranged retained-variance form.  The denominator is positive when the
fixed endpoint tilt satisfies `eta * m < 2 * (m - 1)`. -/
theorem reverseBesselEpoch_posteriorVariance_lt_of_not_mem
    [Fintype Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m)
    (p : Z → ℝ)
    (prior : ι → ℝ)
    (ell : ι → Z → ℝ) {eta delta : ℝ} (heta : 0 < eta)
    (heta_range : eta * (m : ℝ) < 2 * ((m : ℝ) - 1))
    (x : Fin N → Z)
    (hx : x ∉ reverseBesselEpochAnyPosteriorFailure
      prior N hN m p ell eta delta)
    (k : ℕ) (hk : k ≤ N - m)
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho (fun i ↦ finitePopulationVariance p ell i) <
      (posteriorAverage rho
          (fun i ↦ reverseBesselProcess N hN (ell i) k x) +
        (klDiv rho prior + Real.log (1 / delta)) / (eta * (m : ℝ))) /
      (1 - (eta * (m : ℝ)) / (2 * ((m : ℝ) - 1))) := by
  have hgap := reverseBesselEpoch_posteriorVarianceGap_lt_of_not_mem
    N m hN hm p prior ell heta x hx k hk hrho
  have hden : 0 < 2 * ((m : ℝ) - 1) := by
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hcoef : 0 < 1 - (eta * (m : ℝ)) / (2 * ((m : ℝ) - 1)) := by
    rw [sub_pos, div_lt_one hden]
    exact heta_range
  apply (lt_div_iff₀ hcoef).2
  linarith

/-- Prefix-size form of the retained posterior-variance theorem.  On the same
epoch event, every prefix size `t` between the fixed endpoint `m` and horizon
`N` is controlled simultaneously, for every posterior selected after the
whole horizon sample is observed. -/
theorem reverseBesselEpoch_posteriorVariance_prefix_lt_of_not_mem
    [Fintype Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι]
    (N m t : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m)
    (hmt : m ≤ t) (htN : t ≤ N)
    (p : Z → ℝ)
    (prior : ι → ℝ)
    (ell : ι → Z → ℝ) {eta delta : ℝ} (heta : 0 < eta)
    (heta_range : eta * (m : ℝ) < 2 * ((m : ℝ) - 1))
    (x : Fin N → Z)
    (hx : x ∉ reverseBesselEpochAnyPosteriorFailure
      prior N hN m p ell eta delta)
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho (fun i ↦ finitePopulationVariance p ell i) <
      (posteriorAverage rho
          (fun i ↦ finiteEmpiricalVariance ell i (samplePrefix htN x)) +
        (klDiv rho prior + Real.log (1 / delta)) / (eta * (m : ℝ))) /
      (1 - (eta * (m : ℝ)) / (2 * ((m : ℝ) - 1))) := by
  have ht_two : 2 ≤ t := hm.trans hmt
  have hk : N - t ≤ N - m := Nat.sub_le_sub_left hmt N
  simpa only [reverseBesselProcess_sub_eq_prefix hN ht_two htN,
    prefixBesselVariance, finiteEmpiricalVariance] using
    (reverseBesselEpoch_posteriorVariance_lt_of_not_mem
      N m hN hm p prior ell heta heta_range x hx (N - t) hk hrho)

end

end FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse
