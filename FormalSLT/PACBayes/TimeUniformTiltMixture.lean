/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayes.TimeUniformPACBayes
import FormalSLT.AnytimeValid.EProcess

/-!
# Time-uniform PAC-Bayes with a finite weighted tilt mixture

This module realizes finite weighted tilt selection through one master
e-process.  For a finite hypothesis prior `prior`, a finite tilt prior
`weight`, and declared tilts `lam`, the process

`sum_j weight j * sum_i prior i * exp(lam_j * S_{i,n} - n * psi(lam_j))`

is a single normalized nonnegative supermartingale.  One application of
Ville's inequality therefore controls every declared tilt and every posterior
on the same event.  Selecting tilt `j` after observing the path incurs the exact
prior-weight penalty `log (1 / (delta * weight j))`.

The result is finite and process-level.  The tilt family and its positive
normalized weights are fixed before observing the path.  This is not
optimization over all real tilts, a countable mixture, or a new concentration
inequality.  It selects one declared tilt atom rather than an arbitrary joint
posterior on hypothesis--tilt pairs.  The contribution is the checked finite
hypothesis--tilt master e-process and its posterior/tilt selection semantics;
unlike the finite-grid wrapper in `TimeUniformIIDGrid`, the proof below derives
the weight penalty from one process without entrywise probability bounds or a
union bound.

The statistical mechanism follows the supermartingale-mixture,
Donsker--Varadhan, and Ville recipe of Chugg, Wang, and Ramdas (2023), now with
the finite tilt prior included in the checked master process.  The e-process
and optional-continuation terminology follows the safe anytime-valid inference
literature recorded in `docs/references.md`.  No priority claim is made.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open Finset Real BigOperators

namespace FormalSLT.PACBayes.TimeUniform

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {ι κ Ω : Type*}
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ mΩ}

/-! ### The master hypothesis--tilt e-process -/

/--
Finite weighted mixture of the fixed-tilt PAC-Bayes prior-mixture processes.

Expanding the two sums gives a product-prior mixture over hypothesis--tilt
pairs.  Keeping the sums nested lets the public bound retain the familiar
posterior on hypotheses and an explicit selected tilt.
-/
def pacBayesPriorTiltMixtureProcess
    (prior : ι → ℝ) (weight : κ → ℝ)
    (X : ι → ℕ → Ω → ℝ) (sigma2 b : ℝ) (lam : κ → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ j : κ, weight j *
    pacBayesPriorMixtureProcess prior X sigma2 b (lam j) n ω

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ] in
/-- The master mixture is pointwise nonnegative under nonnegative priors. -/
theorem pacBayesPriorTiltMixtureProcess_nonneg
    {prior : ι → ℝ} (hprior : IsPMF prior)
    {weight : κ → ℝ} (hweight : IsPMF weight)
    (X : ι → ℕ → Ω → ℝ) (sigma2 b : ℝ) (lam : κ → ℝ)
    (n : ℕ) (ω : Ω) :
    0 ≤ pacBayesPriorTiltMixtureProcess
      prior weight X sigma2 b lam n ω := by
  classical
  unfold pacBayesPriorTiltMixtureProcess pacBayesPriorMixtureProcess
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (hweight.nonneg j)
      (Finset.sum_nonneg fun i _ =>
        mul_nonneg (hprior.nonneg i) (Real.exp_pos _).le)

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ] in
/-- The normalized hypothesis--tilt mixture starts at one. -/
theorem pacBayesPriorTiltMixtureProcess_zero
    (prior : ι → ℝ) (hprior : IsPMF prior)
    (weight : κ → ℝ) (hweight : IsPMF weight)
    (X : ι → ℕ → Ω → ℝ) (sigma2 b : ℝ) (lam : κ → ℝ)
    (ω : Ω) :
    pacBayesPriorTiltMixtureProcess
      prior weight X sigma2 b lam 0 ω = 1 := by
  classical
  unfold pacBayesPriorTiltMixtureProcess
  simp_rw [pacBayesPriorMixtureProcess_zero prior hprior X sigma2 b]
  simpa using hweight.sum_one

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ] in
/--
The finite weighted hypothesis--tilt mixture is a nonnegative
supermartingale.
-/
theorem pacBayesPriorTiltMixture_supermartingale
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {X : ι → ℕ → Ω → ℝ} {sigma2 b : ℝ} {lam : κ → ℝ}
    (hb : 0 < b) (hσ : 0 ≤ sigma2)
    (hlam : ∀ j, 0 < lam j) (hblam : ∀ j, b * lam j < 3)
    (hX_meas : ∀ i k, Measurable (X i k))
    (hX_int : ∀ i k, Integrable (X i k) μ)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (h_integrable :
      ∀ i j n, Integrable
        (subGammaExponentialProcess (X i) sigma2 b (lam j) n) μ)
    (hbound : ∀ i k, ∀ᵐ ω ∂μ, |X i k ω| ≤ b)
    (hcenter : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ i k,
      μ[fun ω => (X i k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    Supermartingale
        (pacBayesPriorTiltMixtureProcess prior weight X sigma2 b lam) ℱ μ
      ∧ ∀ n ω,
        0 ≤ pacBayesPriorTiltMixtureProcess
          prior weight X sigma2 b lam n ω := by
  classical
  have hfixed : ∀ j : κ,
      Supermartingale
        (fun n ω => weight j *
          pacBayesPriorMixtureProcess prior X sigma2 b (lam j) n ω) ℱ μ := by
    intro j
    have hinner : Supermartingale
        (pacBayesPriorMixtureProcess prior X sigma2 b (lam j)) ℱ μ :=
      (pacBayesPriorMixture_supermartingale
        (μ := μ) (ℱ := ℱ) hprior hb hσ (hlam j) (hblam j)
        hX_meas hX_int hX_adapted (fun i n => h_integrable i j n)
        hbound hcenter hvar).1
    have hscaled := hinner.smul_nonneg
      (c := weight j) (hweight.nonneg j)
    change Supermartingale
      (weight j • pacBayesPriorMixtureProcess
        prior X sigma2 b (lam j)) ℱ μ
    exact hscaled
  refine ⟨?_, ?_⟩
  · have hsum : Supermartingale
        (fun n ω => ∑ j ∈ (Finset.univ : Finset κ),
          weight j * pacBayesPriorMixtureProcess
            prior X sigma2 b (lam j) n ω) ℱ μ :=
      supermartingale_finset_sum_index (Finset.univ : Finset κ)
        (fun j n ω => weight j *
          pacBayesPriorMixtureProcess prior X sigma2 b (lam j) n ω)
        (fun j _ => hfixed j)
    change Supermartingale
      (fun n ω => ∑ j ∈ (Finset.univ : Finset κ),
        weight j * pacBayesPriorMixtureProcess
          prior X sigma2 b (lam j) n ω) ℱ μ
    exact hsum
  · exact pacBayesPriorTiltMixtureProcess_nonneg
      hprior.toIsPMF hweight.toIsPMF X sigma2 b lam

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ] in
/-- The master finite hypothesis--tilt mixture, packaged as an `EProcess`. -/
theorem pacBayesPriorTiltMixture_eProcess
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {X : ι → ℕ → Ω → ℝ} {sigma2 b : ℝ} {lam : κ → ℝ}
    (hb : 0 < b) (hσ : 0 ≤ sigma2)
    (hlam : ∀ j, 0 < lam j) (hblam : ∀ j, b * lam j < 3)
    (hX_meas : ∀ i k, Measurable (X i k))
    (hX_int : ∀ i k, Integrable (X i k) μ)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (h_integrable :
      ∀ i j n, Integrable
        (subGammaExponentialProcess (X i) sigma2 b (lam j) n) μ)
    (hbound : ∀ i k, ∀ᵐ ω ∂μ, |X i k ω| ≤ b)
    (hcenter : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ i k,
      μ[fun ω => (X i k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    EProcess μ ℱ
      (pacBayesPriorTiltMixtureProcess prior weight X sigma2 b lam) := by
  obtain ⟨hsuper, hnonneg⟩ :=
    pacBayesPriorTiltMixture_supermartingale
      (μ := μ) (ℱ := ℱ) hprior hweight hb hσ hlam hblam
      hX_meas hX_int hX_adapted h_integrable hbound hcenter hvar
  exact
    { nonneg := hnonneg
      start_one := pacBayesPriorTiltMixtureProcess_zero
        prior hprior.toIsPMF weight hweight.toIsPMF X sigma2 b lam
      supermartingale := hsuper }

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ] in
/-- A bounded data-dependent stopping rule preserves the master mixture's
e-value guarantee. This is the operational payoff of packaging the finite
hypothesis--tilt mixture as one e-process. -/
theorem pacBayesPriorTiltMixture_optionalContinuation
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {X : ι → ℕ → Ω → ℝ} {sigma2 b : ℝ} {lam : κ → ℝ}
    (hb : 0 < b) (hσ : 0 ≤ sigma2)
    (hlam : ∀ j, 0 < lam j) (hblam : ∀ j, b * lam j < 3)
    (hX_meas : ∀ i k, Measurable (X i k))
    (hX_int : ∀ i k, Integrable (X i k) μ)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (h_integrable :
      ∀ i j n, Integrable
        (subGammaExponentialProcess (X i) sigma2 b (lam j) n) μ)
    (hbound : ∀ i k, ∀ᵐ ω ∂μ, |X i k ω| ≤ b)
    (hcenter : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ i k,
      μ[fun ω => (X i k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2)
    {τ : Ω → ℕ∞} (hτ_stop : IsStoppingTime ℱ τ)
    {n : ℕ} (hτ_le : ∀ ω, τ ω ≤ (n : ℕ∞)) :
    ∫ ω, stoppedValue
        (pacBayesPriorTiltMixtureProcess prior weight X sigma2 b lam) τ ω ∂μ ≤
      1 := by
  exact eProcess_optionalContinuation
    (pacBayesPriorTiltMixture_eProcess
      (μ := μ) (ℱ := ℱ) hprior hweight hb hσ hlam hblam
      hX_meas hX_int hX_adapted h_integrable hbound hcenter hvar)
    hτ_stop hτ_le

/-! ### One Ville event for every posterior and declared tilt -/

/--
Failure of the fixed-tilt PAC-Bayes boundary for some declared tilt and some
posterior.  Entry `j` carries the exact master-mixture penalty
`log (1 / (delta * weight j))`.
-/
def timeUniformPACBayesTiltMixtureAnyPosteriorUpperFailure
    (prior : ι → ℝ) (weight : κ → ℝ)
    (X : ι → ℕ → Ω → ℝ) (sigma2 b : ℝ)
    (lam : κ → ℝ) (delta : ℝ) : Set Ω :=
  {ω | ∃ j : κ, ∃ posterior : ι → ℝ,
    IsPMF posterior ∧
      ω ∈ timeUniformPACBayesUpperFailure
        prior posterior X sigma2 b (lam j) (delta * weight j)}

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ] in
/-- All-time Ville control for the single finite master mixture process. -/
theorem timeUniformPACBayes_tiltMixture_crossing_bound
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {X : ι → ℕ → Ω → ℝ} {sigma2 b : ℝ}
    {lam : κ → ℝ} {delta : ℝ}
    (hδ : 0 < delta)
    (hb : 0 < b) (hσ : 0 ≤ sigma2)
    (hlam : ∀ j, 0 < lam j) (hblam : ∀ j, b * lam j < 3)
    (hX_meas : ∀ i k, Measurable (X i k))
    (hX_int : ∀ i k, Integrable (X i k) μ)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (h_integrable :
      ∀ i j n, Integrable
        (subGammaExponentialProcess (X i) sigma2 b (lam j) n) μ)
    (hbound : ∀ i k, ∀ᵐ ω ∂μ, |X i k ω| ≤ b)
    (hcenter : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ i k,
      μ[fun ω => (X i k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    μ.real {ω | ∃ n : ℕ, 0 < n ∧
      (1 / delta) ≤ pacBayesPriorTiltMixtureProcess
        prior weight X sigma2 b lam n ω} ≤ delta := by
  have hE := pacBayesPriorTiltMixture_eProcess
    (μ := μ) (ℱ := ℱ) hprior hweight hb hσ hlam hblam
    hX_meas hX_int hX_adapted h_integrable hbound hcenter hvar
  have hthreshold : 0 < (1 : ℝ) / delta := one_div_pos.mpr hδ
  have hville := ville_atTop_maximal_ineq
    hE.supermartingale hE.nonneg hthreshold
  rw [hE.integral_start_eq_one] at hville
  have h_atTop :
      μ.real (atTopCrossingEvent
        (pacBayesPriorTiltMixtureProcess prior weight X sigma2 b lam)
          (1 / delta)) ≤ delta := by
    calc
      μ.real (atTopCrossingEvent
          (pacBayesPriorTiltMixtureProcess prior weight X sigma2 b lam)
            (1 / delta))
          = delta * ((1 / delta) *
              μ.real (atTopCrossingEvent
                (pacBayesPriorTiltMixtureProcess
                  prior weight X sigma2 b lam) (1 / delta))) := by
              field_simp [hδ.ne']
      _ ≤ delta * 1 := mul_le_mul_of_nonneg_left hville hδ.le
      _ = delta := by ring
  have hsubset :
      {ω | ∃ n : ℕ, 0 < n ∧
        (1 / delta) ≤ pacBayesPriorTiltMixtureProcess
          prior weight X sigma2 b lam n ω}
        ⊆ atTopCrossingEvent
          (pacBayesPriorTiltMixtureProcess prior weight X sigma2 b lam)
            (1 / delta) := by
    intro ω hω
    rcases hω with ⟨n, _hn, hcross⟩
    exact ⟨n, hcross⟩
  exact (measureReal_mono hsubset).trans h_atTop

omit [DecidableEq ι] [DecidableEq κ] [Nonempty κ] in
/--
Every posterior/tilt boundary failure forces the single master process to
cross `1 / delta`.  This is the step that replaces a finite union bound.
-/
theorem timeUniformPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_crossing
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {X : ι → ℕ → Ω → ℝ} {sigma2 b : ℝ}
    {lam : κ → ℝ} {delta : ℝ}
    (hδ : 0 < delta) (hlam : ∀ j, 0 < lam j) :
    timeUniformPACBayesTiltMixtureAnyPosteriorUpperFailure
        prior weight X sigma2 b lam delta
      ⊆
    {ω | ∃ n : ℕ, 0 < n ∧
      (1 / delta) ≤ pacBayesPriorTiltMixtureProcess
        prior weight X sigma2 b lam n ω} := by
  classical
  intro ω hω
  rcases hω with ⟨j, posterior, hposterior, hfailure⟩
  have hfixed := timeUniformPACBayesUpperFailure_subset_crossing
    hprior hposterior (mul_pos hδ (hweight.pos j)) (hlam j) hfailure
  rcases hfixed with ⟨n, hn, hcross⟩
  refine ⟨n, hn, ?_⟩
  have hweighted :
      weight j * (1 / (delta * weight j)) ≤
        weight j * pacBayesPriorMixtureProcess
          prior X sigma2 b (lam j) n ω :=
    mul_le_mul_of_nonneg_left hcross (hweight.nonneg j)
  have hsingle :
      weight j * pacBayesPriorMixtureProcess
          prior X sigma2 b (lam j) n ω ≤
        ∑ k : κ, weight k * pacBayesPriorMixtureProcess
          prior X sigma2 b (lam k) n ω :=
    Finset.single_le_sum
      (f := fun k => weight k * pacBayesPriorMixtureProcess
        prior X sigma2 b (lam k) n ω)
      (fun k _ => mul_nonneg (hweight.nonneg k)
        (by
          unfold pacBayesPriorMixtureProcess
          exact Finset.sum_nonneg fun i _ =>
            mul_nonneg (hprior.nonneg i) (Real.exp_pos _).le))
      (Finset.mem_univ j)
  rw [show weight j * (1 / (delta * weight j)) = 1 / delta by
    field_simp [hδ.ne', (hweight.pos j).ne']] at hweighted
  exact hweighted.trans hsingle

omit [DecidableEq ι] [DecidableEq κ] [Nonempty κ] in
/--
Outer-probability time-uniform PAC-Bayes bound for one finite weighted tilt
mixture.  Both the posterior and the declared tilt may be selected after
observing the path.
-/
theorem timeUniformPACBayes_tiltMixture_allPosteriors_bound
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {X : ι → ℕ → Ω → ℝ} {sigma2 b : ℝ}
    {lam : κ → ℝ} {delta : ℝ}
    (hδ : 0 < delta)
    (hb : 0 < b) (hσ : 0 ≤ sigma2)
    (hlam : ∀ j, 0 < lam j) (hblam : ∀ j, b * lam j < 3)
    (hX_meas : ∀ i k, Measurable (X i k))
    (hX_int : ∀ i k, Integrable (X i k) μ)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (h_integrable :
      ∀ i j n, Integrable
        (subGammaExponentialProcess (X i) sigma2 b (lam j) n) μ)
    (hbound : ∀ i k, ∀ᵐ ω ∂μ, |X i k ω| ≤ b)
    (hcenter : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ i k,
      μ[fun ω => (X i k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    μ.real (timeUniformPACBayesTiltMixtureAnyPosteriorUpperFailure
      prior weight X sigma2 b lam delta) ≤ delta := by
  exact (measureReal_mono
    (timeUniformPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_crossing
      hprior hweight hδ hlam)).trans
    (timeUniformPACBayes_tiltMixture_crossing_bound
      (μ := μ) (ℱ := ℱ) hprior hweight hδ hb hσ hlam hblam
      hX_meas hX_int hX_adapted h_integrable hbound hcenter hvar)

omit [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] [Nonempty κ] in
/--
Outside the master failure event, every posterior satisfies every declared
tilt boundary at every positive time.
-/
theorem timeUniformPACBayes_tiltMixture_allPosteriors_of_not_mem
    {prior : ι → ℝ} {weight : κ → ℝ}
    {X : ι → ℕ → Ω → ℝ} {sigma2 b : ℝ}
    {lam : κ → ℝ} {delta : ℝ} {ω : Ω}
    (hω : ω ∉ timeUniformPACBayesTiltMixtureAnyPosteriorUpperFailure
      prior weight X sigma2 b lam delta) :
    ∀ j : κ, ∀ posterior : ι → ℝ, IsPMF posterior →
      ∀ n : ℕ, 0 < n →
        posteriorAverage posterior (fun i => runningMean (X i) n ω) <
          subGammaCgf sigma2 b (lam j) / lam j +
            (klDiv posterior prior +
              Real.log (1 / (delta * weight j))) /
                ((n : ℝ) * lam j) := by
  intro j posterior hposterior n hn
  apply lt_of_not_ge
  intro hfailure
  apply hω
  exact ⟨j, posterior, hposterior, n, hn, hfailure⟩

omit [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] [Nonempty κ] in
/--
Explicit post-data selector corollary.  The selector may inspect both the path
and the posterior because the common event is already uniform in both.
-/
theorem timeUniformPACBayes_tiltMixture_selected_of_not_mem
    {prior : ι → ℝ} {weight : κ → ℝ}
    {X : ι → ℕ → Ω → ℝ} {sigma2 b : ℝ}
    {lam : κ → ℝ} {delta : ℝ} {ω : Ω}
    (hω : ω ∉ timeUniformPACBayesTiltMixtureAnyPosteriorUpperFailure
      prior weight X sigma2 b lam delta)
    (select : Ω → (ι → ℝ) → κ)
    (posterior : ι → ℝ) (hposterior : IsPMF posterior)
    (n : ℕ) (hn : 0 < n) :
    posteriorAverage posterior (fun i => runningMean (X i) n ω) <
      subGammaCgf sigma2 b (lam (select ω posterior)) /
          lam (select ω posterior) +
        (klDiv posterior prior +
          Real.log (1 / (delta * weight (select ω posterior)))) /
            ((n : ℝ) * lam (select ω posterior)) :=
  timeUniformPACBayes_tiltMixture_allPosteriors_of_not_mem hω
    (select ω posterior) posterior hposterior n hn

end

end FormalSLT.PACBayes.TimeUniform
