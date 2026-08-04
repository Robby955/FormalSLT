/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayes.ChangeOfMeasure
import FormalSLT.AnytimeValid.MixtureCS

/-!
# Time-uniform PAC-Bayes confidence sequence (process level)

This module formalizes a finite fixed-tilt time-uniform bound at the level of an
abstract martingale-difference process.  Each hypothesis `i` carries an adapted,
conditionally centered, conditionally sub-Gamma increment process `X i`; nothing
here fixes `X` to a loss or a sample.  The construction is the Chugg-Wang-Ramdas
mechanism: mix the per-hypothesis exponential supermartingales against the prior
into a single nonnegative supermartingale, apply Ville over all times, then run
the finite Donsker-Varadhan change-of-measure step at the realized time and
posterior.  The headline `timeUniformPACBayes_bound` controls, with probability
at least `1 - δ` simultaneously for every `n ≥ 1`, the posterior running mean of
`X` against a `cgf`/KL/`log(1/δ)` boundary.

This is therefore a process-level Ville-supermartingale confidence sequence, not
a proven generalization bound.  The PAC-Bayes reading — taking each `X i` to be a
per-sample population-minus-empirical risk gap so the running mean is the
generalization gap — is the intended interpretation.  The statements below are
about the abstract process; `FormalSLT.PACBayes.TimeUniformIID` discharges these
hypotheses for a concrete i.i.d. sample stream with measurable `[0,1]` losses.

The theorem names avoid priority or "first" wording.  The disambiguation is
source-level: the bound is time-uniform in `n`, not a fixed-sample bound with a
union-bound wrapper.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open Finset Real BigOperators
open scoped ENNReal

namespace FormalSLT.PACBayes.TimeUniform

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ mΩ}

/-! ### Finite prior mixture of supermartingales -/

/-- A finite sum of supermartingales is a supermartingale. -/
theorem supermartingale_finset_sum_index {α : Type*}
    (s : Finset α) (M : α → ℕ → Ω → ℝ)
    [IsFiniteMeasure μ]
    (hM : ∀ i ∈ s, Supermartingale (M i) ℱ μ) :
    Supermartingale (fun n ω => ∑ i ∈ s, M i n ω) ℱ μ := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      have h : Martingale (0 : ℕ → Ω → ℝ) ℱ μ := MeasureTheory.martingale_zero ℝ ℱ μ
      exact h.supermartingale
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      have ha' : Supermartingale (M a) ℱ μ := hM a (Finset.mem_insert_self a s)
      have ihs : Supermartingale (fun n ω => ∑ i ∈ s, M i n ω) ℱ μ :=
        ih (fun i hi => hM i (Finset.mem_insert_of_mem hi))
      exact ha'.add ihs

/--
Prior mixture of per-hypothesis fixed-tilt exponential processes.

For each hypothesis `i`, `X i` is an abstract adapted martingale-difference
process; its running mean at time `n` is what the bound controls.  Under the
intended PAC-Bayes reading `X i` is the per-sample risk gap, but that
interpretation is not assumed by anything here.
-/
def pacBayesPriorMixtureProcess
    (prior : ι → ℝ) (X : ι → ℕ → Ω → ℝ) (sigma2 b lam : ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i : ι, prior i * subGammaExponentialProcess (X i) sigma2 b lam n ω

omit [DecidableEq ι] [Nonempty ι] in
/-- The prior-mixture process starts at one. -/
theorem pacBayesPriorMixtureProcess_zero
    (prior : ι → ℝ) (hprior : IsPMF prior)
    (X : ι → ℕ → Ω → ℝ) (sigma2 b lam : ℝ) (ω : Ω) :
    pacBayesPriorMixtureProcess prior X sigma2 b lam 0 ω = 1 := by
  simp [pacBayesPriorMixtureProcess, subGammaExponentialProcess, runningSum,
    hprior.sum_one]

omit [DecidableEq ι] [Nonempty ι] in
/--
The finite prior mixture of per-hypothesis exponential processes is a
nonnegative supermartingale.
-/
theorem pacBayesPriorMixture_supermartingale
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {X : ι → ℕ → Ω → ℝ} {sigma2 b lam : ℝ}
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : ∀ i k, Measurable (X i k))
    (hX_int : ∀ i k, Integrable (X i k) μ)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (h_integrable :
      ∀ i n, Integrable (subGammaExponentialProcess (X i) sigma2 b lam n) μ)
    (hbound : ∀ i k, ∀ᵐ ω ∂μ, |X i k ω| ≤ b)
    (hcenter : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ i k, μ[fun ω => (X i k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    Supermartingale (pacBayesPriorMixtureProcess prior X sigma2 b lam) ℱ μ
      ∧ ∀ n ω, 0 ≤ pacBayesPriorMixtureProcess prior X sigma2 b lam n ω := by
  classical
  have hfixed : ∀ i : ι,
      Supermartingale
        (fun n ω => prior i * subGammaExponentialProcess (X i) sigma2 b lam n ω) ℱ μ := by
    intro i
    have hadapted :=
      stronglyAdapted_subGammaExponentialProcess_of_adapted sigma2 b lam (hX_adapted i)
    have hsup_i : Supermartingale (subGammaExponentialProcess (X i) sigma2 b lam) ℱ μ :=
      (nonneg_supermartingale_of_condSubGamma hadapted (h_integrable i)
        (condSubGamma_supermartingale_step hb hσ hlam.le hblam
          (hX_meas i) (hX_int i) hadapted (hbound i) (hcenter i) (hvar i))).1
    have hscaled := hsup_i.smul_nonneg (c := prior i) (hprior.nonneg i)
    change Supermartingale
      (prior i • subGammaExponentialProcess (X i) sigma2 b lam) ℱ μ
    exact hscaled
  refine ⟨?_, ?_⟩
  · have hsum : Supermartingale
        (fun n ω =>
          ∑ i ∈ (Finset.univ : Finset ι),
            prior i * subGammaExponentialProcess (X i) sigma2 b lam n ω) ℱ μ :=
      supermartingale_finset_sum_index (Finset.univ : Finset ι)
        (fun i n ω => prior i * subGammaExponentialProcess (X i) sigma2 b lam n ω)
        (fun i _ => hfixed i)
    change Supermartingale
      (fun n ω => ∑ i ∈ (Finset.univ : Finset ι),
        prior i * subGammaExponentialProcess (X i) sigma2 b lam n ω) ℱ μ
    exact hsum
  · intro n ω
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (hprior.nonneg i) (Real.exp_pos _).le

/-! ### Ville crossing and PAC-Bayes inversion -/

omit [DecidableEq ι] [Nonempty ι] in
/-- Countable-time Ville bound for the finite PAC-Bayes prior-mixture process. -/
theorem timeUniformPACBayes_crossing_bound
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {X : ι → ℕ → Ω → ℝ} {sigma2 b lam delta : ℝ}
    (hδ : 0 < delta)
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : ∀ i k, Measurable (X i k))
    (hX_int : ∀ i k, Integrable (X i k) μ)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (h_integrable :
      ∀ i n, Integrable (subGammaExponentialProcess (X i) sigma2 b lam n) μ)
    (hbound : ∀ i k, ∀ᵐ ω ∂μ, |X i k ω| ≤ b)
    (hcenter : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ i k, μ[fun ω => (X i k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    μ.real {ω | ∃ n : ℕ, 0 < n ∧
      (1 / delta) ≤ pacBayesPriorMixtureProcess prior X sigma2 b lam n ω} ≤ delta := by
  obtain ⟨hsup, hnonneg⟩ :=
    pacBayesPriorMixture_supermartingale
      (μ := μ) (ℱ := ℱ) hprior hb hσ hlam hblam
      hX_meas hX_int hX_adapted h_integrable hbound hcenter hvar
  have ha : 0 < 1 / delta := one_div_pos.mpr hδ
  have hville :=
    ville_atTop_maximal_ineq
      (μ := μ) (𝒢 := ℱ)
      (M := pacBayesPriorMixtureProcess prior X sigma2 b lam)
      hsup hnonneg ha
  have hM0 :
      ∫ ω, pacBayesPriorMixtureProcess prior X sigma2 b lam 0 ω ∂μ = 1 := by
    have hbody :
        (fun ω => pacBayesPriorMixtureProcess prior X sigma2 b lam 0 ω) =ᵐ[μ]
          fun _ => (1 : ℝ) :=
      Filter.Eventually.of_forall fun ω =>
        pacBayesPriorMixtureProcess_zero prior hprior.toIsPMF X sigma2 b lam ω
    rw [integral_congr_ae hbody]
    simp [integral_const]
  rw [hM0] at hville
  have h_atTop :
      μ.real (atTopCrossingEvent
        (pacBayesPriorMixtureProcess prior X sigma2 b lam) (1 / delta)) ≤ delta := by
    calc
      μ.real (atTopCrossingEvent
          (pacBayesPriorMixtureProcess prior X sigma2 b lam) (1 / delta))
          = delta *
            ((1 / delta) *
              μ.real (atTopCrossingEvent
                (pacBayesPriorMixtureProcess prior X sigma2 b lam) (1 / delta))) := by
              field_simp [hδ.ne']
      _ ≤ delta * 1 := mul_le_mul_of_nonneg_left hville hδ.le
      _ = delta := by ring
  have hsubset :
      {ω | ∃ n : ℕ, 0 < n ∧
        (1 / delta) ≤ pacBayesPriorMixtureProcess prior X sigma2 b lam n ω}
        ⊆
      atTopCrossingEvent (pacBayesPriorMixtureProcess prior X sigma2 b lam) (1 / delta) := by
    intro ω hω
    rcases hω with ⟨n, _hn, hcross⟩
    exact ⟨n, hcross⟩
  exact (measureReal_mono hsubset).trans h_atTop

/-- Posterior time-uniform fixed-tilt PAC-Bayes upper-failure event. -/
def timeUniformPACBayesUpperFailure
    (prior posterior : ι → ℝ) (X : ι → ℕ → Ω → ℝ)
    (sigma2 b lam delta : ℝ) : Set Ω :=
  {ω | ∃ n : ℕ, 0 < n ∧
    subGammaCgf sigma2 b lam / lam
      + (klDiv posterior prior + Real.log (1 / delta)) / ((n : ℝ) * lam)
      ≤ posteriorAverage posterior (fun i => runningMean (X i) n ω)}

/-- Bad event that the time-uniform PAC-Bayes boundary fails for some posterior.

Unlike `timeUniformPACBayesUpperFailure`, which fixes the posterior before
forming the event, this event quantifies over every posterior PMF on the finite
hypothesis class. Its complement is therefore a single sample event on which
the bound holds simultaneously for every time and every posterior, including a
posterior selected after observing the sample path. -/
def timeUniformPACBayesAnyPosteriorUpperFailure
    (prior : ι → ℝ) (X : ι → ℕ → Ω → ℝ)
    (sigma2 b lam delta : ℝ) : Set Ω :=
  {ω | ∃ posterior : ι → ℝ,
    IsPMF posterior ∧
      ω ∈ timeUniformPACBayesUpperFailure prior posterior X sigma2 b lam delta}

omit [DecidableEq ι] in
private theorem pacBayesPriorMixtureProcess_pos
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (X : ι → ℕ → Ω → ℝ) (sigma2 b lam : ℝ) (n : ℕ) (ω : Ω) :
    0 < pacBayesPriorMixtureProcess prior X sigma2 b lam n ω := by
  classical
  unfold pacBayesPriorMixtureProcess
  apply Finset.sum_pos
  · intro i _
    exact mul_pos (hprior.pos i) (Real.exp_pos _)
  · exact Finset.univ_nonempty

omit [DecidableEq ι] in
/--
DV inversion: a posterior-boundary failure forces the prior-mixture
supermartingale to cross `1 / delta`.
-/
theorem timeUniformPACBayesUpperFailure_subset_crossing
    {prior posterior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (hposterior : IsPMF posterior)
    {X : ι → ℕ → Ω → ℝ} {sigma2 b lam delta : ℝ}
    (hδ : 0 < delta) (hlam : 0 < lam) :
    timeUniformPACBayesUpperFailure prior posterior X sigma2 b lam delta
      ⊆
    {ω | ∃ n : ℕ, 0 < n ∧
      (1 / delta) ≤ pacBayesPriorMixtureProcess prior X sigma2 b lam n ω} := by
  classical
  intro ω hω
  rcases hω with ⟨n, hn_pos, hfail⟩
  refine ⟨n, hn_pos, ?_⟩
  set M : ℝ := pacBayesPriorMixtureProcess prior X sigma2 b lam n ω with hM_def
  have hM_pos : 0 < M := by
    rw [hM_def]
    exact pacBayesPriorMixtureProcess_pos hprior X sigma2 b lam n ω
  set avg : ℝ := posteriorAverage posterior (fun i => runningMean (X i) n ω) with havg_def
  set cgf : ℝ := subGammaCgf sigma2 b lam with hcgf_def
  have hn_cast_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hden_pos : 0 < (n : ℝ) * lam := mul_pos hn_cast_pos hlam
  have hfail_mul :
      (n : ℝ) * cgf + klDiv posterior prior + Real.log (1 / delta)
        ≤ (n : ℝ) * lam * avg := by
    have hmul := mul_le_mul_of_nonneg_left hfail hden_pos.le
    rw [havg_def, hcgf_def] at hmul
    field_simp [hlam.ne', ne_of_gt hn_cast_pos] at hmul
    nlinarith
  have hdv :=
    posterior_change_of_measure hposterior hprior
      (fun i : ι =>
        lam * runningSum (X i) n ω - (n : ℝ) * cgf)
  have hsum_eq :
      posteriorAverage posterior
          (fun i : ι => lam * runningSum (X i) n ω - (n : ℝ) * cgf)
        = (n : ℝ) * lam * avg - (n : ℝ) * cgf := by
    unfold posteriorAverage
    rw [havg_def]
    unfold posteriorAverage runningMean
    rw [show
        (∑ i : ι, posterior i *
          (lam * runningSum (X i) n ω - (n : ℝ) * cgf))
          =
        (∑ i : ι,
          (posterior i * (lam * runningSum (X i) n ω)
            - posterior i * ((n : ℝ) * cgf))) from by
          apply Finset.sum_congr rfl
          intro i _
          ring]
    rw [Finset.sum_sub_distrib]
    have hleft :
        ∑ i : ι, posterior i * (lam * runningSum (X i) n ω)
          = (n : ℝ) * lam *
              ∑ i : ι, posterior i * (runningSum (X i) n ω / (n : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [ne_of_gt hn_cast_pos]
    have hright :
        ∑ i : ι, posterior i * ((n : ℝ) * cgf) = (n : ℝ) * cgf := by
      rw [← Finset.sum_mul, hposterior.sum_one, one_mul]
    rw [hleft, hright]
  have hmoment_eq :
      (∑ i : ι, prior i *
        Real.exp (lam * runningSum (X i) n ω - (n : ℝ) * cgf)) = M := by
    rw [hM_def]
    rfl
  rw [hsum_eq, hmoment_eq] at hdv
  have hlog_le : Real.log (1 / delta) ≤ Real.log M := by
    linarith
  have hdelta_inv_pos : 0 < 1 / delta := one_div_pos.mpr hδ
  exact (Real.log_le_log_iff hdelta_inv_pos hM_pos).mp hlog_le

omit [DecidableEq ι] in
/-- A failure for any posterior forces the common prior-mixture process to cross. -/
theorem timeUniformPACBayesAnyPosteriorUpperFailure_subset_crossing
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {X : ι → ℕ → Ω → ℝ} {sigma2 b lam delta : ℝ}
    (hδ : 0 < delta) (hlam : 0 < lam) :
    timeUniformPACBayesAnyPosteriorUpperFailure prior X sigma2 b lam delta
      ⊆
    {ω | ∃ n : ℕ, 0 < n ∧
      (1 / delta) ≤ pacBayesPriorMixtureProcess prior X sigma2 b lam n ω} := by
  intro ω hω
  rcases hω with ⟨posterior, hposterior, hfail⟩
  exact timeUniformPACBayesUpperFailure_subset_crossing
    hprior hposterior hδ hlam hfail

omit [DecidableEq ι] in
/--
Time-uniform fixed-tilt PAC-Bayes bound. With probability at least `1 - δ`,
simultaneously for every `n >= 1`, the posterior running-mean gap is at most

`cgf(λ) / λ + (KL(Q || P) + log(1/δ)) / (n λ)`.
-/
theorem timeUniformPACBayes_bound
    [IsProbabilityMeasure μ]
    {prior posterior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (hposterior : IsPMF posterior)
    {X : ι → ℕ → Ω → ℝ} {sigma2 b lam delta : ℝ}
    (hδ : 0 < delta)
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : ∀ i k, Measurable (X i k))
    (hX_int : ∀ i k, Integrable (X i k) μ)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (h_integrable :
      ∀ i n, Integrable (subGammaExponentialProcess (X i) sigma2 b lam n) μ)
    (hbound : ∀ i k, ∀ᵐ ω ∂μ, |X i k ω| ≤ b)
    (hcenter : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ i k, μ[fun ω => (X i k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    μ.real (timeUniformPACBayesUpperFailure prior posterior X sigma2 b lam delta)
      ≤ delta := by
  exact (measureReal_mono
    (timeUniformPACBayesUpperFailure_subset_crossing
      (Ω := Ω) hprior hposterior (X := X) (sigma2 := sigma2) (b := b)
      (lam := lam) (delta := delta) hδ hlam)).trans
    (timeUniformPACBayes_crossing_bound
      (μ := μ) (ℱ := ℱ) hprior hδ hb hσ hlam hblam
      hX_meas hX_int hX_adapted h_integrable hbound hcenter hvar)

omit [DecidableEq ι] in
/-- Time-uniform fixed-tilt PAC-Bayes bound, simultaneous over all posteriors.

With probability at least `1 - δ`, the fixed-tilt boundary holds for every
positive time and every posterior PMF on the finite hypothesis class. Because
the exceptional event already quantifies over all posteriors, the posterior may
be selected from the observed sample path; no separate union bound over
posteriors is needed. -/
theorem timeUniformPACBayes_allPosteriors_bound
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {X : ι → ℕ → Ω → ℝ} {sigma2 b lam delta : ℝ}
    (hδ : 0 < delta)
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : ∀ i k, Measurable (X i k))
    (hX_int : ∀ i k, Integrable (X i k) μ)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (h_integrable :
      ∀ i n, Integrable (subGammaExponentialProcess (X i) sigma2 b lam n) μ)
    (hbound : ∀ i k, ∀ᵐ ω ∂μ, |X i k ω| ≤ b)
    (hcenter : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ i k, μ[fun ω => (X i k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    μ.real (timeUniformPACBayesAnyPosteriorUpperFailure
      prior X sigma2 b lam delta) ≤ delta := by
  exact (measureReal_mono
    (timeUniformPACBayesAnyPosteriorUpperFailure_subset_crossing
      (Ω := Ω) hprior (X := X) (sigma2 := sigma2) (b := b)
      (lam := lam) (delta := delta) hδ hlam)).trans
    (timeUniformPACBayes_crossing_bound
      (μ := μ) (ℱ := ℱ) hprior hδ hb hσ hlam hblam
      hX_meas hX_int hX_adapted h_integrable hbound hcenter hvar)

/-! ### Concrete nonzero witness -/

/-- Uniform probability measure on `Bool`. -/
def μBool : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance : IsProbabilityMeasure μBool := by
  refine ⟨?_⟩
  simp only [μBool, Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact ENNReal.add_halves 1

/-- Uniform prior over two hypotheses. -/
def twoHypPrior : Fin 2 → ℝ := fun _ => (1 : ℝ) / 2

/-- Uniform posterior over two hypotheses. -/
def twoHypPosterior : Fin 2 → ℝ := fun _ => (1 : ℝ) / 2

/-- Two-level filtration: `F 0 = bottom`, `F k = top` for `k >= 1`. -/
def boolDelayFiltration : Filtration ℕ (⊤ : MeasurableSpace Bool) where
  seq := fun k => if k = 0 then ⊥ else ⊤
  mono' := by
    intro i j hij
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · simp [hi, hj]
      · simp only [hi, hj]; exact bot_le
    · have hj : j ≠ 0 := by
        rintro rfl; exact hi (Nat.le_zero.mp hij)
      simp [hi, hj]
  le' := by
    intro i
    by_cases hi : i = 0
    · simp only [hi]; exact bot_le
    · simp [hi]

/-- Nonzero Rademacher-style increments for a finite two-hypothesis class. -/
def rademacherHypGap : Fin 2 → ℕ → Bool → ℝ :=
  fun i k ω =>
    if k = 0 then
      if i = 0 then (if ω then (1 : ℝ) else -1)
      else (if ω then (-1 : ℝ) else 1)
    else 0

theorem twoHypPrior_isFullSupportPMF : IsFullSupportPMF twoHypPrior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> norm_num [twoHypPrior]
  · simp [twoHypPrior]
  · intro i
    fin_cases i <;> norm_num [twoHypPrior]

theorem twoHypPosterior_isPMF : IsPMF twoHypPosterior := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [twoHypPosterior]
  · simp [twoHypPosterior]

theorem rademacherHypGap_nonzero :
    rademacherHypGap 0 0 true = 1 ∧ rademacherHypGap 0 0 false = -1 := by
  constructor <;> norm_num [rademacherHypGap]

/--
Concrete all-posterior witness: two hypotheses, a uniform prior, and a nonzero
Rademacher-style first increment give a numeric time-uniform PAC-Bayes bound
simultaneously over every posterior at `δ = 1/2`, `λ = 1/2`, `b = σ² = 1`.
-/
theorem rademacher_timeUniformPACBayes_allPosteriors_witness :
    (μBool).real
      (timeUniformPACBayesAnyPosteriorUpperFailure
        twoHypPrior rademacherHypGap 1 1 (1 / 2) (1 / 2))
      ≤ (1 / 2 : ℝ) := by
  refine timeUniformPACBayes_allPosteriors_bound
    (μ := μBool) (ℱ := boolDelayFiltration)
    (prior := twoHypPrior)
    (X := rademacherHypGap)
    (sigma2 := 1) (b := 1) (lam := 1 / 2) (delta := 1 / 2)
    twoHypPrior_isFullSupportPMF
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i k
    exact measurable_from_top
  · intro i k
    exact Integrable.of_finite
  · intro i k
    have hk : boolDelayFiltration (k + 1) = ⊤ := by
      simp [boolDelayFiltration]
    rw [show (StronglyMeasurable[boolDelayFiltration (k + 1)] (rademacherHypGap i k)) =
        (StronglyMeasurable[⊤] (rademacherHypGap i k)) from by rw [hk]]
    exact (measurable_from_top).stronglyMeasurable
  · intro i n
    exact Integrable.of_finite
  · intro i k
    refine Filter.Eventually.of_forall ?_
    intro ω
    simp only [rademacherHypGap]
    by_cases hk : k = 0
    · subst hk
      fin_cases i <;> cases ω <;> norm_num
    · simp only [if_neg hk]
      norm_num
  · intro i k
    by_cases hk : k = 0
    · subst hk
      have hℱ0 : boolDelayFiltration 0 = ⊥ := by simp [boolDelayFiltration]
      rw [hℱ0, condExp_bot]
      have hint : ∫ x, rademacherHypGap i 0 x ∂μBool = 0 := by
        haveI : IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac (true : Bool)) :=
          Measure.smul_finite _ (by norm_num)
        haveI : IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac (false : Bool)) :=
          Measure.smul_finite _ (by norm_num)
        rw [μBool, integral_add_measure (Integrable.of_finite) (Integrable.of_finite),
          integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
        fin_cases i <;> simp only [rademacherHypGap, smul_eq_mul] <;> norm_num
      rw [hint]
      rfl
    · have hXk : rademacherHypGap i k = 0 := by
        funext ω
        simp [rademacherHypGap, hk]
      rw [hXk, condExp_zero]
  · intro i k
    by_cases hk : k = 0
    · subst hk
      have hsq : (fun ω => (rademacherHypGap i 0 ω) ^ 2) = (fun _ : Bool => (1 : ℝ)) := by
        funext ω
        fin_cases i <;> cases ω <;> norm_num [rademacherHypGap]
      rw [hsq, condExp_const (boolDelayFiltration.le 0)]
    · have hXk : rademacherHypGap i k = 0 := by
        funext ω
        simp [rademacherHypGap, hk]
      have hsq : (fun ω => (rademacherHypGap i k ω) ^ 2) = (0 : Bool → ℝ) := by
        funext ω
        simp [hXk]
      rw [hsq, condExp_zero]
      exact Filter.Eventually.of_forall (by intro ω; norm_num)

/-- Fixed-posterior specialization of the all-posterior Rademacher witness. -/
theorem rademacher_timeUniformPACBayes_witness :
    (μBool).real
      (timeUniformPACBayesUpperFailure
        twoHypPrior twoHypPosterior rademacherHypGap 1 1 (1 / 2) (1 / 2))
      ≤ (1 / 2 : ℝ) := by
  refine (measureReal_mono ?_).trans
    rademacher_timeUniformPACBayes_allPosteriors_witness
  intro ω hω
  exact ⟨twoHypPosterior, twoHypPosterior_isPMF, hω⟩

end

end FormalSLT.PACBayes.TimeUniform
