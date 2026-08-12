/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.EProcess
import FormalSLT.AnytimeValid.AtTopCS
import FormalSLT.PACBayesKL
import FormalSLT.PACBayes.TimeUniformPACBayes

/-!
# Generic time-uniform score PAC-Bayes compiler

This module factors the finite-hypothesis Ville--Donsker--Varadhan mechanism
away from any particular concentration model. Each hypothesis supplies a score
whose exponential is an e-process. Mixing those e-processes against a
full-support prior gives one e-process, so one countable-time Ville event
controls every time and every finite posterior.

The final theorem is a compiler, not an i.i.d. or loss-specific generalization
bound. A separate adapter transfers the score inequality to a posterior target
when a deterministic regret term bounds the pointwise target-to-score gap.
No posterior kernel, continuous hypothesis space, coin-betting construction, or
post-hoc continuous tuning is claimed here.
-/

open MeasureTheory ProbabilityTheory Finset Real BigOperators
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL

namespace FormalSLT.PACBayes.TimeUniformScore

noncomputable section

variable {ι Ω : Type*} [Fintype ι] [Nonempty ι]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ mΩ}

/-- Prior-weighted finite mixture of exponentiated hypothesis scores. -/
def scorePriorMixtureProcess
    (prior : ι → ℝ) (score : ι → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i : ι, prior i * Real.exp (score i n ω)

omit [Nonempty ι] in
/-- A full-support prior mixture of score e-processes is itself an e-process. -/
theorem scorePriorMixture_eProcess [IsFiniteMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {score : ι → ℕ → Ω → ℝ}
    (hscore : ∀ i, EProcess μ ℱ (fun n ω => Real.exp (score i n ω))) :
    EProcess μ ℱ (scorePriorMixtureProcess prior score) where
  nonneg := by
    intro n ω
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (hprior.nonneg i) (Real.exp_pos _).le
  start_one := by
    intro ω
    calc
      scorePriorMixtureProcess prior score 0 ω
          = ∑ i : ι, prior i * 1 := by
              apply Finset.sum_congr rfl
              intro i _
              rw [(hscore i).start_one ω]
      _ = 1 := by simpa using hprior.sum_one
  supermartingale := by
    have hfixed : ∀ i : ι,
        Supermartingale (fun n ω => prior i * Real.exp (score i n ω)) ℱ μ := by
      intro i
      have hscaled := (hscore i).supermartingale.smul_nonneg
        (c := prior i) (hprior.nonneg i)
      change Supermartingale (prior i • fun n ω => Real.exp (score i n ω)) ℱ μ
      exact hscaled
    have hsum :=
      FormalSLT.PACBayes.TimeUniform.supermartingale_finset_sum_index
        (Finset.univ : Finset ι)
        (fun i n ω => prior i * Real.exp (score i n ω))
        (fun i _ => hfixed i)
    change Supermartingale
      (fun n ω => ∑ i : ι, prior i * Real.exp (score i n ω)) ℱ μ
    exact hsum

/-- Failure of the score PAC-Bayes inequality at some time and posterior. -/
def timeUniformScorePACBayesAnyPosteriorFailure
    (prior : ι → ℝ) (score : ι → ℕ → Ω → ℝ) (delta : ℝ) : Set Ω :=
  {ω | ∃ n : ℕ, ∃ posterior : ι → ℝ,
    IsPMF posterior ∧
      klDiv posterior prior + Real.log (1 / delta)
        ≤ posteriorAverage posterior (fun i => score i n ω)}

private theorem scorePriorMixtureProcess_pos
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (score : ι → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 < scorePriorMixtureProcess prior score n ω := by
  classical
  unfold scorePriorMixtureProcess
  apply Finset.sum_pos
  · intro i _
    exact mul_pos (hprior.pos i) (Real.exp_pos _)
  · exact Finset.univ_nonempty

/-- A score PAC-Bayes failure forces the common prior mixture to cross `1 / delta`. -/
theorem timeUniformScorePACBayesAnyPosteriorFailure_subset_crossing
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {score : ι → ℕ → Ω → ℝ} {delta : ℝ} (hdelta : 0 < delta) :
    timeUniformScorePACBayesAnyPosteriorFailure prior score delta
      ⊆ atTopCrossingEvent (scorePriorMixtureProcess prior score) (1 / delta) := by
  classical
  intro ω hω
  rcases hω with ⟨n, posterior, hposterior, hfail⟩
  refine ⟨n, ?_⟩
  have hdv := donsker_varadhan hposterior hprior (fun i => score i n ω)
  have hdv' :
      posteriorAverage posterior (fun i => score i n ω)
        ≤ klDiv posterior prior
          + Real.log (scorePriorMixtureProcess prior score n ω) := by
    simpa [posteriorAverage, scorePriorMixtureProcess] using hdv
  have hlog_le :
      Real.log (1 / delta)
        ≤ Real.log (scorePriorMixtureProcess prior score n ω) := by
    linarith
  have hinv_pos : 0 < (1 : ℝ) / delta := one_div_pos.mpr hdelta
  have hmix_pos := scorePriorMixtureProcess_pos hprior score n ω
  exact (Real.log_le_log_iff hinv_pos hmix_pos).mp hlog_le

/--
Generic finite-hypothesis time-uniform score PAC-Bayes compiler.

If every exponentiated score is an e-process, then with failure mass at most
`delta`, simultaneously for every time and every posterior,

`posteriorAverage posterior score < KL(posterior || prior) + log (1 / delta)`.
-/
theorem timeUniformScorePACBayes_allPosteriors_bound
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {score : ι → ℕ → Ω → ℝ}
    (hscore : ∀ i, EProcess μ ℱ (fun n ω => Real.exp (score i n ω)))
    {delta : ℝ} (hdelta : 0 < delta) :
    μ.real (timeUniformScorePACBayesAnyPosteriorFailure prior score delta)
      ≤ delta := by
  have hmix := scorePriorMixture_eProcess hprior hscore
  have hthreshold : 0 < (1 : ℝ) / delta := one_div_pos.mpr hdelta
  have hville := ville_atTop_maximal_ineq
    hmix.supermartingale hmix.nonneg hthreshold
  rw [hmix.integral_start_eq_one] at hville
  have hcrossing :
      μ.real (atTopCrossingEvent
        (scorePriorMixtureProcess prior score) (1 / delta)) ≤ delta := by
    calc
      μ.real (atTopCrossingEvent
          (scorePriorMixtureProcess prior score) (1 / delta))
          = delta * ((1 / delta) *
              μ.real (atTopCrossingEvent
                (scorePriorMixtureProcess prior score) (1 / delta))) := by
              field_simp [hdelta.ne']
      _ ≤ delta * 1 := mul_le_mul_of_nonneg_left hville hdelta.le
      _ = delta := by ring
  exact (measureReal_mono
    (timeUniformScorePACBayesAnyPosteriorFailure_subset_crossing
      hprior hdelta)).trans hcrossing

omit [Nonempty ι] in
/--
On the compiler's common good event, a deterministic pointwise regret bound
transfers the posterior score inequality to any posterior target.
-/
theorem posteriorTarget_le_of_not_mem_timeUniformScorePACBayesFailure
    {prior : ι → ℝ} {score target : ι → ℕ → Ω → ℝ}
    {regret : ℕ → ℝ} {delta : ℝ} {ω : Ω}
    (hgood :
      ω ∉ timeUniformScorePACBayesAnyPosteriorFailure prior score delta)
    {posterior : ι → ℝ} (hposterior : IsPMF posterior) (n : ℕ)
    (hregret : ∀ i, target i n ω ≤ score i n ω + regret n) :
    posteriorAverage posterior (fun i => target i n ω)
      ≤ klDiv posterior prior + Real.log (1 / delta) + regret n := by
  have hscore_le :
      posteriorAverage posterior (fun i => score i n ω)
        ≤ klDiv posterior prior + Real.log (1 / delta) := by
    apply le_of_lt
    by_contra hnot
    have hfailure :
        klDiv posterior prior + Real.log (1 / delta)
          ≤ posteriorAverage posterior (fun i => score i n ω) :=
      le_of_not_gt hnot
    exact hgood ⟨n, posterior, hposterior, hfailure⟩
  have htarget_le :
      posteriorAverage posterior (fun i => target i n ω)
        ≤ posteriorAverage posterior (fun i => score i n ω) + regret n := by
    unfold posteriorAverage
    calc
      ∑ i : ι, posterior i * target i n ω
          ≤ ∑ i : ι, posterior i * (score i n ω + regret n) := by
              apply Finset.sum_le_sum
              intro i _
              exact mul_le_mul_of_nonneg_left (hregret i) (hposterior.nonneg i)
      _ = ∑ i : ι, posterior i * score i n ω + regret n := by
              simp_rw [mul_add]
              rw [Finset.sum_add_distrib, ← Finset.sum_mul, hposterior.sum_one, one_mul]
  have hscore_regret := add_le_add_right hscore_le (regret n)
  exact htarget_le.trans (by simpa [add_comm] using hscore_regret)

end

end FormalSLT.PACBayes.TimeUniformScore
