/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayes.TimeUniformTiltMixture
import FormalSLT.PACBayes.TimeUniformIID

/-!
# Time-uniform IID PAC-Bayes from one weighted hypothesis--tilt e-process

This module specializes the finite weighted master e-process from
`TimeUniformTiltMixture` to measurable `[0,1]` losses on an i.i.d. stream.
Outside one measurable exceptional event of probability at most `delta`, the
PAC-Bayes generalization bound holds simultaneously for every positive time,
every posterior PMF, and every tilt in the declared finite family.

The hypothesis and tilt types are finite, both priors have full support, and
every declared tilt is positive and strictly below three. The posterior and
selected tilt atom may both depend on the observed path. Entry `j` pays the
exact prior-weight cost
`log (1 / (delta * weight j))`.  The proof derives this cost from one master
e-process without proving entrywise probability bounds or invoking a finite
union bound. It does not establish a countable mixture, all-real optimization,
an arbitrary joint posterior on hypothesis--tilt pairs, or an
empirical-variance boundary.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open Finset Real BigOperators

namespace FormalSLT.PACBayes.TimeUniformIIDTiltMixture

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

open FormalSLT.PACBayes.TimeUniform
open FormalSLT.PACBayes.TimeUniformIID

variable {ι κ Z Ω : Type*}
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]

/--
Failure of the weighted-tilt IID PAC-Bayes bound for some declared tilt,
posterior, and positive time.
-/
def timeUniformIIDPACBayesTiltMixtureAnyPosteriorUpperFailure
    [MeasurableSpace Z]
    (dataLaw : Measure Z) (prior : ι → ℝ) (weight : κ → ℝ)
    (loss : ι → Z → ℝ) (sample : ℕ → Ω → Z)
    (lam : κ → ℝ) (delta : ℝ) : Set Ω :=
  {ω | ∃ j : κ, ∃ posterior : ι → ℝ,
    IsPMF posterior ∧
      ∃ n : ℕ, 0 < n ∧
        subGammaCgf 1 1 (lam j) / lam j +
            (klDiv posterior prior +
              Real.log (1 / (delta * weight j))) /
                ((n : ℝ) * lam j)
          ≤ iidPosteriorPopulationRisk dataLaw loss posterior -
              iidPosteriorEmpiricalRisk loss sample posterior n ω}

/-- A measurable hull of the raw posterior/tilt-existential failure set. -/
def timeUniformIIDPACBayesTiltMixtureMeasurableExceptionalEvent
    [MeasurableSpace Z] [MeasurableSpace Ω]
    (μ : Measure Ω) (dataLaw : Measure Z)
    (prior : ι → ℝ) (weight : κ → ℝ)
    (loss : ι → Z → ℝ) (sample : ℕ → Ω → Z)
    (lam : κ → ℝ) (delta : ℝ) : Set Ω :=
  toMeasurable μ
    (timeUniformIIDPACBayesTiltMixtureAnyPosteriorUpperFailure
      dataLaw prior weight loss sample lam delta)

omit [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] [Nonempty κ] in
/-- The measurable exceptional event is measurable by construction. -/
theorem timeUniformIIDPACBayesTiltMixtureMeasurableExceptionalEvent_measurable
    [MeasurableSpace Z] [MeasurableSpace Ω]
    (μ : Measure Ω) (dataLaw : Measure Z)
    (prior : ι → ℝ) (weight : κ → ℝ)
    (loss : ι → Z → ℝ) (sample : ℕ → Ω → Z)
    (lam : κ → ℝ) (delta : ℝ) :
    MeasurableSet
      (timeUniformIIDPACBayesTiltMixtureMeasurableExceptionalEvent
        μ dataLaw prior weight loss sample lam delta) :=
  measurableSet_toMeasurable _ _

omit [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] [Nonempty κ] in
/-- The measurable hull contains every raw posterior/tilt failure. -/
theorem timeUniformIIDPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_measurableExceptionalEvent
    [MeasurableSpace Z] [MeasurableSpace Ω]
    (μ : Measure Ω) (dataLaw : Measure Z)
    (prior : ι → ℝ) (weight : κ → ℝ)
    (loss : ι → Z → ℝ) (sample : ℕ → Ω → Z)
    (lam : κ → ℝ) (delta : ℝ) :
    timeUniformIIDPACBayesTiltMixtureAnyPosteriorUpperFailure
        dataLaw prior weight loss sample lam delta
      ⊆
    timeUniformIIDPACBayesTiltMixtureMeasurableExceptionalEvent
      μ dataLaw prior weight loss sample lam delta :=
  subset_toMeasurable _ _

omit [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] [Nonempty κ] in
/-- The concrete IID failure event is contained in the master process event. -/
theorem timeUniformIIDPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_processFailure
    [MeasurableSpace Z]
    {dataLaw : Measure Z} {prior : ι → ℝ} {weight : κ → ℝ}
    {loss : ι → Z → ℝ} {sample : ℕ → Ω → Z}
    {lam : κ → ℝ} {delta : ℝ} :
    timeUniformIIDPACBayesTiltMixtureAnyPosteriorUpperFailure
        dataLaw prior weight loss sample lam delta
      ⊆
    timeUniformPACBayesTiltMixtureAnyPosteriorUpperFailure
      prior weight (iidLossGap dataLaw loss sample) 1 1 lam delta := by
  intro ω hω
  rcases hω with ⟨j, posterior, hposterior, n, hn, hfailure⟩
  refine ⟨j, posterior, hposterior, n, hn, ?_⟩
  rw [posteriorAverage_iidLossGap_runningMean
    dataLaw loss sample posterior hn ω]
  exact hfailure

omit [DecidableEq ι] [DecidableEq κ] [Nonempty κ] in
/--
Outer-probability IID PAC-Bayes bound obtained from one weighted
hypothesis--tilt master e-process.
-/
theorem timeUniformIIDPACBayes_tiltMixture_allPosteriors_bound
    [mZ : MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [TopologicalSpace.MetrizableSpace Z]
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {dataLaw : Measure Z} [IsProbabilityMeasure dataLaw]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {loss : ι → Z → ℝ} {sample : ℕ → Ω → Z}
    {lam : κ → ℝ} {delta : ℝ}
    (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_three : ∀ j, lam j < 3)
    (hloss : ∀ i, StronglyMeasurable (loss i))
    (hloss_range : ∀ i z, 0 ≤ loss i z ∧ loss i z ≤ 1)
    (hsample : ∀ k, StronglyMeasurable (sample k))
    (hsample_indep : iIndepFun sample μ)
    (hsample_law : ∀ k, HasLaw (sample k) dataLaw μ) :
    μ.real (timeUniformIIDPACBayesTiltMixtureAnyPosteriorUpperFailure
      dataLaw prior weight loss sample lam delta) ≤ delta := by
  let ℱ : Filtration ℕ mΩ := Filtration.natural sample hsample
  let X : ι → ℕ → Ω → ℝ := iidLossGap dataLaw loss sample
  have hX_meas : ∀ i k, Measurable (X i k) := by
    intro i k
    exact iidLossGap_measurable i k (hloss i) hsample
  have hbound : ∀ i k, ∀ᵐ ω ∂μ, |X i k ω| ≤ (1 : ℝ) := by
    intro i k
    exact Filter.Eventually.of_forall fun ω =>
      abs_iidLossGap_le_one i k ω (hloss i) (hloss_range i)
  have hX_int : ∀ i k, Integrable (X i k) μ := by
    intro i k
    exact iidLossGap_integrable i k (hloss i) (hloss_range i) hsample
  have hX_adapted : ∀ i, IncrementAdapted ℱ (X i) := by
    intro i
    exact iidLossGap_incrementAdapted i (hloss i) hsample
  have hcenter : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] 0 := by
    intro i k
    exact iidLossGap_condExp_eq_zero i k (hloss i) (hloss_range i)
      hsample hsample_indep hsample_law
  have hvar : ∀ i k,
      μ[fun ω => (X i k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => (1 : ℝ) := by
    intro i k
    exact iidLossGap_condExp_sq_le_one i k
      (hloss i) (hloss_range i) hsample
  have h_integrable : ∀ i j n,
      Integrable (subGammaExponentialProcess (X i) 1 1 (lam j) n) μ := by
    intro i j n
    exact integrable_subGammaExponentialProcess_of_bounded n
      (by norm_num) (by norm_num) (hlam j).le
      (by simpa using hlam_three j) (hX_meas i) (hbound i)
  exact (measureReal_mono
    (timeUniformIIDPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_processFailure
      (dataLaw := dataLaw) (prior := prior) (weight := weight)
      (loss := loss) (sample := sample) (lam := lam) (delta := delta))).trans
    (timeUniformPACBayes_tiltMixture_allPosteriors_bound
      (μ := μ) (ℱ := ℱ) hprior hweight hdelta
      (by norm_num) (by norm_num) hlam (by simpa using hlam_three)
      hX_meas hX_int hX_adapted h_integrable hbound hcenter hvar)

omit [DecidableEq ι] [DecidableEq κ] [Nonempty κ] in
/--
Ordinary-probability specification of the measurable IID exceptional event.
-/
theorem timeUniformIIDPACBayes_tiltMixture_measurableExceptionalEvent_spec
    [mZ : MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [TopologicalSpace.MetrizableSpace Z]
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {dataLaw : Measure Z} [IsProbabilityMeasure dataLaw]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {loss : ι → Z → ℝ} {sample : ℕ → Ω → Z}
    {lam : κ → ℝ} {delta : ℝ}
    (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_three : ∀ j, lam j < 3)
    (hloss : ∀ i, StronglyMeasurable (loss i))
    (hloss_range : ∀ i z, 0 ≤ loss i z ∧ loss i z ≤ 1)
    (hsample : ∀ k, StronglyMeasurable (sample k))
    (hsample_indep : iIndepFun sample μ)
    (hsample_law : ∀ k, HasLaw (sample k) dataLaw μ) :
    MeasurableSet
        (timeUniformIIDPACBayesTiltMixtureMeasurableExceptionalEvent
          μ dataLaw prior weight loss sample lam delta) ∧
      timeUniformIIDPACBayesTiltMixtureAnyPosteriorUpperFailure
          dataLaw prior weight loss sample lam delta
        ⊆ timeUniformIIDPACBayesTiltMixtureMeasurableExceptionalEvent
          μ dataLaw prior weight loss sample lam delta ∧
      μ.real (timeUniformIIDPACBayesTiltMixtureMeasurableExceptionalEvent
        μ dataLaw prior weight loss sample lam delta) ≤ delta := by
  refine ⟨
    timeUniformIIDPACBayesTiltMixtureMeasurableExceptionalEvent_measurable
      μ dataLaw prior weight loss sample lam delta,
    timeUniformIIDPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_measurableExceptionalEvent
      μ dataLaw prior weight loss sample lam delta,
    ?_⟩
  rw [timeUniformIIDPACBayesTiltMixtureMeasurableExceptionalEvent,
    Measure.real, measure_toMeasurable]
  exact timeUniformIIDPACBayes_tiltMixture_allPosteriors_bound
    (μ := μ) (dataLaw := dataLaw) hprior hweight hdelta
    hlam hlam_three hloss hloss_range hsample hsample_indep hsample_law

omit [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] [Nonempty κ] in
/--
Outside the measurable exceptional event, every declared tilt, posterior, and
positive time satisfies the weighted master-mixture boundary.
-/
theorem timeUniformIIDPACBayes_tiltMixture_allPosteriors_of_not_mem_measurableExceptionalEvent
    [MeasurableSpace Z] [MeasurableSpace Ω]
    {μ : Measure Ω} {dataLaw : Measure Z}
    {prior : ι → ℝ} {weight : κ → ℝ}
    {loss : ι → Z → ℝ} {sample : ℕ → Ω → Z}
    {lam : κ → ℝ} {delta : ℝ} {omega : Ω}
    (homega : omega ∉
      timeUniformIIDPACBayesTiltMixtureMeasurableExceptionalEvent
        μ dataLaw prior weight loss sample lam delta) :
    ∀ j : κ, ∀ posterior : ι → ℝ, IsPMF posterior →
      ∀ n : ℕ, 0 < n →
        iidPosteriorPopulationRisk dataLaw loss posterior -
            iidPosteriorEmpiricalRisk loss sample posterior n omega <
          subGammaCgf 1 1 (lam j) / lam j +
            (klDiv posterior prior +
              Real.log (1 / (delta * weight j))) /
                ((n : ℝ) * lam j) := by
  intro j posterior hposterior n hn
  apply lt_of_not_ge
  intro hfailure
  apply homega
  apply timeUniformIIDPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_measurableExceptionalEvent
    μ dataLaw prior weight loss sample lam delta
  exact ⟨j, posterior, hposterior, n, hn, hfailure⟩

omit [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] [Nonempty κ] in
/-- Explicit path- and posterior-dependent tilt-selector corollary. -/
theorem timeUniformIIDPACBayes_tiltMixture_selected_of_not_mem_measurableExceptionalEvent
    [MeasurableSpace Z] [MeasurableSpace Ω]
    {μ : Measure Ω} {dataLaw : Measure Z}
    {prior : ι → ℝ} {weight : κ → ℝ}
    {loss : ι → Z → ℝ} {sample : ℕ → Ω → Z}
    {lam : κ → ℝ} {delta : ℝ} {omega : Ω}
    (homega : omega ∉
      timeUniformIIDPACBayesTiltMixtureMeasurableExceptionalEvent
        μ dataLaw prior weight loss sample lam delta)
    (select : Ω → (ι → ℝ) → κ)
    (posterior : ι → ℝ) (hposterior : IsPMF posterior)
    (n : ℕ) (hn : 0 < n) :
    iidPosteriorPopulationRisk dataLaw loss posterior -
        iidPosteriorEmpiricalRisk loss sample posterior n omega <
      subGammaCgf 1 1 (lam (select omega posterior)) /
          lam (select omega posterior) +
        (klDiv posterior prior +
          Real.log (1 / (delta * weight (select omega posterior)))) /
            ((n : ℝ) * lam (select omega posterior)) :=
  timeUniformIIDPACBayes_tiltMixture_allPosteriors_of_not_mem_measurableExceptionalEvent
    homega (select omega posterior) posterior hposterior n hn

end

end FormalSLT.PACBayes.TimeUniformIIDTiltMixture
