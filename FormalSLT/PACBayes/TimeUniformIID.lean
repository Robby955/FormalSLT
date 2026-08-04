/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayes.TimeUniformPACBayes
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.HasLaw

/-!
# Time-uniform PAC-Bayes for i.i.d. bounded losses

This module wires the process-level theorem in `TimeUniformPACBayes` to an
actual i.i.d. learning model.  The sample stream is independent, every
coordinate has a common law, and every hypothesis has a measurable loss in
`[0, 1]`.  The resulting exceptional event is simultaneous over every positive
time and every posterior PMF on the finite hypothesis class.

The first coordinate is used only to identify the common law.  The running
empirical risk at time `n` uses sample coordinates `1, ..., n`; this matches the
increment convention in the anytime-valid library, where increment `k` is
revealed at filtration time `k + 1` and centered against the past at time `k`.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open Finset Real BigOperators

namespace FormalSLT.PACBayes.TimeUniformIID

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {ι Z Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Population risk under the common data law. -/
def iidLossPopulationRisk [MeasurableSpace Z]
    (dataLaw : Measure Z) (loss : ι → Z → ℝ) (i : ι) : ℝ :=
  ∫ z, loss i z ∂dataLaw

/-- Running empirical risk from the first `n` revealed increments. -/
def iidLossEmpiricalRisk
    (loss : ι → Z → ℝ) (sample : ℕ → Ω → Z)
    (i : ι) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ k ∈ Finset.range n, loss i (sample (k + 1) ω)) / (n : ℝ)

/-- Posterior-averaged population risk. -/
def iidPosteriorPopulationRisk [MeasurableSpace Z]
    (dataLaw : Measure Z) (loss : ι → Z → ℝ) (posterior : ι → ℝ) : ℝ :=
  posteriorAverage posterior (iidLossPopulationRisk dataLaw loss)

/-- Posterior-averaged running empirical risk. -/
def iidPosteriorEmpiricalRisk
    (loss : ι → Z → ℝ) (sample : ℕ → Ω → Z)
    (posterior : ι → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  posteriorAverage posterior (fun i => iidLossEmpiricalRisk loss sample i n ω)

/-- Centered population-minus-observed loss increment. -/
def iidLossGap [MeasurableSpace Z]
    (dataLaw : Measure Z) (loss : ι → Z → ℝ) (sample : ℕ → Ω → Z)
    (i : ι) (k : ℕ) (ω : Ω) : ℝ :=
  iidLossPopulationRisk dataLaw loss i - loss i (sample (k + 1) ω)

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- The running mean of the centered loss increments is the generalization gap. -/
theorem iidLossGap_runningMean [MeasurableSpace Z]
    (dataLaw : Measure Z) (loss : ι → Z → ℝ) (sample : ℕ → Ω → Z)
    (i : ι) {n : ℕ} (hn : 0 < n) (ω : Ω) :
    runningMean (iidLossGap dataLaw loss sample i) n ω =
      iidLossPopulationRisk dataLaw loss i -
        iidLossEmpiricalRisk loss sample i n ω := by
  unfold iidLossGap iidLossEmpiricalRisk runningMean runningSum
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr hn.ne']

omit [DecidableEq ι] [Nonempty ι] in
/-- Posterior averaging preserves the population-minus-empirical gap identity. -/
theorem posteriorAverage_iidLossGap_runningMean [MeasurableSpace Z]
    (dataLaw : Measure Z) (loss : ι → Z → ℝ) (sample : ℕ → Ω → Z)
    (posterior : ι → ℝ) {n : ℕ} (hn : 0 < n) (ω : Ω) :
    posteriorAverage posterior
        (fun i => runningMean (iidLossGap dataLaw loss sample i) n ω) =
      iidPosteriorPopulationRisk dataLaw loss posterior -
        iidPosteriorEmpiricalRisk loss sample posterior n ω := by
  unfold iidPosteriorPopulationRisk iidPosteriorEmpiricalRisk posteriorAverage
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  change posterior i * runningMean (iidLossGap dataLaw loss sample i) n ω =
    posterior i * iidLossPopulationRisk dataLaw loss i -
      posterior i * iidLossEmpiricalRisk loss sample i n ω
  rw [iidLossGap_runningMean dataLaw loss sample i hn ω]
  ring

/-- Failure of the i.i.d. loss bound for some posterior and some time. -/
def timeUniformIIDPACBayesAnyPosteriorUpperFailure [MeasurableSpace Z]
    (dataLaw : Measure Z) (prior : ι → ℝ) (loss : ι → Z → ℝ)
    (sample : ℕ → Ω → Z) (lam delta : ℝ) : Set Ω :=
  {ω | ∃ posterior : ι → ℝ,
    IsPMF posterior ∧
      ∃ n : ℕ, 0 < n ∧
        subGammaCgf 1 1 lam / lam
            + (klDiv posterior prior + Real.log (1 / delta)) / ((n : ℝ) * lam)
          ≤ iidPosteriorPopulationRisk dataLaw loss posterior -
              iidPosteriorEmpiricalRisk loss sample posterior n ω}

omit [DecidableEq ι] [Nonempty ι] in
/-- The concrete i.i.d. failure event is the corresponding process failure event. -/
theorem timeUniformIIDPACBayesAnyPosteriorUpperFailure_subset_processFailure
    [MeasurableSpace Z]
    {dataLaw : Measure Z} {prior : ι → ℝ} {loss : ι → Z → ℝ}
    {sample : ℕ → Ω → Z} {lam delta : ℝ} :
    timeUniformIIDPACBayesAnyPosteriorUpperFailure
        dataLaw prior loss sample lam delta
      ⊆
    TimeUniform.timeUniformPACBayesAnyPosteriorUpperFailure
      prior (iidLossGap dataLaw loss sample) 1 1 lam delta := by
  intro ω hω
  rcases hω with ⟨posterior, hposterior, n, hn, hfail⟩
  refine ⟨posterior, hposterior, n, hn, ?_⟩
  rw [posteriorAverage_iidLossGap_runningMean
    dataLaw loss sample posterior hn ω]
  exact hfail

/-- A fixed-tilt sub-Gamma exponential process is integrable under bounded increments. -/
theorem integrable_subGammaExponentialProcess_of_bounded
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {sigma2 b lam : ℝ} (n : ℕ)
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam : 0 ≤ lam) (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k))
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b) :
    Integrable (subGammaExponentialProcess X sigma2 b lam n) μ := by
  refine Integrable.of_bound ?_ (Real.exp (lam * (n : ℝ) * b)) ?_
  · have hpair : Measurable (fun ω : Ω => (lam, ω)) :=
      measurable_const.prodMk measurable_id
    exact ((measurable_subGammaExponentialProcess_prod X sigma2 b n hX_meas).comp
      hpair).aestronglyMeasurable
  · have hall : ∀ᵐ ω ∂μ, ∀ k, |X k ω| ≤ b := ae_all_iff.2 hbound
    filter_upwards [hall] with ω hω
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by unfold subGammaExponentialProcess; positivity)]
    exact subGammaExponentialProcess_le_of_bound
      X sigma2 b lam lam n ω hb hσ hlam le_rfl hblam
      (fun i _hi => hω i)

/-- A future coordinate is independent of the natural filtration generated by
the earlier coordinates.  This is the measurable-space form needed for
nonlinear loss functions; unlike the real-valued convenience lemma in
`BorelCantelli`, the observation type need not be a normed group. -/
theorem iIndepFun_indep_comap_natural_of_lt
    {κ : Type*} [LinearOrder κ]
    {mZ : MeasurableSpace Z} [TopologicalSpace Z] [BorelSpace Z]
    [TopologicalSpace.MetrizableSpace Z]
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {sample : κ → Ω → Z} {i j : κ}
    (hsample : ∀ k, StronglyMeasurable (sample k))
    (hsample_indep : iIndepFun sample μ) (hij : i < j) :
    Indep (MeasurableSpace.comap (sample j) mZ)
      (Filtration.natural sample hsample i) μ := by
  suffices Indep
      (⨆ k ∈ ({j} : Set κ), MeasurableSpace.comap (sample k) mZ)
      (⨆ k ∈ {k | k ≤ i}, MeasurableSpace.comap (sample k) mZ) μ by
    rwa [_root_.iSup_singleton] at this
  exact indep_iSup_of_disjoint
    (fun k => (hsample k).measurable.comap_le) hsample_indep (by simpa)

omit [DecidableEq ι] in
/-- Time-uniform PAC-Bayes generalization bound for finite classes and i.i.d. `[0,1]` losses.

With probability at least `1 - delta`, simultaneously for every positive time
and every posterior PMF, the posterior population risk minus its running
empirical risk is at most

`subGammaCgf 1 1 lam / lam + (KL + log (1 / delta)) / (n * lam)`.

The posterior may depend on the observed sample path. -/
theorem timeUniformIIDPACBayes_allPosteriors_bound
    [mZ : MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [TopologicalSpace.MetrizableSpace Z]
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {dataLaw : Measure Z} [IsProbabilityMeasure dataLaw]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {loss : ι → Z → ℝ} {sample : ℕ → Ω → Z} {lam delta : ℝ}
    (hδ : 0 < delta) (hlam : 0 < lam) (hlam_three : lam < 3)
    (hloss : ∀ i, StronglyMeasurable (loss i))
    (hloss_range : ∀ i z, 0 ≤ loss i z ∧ loss i z ≤ 1)
    (hsample : ∀ k, StronglyMeasurable (sample k))
    (hsample_indep : iIndepFun sample μ)
    (hsample_law : ∀ k, HasLaw (sample k) dataLaw μ) :
    μ.real (timeUniformIIDPACBayesAnyPosteriorUpperFailure
      dataLaw prior loss sample lam delta) ≤ delta := by
  let ℱ : Filtration ℕ mΩ := Filtration.natural sample hsample
  let X : ι → ℕ → Ω → ℝ := iidLossGap dataLaw loss sample
  have hloss_int : ∀ i, Integrable (loss i) dataLaw := by
    intro i
    refine Integrable.of_bound (hloss i).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hloss_range i z).1]
      exact (hloss_range i z).2
  have hrisk : ∀ i, iidLossPopulationRisk dataLaw loss i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    constructor
    · exact integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun z => (hloss_range i z).1)
    · have hle := integral_mono_ae (hloss_int i) (integrable_const (1 : ℝ))
          (Filter.Eventually.of_forall fun z => (hloss_range i z).2)
      simpa [iidLossPopulationRisk] using hle
  have hX_meas : ∀ i k, Measurable (X i k) := by
    intro i k
    have hcomp : StronglyMeasurable (fun ω => loss i (sample (k + 1) ω)) :=
      (hloss i).comp_measurable (hsample (k + 1)).measurable
    change Measurable
      ((fun _ : Ω => iidLossPopulationRisk dataLaw loss i) -
        fun ω => loss i (sample (k + 1) ω))
    exact (stronglyMeasurable_const.sub hcomp).measurable
  have hbound : ∀ i k, ∀ᵐ ω ∂μ, |X i k ω| ≤ (1 : ℝ) := by
    intro i k
    exact Filter.Eventually.of_forall fun ω => by
      change |iidLossPopulationRisk dataLaw loss i - loss i (sample (k + 1) ω)| ≤ 1
      rw [abs_le]
      constructor <;>
        nlinarith [(hrisk i).1, (hrisk i).2,
          (hloss_range i (sample (k + 1) ω)).1,
          (hloss_range i (sample (k + 1) ω)).2]
  have hX_int : ∀ i k, Integrable (X i k) μ := by
    intro i k
    exact Integrable.of_bound (hX_meas i k).aestronglyMeasurable 1 (hbound i k)
  have hX_adapted : ∀ i, IncrementAdapted ℱ (X i) := by
    have hsample_adapted := Filtration.stronglyAdapted_natural hsample
    intro i k
    have hcomp : StronglyMeasurable[ℱ (k + 1)]
        (fun ω => loss i (sample (k + 1) ω)) :=
      (hloss i).comp_measurable (hsample_adapted (k + 1)).measurable
    change StronglyMeasurable[ℱ (k + 1)]
      ((fun _ : Ω => iidLossPopulationRisk dataLaw loss i) -
        fun ω => loss i (sample (k + 1) ω))
    exact stronglyMeasurable_const.sub hcomp
  have hcenter : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] 0 := by
    intro i k
    let observedLoss : Ω → ℝ := fun ω => loss i (sample (k + 1) ω)
    have hobserved_strong : StronglyMeasurable observedLoss :=
      (hloss i).comp_measurable (hsample (k + 1)).measurable
    have hobserved_int : Integrable observedLoss μ := by
      refine Integrable.of_bound hobserved_strong.aestronglyMeasurable 1 ?_
      exact Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hloss_range i (sample (k + 1) ω)).1]
        exact (hloss_range i (sample (k + 1) ω)).2
    have hsample_independent := iIndepFun_indep_comap_natural_of_lt
      hsample hsample_indep (Nat.lt_succ_self k)
    have hcomap :
        MeasurableSpace.comap observedLoss (borel ℝ) ≤
          MeasurableSpace.comap (sample (k + 1)) mZ := by
      change MeasurableSpace.comap (loss i ∘ sample (k + 1)) (borel ℝ) ≤ _
      rw [← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (hloss i).measurable.comap_le
    have hobserved_independent :
        Indep (MeasurableSpace.comap observedLoss (borel ℝ)) (ℱ k) μ :=
      indep_of_indep_of_le_left hsample_independent hcomap
    have hcond := condExp_indep_eq
      (m₁ := MeasurableSpace.comap observedLoss (borel ℝ))
      (m₂ := ℱ k) (m := mΩ) (μ := μ) (f := observedLoss)
      hobserved_strong.measurable.comap_le (ℱ.le k)
      (comap_measurable observedLoss).stronglyMeasurable hobserved_independent
    have hmean : (∫ ω, observedLoss ω ∂μ) =
        iidLossPopulationRisk dataLaw loss i := by
      simpa [observedLoss, iidLossPopulationRisk, Function.comp_def] using
        (hsample_law (k + 1)).integral_comp (hloss i).aestronglyMeasurable
    have hsub := condExp_sub
      (integrable_const (iidLossPopulationRisk dataLaw loss i))
      hobserved_int (ℱ k)
    filter_upwards [hsub, hcond] with ω hsubω hcondω
    change μ[(fun _ : Ω => iidLossPopulationRisk dataLaw loss i) - observedLoss | ℱ k] ω = 0
    rw [hsubω, condExp_const (ℱ.le k)]
    change iidLossPopulationRisk dataLaw loss i - μ[observedLoss | ℱ k] ω = 0
    rw [hcondω, hmean, sub_self]
  have hvar : ∀ i k, μ[fun ω => (X i k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => (1 : ℝ) := by
    intro i k
    have hsq_int : Integrable (fun ω => (X i k ω) ^ 2) μ := by
      refine Integrable.of_bound ((hX_meas i k).pow_const 2).aestronglyMeasurable 1 ?_
      filter_upwards [hbound i k] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X i k ω))]
      rcases abs_le.mp hω with ⟨hneg, hpos⟩
      nlinarith
    have hmono := condExp_mono (m := ℱ k) (μ := μ)
      hsq_int (integrable_const (1 : ℝ))
      ((hbound i k).mono fun ω hω => by
        rcases abs_le.mp hω with ⟨hneg, hpos⟩
        nlinarith)
    filter_upwards [hmono] with ω hω
    simpa [condExp_const (ℱ.le k)] using hω
  have h_integrable :
      ∀ i n, Integrable (subGammaExponentialProcess (X i) 1 1 lam n) μ := by
    intro i n
    exact integrable_subGammaExponentialProcess_of_bounded n
      (by norm_num) (by norm_num) hlam.le (by simpa using hlam_three)
      (hX_meas i) (hbound i)
  exact (measureReal_mono
    (timeUniformIIDPACBayesAnyPosteriorUpperFailure_subset_processFailure
      (dataLaw := dataLaw) (prior := prior) (loss := loss) (sample := sample)
      (lam := lam) (delta := delta))).trans
    (TimeUniform.timeUniformPACBayes_allPosteriors_bound
      (μ := μ) (ℱ := ℱ) hprior hδ
      (by norm_num) (by norm_num) hlam (by simpa using hlam_three)
      hX_meas hX_int hX_adapted h_integrable hbound hcenter hvar)

end

end FormalSLT.PACBayes.TimeUniformIID
