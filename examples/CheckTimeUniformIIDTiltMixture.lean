/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayes.TimeUniformIIDTiltMixture
import FormalSLT.PACBayes.IIDContinuousGaussian

/-!
# Checked finite hypothesis--tilt e-process certificate

This checker instantiates the weighted master e-process with two constant
Boolean classifiers, two nonzero tilts, and normalized positive tilt weights.
Both the posterior and the tilt are selected from the observed path.

Outside one measurable event of probability at most `1 / 16`, the selected
posterior has empirical risk at most `1 / 2`, generalization gap below `3 / 8`,
and population risk below `7 / 8`. The strict mass bound proves that a good path
exists, so the final risk certificate is genuinely nonvacuous. That good path
is existential rather than named. The two explicit selector-branch exercises
below are not proved to lie outside the exceptional event. This is a finite
declared family, not optimization over all real tilts.
-/

namespace FormalSLT.Examples.CheckTimeUniformIIDTiltMixture

open MeasureTheory ProbabilityTheory
open Finset Real BigOperators
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.TimeUniform
open FormalSLT.PACBayes.TimeUniformIID
open FormalSLT.PACBayes.TimeUniformIIDTiltMixture
open FormalSLT.PACBayes.IIDContinuousGaussian

noncomputable section

local instance (q : Prop) : Decidable q := Classical.propDecidable q

/-! ### Two hypotheses and a path-selected posterior -/

/-- Uniform prior on the two constant Boolean classifiers. -/
def uniformBoolPrior : Bool → ℝ := fun _ => (1 : ℝ) / 2

theorem uniformBoolPrior_isFullSupportPMF :
    IsFullSupportPMF uniformBoolPrior := by
  constructor
  · constructor <;> simp [uniformBoolPrior]
  · intro i
    simp [uniformBoolPrior]

/-- Point posterior on the constant-true classifier. -/
def truePosterior : Bool → ℝ := fun classifier => if classifier then 1 else 0

theorem truePosterior_isPMF : IsPMF truePosterior := by
  constructor
  · intro classifier
    cases classifier <;> simp [truePosterior]
  · simp [truePosterior]

/-- Point posterior on the constant-false classifier. -/
def falsePosterior : Bool → ℝ := fun classifier => if classifier then 0 else 1

theorem falsePosterior_isPMF : IsPMF falsePosterior := by
  constructor
  · intro classifier
    cases classifier <;> simp [falsePosterior]
  · simp [falsePosterior]

/-- Zero-one disagreement loss for the two constant classifiers. -/
def disagreementLoss : Bool → Bool → ℝ := fun classifier label =>
  if classifier = label then 0 else 1

theorem disagreementLoss_stronglyMeasurable (classifier : Bool) :
    StronglyMeasurable (disagreementLoss classifier) :=
  (measurable_of_finite _).stronglyMeasurable

theorem disagreementLoss_mem_unitInterval (classifier label : Bool) :
    0 ≤ disagreementLoss classifier label ∧
      disagreementLoss classifier label ≤ 1 := by
  by_cases h : classifier = label <;> simp [disagreementLoss, h]

/-- Select the point posterior with smaller empirical risk; ties select true. -/
def lowerEmpiricalRiskPosterior {Omega : Type*}
    (sample : ℕ → Omega → Bool) (n : ℕ) (omega : Omega) : Bool → ℝ :=
  if iidLossEmpiricalRisk disagreementLoss sample true n omega ≤
      iidLossEmpiricalRisk disagreementLoss sample false n omega then
    truePosterior
  else
    falsePosterior

theorem lowerEmpiricalRiskPosterior_isPMF {Omega : Type*}
    (sample : ℕ → Omega → Bool) (n : ℕ) (omega : Omega) :
    IsPMF (lowerEmpiricalRiskPosterior sample n omega) := by
  unfold lowerEmpiricalRiskPosterior
  split
  · exact truePosterior_isPMF
  · exact falsePosterior_isPMF

theorem complementaryClassifier_empiricalRisks_add_eq_one
    {Omega : Type*} (sample : ℕ → Omega → Bool)
    (n : ℕ) (hn : 0 < n) (omega : Omega) :
    iidLossEmpiricalRisk disagreementLoss sample true n omega +
        iidLossEmpiricalRisk disagreementLoss sample false n omega = 1 := by
  unfold iidLossEmpiricalRisk
  have hsum :
      (∑ k ∈ Finset.range n,
          disagreementLoss true (sample (k + 1) omega)) +
        (∑ k ∈ Finset.range n,
          disagreementLoss false (sample (k + 1) omega)) = n := by
    rw [← Finset.sum_add_distrib]
    calc
      ∑ k ∈ Finset.range n,
          (disagreementLoss true (sample (k + 1) omega) +
            disagreementLoss false (sample (k + 1) omega)) =
          ∑ _k ∈ Finset.range n, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro k _hk
            cases sample (k + 1) omega <;> norm_num [disagreementLoss]
      _ = n := by simp
  rw [← add_div, hsum]
  exact div_self (by exact_mod_cast hn.ne')

/-- The selected posterior's empirical risk is at most one half on every path. -/
theorem lowerEmpiricalRiskPosterior_empiricalRisk_le_half
    {Omega : Type*} (sample : ℕ → Omega → Bool)
    (n : ℕ) (hn : 0 < n) (omega : Omega) :
    iidPosteriorEmpiricalRisk disagreementLoss sample
        (lowerEmpiricalRiskPosterior sample n omega) n omega ≤
      (1 : ℝ) / 2 := by
  have hsum := complementaryClassifier_empiricalRisks_add_eq_one
    sample n hn omega
  by_cases hselect :
      iidLossEmpiricalRisk disagreementLoss sample true n omega ≤
        iidLossEmpiricalRisk disagreementLoss sample false n omega
  · simp only [lowerEmpiricalRiskPosterior, hselect, if_pos,
      iidPosteriorEmpiricalRisk, posteriorAverage]
    rw [Fintype.sum_bool]
    simp [truePosterior]
    linarith
  · have hlt :
        iidLossEmpiricalRisk disagreementLoss sample false n omega <
          iidLossEmpiricalRisk disagreementLoss sample true n omega :=
      lt_of_not_ge hselect
    simp only [lowerEmpiricalRiskPosterior, hselect, if_false,
      iidPosteriorEmpiricalRisk, posteriorAverage]
    rw [Fintype.sum_bool]
    simp [falsePosterior]
    linarith

theorem truePosterior_kl_uniform_eq_log_two :
    klDiv truePosterior uniformBoolPrior = Real.log 2 := by
  simp [klDiv, truePosterior, uniformBoolPrior]

theorem falsePosterior_kl_uniform_eq_log_two :
    klDiv falsePosterior uniformBoolPrior = Real.log 2 := by
  simp [klDiv, falsePosterior, uniformBoolPrior]

/-- Either selected point posterior has KL cost exactly `log 2`. -/
theorem lowerEmpiricalRiskPosterior_kl_uniform_eq_log_two
    {Omega : Type*} (sample : ℕ → Omega → Bool) (n : ℕ) (omega : Omega) :
    klDiv (lowerEmpiricalRiskPosterior sample n omega) uniformBoolPrior =
      Real.log 2 := by
  unfold lowerEmpiricalRiskPosterior
  split
  · exact truePosterior_kl_uniform_eq_log_two
  · exact falsePosterior_kl_uniform_eq_log_two

/-! ### Two weighted tilts and a path-dependent selector -/

/-- Positive normalized weights on the two declared tilts. -/
def uniformTiltWeight : Bool → ℝ := fun _ => (1 : ℝ) / 2

theorem uniformTiltWeight_isFullSupportPMF :
    IsFullSupportPMF uniformTiltWeight := by
  constructor
  · constructor <;> simp [uniformTiltWeight]
  · intro j
    simp [uniformTiltWeight]

/-- The declared tilt family: `false ↦ 1/10`, `true ↦ 1/2`. -/
def twoTilts : Bool → ℝ := fun j => if j then (1 : ℝ) / 2 else (1 : ℝ) / 10

theorem twoTilts_pos (j : Bool) : 0 < twoTilts j := by
  cases j <;> norm_num [twoTilts]

theorem twoTilts_lt_three (j : Bool) : twoTilts j < 3 := by
  cases j <;> norm_num [twoTilts]

/-- Select the larger tilt only when the supplied posterior's observed risk is
at most one quarter.  This is a declared path-dependent rule, not an optimizer. -/
def empiricalRiskTiltSelector {Omega : Type*}
    (sample : ℕ → Omega → Bool) (n : ℕ)
    (omega : Omega) (posterior : Bool → ℝ) : Bool :=
  decide
    (iidPosteriorEmpiricalRisk disagreementLoss sample posterior n omega ≤
      (1 : ℝ) / 4)

/-- An explicit path used only to exercise the selector's two branches. -/
def allTrueStream : FairBoolStream := fun _ => true

theorem empiricalRiskTiltSelector_allTrue_eq_true :
    empiricalRiskTiltSelector fairBoolCoordinateSample 200 allTrueStream
        (lowerEmpiricalRiskPosterior fairBoolCoordinateSample 200
          allTrueStream) = true := by
  norm_num [empiricalRiskTiltSelector, lowerEmpiricalRiskPosterior,
    iidPosteriorEmpiricalRisk, posteriorAverage, iidLossEmpiricalRisk,
    disagreementLoss, truePosterior, falsePosterior, fairBoolCoordinateSample,
    allTrueStream]

theorem empiricalRiskTiltSelector_allTrue_uniform_eq_false :
    empiricalRiskTiltSelector fairBoolCoordinateSample 200 allTrueStream
        uniformBoolPrior = false := by
  norm_num [empiricalRiskTiltSelector, lowerEmpiricalRiskPosterior,
    iidPosteriorEmpiricalRisk, posteriorAverage, iidLossEmpiricalRisk,
    disagreementLoss, truePosterior, falsePosterior, fairBoolCoordinateSample,
    uniformBoolPrior, allTrueStream]

/-- Both possible selected-tilt boundaries are at most `3 / 8` at time 200. -/
theorem selectedBoundary_le_three_eighths
    {Omega : Type*} (sample : ℕ → Omega → Bool) (omega : Omega) (j : Bool) :
    subGammaCgf 1 1 (twoTilts j) / twoTilts j +
        (klDiv (lowerEmpiricalRiskPosterior sample 200 omega) uniformBoolPrior +
          Real.log (1 / (((1 : ℝ) / 16) * uniformTiltWeight j))) /
            ((200 : ℝ) * twoTilts j) ≤
      (3 : ℝ) / 8 := by
  rw [lowerEmpiricalRiskPosterior_kl_uniform_eq_log_two]
  have hlog32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    calc
      Real.log (32 : ℝ) = Real.log ((2 : ℝ) ^ (5 : ℕ)) := by norm_num
      _ = (5 : ℕ) * Real.log 2 := by rw [Real.log_pow]
      _ = 5 * Real.log 2 := by norm_num
  have hlog2 : Real.log 2 ≤ 1 := by
    have hraw := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hraw ⊢
    exact hraw
  cases j <;> norm_num [twoTilts, uniformTiltWeight, subGammaCgf, hlog32] <;>
    linarith

/-! ### Closed fair-Bool stream certificate -/

/-- The canonical measurable exceptional event for the joint mixture. -/
def fairBoolStreamTiltMixtureExceptionalEvent : Set FairBoolStream :=
  timeUniformIIDPACBayesTiltMixtureMeasurableExceptionalEvent
    fairBoolStreamLaw fairBoolLaw uniformBoolPrior uniformTiltWeight
      disagreementLoss fairBoolCoordinateSample twoTilts ((1 : ℝ) / 16)

/-- The canonical event is measurable and has probability at most `1 / 16`. -/
theorem fairBoolStream_tiltMixture_measurableExceptionalEvent_spec :
    MeasurableSet fairBoolStreamTiltMixtureExceptionalEvent ∧
      timeUniformIIDPACBayesTiltMixtureAnyPosteriorUpperFailure
          fairBoolLaw uniformBoolPrior uniformTiltWeight disagreementLoss
            fairBoolCoordinateSample twoTilts ((1 : ℝ) / 16)
        ⊆ fairBoolStreamTiltMixtureExceptionalEvent ∧
      fairBoolStreamLaw.real fairBoolStreamTiltMixtureExceptionalEvent ≤
        (1 : ℝ) / 16 := by
  letI := fairBoolLaw_isProbabilityMeasure
  letI := fairBoolStreamLaw_isProbabilityMeasure
  exact timeUniformIIDPACBayes_tiltMixture_measurableExceptionalEvent_spec
    (μ := fairBoolStreamLaw) (dataLaw := fairBoolLaw)
    (lam := twoTilts) (delta := (1 : ℝ) / 16)
    uniformBoolPrior_isFullSupportPMF uniformTiltWeight_isFullSupportPMF
    (by norm_num) twoTilts_pos twoTilts_lt_three
    disagreementLoss_stronglyMeasurable disagreementLoss_mem_unitInterval
    (fun k => by
      change StronglyMeasurable (fun omega : ℕ → Bool => omega k)
      exact (measurable_pi_apply k).stronglyMeasurable)
    fairBoolCoordinateSample_iIndep fairBoolCoordinateSample_hasLaw

/--
The strict exceptional-event mass bound guarantees a good stream. This theorem
does not identify that stream, and in particular does not place `allTrueStream`
outside the exceptional event.
-/
theorem fairBoolStream_tiltMixture_goodPath_exists :
    ∃ omega : FairBoolStream,
      omega ∉ fairBoolStreamTiltMixtureExceptionalEvent := by
  letI := fairBoolStreamLaw_isProbabilityMeasure
  by_contra h
  push Not at h
  have h_univ : fairBoolStreamTiltMixtureExceptionalEvent = Set.univ := by
    ext omega
    simp [h omega]
  have hmass :=
    fairBoolStream_tiltMixture_measurableExceptionalEvent_spec.2.2
  rw [h_univ] at hmass
  norm_num at hmass

/-- Outside the common event, the path-selected posterior and path-selected
tilt have generalization gap below `3 / 8`. -/
theorem dataSelectedGap_lt_three_eighths_of_not_mem
    {omega : FairBoolStream}
    (hgood : omega ∉ fairBoolStreamTiltMixtureExceptionalEvent) :
    iidPosteriorPopulationRisk fairBoolLaw disagreementLoss
          (lowerEmpiricalRiskPosterior fairBoolCoordinateSample 200 omega) -
        iidPosteriorEmpiricalRisk disagreementLoss fairBoolCoordinateSample
          (lowerEmpiricalRiskPosterior fairBoolCoordinateSample 200 omega)
            200 omega <
      (3 : ℝ) / 8 := by
  let posterior := lowerEmpiricalRiskPosterior
    fairBoolCoordinateSample 200 omega
  let selector := empiricalRiskTiltSelector fairBoolCoordinateSample 200
  have hgap :=
    timeUniformIIDPACBayes_tiltMixture_selected_of_not_mem_measurableExceptionalEvent
      (μ := fairBoolStreamLaw) (dataLaw := fairBoolLaw)
      (prior := uniformBoolPrior) (weight := uniformTiltWeight)
      (loss := disagreementLoss) (sample := fairBoolCoordinateSample)
      (lam := twoTilts) (delta := (1 : ℝ) / 16)
      (omega := omega) hgood selector posterior
      (lowerEmpiricalRiskPosterior_isPMF
        fairBoolCoordinateSample 200 omega) 200 (by norm_num)
  exact hgap.trans_le
    (selectedBoundary_le_three_eighths fairBoolCoordinateSample omega
      (selector omega posterior))

/-- The path-selected posterior receives the nonvacuous risk bound `R < 7/8`. -/
theorem dataSelectedRisk_lt_seven_eighths_of_not_mem
    {omega : FairBoolStream}
    (hgood : omega ∉ fairBoolStreamTiltMixtureExceptionalEvent) :
    iidPosteriorPopulationRisk fairBoolLaw disagreementLoss
        (lowerEmpiricalRiskPosterior fairBoolCoordinateSample 200 omega) <
      (7 : ℝ) / 8 := by
  have hgap := dataSelectedGap_lt_three_eighths_of_not_mem hgood
  have hemp := lowerEmpiricalRiskPosterior_empiricalRisk_le_half
    fairBoolCoordinateSample 200 (by norm_num) omega
  linarith

/--
End-to-end receipt: one measurable event has probability at most `1 / 16`; on
its complement, both a posterior and a tilt selected from the path receive a
gap below `3 / 8` and a risk certificate below one.
-/
theorem fairBoolStream_jointTilt_selected_certificate :
    ∃ E : Set FairBoolStream,
      MeasurableSet E ∧
      fairBoolStreamLaw.real E ≤ (1 : ℝ) / 16 ∧
      ∀ omega ∉ E,
        iidPosteriorPopulationRisk fairBoolLaw disagreementLoss
              (lowerEmpiricalRiskPosterior fairBoolCoordinateSample 200 omega) -
            iidPosteriorEmpiricalRisk disagreementLoss fairBoolCoordinateSample
              (lowerEmpiricalRiskPosterior fairBoolCoordinateSample 200 omega)
                200 omega < (3 : ℝ) / 8 ∧
          iidPosteriorEmpiricalRisk disagreementLoss fairBoolCoordinateSample
              (lowerEmpiricalRiskPosterior fairBoolCoordinateSample 200 omega)
                200 omega ≤ (1 : ℝ) / 2 ∧
          iidPosteriorPopulationRisk fairBoolLaw disagreementLoss
              (lowerEmpiricalRiskPosterior fairBoolCoordinateSample 200 omega) <
            (7 : ℝ) / 8 := by
  refine ⟨fairBoolStreamTiltMixtureExceptionalEvent,
    fairBoolStream_tiltMixture_measurableExceptionalEvent_spec.1,
    fairBoolStream_tiltMixture_measurableExceptionalEvent_spec.2.2, ?_⟩
  intro omega hgood
  exact ⟨dataSelectedGap_lt_three_eighths_of_not_mem hgood,
    lowerEmpiricalRiskPosterior_empiricalRisk_le_half
      fairBoolCoordinateSample 200 (by norm_num) omega,
    dataSelectedRisk_lt_seven_eighths_of_not_mem hgood⟩

/--
Existential nonvacuity of the numerical receipt. The witness comes from the
strict exceptional-event mass bound; it is not an explicit selector-branch
example.
-/
theorem fairBoolStream_jointTilt_selected_goodPath_exists :
    ∃ omega : FairBoolStream,
      omega ∉ fairBoolStreamTiltMixtureExceptionalEvent ∧
        iidPosteriorPopulationRisk fairBoolLaw disagreementLoss
              (lowerEmpiricalRiskPosterior fairBoolCoordinateSample 200 omega) -
            iidPosteriorEmpiricalRisk disagreementLoss fairBoolCoordinateSample
              (lowerEmpiricalRiskPosterior fairBoolCoordinateSample 200 omega)
                200 omega < (3 : ℝ) / 8 ∧
          iidPosteriorEmpiricalRisk disagreementLoss fairBoolCoordinateSample
              (lowerEmpiricalRiskPosterior fairBoolCoordinateSample 200 omega)
                200 omega ≤ (1 : ℝ) / 2 ∧
          iidPosteriorPopulationRisk fairBoolLaw disagreementLoss
              (lowerEmpiricalRiskPosterior fairBoolCoordinateSample 200 omega) <
            (7 : ℝ) / 8 := by
  obtain ⟨omega, hgood⟩ := fairBoolStream_tiltMixture_goodPath_exists
  exact ⟨omega, hgood,
    dataSelectedGap_lt_three_eighths_of_not_mem hgood,
    lowerEmpiricalRiskPosterior_empiricalRisk_le_half
      fairBoolCoordinateSample 200 (by norm_num) omega,
    dataSelectedRisk_lt_seven_eighths_of_not_mem hgood⟩

#check @pacBayesPriorTiltMixtureProcess
#check @pacBayesPriorTiltMixtureProcess_nonneg
#check @pacBayesPriorTiltMixtureProcess_zero
#check @pacBayesPriorTiltMixture_supermartingale
#check @pacBayesPriorTiltMixture_eProcess
#check @pacBayesPriorTiltMixture_optionalContinuation
#check @timeUniformPACBayes_tiltMixture_crossing_bound
#check @timeUniformPACBayesTiltMixtureAnyPosteriorUpperFailure
#check @timeUniformPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_crossing
#check @timeUniformPACBayes_tiltMixture_allPosteriors_bound
#check @timeUniformPACBayes_tiltMixture_allPosteriors_of_not_mem
#check @timeUniformPACBayes_tiltMixture_selected_of_not_mem

#check @timeUniformIIDPACBayesTiltMixtureAnyPosteriorUpperFailure
#check @timeUniformIIDPACBayesTiltMixtureMeasurableExceptionalEvent
#check @timeUniformIIDPACBayesTiltMixtureMeasurableExceptionalEvent_measurable
#check @timeUniformIIDPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_measurableExceptionalEvent
#check @timeUniformIIDPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_processFailure
#check @timeUniformIIDPACBayes_tiltMixture_allPosteriors_bound
#check @timeUniformIIDPACBayes_tiltMixture_measurableExceptionalEvent_spec
#check @timeUniformIIDPACBayes_tiltMixture_allPosteriors_of_not_mem_measurableExceptionalEvent
#check @timeUniformIIDPACBayes_tiltMixture_selected_of_not_mem_measurableExceptionalEvent

#check uniformBoolPrior_isFullSupportPMF
#check truePosterior_isPMF
#check falsePosterior_isPMF
#check disagreementLoss_stronglyMeasurable
#check disagreementLoss_mem_unitInterval
#check lowerEmpiricalRiskPosterior_isPMF
#check complementaryClassifier_empiricalRisks_add_eq_one
#check lowerEmpiricalRiskPosterior_empiricalRisk_le_half
#check truePosterior_kl_uniform_eq_log_two
#check falsePosterior_kl_uniform_eq_log_two
#check lowerEmpiricalRiskPosterior_kl_uniform_eq_log_two
#check uniformTiltWeight_isFullSupportPMF
#check twoTilts_pos
#check twoTilts_lt_three
#check selectedBoundary_le_three_eighths
#check fairBoolStream_tiltMixture_measurableExceptionalEvent_spec
#check fairBoolStream_tiltMixture_goodPath_exists
#check empiricalRiskTiltSelector_allTrue_eq_true
#check empiricalRiskTiltSelector_allTrue_uniform_eq_false
#check dataSelectedGap_lt_three_eighths_of_not_mem
#check dataSelectedRisk_lt_seven_eighths_of_not_mem
#check fairBoolStream_jointTilt_selected_certificate
#check fairBoolStream_jointTilt_selected_goodPath_exists

#print axioms pacBayesPriorTiltMixtureProcess_nonneg
#print axioms pacBayesPriorTiltMixtureProcess_zero
#print axioms pacBayesPriorTiltMixture_supermartingale
#print axioms pacBayesPriorTiltMixture_eProcess
#print axioms pacBayesPriorTiltMixture_optionalContinuation
#print axioms timeUniformPACBayes_tiltMixture_crossing_bound
#print axioms timeUniformPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_crossing
#print axioms timeUniformPACBayes_tiltMixture_allPosteriors_bound
#print axioms timeUniformPACBayes_tiltMixture_allPosteriors_of_not_mem
#print axioms timeUniformPACBayes_tiltMixture_selected_of_not_mem

#print axioms timeUniformIIDPACBayesTiltMixtureMeasurableExceptionalEvent_measurable
#print axioms timeUniformIIDPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_measurableExceptionalEvent
#print axioms timeUniformIIDPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_processFailure
#print axioms timeUniformIIDPACBayes_tiltMixture_allPosteriors_bound
#print axioms timeUniformIIDPACBayes_tiltMixture_measurableExceptionalEvent_spec
#print axioms timeUniformIIDPACBayes_tiltMixture_allPosteriors_of_not_mem_measurableExceptionalEvent
#print axioms timeUniformIIDPACBayes_tiltMixture_selected_of_not_mem_measurableExceptionalEvent

#print axioms uniformBoolPrior_isFullSupportPMF
#print axioms truePosterior_isPMF
#print axioms falsePosterior_isPMF
#print axioms disagreementLoss_stronglyMeasurable
#print axioms disagreementLoss_mem_unitInterval
#print axioms lowerEmpiricalRiskPosterior_isPMF
#print axioms complementaryClassifier_empiricalRisks_add_eq_one
#print axioms lowerEmpiricalRiskPosterior_empiricalRisk_le_half
#print axioms truePosterior_kl_uniform_eq_log_two
#print axioms falsePosterior_kl_uniform_eq_log_two
#print axioms lowerEmpiricalRiskPosterior_kl_uniform_eq_log_two
#print axioms uniformTiltWeight_isFullSupportPMF
#print axioms twoTilts_pos
#print axioms twoTilts_lt_three
#print axioms selectedBoundary_le_three_eighths
#print axioms fairBoolStream_tiltMixture_measurableExceptionalEvent_spec
#print axioms fairBoolStream_tiltMixture_goodPath_exists
#print axioms empiricalRiskTiltSelector_allTrue_eq_true
#print axioms empiricalRiskTiltSelector_allTrue_uniform_eq_false
#print axioms dataSelectedGap_lt_three_eighths_of_not_mem
#print axioms dataSelectedRisk_lt_seven_eighths_of_not_mem
#print axioms fairBoolStream_jointTilt_selected_certificate
#print axioms fairBoolStream_jointTilt_selected_goodPath_exists

end

end FormalSLT.Examples.CheckTimeUniformIIDTiltMixture
