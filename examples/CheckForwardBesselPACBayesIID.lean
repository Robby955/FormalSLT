import FormalSLT.PACBayes.ForwardBesselPACBayesIID
import FormalSLT.PACBayes.IIDContinuousGaussian

/-!
# Fair-Bool receipt for the forward-Bessel IID PAC-Bayes bound

This checker uses a genuinely random fair-Bool stream, two constant Boolean
hypotheses, and two positive tilt atoms.  The posterior depends on the realized
path and current time, and the tilt selector inspects the path, time, and that
posterior.  The receipt keeps the hybrid-Bessel width symbolic; its purpose is
to exercise the common-event and selector semantics without a separate numeric
optimization argument.
-/

namespace FormalSLT.Examples.CheckForwardBesselPACBayesIID

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.TimeUniformIID
open FormalSLT.PACBayes.ForwardBesselPACBayes
open FormalSLT.PACBayes.ForwardBesselPACBayesIID
open FormalSLT.PACBayes.IIDContinuousGaussian

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Uniform prior on the two constant Boolean hypotheses. -/
def boolHypothesisPrior : Bool → ℝ := fun _ ↦ (1 : ℝ) / 2

theorem boolHypothesisPrior_isFullSupportPMF :
    IsFullSupportPMF boolHypothesisPrior := by
  constructor
  · constructor <;> simp [boolHypothesisPrior]
  · intro i
    simp [boolHypothesisPrior]

/-- Uniform prior on two predeclared positive tilts. -/
def boolTiltWeight : Bool → ℝ := fun _ ↦ (1 : ℝ) / 2

theorem boolTiltWeight_isFullSupportPMF :
    IsFullSupportPMF boolTiltWeight := by
  constructor
  · constructor <;> simp [boolTiltWeight]
  · intro j
    simp [boolTiltWeight]

/-- The tilt catalog `false ↦ 1/4`, `true ↦ 1/2`. -/
def boolTilts : Bool → ℝ := fun j ↦
  if j then (1 : ℝ) / 2 else (1 : ℝ) / 4

theorem boolTilts_pos (j : Bool) : 0 < boolTilts j := by
  cases j <;> norm_num [boolTilts]

theorem boolTilts_lt_one (j : Bool) : boolTilts j < 1 := by
  cases j <;> norm_num [boolTilts]

/-- Zero-one disagreement loss for constant Boolean hypotheses. -/
def disagreementLoss (hypothesis label : Bool) : ℝ :=
  if hypothesis = label then 0 else 1

theorem disagreementLoss_stronglyMeasurable (hypothesis : Bool) :
    StronglyMeasurable (disagreementLoss hypothesis) :=
  (measurable_of_finite _).stronglyMeasurable

theorem disagreementLoss_mem_unitInterval (hypothesis label : Bool) :
    0 ≤ disagreementLoss hypothesis label ∧
      disagreementLoss hypothesis label ≤ 1 := by
  by_cases h : hypothesis = label <;> simp [disagreementLoss, h]

/-- At time `n`, select the point posterior on the last observed label. -/
def lastLabelPosterior
    (ω : FairBoolStream) (n : ℕ) (hypothesis : Bool) : ℝ :=
  if hypothesis = fairBoolCoordinateSample n ω then 1 else 0

theorem lastLabelPosterior_isPMF (ω : FairBoolStream) (n : ℕ) :
    IsPMF (lastLabelPosterior ω n) := by
  constructor
  · intro hypothesis
    by_cases h : hypothesis = fairBoolCoordinateSample n ω <;>
      simp [lastLabelPosterior, h]
  · rw [Fintype.sum_bool]
    cases hlabel : fairBoolCoordinateSample n ω <;>
      simp [lastLabelPosterior, hlabel]

/-- The selected point posterior pays the nonzero hypothesis cost `log 2`. -/
theorem lastLabelPosterior_kl_eq_log_two
    (ω : FairBoolStream) (n : ℕ) :
    klDiv (lastLabelPosterior ω n) boolHypothesisPrior = Real.log 2 := by
  cases hlabel : fairBoolCoordinateSample n ω <;>
    simp [klDiv, lastLabelPosterior, boolHypothesisPrior, hlabel]

/-- A declared tilt selector that explicitly inspects the path, current time,
and supplied posterior. -/
def posteriorAwareTiltSelector
    (ω : FairBoolStream) (n : ℕ) (posterior : Bool → ℝ) : Bool :=
  if posterior (fairBoolCoordinateSample n ω) = 1 then
    fairBoolCoordinateSample n ω
  else
    false

/-- Along the selected posterior, the chosen tilt atom is the observed label.
This exercises both data values pointwise; it does not claim that both values
occur on the existential good path below. -/
theorem posteriorAwareTiltSelector_lastLabel_eq_observed
    (ω : FairBoolStream) (n : ℕ) :
    posteriorAwareTiltSelector ω n (lastLabelPosterior ω n) =
      fairBoolCoordinateSample n ω := by
  simp [posteriorAwareTiltSelector, lastLabelPosterior]

/-- The one master atTop event at confidence level `1/2`. -/
def fairBoolForwardBesselEvent : Set FairBoolStream :=
  forwardIIDBesselPACBayesExceptionalEvent
    fairBoolLaw boolHypothesisPrior boolTiltWeight disagreementLoss
      fairBoolCoordinateSample boolTilts ((1 : ℝ) / 2)

/-- The master event has outer probability at most one half. -/
theorem fairBoolForwardBesselEvent_mass_le_half :
    fairBoolStreamLaw.real fairBoolForwardBesselEvent ≤ (1 : ℝ) / 2 := by
  letI := fairBoolLaw_isProbabilityMeasure
  letI := fairBoolStreamLaw_isProbabilityMeasure
  exact forwardIIDBesselPACBayesExceptionalEvent_mass_le_delta
    (μ := fairBoolStreamLaw) (dataLaw := fairBoolLaw)
    (prior := boolHypothesisPrior) (weight := boolTiltWeight)
    (loss := disagreementLoss) (sample := fairBoolCoordinateSample)
    (lam := boolTilts) (delta := (1 : ℝ) / 2)
    boolHypothesisPrior_isFullSupportPMF
    boolTiltWeight_isFullSupportPMF
    (by norm_num) boolTilts_pos boolTilts_lt_one
    disagreementLoss_stronglyMeasurable
    disagreementLoss_mem_unitInterval
    (fun k ↦ by
      change StronglyMeasurable (fun ω : ℕ → Bool ↦ ω k)
      exact (measurable_pi_apply k).stronglyMeasurable)
    fairBoolCoordinateSample_iIndep fairBoolCoordinateSample_hasLaw

/-- A path outside the master event exists because its mass is strictly below
the total probability mass. -/
theorem fairBoolForwardBessel_goodPath_exists :
    ∃ ω : FairBoolStream, ω ∉ fairBoolForwardBesselEvent := by
  letI := fairBoolStreamLaw_isProbabilityMeasure
  by_contra h
  push Not at h
  have h_univ : fairBoolForwardBesselEvent = Set.univ := by
    ext ω
    simp [h ω]
  have hmass := fairBoolForwardBesselEvent_mass_le_half
  rw [h_univ] at hmass
  norm_num at hmass

/-- On every good path, the path-and-time posterior and the
path/time/posterior-selected tilt satisfy the IID risk bound at every `n >= 2`. -/
theorem fairBoolForwardBessel_selected_of_not_mem
    {ω : FairBoolStream} (hω : ω ∉ fairBoolForwardBesselEvent)
    (n : ℕ) (hn : 2 ≤ n) :
    iidPosteriorPopulationRisk fairBoolLaw disagreementLoss
        (lastLabelPosterior ω n) <
      iidPosteriorEmpiricalRisk disagreementLoss fairBoolCoordinateSample
          (lastLabelPosterior ω n) n ω +
        forwardIIDBesselPACBayesBoundary
          boolHypothesisPrior boolTiltWeight boolTilts disagreementLoss
            fairBoolCoordinateSample (lastLabelPosterior ω n)
              ((1 : ℝ) / 2)
              (posteriorAwareTiltSelector ω n (lastLabelPosterior ω n)) n ω := by
  exact forwardIIDBesselPACBayes_selected_of_not_mem
    boolHypothesisPrior_isFullSupportPMF
    boolTiltWeight_isFullSupportPMF
    (by norm_num) boolTilts_pos boolTilts_lt_one
    disagreementLoss_mem_unitInterval hω
    (fun ω n ↦ lastLabelPosterior ω n)
    lastLabelPosterior_isPMF posteriorAwareTiltSelector n hn

/-- Selected common-event receipt: one good stochastic path carries every
eligible-time selected-posterior/selected-tilt bound. -/
theorem fairBoolForwardBessel_selected_goodPath_exists :
    ∃ ω : FairBoolStream,
      ω ∉ fairBoolForwardBesselEvent ∧
        ∀ n : ℕ, 2 ≤ n →
          iidPosteriorPopulationRisk fairBoolLaw disagreementLoss
              (lastLabelPosterior ω n) <
            iidPosteriorEmpiricalRisk disagreementLoss
                fairBoolCoordinateSample (lastLabelPosterior ω n) n ω +
              forwardIIDBesselPACBayesBoundary
                boolHypothesisPrior boolTiltWeight boolTilts disagreementLoss
                  fairBoolCoordinateSample (lastLabelPosterior ω n)
                    ((1 : ℝ) / 2)
                    (posteriorAwareTiltSelector
                      ω n (lastLabelPosterior ω n)) n ω := by
  obtain ⟨ω, hω⟩ := fairBoolForwardBessel_goodPath_exists
  exact ⟨ω, hω, fun n hn ↦
    fairBoolForwardBessel_selected_of_not_mem hω n hn⟩

#check iidObservedLoss
#check forwardPrefixMean_iidObservedLoss
#check posteriorAverage_forwardPrefixMean_iidObservedLoss
#check iidObservedLoss_incrementAdapted
#check iidObservedLoss_integrable
#check iidObservedLoss_condExp_eq_populationRisk
#check forwardIIDBesselPACBayesExceptionalEvent_mass_le_delta
#check forwardIIDBesselPACBayes_allPosteriors_of_not_mem
#check forwardIIDBesselPACBayes_selected_of_not_mem
#check exists_forwardIIDBesselPACBayes_event
#check fairBoolForwardBesselEvent_mass_le_half
#check lastLabelPosterior_kl_eq_log_two
#check posteriorAwareTiltSelector_lastLabel_eq_observed
#check fairBoolForwardBessel_selected_goodPath_exists

#print axioms forwardPrefixMean_iidObservedLoss
#print axioms posteriorAverage_forwardPrefixMean_iidObservedLoss
#print axioms iidObservedLoss_incrementAdapted
#print axioms iidObservedLoss_integrable
#print axioms iidObservedLoss_condExp_eq_populationRisk
#print axioms forwardIIDBesselPACBayesExceptionalEvent_mass_le_delta
#print axioms forwardIIDBesselPACBayes_allPosteriors_of_not_mem
#print axioms forwardIIDBesselPACBayes_selected_of_not_mem
#print axioms exists_forwardIIDBesselPACBayes_event
#print axioms fairBoolForwardBesselEvent_mass_le_half
#print axioms lastLabelPosterior_kl_eq_log_two
#print axioms posteriorAwareTiltSelector_lastLabel_eq_observed
#print axioms fairBoolForwardBessel_selected_goodPath_exists

end

end FormalSLT.Examples.CheckForwardBesselPACBayesIID
