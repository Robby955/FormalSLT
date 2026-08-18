/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.StochasticDynamics.TrajectoryPACBayes

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.PACBayesKL
open scoped ENNReal NNReal

namespace FormalSLT.Examples.CheckTrajectoryPACBayes

open StochasticDynamics

noncomputable section

/-- A prefix summary that reads both the initial and current coordinates. -/
def prefixAgreement (n : ℕ) (u : (i : Finset.Iic n) → Bool) : Bool :=
  decide (u ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩ =
    u ⟨n, Finset.mem_Iic.mpr le_rfl⟩)

/-- A nondegenerate next-state law selected by the whole prefix summary. -/
def historyDependentBoolPMF (n : ℕ)
    (u : (i : Finset.Iic n) → Bool) : PMF Bool :=
  PMF.ofFintype
    (fun y ↦ if y = prefixAgreement n u
      then ((3 / 4 : NNReal) : ENNReal)
      else ((1 / 4 : NNReal) : ENNReal))
    (by
      have hsumNN : (3 / 4 : NNReal) + 1 / 4 = 1 := by norm_num
      have hsum : ((3 / 4 : NNReal) : ENNReal) +
          ((1 / 4 : NNReal) : ENNReal) = 1 := by
        rw [← ENNReal.coe_add, hsumNN]
        rfl
      cases h : prefixAgreement n u <;>
        simpa [Fintype.sum_bool, h, add_comm] using hsum)

/-- A genuinely history-dependent trajectory kernel. -/
def historyDependentBoolKernel (n : ℕ) :
    Kernel ((i : Finset.Iic n) → Bool) Bool :=
  Kernel.ofFunOfCountable fun u ↦ (historyDependentBoolPMF n u).toMeasure

instance historyDependentBoolKernel.instIsMarkovKernel (n : ℕ) :
    IsMarkovKernel (historyDependentBoolKernel n) :=
  ⟨fun u ↦ by
    change IsProbabilityMeasure (historyDependentBoolPMF n u).toMeasure
    infer_instance⟩

/-- Two bounded online scoring rules.  The `false` atom uses both ends of the
prefix; the `true` atom uses its initial coordinate. -/
def historyDependentBoolScore (i : Bool) : TrajectoryScore Bool :=
  fun n u y ↦
    if i then
      if y = u ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩ then 1 else 0
    else
      if y = prefixAgreement n u then 1 else 0

theorem historyDependentBoolScore_mem_Icc :
    ∀ i n u y, historyDependentBoolScore i n u y ∈ Set.Icc (0 : ℝ) 1 := by
  intro i n u y
  fin_cases i <;> simp [historyDependentBoolScore] <;> split_ifs <;> norm_num

def trueThenFalsePath (n : ℕ) : Bool :=
  if n = 0 then true else false

def allFalsePath (_n : ℕ) : Bool := false

/-- The witness paths agree at the current state at time one. -/
theorem historyWitness_same_current :
    trueThenFalsePath 1 = allFalsePath 1 := by
  simp [trueThenFalsePath, allFalsePath]

/-- Nevertheless, the kernel assigns different next-state probabilities. -/
theorem historyDependentBool_kernel_witness :
    historyDependentBoolPMF 1
        (Preorder.frestrictLe 1 trueThenFalsePath) true = 1 / 4 ∧
      historyDependentBoolPMF 1
        (Preorder.frestrictLe 1 allFalsePath) true = 3 / 4 := by
  constructor <;>
    norm_num [historyDependentBoolPMF, prefixAgreement, PMF.ofFintype_apply,
      Preorder.frestrictLe_apply, trueThenFalsePath, allFalsePath]

/-- The `false` score atom also distinguishes the two histories even though
their current states agree. -/
theorem historyDependentBool_score_witness :
    historyDependentBoolScore false 1
        (Preorder.frestrictLe 1 trueThenFalsePath) true = 0 ∧
      historyDependentBoolScore false 1
        (Preorder.frestrictLe 1 allFalsePath) true = 1 := by
  constructor <;>
    norm_num [historyDependentBoolScore, prefixAgreement,
      Preorder.frestrictLe_apply, trueThenFalsePath, allFalsePath]

def uniformBoolPrior (_i : Bool) : ℝ := 1 / 2

theorem uniformBoolPrior_isFullSupportPMF :
    IsFullSupportPMF uniformBoolPrior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> norm_num [uniformBoolPrior]
  · norm_num [uniformBoolPrior, Fintype.sum_bool]
  · intro i
    fin_cases i <;> norm_num [uniformBoolPrior]

def uniformBoolTiltWeight (_j : Bool) : ℝ := 1 / 2

theorem uniformBoolTiltWeight_isFullSupportPMF :
    IsFullSupportPMF uniformBoolTiltWeight := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro j
    fin_cases j <;> norm_num [uniformBoolTiltWeight]
  · norm_num [uniformBoolTiltWeight, Fintype.sum_bool]
  · intro j
    fin_cases j <;> norm_num [uniformBoolTiltWeight]

def twoTrajectoryTilts (j : Bool) : ℝ := if j then 1 / 5 else 1 / 6

theorem twoTrajectoryTilts_pos (j : Bool) : 0 < twoTrajectoryTilts j := by
  fin_cases j <;> norm_num [twoTrajectoryTilts]

theorem twoTrajectoryTilts_lt_three (j : Bool) :
    twoTrajectoryTilts j < 3 := by
  fin_cases j <;> norm_num [twoTrajectoryTilts]

/-- Point posterior selected by a Boolean path statistic. -/
def boolPointPosterior (selected i : Bool) : ℝ :=
  if i = selected then 1 else 0

theorem boolPointPosterior_isPMF (selected : Bool) :
    IsPMF (boolPointPosterior selected) := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases selected <;> fin_cases i <;> norm_num [boolPointPosterior]
  · fin_cases selected <;> norm_num [boolPointPosterior, Fintype.sum_bool]

def firstTransitionPosterior (x : ℕ → Bool) : Bool → ℝ :=
  boolPointPosterior (x 1)

theorem firstTransitionPosterior_isPMF (x : ℕ → Bool) :
    IsPMF (firstTransitionPosterior x) :=
  boolPointPosterior_isPMF _

/-- Concrete instantiation of the common-event theorem for a kernel and score
catalog that provably depend on more than the current state. -/
theorem historyDependentBool_trajectoryPACBayes_certificate :
    ∃ E : Set (ℕ → Bool),
      MeasurableSet E ∧
      (trajectoryMeasure historyDependentBoolKernel false).real E ≤ 1 / 20 ∧
      ∀ x ∉ E, ∀ j : Bool,
        ∀ posterior : Bool → ℝ, IsPMF posterior →
          ∀ n : ℕ, 0 < n →
            trajectoryPosteriorAverageConditionalRisk
                historyDependentBoolKernel historyDependentBoolScore
                posterior n x <
              trajectoryPosteriorEmpiricalPrequentialRisk
                  historyDependentBoolScore posterior n x +
                twoTrajectoryTilts j /
                  (8 * (1 - twoTrajectoryTilts j / 3)) +
                (klDiv posterior uniformBoolPrior +
                  Real.log
                    (1 / ((1 / 20 : ℝ) * uniformBoolTiltWeight j))) /
                  ((n : ℝ) * twoTrajectoryTilts j) := by
  exact trajectoryPACBayes_tiltMixture_prequentialRisk_certificate
    (ι := Bool) (τ := Bool) historyDependentBoolKernel false
    historyDependentBoolScore_mem_Icc
    uniformBoolPrior_isFullSupportPMF uniformBoolTiltWeight_isFullSupportPMF
    (lam := twoTrajectoryTilts) (delta := (1 / 20 : ℝ))
    (by norm_num) twoTrajectoryTilts_pos twoTrajectoryTilts_lt_three

/-- The same common event permits both posterior and tilt selection from the
observed first transition.  This is pointwise post-data selection from the
predeclared finite families, not construction of a selected process. -/
theorem historyDependentBool_selectedPosteriorTilt_certificate :
    ∃ E : Set (ℕ → Bool),
      MeasurableSet E ∧
      (trajectoryMeasure historyDependentBoolKernel false).real E ≤ 1 / 20 ∧
      ∀ x ∉ E,
        let posterior := firstTransitionPosterior x
        let j := x 1
        IsPMF posterior ∧
        trajectoryPosteriorAverageConditionalRisk
            historyDependentBoolKernel historyDependentBoolScore
            posterior 32 x <
          trajectoryPosteriorEmpiricalPrequentialRisk
              historyDependentBoolScore posterior 32 x +
            twoTrajectoryTilts j /
              (8 * (1 - twoTrajectoryTilts j / 3)) +
            (klDiv posterior uniformBoolPrior +
              Real.log
                (1 / ((1 / 20 : ℝ) * uniformBoolTiltWeight j))) /
              ((32 : ℝ) * twoTrajectoryTilts j) := by
  rcases historyDependentBool_trajectoryPACBayes_certificate with
    ⟨E, hE, hmass, houtside⟩
  refine ⟨E, hE, hmass, ?_⟩
  intro x hx
  let posterior := firstTransitionPosterior x
  let j := x 1
  have hposterior : IsPMF posterior := firstTransitionPosterior_isPMF x
  exact ⟨hposterior, houtside x hx j posterior hposterior 32 (by norm_num)⟩

/-! Public theorem and receipt audit. -/

#check StochasticDynamics.trajectoryRiskShortfall
#check StochasticDynamics.trajectoryEmpiricalPrequentialRisk
#check StochasticDynamics.trajectoryAverageConditionalRisk
#check StochasticDynamics.trajectoryPosteriorEmpiricalPrequentialRisk
#check StochasticDynamics.trajectoryPosteriorAverageConditionalRisk
#check StochasticDynamics.runningMean_trajectoryRiskShortfall
#check StochasticDynamics.posteriorAverage_runningMean_trajectoryRiskShortfall
#check StochasticDynamics.trajectoryRiskShortfall_incrementAdapted
#check StochasticDynamics.measurable_trajectoryRiskShortfall
#check StochasticDynamics.integrable_trajectoryRiskShortfall
#check StochasticDynamics.abs_trajectoryRiskShortfall_le_one
#check StochasticDynamics.trajectoryRiskShortfall_condExp_eq_zero
#check StochasticDynamics.trajectoryRiskShortfall_condSecondMoment_le_one_fourth
#check StochasticDynamics.trajectoryPACBayesTiltMixtureAnyPosteriorUpperFailure
#check StochasticDynamics.trajectoryPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_processFailure
#check StochasticDynamics.trajectoryPACBayes_tiltMixture_allPosteriors_bound
#check StochasticDynamics.trajectoryPACBayesTiltMixtureExceptionalEvent
#check StochasticDynamics.trajectoryPACBayesTiltMixtureExceptionalEvent_measurable
#check StochasticDynamics.trajectoryPACBayesTiltMixtureRawFailure_subset_exceptionalEvent
#check StochasticDynamics.trajectoryPACBayesTiltMixtureExceptionalEvent_mass_le_delta
#check StochasticDynamics.trajectoryPosteriorAverageConditionalRisk_lt_tiltMixture_of_not_mem
#check StochasticDynamics.trajectoryPACBayes_tiltMixture_prequentialRisk_certificate

#print axioms StochasticDynamics.runningMean_trajectoryRiskShortfall
#print axioms StochasticDynamics.posteriorAverage_runningMean_trajectoryRiskShortfall
#print axioms StochasticDynamics.trajectoryRiskShortfall_incrementAdapted
#print axioms StochasticDynamics.measurable_trajectoryRiskShortfall
#print axioms StochasticDynamics.integrable_trajectoryRiskShortfall
#print axioms StochasticDynamics.abs_trajectoryRiskShortfall_le_one
#print axioms StochasticDynamics.trajectoryRiskShortfall_condExp_eq_zero
#print axioms StochasticDynamics.trajectoryRiskShortfall_condSecondMoment_le_one_fourth
#print axioms StochasticDynamics.trajectoryPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_processFailure
#print axioms StochasticDynamics.trajectoryPACBayes_tiltMixture_allPosteriors_bound
#print axioms StochasticDynamics.trajectoryPACBayesTiltMixtureExceptionalEvent_measurable
#print axioms StochasticDynamics.trajectoryPACBayesTiltMixtureRawFailure_subset_exceptionalEvent
#print axioms StochasticDynamics.trajectoryPACBayesTiltMixtureExceptionalEvent_mass_le_delta
#print axioms StochasticDynamics.trajectoryPosteriorAverageConditionalRisk_lt_tiltMixture_of_not_mem
#print axioms StochasticDynamics.trajectoryPACBayes_tiltMixture_prequentialRisk_certificate

#check historyDependentBool_kernel_witness
#check historyDependentBool_score_witness
#check historyDependentBool_trajectoryPACBayes_certificate
#check historyDependentBool_selectedPosteriorTilt_certificate

#print axioms historyDependentBool_kernel_witness
#print axioms historyDependentBool_score_witness
#print axioms historyDependentBool_trajectoryPACBayes_certificate
#print axioms historyDependentBool_selectedPosteriorTilt_certificate

end

end FormalSLT.Examples.CheckTrajectoryPACBayes
