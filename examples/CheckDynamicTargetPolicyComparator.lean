/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.PrefixDynamicTargetPolicyComparator

/-!
# Dynamic target-policy comparator receipt

Both Boolean target policies and the behavior policy inspect an interior
action in the observed prefix.  Two prefixes with identical initial and
current coordinates but different interior actions therefore induce different
target-policy conditional risks.  A displayed behavior path also gives
strictly positive hybrid-Bessel variation for both target atoms.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Examples.CheckDynamicTargetPolicyComparator

open FormalSLT.StochasticDynamics

noncomputable section

/-- Boolean PMF with masses `3/4` and `1/4`. -/
def dynamicBiasedBoolPMF (favored : Bool) : PMF Bool :=
  PMF.ofFintype
    (fun b ↦ if b = favored
      then ((3 / 4 : NNReal) : ENNReal)
      else ((1 / 4 : NNReal) : ENNReal))
    (by
      have hsumNN : (3 / 4 : NNReal) + 1 / 4 = 1 := by norm_num
      have hsum : ((3 / 4 : NNReal) : ENNReal) +
          ((1 / 4 : NNReal) : ENNReal) = 1 := by
        rw [← ENNReal.coe_add, hsumNN]
        rfl
      cases favored <;>
        simpa [Fintype.sum_bool, add_comm] using hsum)

theorem dynamicBiasedBoolPMF_pos (favored b : Bool) :
    0 < dynamicBiasedBoolPMF favored b := by
  simp only [dynamicBiasedBoolPMF, PMF.ofFintype_apply]
  split_ifs <;> norm_num

/-- The environment outcome favors whether state and action agree. -/
def dynamicBoolEnvironment (s a : Bool) : PMF Bool :=
  dynamicBiasedBoolPMF (s == a)

/-- Read coordinate one's action when it exists.  This is a genuine interior
history feature at every time at least one. -/
def dynamicInteriorAction (n : ℕ)
    (u : (i : Finset.Iic n) → ControlledObservation Bool Bool) : Bool :=
  if h : 1 ≤ n then
    (u ⟨1, Finset.mem_Iic.mpr h⟩).1
  else
    (u ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩).1

/-- A genuinely time- and prefix-dependent environment.  At even times it
favors agreement between the current state and action.  At odd times it also
compares that agreement bit with the recorded interior action. -/
def prefixDynamicBoolEnvironment : PrefixControlledEnvironment Bool Bool :=
  fun n u a ↦
    let current := (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
    let favored :=
      if n % 2 = 0 then current == a
      else (current == a) == dynamicInteriorAction n u
    dynamicBiasedBoolPMF favored

/-- History-dependent behavior favors the recorded interior action. -/
def dynamicHistoryBehavior : BehaviorPolicy Bool Bool :=
  fun n u ↦ dynamicBiasedBoolPMF (dynamicInteriorAction n u)

theorem dynamicHistoryBehavior_pos (n : ℕ)
    (u : (i : Finset.Iic n) → ControlledObservation Bool Bool) (a : Bool) :
    0 < dynamicHistoryBehavior n u a :=
  dynamicBiasedBoolPMF_pos _ _

theorem prefixDynamicBoolEnvironment_pos (n : ℕ)
    (u : (i : Finset.Iic n) → ControlledObservation Bool Bool)
    (a y : Bool) :
    0 < prefixDynamicBoolEnvironment n u a y :=
  dynamicBiasedBoolPMF_pos _ _

/-- Every finite continuation atom used by the variance receipt is possible;
the displayed path is not an off-support arithmetic construction. -/
theorem prefixDynamicContinuationPMF_pos (n : ℕ)
    (u : (i : Finset.Iic n) → ControlledObservation Bool Bool)
    (next : ControlledObservation Bool Bool) :
    0 < prefixControlledContinuationPMF prefixDynamicBoolEnvironment
      dynamicHistoryBehavior n u next := by
  rw [show next = (next.1, next.2) by exact Prod.eta next,
    prefixControlledContinuationPMF_apply]
  exact ENNReal.mul_pos_iff.2
    ⟨dynamicHistoryBehavior_pos n u next.1,
      prefixDynamicBoolEnvironment_pos n u next.1 next.2⟩

/-- Target `false` favors the recorded interior action; target `true` favors
its complement.  Thus both catalog atoms inspect the full prefix interface. -/
def dynamicTargetCatalog (i : Bool) : TargetPolicy Bool Bool :=
  fun n u ↦ dynamicBiasedBoolPMF
    (if i then !(dynamicInteriorAction n u) else dynamicInteriorAction n u)

/-- Loss is the indicator that the revealed next state is `true`. -/
def dynamicBoolScore (_i : Bool) : ControlledTransitionScore Bool Bool :=
  fun _n _u _a y ↦ if y then 1 else 0

theorem dynamicBoolScore_mem_Icc :
    ∀ i n u a y, dynamicBoolScore i n u a y ∈ Set.Icc (0 : ℝ) 1 := by
  intro i n u a y
  fin_cases y <;> norm_num [dynamicBoolScore]

theorem dynamicHistoryBehavior_overlap (i : Bool) :
    ControlledPolicyOverlap dynamicHistoryBehavior
      (dynamicTargetCatalog i) := by
  intro n u a hzero
  simp only [dynamicHistoryBehavior, dynamicBiasedBoolPMF,
    PMF.ofFintype_apply] at hzero
  split_ifs at hzero <;> norm_num at hzero

/-- The common likelihood-ratio cap is `3`; the extremal case compares target
mass `3/4` with behavior mass `1/4`. -/
theorem dynamicHistoryBehavior_ratioBound (i : Bool) :
    ControlledPolicyRatioBound dynamicHistoryBehavior
      (dynamicTargetCatalog i) 3 := by
  intro n u a
  fin_cases i <;> fin_cases a <;>
    simp only [dynamicHistoryBehavior, dynamicTargetCatalog,
      dynamicBiasedBoolPMF, PMF.ofFintype_apply, Bool.false_eq_true] <;>
    split_ifs <;> norm_num

/-- Same deterministic initial and current coordinates, but opposite interior
actions. -/
def dynamicInteriorFalsePath (_n : ℕ) : ControlledObservation Bool Bool :=
  (false, false)

def dynamicInteriorTruePath (n : ℕ) : ControlledObservation Bool Bool :=
  if n = 1 then (true, false) else (false, false)

theorem dynamicHistoryWitness_same_initial_current :
    dynamicInteriorFalsePath 0 = dynamicInteriorTruePath 0 ∧
      dynamicInteriorFalsePath 2 = dynamicInteriorTruePath 2 := by
  norm_num [dynamicInteriorFalsePath, dynamicInteriorTruePath]

theorem dynamicHistoryWitness_different_interior :
    (dynamicInteriorFalsePath 1).1 ≠ (dynamicInteriorTruePath 1).1 := by
  norm_num [dynamicInteriorFalsePath, dynamicInteriorTruePath]

/-- At odd time one, two prefixes with the same current state and queried
action but opposite interior actions give different environment rows. -/
theorem prefixDynamicEnvironment_history_witness :
    prefixDynamicBoolEnvironment 1
        (Preorder.frestrictLe 1 dynamicInteriorFalsePath) false true = 1 / 4 ∧
      prefixDynamicBoolEnvironment 1
        (Preorder.frestrictLe 1 dynamicInteriorTruePath) false true = 3 / 4 := by
  constructor <;>
    norm_num [prefixDynamicBoolEnvironment, dynamicInteriorAction,
      dynamicInteriorFalsePath, dynamicInteriorTruePath,
      dynamicBiasedBoolPMF, PMF.ofFintype_apply,
      Preorder.frestrictLe_apply]

/-- At the same current state, target `false` has risks `5/8` and `3/8`
depending only on the earlier recorded action. -/
theorem dynamicTargetFalse_history_changes_risk :
    encounteredTargetConditionalRisk dynamicBoolEnvironment
        (dynamicTargetCatalog false) (dynamicBoolScore false)
        2 dynamicInteriorFalsePath = 5 / 8 ∧
      encounteredTargetConditionalRisk dynamicBoolEnvironment
        (dynamicTargetCatalog false) (dynamicBoolScore false)
        2 dynamicInteriorTruePath = 3 / 8 := by
  constructor <;>
    norm_num [encounteredTargetConditionalRisk, dynamicBoolEnvironment,
      dynamicTargetCatalog, dynamicBoolScore, dynamicInteriorAction,
      dynamicInteriorFalsePath, dynamicInteriorTruePath,
      dynamicBiasedBoolPMF, PMF.ofFintype_apply,
      Preorder.frestrictLe_apply, Fintype.sum_bool]

/-- Target `true` reverses the two risks. -/
theorem dynamicTargetTrue_history_changes_risk :
    encounteredTargetConditionalRisk dynamicBoolEnvironment
        (dynamicTargetCatalog true) (dynamicBoolScore true)
        2 dynamicInteriorFalsePath = 3 / 8 ∧
      encounteredTargetConditionalRisk dynamicBoolEnvironment
        (dynamicTargetCatalog true) (dynamicBoolScore true)
        2 dynamicInteriorTruePath = 5 / 8 := by
  constructor <;>
    norm_num [encounteredTargetConditionalRisk, dynamicBoolEnvironment,
      dynamicTargetCatalog, dynamicBoolScore, dynamicInteriorAction,
      dynamicInteriorFalsePath, dynamicInteriorTruePath,
      dynamicBiasedBoolPMF, PMF.ofFintype_apply,
      Preorder.frestrictLe_apply, Fintype.sum_bool]

/-- The stronger prefix-dynamic semantics retains the nonconstant encountered
risk at even time two, while its odd-time rows are genuinely history
dependent as checked above. -/
theorem prefixDynamicTargetFalse_history_changes_risk :
    prefixEncounteredTargetConditionalRisk prefixDynamicBoolEnvironment
        (dynamicTargetCatalog false) (dynamicBoolScore false)
        2 dynamicInteriorFalsePath = 5 / 8 ∧
      prefixEncounteredTargetConditionalRisk prefixDynamicBoolEnvironment
        (dynamicTargetCatalog false) (dynamicBoolScore false)
        2 dynamicInteriorTruePath = 3 / 8 := by
  constructor <;>
    norm_num [prefixEncounteredTargetConditionalRisk,
      prefixDynamicBoolEnvironment, dynamicTargetCatalog, dynamicBoolScore,
      dynamicInteriorAction, dynamicInteriorFalsePath,
      dynamicInteriorTruePath, dynamicBiasedBoolPMF,
      PMF.ofFintype_apply, Preorder.frestrictLe_apply, Fintype.sum_bool]

/-- A path with a positive first score and zero second score for both target
atoms. -/
def dynamicVariancePath (n : ℕ) : ControlledObservation Bool Bool :=
  if n = 1 then (false, true)
  else if n = 2 then (true, false)
  else (false, false)

theorem dynamicVariancePath_scores (i : Bool) :
    controlledObservedImportanceScore dynamicHistoryBehavior
        (dynamicTargetCatalog i) (dynamicBoolScore i) 3
        0 dynamicVariancePath = (if i then 1 / 9 else 1 / 3) ∧
      controlledObservedImportanceScore dynamicHistoryBehavior
        (dynamicTargetCatalog i) (dynamicBoolScore i) 3
        1 dynamicVariancePath = 0 := by
  fin_cases i <;>
    norm_num [controlledObservedImportanceScore, observedTrajectoryScore,
      controlledNormalizedImportanceScore, controlledImportanceRatio,
      dynamicHistoryBehavior, dynamicTargetCatalog, dynamicBoolScore,
      dynamicInteriorAction, dynamicVariancePath, dynamicBiasedBoolPMF,
      PMF.ofFintype_apply, Preorder.frestrictLe_apply]

/-- The observed empirical-Bernstein variance term is nonzero for each target
policy, rather than degenerating to a constant-score receipt. -/
theorem dynamicVariancePath_positive (i : Bool) :
    0 < forwardBesselQ
      (fun k ↦ controlledObservedImportanceScore dynamicHistoryBehavior
        (dynamicTargetCatalog i) (dynamicBoolScore i) 3
        k dynamicVariancePath) 2 := by
  rcases dynamicVariancePath_scores i with ⟨hzero, hone⟩
  fin_cases i <;>
    norm_num [forwardBesselQ, forwardPrefixMean, hzero, hone,
      Finset.sum_range_succ]

def dynamicUniformPrior (_i : Bool) : ℝ := 1 / 2

theorem dynamicUniformPrior_isFullSupportPMF :
    IsFullSupportPMF dynamicUniformPrior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> norm_num [dynamicUniformPrior]
  · norm_num [dynamicUniformPrior, Fintype.sum_bool]
  · intro i
    fin_cases i <;> norm_num [dynamicUniformPrior]

def dynamicTiltWeight (_j : Bool) : ℝ := 1 / 2

theorem dynamicTiltWeight_isFullSupportPMF :
    IsFullSupportPMF dynamicTiltWeight := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro j
    fin_cases j <;> norm_num [dynamicTiltWeight]
  · norm_num [dynamicTiltWeight, Fintype.sum_bool]
  · intro j
    fin_cases j <;> norm_num [dynamicTiltWeight]

def dynamicTilts (j : Bool) : ℝ := if j then 1 / 4 else 1 / 5

theorem dynamicTilts_pos (j : Bool) : 0 < dynamicTilts j := by
  fin_cases j <;> norm_num [dynamicTilts]

theorem dynamicTilts_lt_one (j : Bool) : dynamicTilts j < 1 := by
  fin_cases j <;> norm_num [dynamicTilts]

/-- Concrete all-time certificate for two genuinely history-dependent target
policies under a genuinely history-dependent behavior policy. -/
theorem dynamicBoolComparator_certificate :
    ∃ goodEvent : Set (ℕ → ControlledObservation Bool Bool),
      (controlledTrajectoryMeasure dynamicBoolEnvironment
          dynamicHistoryBehavior (false, false)).real goodEventᶜ ≤ 1 / 20 ∧
        ∀ x ∈ goodEvent, ∀ j : Bool,
          ∀ posterior : Bool → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              dynamicTargetPolicyPosteriorEncounteredRisk
                  dynamicBoolEnvironment dynamicTargetCatalog
                    dynamicBoolScore posterior n x <
                dynamicTargetPolicyComparatorBoundary
                  dynamicUniformPrior dynamicTiltWeight dynamicTilts
                    dynamicHistoryBehavior dynamicTargetCatalog
                      dynamicBoolScore 3 posterior (1 / 20) j n x := by
  exact exists_dynamicTargetPolicyComparator_event
    (ι := Bool) (τ := Bool)
    dynamicBoolEnvironment dynamicHistoryBehavior (false, false)
    dynamicTargetCatalog dynamicBoolScore dynamicBoolScore_mem_Icc
    (C := 3) (by norm_num) dynamicHistoryBehavior_overlap
    dynamicHistoryBehavior_ratioBound
    dynamicUniformPrior_isFullSupportPMF
    dynamicTiltWeight_isFullSupportPMF
    (lam := dynamicTilts) (delta := (1 / 20 : ℝ))
    (by norm_num) dynamicTilts_pos dynamicTilts_lt_one

/-- Stronger certificate with the genuinely prefix/time-dependent environment
kernel. -/
theorem prefixDynamicBoolComparator_certificate :
    ∃ goodEvent : Set (ℕ → ControlledObservation Bool Bool),
      (prefixControlledTrajectoryMeasure prefixDynamicBoolEnvironment
          dynamicHistoryBehavior (false, false)).real goodEventᶜ ≤ 1 / 20 ∧
        ∀ x ∈ goodEvent, ∀ j : Bool,
          ∀ posterior : Bool → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              prefixDynamicTargetPolicyPosteriorEncounteredRisk
                  prefixDynamicBoolEnvironment dynamicTargetCatalog
                    dynamicBoolScore posterior n x <
                prefixDynamicTargetPolicyComparatorBoundary
                  dynamicUniformPrior dynamicTiltWeight dynamicTilts
                    dynamicHistoryBehavior dynamicTargetCatalog
                      dynamicBoolScore 3 posterior (1 / 20) j n x := by
  exact exists_prefixDynamicTargetPolicyComparator_event
    (ι := Bool) (τ := Bool)
    prefixDynamicBoolEnvironment dynamicHistoryBehavior (false, false)
    dynamicTargetCatalog dynamicBoolScore dynamicBoolScore_mem_Icc
    (C := 3) (by norm_num) dynamicHistoryBehavior_overlap
    dynamicHistoryBehavior_ratioBound
    dynamicUniformPrior_isFullSupportPMF
    dynamicTiltWeight_isFullSupportPMF
    (lam := dynamicTilts) (delta := (1 / 20 : ℝ))
    (by norm_num) dynamicTilts_pos dynamicTilts_lt_one

/-! Public theorem and receipt audit. -/

#check encounteredTargetConditionalRisk
#check controlledTargetConditionalMean_eq_encounteredRisk_div
#check dynamicTargetPolicyPosteriorEncounteredRisk
#check forwardPrefixMean_div
#check dynamicTargetPolicyPosteriorEmpiricalScore
#check posteriorAverage_forwardPrefixMean_controlledTargetConditionalMean
#check dynamicTargetPolicyComparatorBoundary
#check exists_dynamicTargetPolicyComparator_event
#check dynamicTargetPolicyComparator_selected_of_simultaneous
#check PrefixControlledEnvironment
#check homogeneousPrefixControlledEnvironment
#check prefixControlledContinuationPMF
#check prefixControlledContinuationPMF_apply
#check prefixControlledPrefixKernel
#check prefixControlledTrajectoryMeasure
#check prefixControlledTargetConditionalMean
#check conditionalTrajectoryRisk_prefixControlledNormalizedImportanceScore
#check prefixControlledObservedImportanceScore_condExp
#check prefixControlledTargetConditionalMean_stronglyAdapted
#check prefixControlledImportanceCatalog_predictableMean_interfaces
#check prefixEncounteredTargetConditionalRisk
#check prefixControlledTargetConditionalMean_eq_risk_div
#check prefixDynamicTargetPolicyPosteriorEncounteredRisk
#check posteriorAverage_forwardPrefixMean_prefixControlledTargetMean
#check prefixDynamicTargetPolicyComparatorBoundary
#check exists_prefixDynamicTargetPolicyComparator_event
#check prefixDynamicTargetPolicyComparator_selected_of_simultaneous

#print axioms controlledTargetConditionalMean_eq_encounteredRisk_div
#print axioms forwardPrefixMean_div
#print axioms posteriorAverage_forwardPrefixMean_controlledTargetConditionalMean
#print axioms exists_dynamicTargetPolicyComparator_event
#print axioms dynamicTargetPolicyComparator_selected_of_simultaneous
#print axioms prefixControlledContinuationPMF_apply
#print axioms conditionalTrajectoryRisk_prefixControlledNormalizedImportanceScore
#print axioms prefixControlledObservedImportanceScore_condExp
#print axioms prefixControlledTargetConditionalMean_stronglyAdapted
#print axioms prefixControlledImportanceCatalog_predictableMean_interfaces
#print axioms prefixControlledTargetConditionalMean_eq_risk_div
#print axioms posteriorAverage_forwardPrefixMean_prefixControlledTargetMean
#print axioms exists_prefixDynamicTargetPolicyComparator_event
#print axioms prefixDynamicTargetPolicyComparator_selected_of_simultaneous

#check dynamicBiasedBoolPMF_pos
#check dynamicHistoryBehavior_pos
#check prefixDynamicBoolEnvironment_pos
#check dynamicBoolScore_mem_Icc
#check dynamicHistoryBehavior_overlap
#check dynamicHistoryBehavior_ratioBound
#check dynamicHistoryWitness_same_initial_current
#check dynamicHistoryWitness_different_interior
#check dynamicTargetFalse_history_changes_risk
#check dynamicTargetTrue_history_changes_risk
#check dynamicVariancePath_scores
#check dynamicVariancePath_positive
#check dynamicUniformPrior_isFullSupportPMF
#check dynamicTiltWeight_isFullSupportPMF
#check dynamicTilts_pos
#check dynamicTilts_lt_one
#check dynamicBoolComparator_certificate
#check prefixDynamicEnvironment_history_witness
#check prefixDynamicContinuationPMF_pos
#check prefixDynamicTargetFalse_history_changes_risk
#check prefixDynamicBoolComparator_certificate

#print axioms dynamicBiasedBoolPMF_pos
#print axioms dynamicHistoryBehavior_pos
#print axioms prefixDynamicBoolEnvironment_pos
#print axioms dynamicBoolScore_mem_Icc
#print axioms dynamicHistoryBehavior_overlap
#print axioms dynamicHistoryBehavior_ratioBound
#print axioms dynamicHistoryWitness_same_initial_current
#print axioms dynamicHistoryWitness_different_interior
#print axioms dynamicTargetFalse_history_changes_risk
#print axioms dynamicTargetTrue_history_changes_risk
#print axioms dynamicVariancePath_scores
#print axioms dynamicVariancePath_positive
#print axioms dynamicUniformPrior_isFullSupportPMF
#print axioms dynamicTiltWeight_isFullSupportPMF
#print axioms dynamicTilts_pos
#print axioms dynamicTilts_lt_one
#print axioms dynamicBoolComparator_certificate
#print axioms prefixDynamicEnvironment_history_witness
#print axioms prefixDynamicContinuationPMF_pos
#print axioms prefixDynamicTargetFalse_history_changes_risk
#print axioms prefixDynamicBoolComparator_certificate

end

end FormalSLT.Examples.CheckDynamicTargetPolicyComparator
