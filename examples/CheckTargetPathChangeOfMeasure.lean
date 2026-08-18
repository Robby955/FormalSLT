/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.TargetPathChangeOfMeasure

/-!
# Finite-horizon target-path change-of-measure receipt

A fair behavior policy and a target policy assigning probability `3/4` to
action `true` use an environment which copies the chosen action into the next
state.  At horizon one, the target occupancy of state `true` is `3/4` while
the behavior occupancy is `1/2`.  The likelihood ratios are exactly `3/2`
and `1/2`, their behavior expectation is one, and likelihood weighting
recovers the target occupancy.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Examples.CheckTargetPathChangeOfMeasure

open FormalSLT.StochasticDynamics

noncomputable section

def pathFairBoolPMF : PMF Bool :=
  PMF.ofFintype
    (fun _b ↦ ((1 / 2 : NNReal) : ENNReal))
    (by
      have hsumNN : (1 / 2 : NNReal) + 1 / 2 = 1 := by norm_num
      have hsum : ((1 / 2 : NNReal) : ENNReal) +
          ((1 / 2 : NNReal) : ENNReal) = 1 := by
        rw [← ENNReal.coe_add, hsumNN]
        rfl
      rw [Fintype.sum_bool]
      exact hsum)

def pathTargetBoolPMF : PMF Bool :=
  PMF.ofFintype
    (fun b ↦ if b then
      ((3 / 4 : NNReal) : ENNReal)
    else ((1 / 4 : NNReal) : ENNReal))
    (by
      have hsumNN : (3 / 4 : NNReal) + 1 / 4 = 1 := by norm_num
      have hsum : ((3 / 4 : NNReal) : ENNReal) +
          ((1 / 4 : NNReal) : ENNReal) = 1 := by
        rw [← ENNReal.coe_add, hsumNN]
        rfl
      simpa [Fintype.sum_bool, add_comm] using hsum)

def pathFairBehavior : BehaviorPolicy Bool Bool :=
  fun _n _u ↦ pathFairBoolPMF

def pathBiasedTarget : TargetPolicy Bool Bool :=
  fun _n _u ↦ pathTargetBoolPMF

/-- The environment deterministically reveals the chosen action as the next
state. -/
def pathCopyEnvironment : PrefixControlledEnvironment Bool Bool :=
  fun _n _u a ↦ PMF.pure a

def pathInitial : ControlledObservation Bool Bool := (false, false)

theorem pathFairBehavior_overlap :
    ControlledPolicyOverlap pathFairBehavior pathBiasedTarget := by
  intro n u a hzero
  fin_cases a <;>
    norm_num [pathFairBehavior, pathFairBoolPMF,
      pathBiasedTarget, pathTargetBoolPMF, PMF.ofFintype_apply] at hzero

theorem pathFairBehavior_ratioBound :
    ControlledPolicyRatioBound pathFairBehavior pathBiasedTarget (3 / 2) := by
  intro n u a
  fin_cases a <;>
    norm_num [pathFairBehavior, pathFairBoolPMF,
      pathBiasedTarget, pathTargetBoolPMF, PMF.ofFintype_apply]

def pathInitialPrefix :
    (i : Finset.Iic 0) → ControlledObservation Bool Bool :=
  fun _ ↦ pathInitial

def pathTruePrefix :
    (i : Finset.Iic 1) → ControlledObservation Bool Bool :=
  controlledPrefixSnoc pathInitialPrefix (true, true)

def pathFalsePrefix :
    (i : Finset.Iic 1) → ControlledObservation Bool Bool :=
  controlledPrefixSnoc pathInitialPrefix (false, false)

/-- The selected true action receives target/behavior weight `(3/4)/(1/2)`. -/
theorem pathTruePrefix_likelihoodRatio :
    controlledFinitePrefixLikelihoodRatio
        pathFairBehavior pathBiasedTarget 1 pathTruePrefix = 3 / 2 := by
  norm_num [controlledFinitePrefixLikelihoodRatio, pathTruePrefix,
    pathInitialPrefix, controlledPrefixSnoc, controlledPrefixRestrict,
    controlledImportanceRatio, pathFairBehavior, pathFairBoolPMF,
    pathBiasedTarget, pathTargetBoolPMF, PMF.ofFintype_apply]

/-- The selected false action receives target/behavior weight `(1/4)/(1/2)`. -/
theorem pathFalsePrefix_likelihoodRatio :
    controlledFinitePrefixLikelihoodRatio
        pathFairBehavior pathBiasedTarget 1 pathFalsePrefix = 1 / 2 := by
  norm_num [controlledFinitePrefixLikelihoodRatio, pathFalsePrefix,
    pathInitialPrefix, controlledPrefixSnoc, controlledPrefixRestrict,
    controlledImportanceRatio, pathFairBehavior, pathFairBoolPMF,
    pathBiasedTarget, pathTargetBoolPMF, PMF.ofFintype_apply]

/-- The behavior law puts probability `1/2` on state `true` after one
decision. -/
theorem pathBehavior_true_occupancy :
    controlledFiniteHorizonStateOccupancy
        pathCopyEnvironment pathFairBehavior pathInitial 1 true = 1 / 2 := by
  norm_num [controlledFiniteHorizonStateOccupancy,
    controlledFinitePrefixEventProbability,
    controlledFinitePrefixExpectation, pathCopyEnvironment,
    pathFairBehavior, pathFairBoolPMF, pathInitial,
    prefixControlledContinuationPMF_apply, PMF.ofFintype_apply,
    controlledPrefixSnoc, pathInitialPrefix, Set.indicator,
    Fintype.sum_prod_type]

/-- The target law puts probability `3/4` on state `true` after one
decision, so its occupancy genuinely differs from behavior. -/
theorem pathTarget_true_occupancy :
    controlledFiniteHorizonStateOccupancy
        pathCopyEnvironment pathBiasedTarget pathInitial 1 true = 3 / 4 := by
  norm_num [controlledFiniteHorizonStateOccupancy,
    controlledFinitePrefixEventProbability,
    controlledFinitePrefixExpectation, pathCopyEnvironment,
    pathBiasedTarget, pathTargetBoolPMF, pathInitial,
    prefixControlledContinuationPMF_apply, PMF.ofFintype_apply,
    controlledPrefixSnoc, pathInitialPrefix, Set.indicator,
    Fintype.sum_prod_type]

theorem pathTarget_behavior_occupancy_ne :
    controlledFiniteHorizonStateOccupancy
        pathCopyEnvironment pathBiasedTarget pathInitial 1 true ≠
      controlledFiniteHorizonStateOccupancy
        pathCopyEnvironment pathFairBehavior pathInitial 1 true := by
  rw [pathTarget_true_occupancy, pathBehavior_true_occupancy]
  norm_num

/-- The cumulative likelihood ratio is normalized under behavior. -/
theorem pathLikelihoodRatio_behaviorExpectation_eq_one :
    controlledFinitePrefixExpectation
        pathCopyEnvironment pathFairBehavior pathInitial 1
        (controlledFinitePrefixLikelihoodRatio
          pathFairBehavior pathBiasedTarget 1) = 1 := by
  calc
    controlledFinitePrefixExpectation
        pathCopyEnvironment pathFairBehavior pathInitial 1
        (controlledFinitePrefixLikelihoodRatio
          pathFairBehavior pathBiasedTarget 1) =
      controlledFinitePrefixExpectation
        pathCopyEnvironment pathFairBehavior pathInitial 1 (fun u ↦
          controlledFinitePrefixLikelihoodRatio
            pathFairBehavior pathBiasedTarget 1 u * 1) := by
              congr 1
              funext u
              ring
    _ = controlledFinitePrefixExpectation
        pathCopyEnvironment pathBiasedTarget pathInitial 1
          (fun _u ↦ 1) :=
      (controlledFinitePrefixExpectation_changeOfMeasure
        pathCopyEnvironment pathFairBehavior pathBiasedTarget pathInitial
          pathFairBehavior_overlap 1 (fun _u ↦ 1)).symm
    _ = 1 := controlledFinitePrefixExpectation_one
      pathCopyEnvironment pathBiasedTarget pathInitial 1

/-- Likelihood weighting recovers the target occupancy `3/4` exactly. -/
theorem pathWeightedBehavior_true_occupancy :
    controlledFinitePrefixExpectation
        pathCopyEnvironment pathFairBehavior pathInitial 1 (fun u ↦
          controlledFinitePrefixLikelihoodRatio
              pathFairBehavior pathBiasedTarget 1 u *
            Set.indicator
              {u | (u ⟨1, Finset.mem_Iic.mpr le_rfl⟩).2 = true}
              (fun _u ↦ 1) u) = 3 / 4 := by
  rw [← controlledFiniteHorizonStateOccupancy_changeOfMeasure
    pathCopyEnvironment pathFairBehavior pathBiasedTarget pathInitial
      pathFairBehavior_overlap 1 true]
  exact pathTarget_true_occupancy

#check prefixControlledTargetTrajectoryMeasure
#check controlledFinitePrefixExpectation_changeOfMeasure
#check controlledFiniteHorizonRisk_changeOfMeasure
#check controlledFinitePrefixEventProbability_changeOfMeasure
#check controlledFiniteHorizonStateOccupancy_changeOfMeasure
#check controlledFinitePrefixLikelihoodRatio_le_pow
#check controlledWeightedPrefixPayoff_mem_Icc

#print axioms controlledFinitePrefixExpectation_one_eq_trajectoryIntegral
#print axioms controlledFinitePrefixExpectation_changeOfMeasure
#print axioms controlledFiniteHorizonStateOccupancy_changeOfMeasure
#print axioms controlledFinitePrefixLikelihoodRatio_le_pow
#print axioms pathLikelihoodRatio_behaviorExpectation_eq_one
#print axioms pathWeightedBehavior_true_occupancy

end

end FormalSLT.Examples.CheckTargetPathChangeOfMeasure
