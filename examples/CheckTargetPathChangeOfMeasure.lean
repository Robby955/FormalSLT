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

/-- The same target occupancy receipt on the actual infinite trajectory law. -/
theorem pathActualTarget_true_occupancy :
    prefixControlledTargetTrajectoryStateOccupancy
        pathCopyEnvironment pathBiasedTarget pathInitial 1 true = 3 / 4 := by
  rw [prefixControlledTargetTrajectoryStateOccupancy_eq_finite]
  exact pathTarget_true_occupancy

/-- The cumulative likelihood ratio is also normalized when integrated over
the actual infinite behavior trajectory law. -/
theorem pathActualLikelihoodRatio_behaviorExpectation_eq_one :
    (∫ x,
        controlledFinitePrefixLikelihoodRatio
          pathFairBehavior pathBiasedTarget 1
            (Preorder.frestrictLe 1 x)
      ∂prefixControlledTrajectoryMeasure
        pathCopyEnvironment pathFairBehavior pathInitial) = 1 := by
  change
    (∫ x,
        controlledFinitePrefixLikelihoodRatio
          pathFairBehavior pathBiasedTarget 1
            (Preorder.frestrictLe 1 x)
      ∂prefixControlledTargetTrajectoryMeasure
        pathCopyEnvironment pathFairBehavior pathInitial) = 1
  rw [← controlledFinitePrefixExpectation_eq_trajectoryIntegral
    pathCopyEnvironment pathFairBehavior pathInitial 1]
  exact pathLikelihoodRatio_behaviorExpectation_eq_one

/-- Actual behavior-path likelihood weighting recovers target occupancy
`3/4`. -/
theorem pathActualWeightedBehavior_true_occupancy :
    (∫ x,
        controlledFinitePrefixLikelihoodRatio
            pathFairBehavior pathBiasedTarget 1
            (Preorder.frestrictLe 1 x) *
          Set.indicator
            {u | (u ⟨1, Finset.mem_Iic.mpr le_rfl⟩).2 = true}
            (fun _u ↦ 1) (Preorder.frestrictLe 1 x)
      ∂prefixControlledTrajectoryMeasure
        pathCopyEnvironment pathFairBehavior pathInitial) = 3 / 4 := by
  rw [← prefixControlledTargetTrajectoryStateOccupancy_changeOfMeasure
    pathCopyEnvironment pathFairBehavior pathBiasedTarget pathInitial
      pathFairBehavior_overlap 1 true]
  exact pathActualTarget_true_occupancy

#check controlledPrefixSnoc
#check controlledPrefixRestrict
#check controlledPrefixRestrict_refl
#check controlledPrefixSnoc_last
#check controlledPrefixRestrict_snoc
#check prefixControlledTargetTrajectoryMeasure
#check prefixControlledTargetTrajectoryMeasure.instIsProbabilityMeasure
#check controlledFinitePrefixExpectation
#check controlledFinitePrefixExpectation_eq_partialTrajIntegral
#check controlledFinitePrefixExpectation_eq_trajectoryIntegral
#check controlledFinitePrefixExpectation_one
#check controlledFinitePrefixLikelihoodRatio
#check controlledFinitePrefixLikelihoodRatio_snoc
#check prefixControlledContinuation_expectation_changeOfMeasure
#check controlledFinitePrefixExpectation_changeOfMeasure
#check prefixControlledTargetTrajectory_integral_changeOfMeasure
#check controlledTrajectoryCylinder
#check measurableSet_controlledTrajectoryCylinder
#check prefixControlledTargetTrajectory_cylinder_changeOfMeasure
#check controlledFiniteHorizonRisk
#check controlledFiniteHorizonRisk_changeOfMeasure
#check controlledFinitePrefixEventProbability
#check controlledFinitePrefixEventProbability_changeOfMeasure
#check controlledFinitePrefixEventProbability_eq_trajectoryCylinderProbability
#check controlledFiniteHorizonStateOccupancy
#check controlledFiniteHorizonStateOccupancy_changeOfMeasure
#check prefixControlledTargetTrajectoryStateOccupancy
#check prefixControlledTargetTrajectoryStateOccupancy_eq_finite
#check prefixControlledTargetTrajectoryStateOccupancy_changeOfMeasure
#check controlledFinitePrefixLikelihoodRatio_le_pow
#check controlledWeightedPrefixPayoff_mem_Icc

#check pathFairBoolPMF
#check pathTargetBoolPMF
#check pathFairBehavior
#check pathBiasedTarget
#check pathCopyEnvironment
#check pathInitial
#check pathFairBehavior_overlap
#check pathFairBehavior_ratioBound
#check pathInitialPrefix
#check pathTruePrefix
#check pathFalsePrefix
#check pathTruePrefix_likelihoodRatio
#check pathFalsePrefix_likelihoodRatio
#check pathBehavior_true_occupancy
#check pathTarget_true_occupancy
#check pathTarget_behavior_occupancy_ne
#check pathLikelihoodRatio_behaviorExpectation_eq_one
#check pathWeightedBehavior_true_occupancy
#check pathActualTarget_true_occupancy
#check pathActualLikelihoodRatio_behaviorExpectation_eq_one
#check pathActualWeightedBehavior_true_occupancy

#print axioms controlledPrefixRestrict_refl
#print axioms controlledPrefixSnoc_last
#print axioms controlledPrefixRestrict_snoc
#print axioms controlledFinitePrefixExpectation_eq_partialTrajIntegral
#print axioms controlledFinitePrefixExpectation_eq_trajectoryIntegral
#print axioms controlledFinitePrefixExpectation_one
#print axioms controlledFinitePrefixLikelihoodRatio_snoc
#print axioms prefixControlledContinuation_expectation_changeOfMeasure
#print axioms controlledFinitePrefixExpectation_changeOfMeasure
#print axioms prefixControlledTargetTrajectory_integral_changeOfMeasure
#print axioms measurableSet_controlledTrajectoryCylinder
#print axioms prefixControlledTargetTrajectory_cylinder_changeOfMeasure
#print axioms controlledFiniteHorizonRisk_changeOfMeasure
#print axioms controlledFinitePrefixEventProbability_changeOfMeasure
#print axioms controlledFinitePrefixEventProbability_eq_trajectoryCylinderProbability
#print axioms controlledFiniteHorizonStateOccupancy_changeOfMeasure
#print axioms prefixControlledTargetTrajectoryStateOccupancy_eq_finite
#print axioms prefixControlledTargetTrajectoryStateOccupancy_changeOfMeasure
#print axioms controlledFinitePrefixLikelihoodRatio_le_pow
#print axioms controlledWeightedPrefixPayoff_mem_Icc

#print axioms pathFairBehavior_overlap
#print axioms pathFairBehavior_ratioBound
#print axioms pathTruePrefix_likelihoodRatio
#print axioms pathFalsePrefix_likelihoodRatio
#print axioms pathBehavior_true_occupancy
#print axioms pathTarget_true_occupancy
#print axioms pathTarget_behavior_occupancy_ne
#print axioms pathLikelihoodRatio_behaviorExpectation_eq_one
#print axioms pathWeightedBehavior_true_occupancy
#print axioms pathActualTarget_true_occupancy
#print axioms pathActualLikelihoodRatio_behaviorExpectation_eq_one
#print axioms pathActualWeightedBehavior_true_occupancy

end

end FormalSLT.Examples.CheckTargetPathChangeOfMeasure
