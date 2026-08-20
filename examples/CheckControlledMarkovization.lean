import FormalSLT.StochasticDynamics.ControlledMarkovization

/-!
# Controlled Markovization receipt

The Boolean behavior policy below changes its favored action with the current
state.  The environment also depends on both the state and action.  The
receipt checks a nonzero augmented transition atom and the exact equality
between the controlled and ordinary Markov path laws.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FormalSLT.Examples.CheckControlledMarkovization

open FormalSLT.StochasticDynamics

noncomputable section

/-- Boolean PMF assigning mass `3/4` to `favored` and `1/4` to the other
atom. -/
def biasedBoolPMF (favored : Bool) : PMF Bool :=
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

/-- Favor the action equal to the current state. -/
def stateDependentBehavior : MarkovBehaviorPolicy Bool Bool :=
  fun state ↦ biasedBoolPMF state

/-- Favor the next state equal to the Boolean comparison of current state and
action, so both arguments affect the row. -/
def stateActionEnvironment (state action : Bool) : PMF Bool :=
  biasedBoolPMF (state == action)

/-- The behavior row genuinely changes with the current state. -/
theorem stateDependentBehavior_witness :
    stateDependentBehavior false true = 1 / 4 ∧
      stateDependentBehavior true true = 3 / 4 := by
  constructor <;>
    norm_num [stateDependentBehavior, biasedBoolPMF, PMF.ofFintype_apply]

/-- From current pair `(false,true)` to `(true,false)`, the selected action
has mass `3/4` and the selected outcome has mass `1/4`. -/
theorem augmentedBehaviorKernel_atom_witness :
    augmentedBehaviorKernel stateActionEnvironment stateDependentBehavior
        (false, true) (true, false) = ((3 / 16 : NNReal) : ENNReal) := by
  have hNN : (3 / 4 : NNReal) * (1 / 4) = 3 / 16 := by norm_num
  have h :
      ((3 / 4 : NNReal) : ENNReal) * ((1 / 4 : NNReal) : ENNReal) =
        ((3 / 16 : NNReal) : ENNReal) := by
    simpa only [ENNReal.coe_mul] using
      congrArg (fun q : NNReal ↦ (q : ENNReal)) hNN
  rw [augmentedBehaviorKernel_apply]
  simpa [stateDependentBehavior, stateActionEnvironment, biasedBoolPMF,
    PMF.ofFintype_apply] using h

/-- Any event, including an empirical-transition confidence event on the
augmented chain, has the same mass under the two extensionally equal
path-law interfaces. -/
theorem controlled_event_mass_rewrite
    (event : Set (ℕ → ControlledObservation Bool Bool)) :
    (controlledTrajectoryMeasure stateActionEnvironment
        (markovBehaviorPolicyAsHistory stateDependentBehavior)
        (false, false)).real event =
      (markovPathMeasure
        (augmentedBehaviorKernel stateActionEnvironment stateDependentBehavior)
        (false, false)).real event := by
  rw [controlledTrajectoryMeasure_markovBehaviorPolicy]

#check MarkovBehaviorPolicy
#check markovBehaviorPolicyAsHistory
#check augmentedBehaviorKernel
#check augmentedBehaviorKernel_apply
#check controlledContinuationPMF_markovBehaviorPolicy
#check controlledPrefixKernel_markovBehaviorPolicy
#check controlledTrajectoryMeasure_markovBehaviorPolicy

#print axioms FormalSLT.StochasticDynamics.augmentedBehaviorKernel_apply
#print axioms FormalSLT.StochasticDynamics.controlledContinuationPMF_markovBehaviorPolicy
#print axioms FormalSLT.StochasticDynamics.controlledPrefixKernel_markovBehaviorPolicy
#print axioms FormalSLT.StochasticDynamics.controlledTrajectoryMeasure_markovBehaviorPolicy

end

end FormalSLT.Examples.CheckControlledMarkovization
