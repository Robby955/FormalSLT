import FormalSLT.StochasticDynamics.ControlledKernelTV

/-!
# Controlled-kernel TV marginalization receipt

The first Boolean example differs maximally at one environment action row and
agrees at the other.  A fair behavior policy therefore hides exactly half of
that discrepancy in the augmented kernel: conditioning costs the sharp factor
`1 / (1/2) = 2`.

The second behavior policy never selects the discrepant action.  Its augmented
kernels are equal even though that unobserved environment row has TV distance
one, witnessing why positive behavior mass is required.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Examples.CheckControlledKernelTV

open FormalSLT.StochasticDynamics

noncomputable section

/-- Fair Boolean probability mass function. -/
def fairBoolPMF : PMF Bool :=
  PMF.ofFintype (fun _ ↦ ((1 / 2 : NNReal) : ENNReal)) (by
    have hNN : (1 / 2 : NNReal) + 1 / 2 = 1 := by norm_num
    have h : ((1 / 2 : NNReal) : ENNReal) +
        ((1 / 2 : NNReal) : ENNReal) = 1 := by
      rw [← ENNReal.coe_add, hNN]
      rfl
    simpa [Fintype.sum_bool, two_mul] using h)

/-- Every state uses the fair action policy. -/
def fairBehavior : MarkovBehaviorPolicy Bool Bool := fun _state ↦ fairBoolPMF

/-- Reference environment: every state--action row is concentrated at
`false`. -/
def referenceEnvironment (_state _action : Bool) : PMF Bool := PMF.pure false

/-- Candidate environment: the `false` action row is concentrated at `true`,
while the `true` action row agrees with the reference. -/
def candidateEnvironment (_state action : Bool) : PMF Bool :=
  if action then PMF.pure false else PMF.pure true

/-- The environments differ maximally at action `false`. -/
theorem discrepantEnvironmentRow_totalVariation :
    finitePMFTotalVariation
        (referenceEnvironment false false)
        (candidateEnvironment false false) = 1 := by
  norm_num [finitePMFTotalVariation, referenceEnvironment,
    candidateEnvironment, Fintype.sum_bool, PMF.pure_apply]

/-- Under fair behavior, the augmented discrepancy is exactly one half at
every action-major current observation. -/
theorem fairBehavior_augmented_totalVariation
    (current : ControlledObservation Bool Bool) :
    finitePMFTotalVariation
        (augmentedBehaviorKernel referenceEnvironment fairBehavior current)
        (augmentedBehaviorKernel candidateEnvironment fairBehavior current) =
      1 / 2 := by
  rw [finitePMFTotalVariation_augmentedBehaviorKernel_eq_sum]
  norm_num [fairBehavior, fairBoolPMF, PMF.ofFintype_apply,
    finitePMFTotalVariation, referenceEnvironment, candidateEnvironment,
    Fintype.sum_bool, PMF.pure_apply]

/-- The action-conditioned theorem recovers the sharp factor-two bound.  In
the current pair `(true,false)`, `true` is the previous action and `false` is
the current state; the conditioned action is the separate `false` argument. -/
theorem fairBehavior_factorTwo_bound :
    finitePMFTotalVariation
        (referenceEnvironment false false)
        (candidateEnvironment false false) ≤
      (1 / 2 : ℝ) / (fairBehavior false false).toReal := by
  apply environmentKernel_rowTV_le_augmentedKernel_rowTV_div_actionProbability
      referenceEnvironment candidateEnvironment fairBehavior
      true false false
  · norm_num [fairBehavior, fairBoolPMF, PMF.ofFintype_apply]
  · rw [fairBehavior_augmented_totalVariation]

/-- The uniform floor theorem simultaneously controls every state--action
row at the sharp worst-case value one. -/
theorem fairBehavior_uniformFloor_bound :
    ∀ state action,
      finitePMFTotalVariation
          (referenceEnvironment state action)
          (candidateEnvironment state action) ≤ 1 := by
  have h := environmentKernel_rowTV_le_div_behaviorFloor
    referenceEnvironment candidateEnvironment fairBehavior
    (behaviorFloor := (1 / 2 : ℝ)) (eta := (1 / 2 : ℝ))
    (by norm_num)
    (by
      intro state action
      norm_num [fairBehavior, fairBoolPMF, PMF.ofFintype_apply])
    (by
      intro current
      rw [fairBehavior_augmented_totalVariation current])
  simpa using h

/-- Deterministic behavior that never selects action `false`. -/
def zeroMassBehavior : MarkovBehaviorPolicy Bool Bool :=
  fun _state ↦ PMF.pure true

/-- With zero behavior mass on the discrepant action, the augmented kernels
are equal while the hidden environment rows remain TV distance one. -/
theorem zeroMass_nonidentifiability_witness :
    finitePMFTotalVariation
        (augmentedBehaviorKernel referenceEnvironment zeroMassBehavior
          (true, false))
        (augmentedBehaviorKernel candidateEnvironment zeroMassBehavior
          (true, false)) = 0 ∧
      finitePMFTotalVariation
        (referenceEnvironment false false)
        (candidateEnvironment false false) = 1 := by
  constructor
  · rw [finitePMFTotalVariation_augmentedBehaviorKernel_eq_sum]
    norm_num [zeroMassBehavior, finitePMFTotalVariation,
      referenceEnvironment, candidateEnvironment, Fintype.sum_bool,
      PMF.pure_apply]
  · exact discrepantEnvironmentRow_totalVariation

#check finitePMFTotalVariation_augmentedBehaviorKernel_eq_sum
#check actionProbability_mul_environmentKernel_rowTV_le_augmentedKernel_rowTV
#check environmentKernel_rowTV_le_augmentedKernel_rowTV_div_actionProbability
#check environmentKernel_rowTV_le_div_behaviorFloor

#print axioms FormalSLT.StochasticDynamics.finitePMFTotalVariation_augmentedBehaviorKernel_eq_sum
#print axioms FormalSLT.StochasticDynamics.actionProbability_mul_environmentKernel_rowTV_le_augmentedKernel_rowTV
#print axioms FormalSLT.StochasticDynamics.environmentKernel_rowTV_le_augmentedKernel_rowTV_div_actionProbability
#print axioms FormalSLT.StochasticDynamics.environmentKernel_rowTV_le_div_behaviorFloor

#check discrepantEnvironmentRow_totalVariation
#check fairBehavior_augmented_totalVariation
#check fairBehavior_factorTwo_bound
#check fairBehavior_uniformFloor_bound
#check zeroMass_nonidentifiability_witness

#print axioms discrepantEnvironmentRow_totalVariation
#print axioms fairBehavior_augmented_totalVariation
#print axioms fairBehavior_factorTwo_bound
#print axioms fairBehavior_uniformFloor_bound
#print axioms zeroMass_nonidentifiability_witness

end

end FormalSLT.Examples.CheckControlledKernelTV
