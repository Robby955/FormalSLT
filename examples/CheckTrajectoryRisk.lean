/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.StochasticDynamics.TrajectoryRisk

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FormalSLT.Examples.CheckTrajectoryRisk

open StochasticDynamics

noncomputable section

/-- Whether the initial and current states of a prefix agree.  Unlike a Markov
state summary, this reads both ends of the supplied prefix. -/
def prefixAgreement (n : ℕ) (u : (i : Finset.Iic n) → Bool) : Bool :=
  decide (u ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩ =
    u ⟨n, Finset.mem_Iic.mpr le_rfl⟩)

/-- A nondegenerate Bool law whose favored next state depends on the whole
prefix through `prefixAgreement`. -/
def prefixDependentBoolPMF (n : ℕ)
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

/-- A trajectory kernel which is not determined by the current state: it also
consults the initial coordinate of the prefix. -/
def prefixDependentBoolKernel (n : ℕ) :
    Kernel ((i : Finset.Iic n) → Bool) Bool :=
  Kernel.ofFunOfCountable fun u ↦ (prefixDependentBoolPMF n u).toMeasure

instance prefixDependentBoolKernel.instIsMarkovKernel (n : ℕ) :
    IsMarkovKernel (prefixDependentBoolKernel n) :=
  ⟨fun u ↦ by
    change IsProbabilityMeasure (prefixDependentBoolPMF n u).toMeasure
    infer_instance⟩

/-- A bounded score which also reads the initial state of the prefix. -/
def prefixDependentBoolScore : TrajectoryScore Bool :=
  fun n u y ↦
    if u ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩ then
      if y then 1 else 0
    else 0

theorem prefixDependentBoolScore_mem_Icc :
    ∀ n u y, prefixDependentBoolScore n u y ∈ Set.Icc (0 : ℝ) 1 := by
  intro n u y
  cases hfirst : u ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩ <;>
    cases y <;> simp [prefixDependentBoolScore, hfirst]

/-- A path with the same current state at time one as `allFalsePath`, but a
different state at time zero. -/
def trueThenFalsePath (n : ℕ) : Bool :=
  if n = 0 then true else false

def allFalsePath (_n : ℕ) : Bool := false

theorem historyWitness_same_current :
    trueThenFalsePath 1 = allFalsePath 1 := by
  simp [trueThenFalsePath, allFalsePath]

theorem historyWitness_different_initial :
    trueThenFalsePath 0 ≠ allFalsePath 0 := by
  simp [trueThenFalsePath, allFalsePath]

/-- The two prefixes have the same current state, but assign different mass to
the next state `true`; this witnesses genuine prefix dependence in the kernel
itself, independently of the score. -/
theorem prefixDependentBool_kernel_witness :
    prefixDependentBoolPMF 1
        (Preorder.frestrictLe 1 trueThenFalsePath) true = 1 / 4 ∧
      prefixDependentBoolPMF 1
        (Preorder.frestrictLe 1 allFalsePath) true = 3 / 4 := by
  constructor <;>
    norm_num [prefixDependentBoolPMF, prefixAgreement, PMF.ofFintype_apply,
      Preorder.frestrictLe_apply, trueThenFalsePath, allFalsePath]

/-- Despite agreeing at the current state `x 1`, the two paths have different
one-step conditional risks.  This is a checked witness that the example does
not collapse to a current-state Markov kernel/score. -/
theorem prefixDependentBool_conditionalRisk_witness :
    conditionalTrajectoryRisk prefixDependentBoolKernel
        prefixDependentBoolScore 1 trueThenFalsePath = 1 / 4 ∧
      conditionalTrajectoryRisk prefixDependentBoolKernel
        prefixDependentBoolScore 1 allFalsePath = 0 := by
  constructor
  · unfold conditionalTrajectoryRisk prefixDependentBoolKernel
    change ∫ y, prefixDependentBoolScore 1
        (Preorder.frestrictLe 1 trueThenFalsePath) y
      ∂(prefixDependentBoolPMF 1
        (Preorder.frestrictLe 1 trueThenFalsePath)).toMeasure = 1 / 4
    rw [PMF.integral_eq_sum]
    norm_num [prefixDependentBoolPMF, prefixDependentBoolScore, prefixAgreement,
      PMF.ofFintype_apply, Fintype.sum_bool, Preorder.frestrictLe_apply,
      trueThenFalsePath]
  · unfold conditionalTrajectoryRisk prefixDependentBoolKernel
    change ∫ y, prefixDependentBoolScore 1
        (Preorder.frestrictLe 1 allFalsePath) y
      ∂(prefixDependentBoolPMF 1
        (Preorder.frestrictLe 1 allFalsePath)).toMeasure = 0
    rw [PMF.integral_eq_sum]
    norm_num [prefixDependentBoolPMF, prefixDependentBoolScore, prefixAgreement,
      PMF.ofFintype_apply, Fintype.sum_bool, Preorder.frestrictLe_apply,
      allFalsePath]

/-! Audit the full public theorem surface of the prefix-dependent layer. -/

#check StochasticDynamics.TrajectoryScore
#check StochasticDynamics.trajectoryMeasure
#check StochasticDynamics.observedTrajectoryScore
#check StochasticDynamics.conditionalTrajectoryRisk
#check StochasticDynamics.trajectoryRiskInnovation

#check StochasticDynamics.stronglyMeasurable_observedTrajectoryScore_succ
#check StochasticDynamics.measurable_observedTrajectoryScore
#check StochasticDynamics.observedTrajectoryScore_mem_Icc
#check StochasticDynamics.integrable_observedTrajectoryScore
#check StochasticDynamics.map_trajectory_next
#check StochasticDynamics.integral_observedTrajectoryScore_traj
#check StochasticDynamics.observedTrajectoryScore_condExp
#check StochasticDynamics.stronglyMeasurable_conditionalTrajectoryRisk
#check StochasticDynamics.conditionalTrajectoryRisk_mem_Icc
#check StochasticDynamics.integrable_conditionalTrajectoryRisk
#check StochasticDynamics.trajectoryRiskInnovation_incrementAdapted
#check StochasticDynamics.measurable_trajectoryRiskInnovation
#check StochasticDynamics.abs_trajectoryRiskInnovation_le_one
#check StochasticDynamics.integrable_trajectoryRiskInnovation
#check StochasticDynamics.trajectoryRiskInnovation_condExp_eq_zero
#check StochasticDynamics.trajectoryRiskInnovation_condSecondMoment_le_one_fourth

#check StochasticDynamics.trajectoryMeasure_prefixKernel_eq_markovPathMeasure
#check StochasticDynamics.markovSquaredTrajectoryScore
#check StochasticDynamics.observedTrajectoryScore_markovSquaredTrajectoryScore
#check StochasticDynamics.conditionalTrajectoryRisk_markovSquaredTrajectoryScore
#check StochasticDynamics.trajectoryRiskInnovation_markovSquaredTrajectoryScore
#check StochasticDynamics.pathSquaredLoss_condExp_via_trajectory

#check prefixDependentBoolScore_mem_Icc
#check historyWitness_same_current
#check historyWitness_different_initial
#check prefixDependentBool_kernel_witness
#check prefixDependentBool_conditionalRisk_witness

#print axioms StochasticDynamics.observedTrajectoryScore_condExp
#print axioms StochasticDynamics.trajectoryRiskInnovation_incrementAdapted
#print axioms StochasticDynamics.trajectoryRiskInnovation_condExp_eq_zero
#print axioms StochasticDynamics.trajectoryRiskInnovation_condSecondMoment_le_one_fourth
#print axioms StochasticDynamics.trajectoryRiskInnovation_markovSquaredTrajectoryScore
#print axioms StochasticDynamics.pathSquaredLoss_condExp_via_trajectory
#print axioms prefixDependentBool_kernel_witness
#print axioms prefixDependentBool_conditionalRisk_witness

end

end FormalSLT.Examples.CheckTrajectoryRisk
