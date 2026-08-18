import FormalSLT.StochasticDynamics.TrajectoryEmpiricalBernsteinPACBayes

/-!
# Prefix-dependent trajectory empirical-Bernstein PAC-Bayes checks

This receipt instantiates the outer-mass theorem with a Boolean kernel whose
transition row and one score atom genuinely inspect an interior prefix
coordinate.  The two witness histories start at the certified initial state,
agree at the current state, and differ at the interior coordinate.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open scoped ENNReal NNReal

namespace FormalSLT.Examples.CheckTrajectoryEmpiricalBernsteinPACBayes

open FormalSLT.StochasticDynamics

noncomputable section

/-- Read the interior coordinate `u 1` when available, with a total fallback
at time zero. -/
def ebInteriorState (n : ℕ) (u : (i : Finset.Iic n) → Bool) : Bool :=
  if h : 1 ≤ n then
    u ⟨1, Finset.mem_Iic.mpr h⟩
  else
    u ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩

/-- A full-support transition row selected by an interior prefix coordinate. -/
def ebHistoryDependentBoolPMF (n : ℕ)
    (u : (i : Finset.Iic n) → Bool) : PMF Bool :=
  PMF.ofFintype
    (fun y ↦ if y = ebInteriorState n u
      then ((3 / 4 : NNReal) : ENNReal)
      else ((1 / 4 : NNReal) : ENNReal))
    (by
      have hsumNN : (3 / 4 : NNReal) + 1 / 4 = 1 := by norm_num
      have hsum : ((3 / 4 : NNReal) : ENNReal) +
          ((1 / 4 : NNReal) : ENNReal) = 1 := by
        rw [← ENNReal.coe_add, hsumNN]
        rfl
      cases h : ebInteriorState n u <;>
        simpa [Fintype.sum_bool, h, add_comm] using hsum)

def ebHistoryDependentBoolKernel (n : ℕ) :
    Kernel ((i : Finset.Iic n) → Bool) Bool :=
  Kernel.ofFunOfCountable fun u ↦ (ebHistoryDependentBoolPMF n u).toMeasure

instance ebHistoryDependentBoolKernel.instIsMarkovKernel (n : ℕ) :
    IsMarkovKernel (ebHistoryDependentBoolKernel n) :=
  ⟨fun u ↦ by
    change IsProbabilityMeasure (ebHistoryDependentBoolPMF n u).toMeasure
    infer_instance⟩

/-- Every transition row gives positive mass to both Boolean next states, so
the contrasting finite histories are not created by an off-support initial
coordinate. -/
theorem ebHistoryDependentBoolPMF_pos (n : ℕ)
    (u : (i : Finset.Iic n) → Bool) (y : Bool) :
    0 < ebHistoryDependentBoolPMF n u y := by
  simp only [ebHistoryDependentBoolPMF, PMF.ofFintype_apply]
  split_ifs <;> norm_num

theorem ebHistoryDependentBoolKernel_singleton_pos (n : ℕ)
    (u : (i : Finset.Iic n) → Bool) (y : Bool) :
    0 < ebHistoryDependentBoolKernel n u {y} := by
  change 0 < (ebHistoryDependentBoolPMF n u).toMeasure {y}
  rw [(ebHistoryDependentBoolPMF n u).toMeasure_apply_singleton y
    (MeasurableSet.singleton y)]
  exact ebHistoryDependentBoolPMF_pos n u y

/-- A two-hypothesis score catalog; the `false` atom reads the same interior
prefix coordinate used by the kernel. -/
def ebHistoryDependentBoolScore (i : Bool) : TrajectoryScore Bool :=
  fun n u y ↦
    if i then
      if y = u ⟨n, Finset.mem_Iic.mpr le_rfl⟩ then 1 else 0
    else
      if y = ebInteriorState n u then 1 else 0

theorem ebHistoryDependentBoolScore_mem_Icc :
    ∀ i n u y, ebHistoryDependentBoolScore i n u y ∈ Set.Icc (0 : ℝ) 1 := by
  intro i n u y
  fin_cases i <;> simp [ebHistoryDependentBoolScore] <;>
    split_ifs <;> norm_num

def ebFalseTrueFalsePath (n : ℕ) : Bool := decide (n = 1)

def ebAllFalsePath (_n : ℕ) : Bool := false

/-- The fixture's history dependence is witnessed on two paths with the same
initial and current states, rather than by changing the deterministic initial
coordinate off support. -/
theorem ebHistoryDependentBool_kernel_witness :
    ebFalseTrueFalsePath 0 = false ∧
      ebAllFalsePath 0 = false ∧
      ebFalseTrueFalsePath 2 = ebAllFalsePath 2 ∧
      ebHistoryDependentBoolPMF 2
          (Preorder.frestrictLe 2 ebFalseTrueFalsePath) true = 3 / 4 ∧
      ebHistoryDependentBoolPMF 2
          (Preorder.frestrictLe 2 ebAllFalsePath) true = 1 / 4 := by
  constructor
  · simp [ebFalseTrueFalsePath]
  constructor
  · simp [ebAllFalsePath]
  constructor
  · simp [ebFalseTrueFalsePath, ebAllFalsePath]
  constructor <;>
    norm_num [ebHistoryDependentBoolPMF, ebInteriorState,
      PMF.ofFintype_apply, Preorder.frestrictLe_apply,
      ebFalseTrueFalsePath, ebAllFalsePath]

def ebUniformBoolPrior (_i : Bool) : ℝ := 1 / 2

theorem ebUniformBoolPrior_isFullSupportPMF :
    IsFullSupportPMF ebUniformBoolPrior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> norm_num [ebUniformBoolPrior]
  · norm_num [ebUniformBoolPrior, Fintype.sum_bool]
  · intro i
    fin_cases i <;> norm_num [ebUniformBoolPrior]

def ebUniformBoolTiltWeight (_j : Bool) : ℝ := 1 / 2

theorem ebUniformBoolTiltWeight_isFullSupportPMF :
    IsFullSupportPMF ebUniformBoolTiltWeight := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro j
    fin_cases j <;> norm_num [ebUniformBoolTiltWeight]
  · norm_num [ebUniformBoolTiltWeight, Fintype.sum_bool]
  · intro j
    fin_cases j <;> norm_num [ebUniformBoolTiltWeight]

def ebTrajectoryTilts (j : Bool) : ℝ := if j then 1 / 5 else 1 / 6

theorem ebTrajectoryTilts_pos (j : Bool) : 0 < ebTrajectoryTilts j := by
  fin_cases j <;> norm_num [ebTrajectoryTilts]

theorem ebTrajectoryTilts_lt_one (j : Bool) : ebTrajectoryTilts j < 1 := by
  fin_cases j <;> norm_num [ebTrajectoryTilts]

/-- The specialized boundary exposes the observed per-hypothesis
hybrid-Bessel penalty literally. -/
theorem ebTrajectory_boundary_definition_receipt
    (posterior : Bool → ℝ) (j : Bool) (n : ℕ) (x : ℕ → Bool) :
    trajectoryEmpiricalBernsteinPACBayesBoundary
        ebUniformBoolPrior ebUniformBoolTiltWeight ebTrajectoryTilts
          ebHistoryDependentBoolScore posterior (1 / 20) j n x =
      (klDiv posterior ebUniformBoolPrior +
          Real.log (1 / ((1 / 20 : ℝ) * ebUniformBoolTiltWeight j)) +
          forwardEmpiricalBernsteinPsi (ebTrajectoryTilts j) *
            trajectoryPosteriorHybridBesselPenalty
              posterior ebHistoryDependentBoolScore n x) /
        ((n : ℝ) * ebTrajectoryTilts j) := by
  rfl

/-- Concrete history-dependent trajectory specialization of the uniform
empirical-Bernstein PAC-Bayes event. -/
theorem ebHistoryDependentBool_trajectoryEmpiricalBernstein_certificate :
    ∃ goodEvent : Set (ℕ → Bool),
      (trajectoryMeasure ebHistoryDependentBoolKernel false).real
          goodEventᶜ ≤ 1 / 20 ∧
        ∀ x ∈ goodEvent, ∀ j : Bool,
          ∀ posterior : Bool → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              trajectoryPosteriorAverageConditionalRisk
                  ebHistoryDependentBoolKernel ebHistoryDependentBoolScore
                    posterior n x <
                trajectoryPosteriorEmpiricalPrequentialRisk
                    ebHistoryDependentBoolScore posterior n x +
                  trajectoryEmpiricalBernsteinPACBayesBoundary
                    ebUniformBoolPrior ebUniformBoolTiltWeight
                      ebTrajectoryTilts ebHistoryDependentBoolScore posterior
                        (1 / 20) j n x := by
  exact exists_trajectoryEmpiricalBernsteinPACBayes_event
    (ι := Bool) (τ := Bool)
    ebHistoryDependentBoolKernel false ebHistoryDependentBoolScore_mem_Icc
    ebUniformBoolPrior_isFullSupportPMF
    ebUniformBoolTiltWeight_isFullSupportPMF
    (lam := ebTrajectoryTilts) (delta := (1 / 20 : ℝ))
    (by norm_num) ebTrajectoryTilts_pos ebTrajectoryTilts_lt_one

def ebPointPosterior (selected i : Bool) : ℝ :=
  if i = selected then 1 else 0

theorem ebPointPosterior_isPMF (selected : Bool) :
    IsPMF (ebPointPosterior selected) := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases selected <;> fin_cases i <;> norm_num [ebPointPosterior]
  · fin_cases selected <;> norm_num [ebPointPosterior, Fintype.sum_bool]

def ebPathPosterior (x : ℕ → Bool) (_n : ℕ) : Bool → ℝ :=
  ebPointPosterior (x 1)

theorem ebPathPosterior_isPMF (x : ℕ → Bool) (n : ℕ) :
    IsPMF (ebPathPosterior x n) := ebPointPosterior_isPMF _

def ebPathTiltSelector (x : ℕ → Bool) (_n : ℕ) (_posterior : Bool → ℝ) : Bool :=
  x 1

/-- The same event permits both the posterior and declared tilt to be selected
from the realized path after data observation. -/
theorem ebHistoryDependentBool_selected_certificate :
    ∃ goodEvent : Set (ℕ → Bool),
      (trajectoryMeasure ebHistoryDependentBoolKernel false).real
          goodEventᶜ ≤ 1 / 20 ∧
        ∀ x ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
          trajectoryPosteriorAverageConditionalRisk
              ebHistoryDependentBoolKernel ebHistoryDependentBoolScore
                (ebPathPosterior x n) n x <
            trajectoryPosteriorEmpiricalPrequentialRisk
                ebHistoryDependentBoolScore (ebPathPosterior x n) n x +
              trajectoryEmpiricalBernsteinPACBayesBoundary
                ebUniformBoolPrior ebUniformBoolTiltWeight ebTrajectoryTilts
                  ebHistoryDependentBoolScore (ebPathPosterior x n) (1 / 20)
                    (ebPathTiltSelector x n (ebPathPosterior x n)) n x := by
  exact exists_trajectoryEmpiricalBernsteinPACBayes_selected_event
    (ι := Bool) (τ := Bool)
    ebHistoryDependentBoolKernel false ebHistoryDependentBoolScore_mem_Icc
    ebUniformBoolPrior_isFullSupportPMF
    ebUniformBoolTiltWeight_isFullSupportPMF
    (lam := ebTrajectoryTilts) (delta := (1 / 20 : ℝ))
    (by norm_num) ebTrajectoryTilts_pos ebTrajectoryTilts_lt_one
    ebPathPosterior ebPathPosterior_isPMF ebPathTiltSelector

/-! Public endpoint and receipt audit. -/

#check observedTrajectoryScore_incrementAdapted
#check conditionalTrajectoryRisk_stronglyAdapted
#check forwardPrefixMean_observedTrajectoryScore
#check forwardPrefixMean_conditionalTrajectoryRisk
#check trajectoryPosteriorHybridBesselPenalty
#check trajectoryEmpiricalBernsteinPACBayesBoundary
#check trajectoryEmpiricalBernsteinPACBayesBoundary_eq_generic
#check exists_trajectoryEmpiricalBernsteinPACBayes_event
#check exists_trajectoryEmpiricalBernsteinPACBayes_selected_event

#print axioms observedTrajectoryScore_incrementAdapted
#print axioms conditionalTrajectoryRisk_stronglyAdapted
#print axioms forwardPrefixMean_observedTrajectoryScore
#print axioms forwardPrefixMean_conditionalTrajectoryRisk
#print axioms trajectoryEmpiricalBernsteinPACBayesBoundary_eq_generic
#print axioms exists_trajectoryEmpiricalBernsteinPACBayes_event
#print axioms exists_trajectoryEmpiricalBernsteinPACBayes_selected_event

#check ebHistoryDependentBool_kernel_witness
#check ebHistoryDependentBoolPMF_pos
#check ebHistoryDependentBoolKernel_singleton_pos
#check ebTrajectory_boundary_definition_receipt
#check ebHistoryDependentBool_trajectoryEmpiricalBernstein_certificate
#check ebHistoryDependentBool_selected_certificate

#print axioms ebHistoryDependentBool_kernel_witness
#print axioms ebHistoryDependentBoolPMF_pos
#print axioms ebHistoryDependentBoolKernel_singleton_pos
#print axioms ebTrajectory_boundary_definition_receipt
#print axioms ebHistoryDependentBool_trajectoryEmpiricalBernstein_certificate
#print axioms ebHistoryDependentBool_selected_certificate

end

end FormalSLT.Examples.CheckTrajectoryEmpiricalBernsteinPACBayes
