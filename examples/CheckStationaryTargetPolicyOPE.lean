import FormalSLT.StochasticDynamics.StationaryTargetPolicyOPE

/-!
# Stationary target-policy OPE receipt

The receipt uses Boolean states and actions.  An action deterministically
becomes the next state.  The behavior policy is uniform, while two distinct
target policies prefer their indexed state with transition probabilities
`3/4` and `1/2`; their importance ratios are genuinely `1/2`, `1`, and `3/2`.
Each target has invariant mass `2/3` on its preferred state, stationary loss
`1/3`, and a nonconstant exact Poisson potential of span `1/3`.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Examples.CheckStationaryTargetPolicyOPE

open FormalSLT.StochasticDynamics

noncomputable section

/-- Uniform Boolean behavior row. -/
def opeFairBoolPMF : PMF Bool :=
  PMF.ofFintype
    (fun _ ↦ ((1 / 2 : NNReal) : ENNReal))
    (by
      have hsumNN : (1 / 2 : NNReal) + 1 / 2 = 1 := by norm_num
      have hsum : ((1 / 2 : NNReal) : ENNReal) +
          ((1 / 2 : NNReal) : ENNReal) = 1 := by
        rw [← ENNReal.coe_add, hsumNN]
        rfl
      simpa [Fintype.sum_bool, two_mul] using hsum)

/-- Every selected action becomes the next state. -/
def opeBoolEnvironment (_z a : Bool) : PMF Bool := PMF.pure a

/-- History-dependent policies are allowed by the theorem; this receipt uses
the uniform special case so all nontrivial ratios come from the targets. -/
def opeUniformBehavior : BehaviorPolicy Bool Bool :=
  fun _n _u ↦ opeFairBoolPMF

/-- Target `i` stays at `i` with probability `3/4` and returns to `i` from the
other state with probability `1/2`. -/
def opeBoolTargetPolicy (i : Bool) : MarkovTargetPolicy Bool Bool :=
  fun z ↦ PMF.ofFintype
    (fun a ↦
      if a = i then
        if z = i then ((3 / 4 : NNReal) : ENNReal)
        else ((1 / 2 : NNReal) : ENNReal)
      else
        if z = i then ((1 / 4 : NNReal) : ENNReal)
        else ((1 / 2 : NNReal) : ENNReal))
    (by
      have hquarterNN : (3 / 4 : NNReal) + 1 / 4 = 1 := by norm_num
      have hquarter : ((3 / 4 : NNReal) : ENNReal) +
          ((1 / 4 : NNReal) : ENNReal) = 1 := by
        rw [← ENNReal.coe_add, hquarterNN]
        rfl
      have hhalfNN : (1 / 2 : NNReal) + 1 / 2 = 1 := by norm_num
      have hhalf : ((1 / 2 : NNReal) : ENNReal) +
          ((1 / 2 : NNReal) : ENNReal) = 1 := by
        rw [← ENNReal.coe_add, hhalfNN]
        rfl
      fin_cases i <;> fin_cases z
      · simpa [Fintype.sum_bool, add_comm] using hquarter
      · simpa [Fintype.sum_bool, add_comm, two_mul] using hhalf
      · simpa [Fintype.sum_bool, add_comm, two_mul] using hhalf
      · simpa [Fintype.sum_bool, add_comm] using hquarter)

/-- The invariant law puts mass `2/3` on the target's preferred state. -/
def opeBoolStationary (i : Bool) : PMF Bool :=
  PMF.ofFintype
    (fun z ↦ if z = i
      then ((2 / 3 : NNReal) : ENNReal)
      else ((1 / 3 : NNReal) : ENNReal))
    (by
      have hsumNN : (2 / 3 : NNReal) + 1 / 3 = 1 := by norm_num
      have hsum : ((2 / 3 : NNReal) : ENNReal) +
          ((1 / 3 : NNReal) : ENNReal) = 1 := by
        rw [← ENNReal.coe_add, hsumNN]
        rfl
      cases i <;> simpa [Fintype.sum_bool, add_comm] using hsum)

/-- Loss is one when the target transitions away from its preferred state. -/
def opeBoolScore (i : Bool) : TargetPolicyTransitionScore Bool Bool :=
  fun _z _a y ↦ if y = i then 0 else 1

theorem opeBoolScore_mem_Icc :
    ∀ i z a y, opeBoolScore i z a y ∈ Set.Icc (0 : ℝ) 1 := by
  intro i z a y
  simp only [opeBoolScore]
  split_ifs <;> norm_num

/-- Exact potential: zero at `i`, `1/3` at the other state. -/
def opeBoolPotential (i z : Bool) : ℝ :=
  if z = i then 0 else 1 / 3

theorem opeBoolPotential_span :
    ∀ i z y, |opeBoolPotential i y - opeBoolPotential i z| ≤ (1 / 3 : ℝ) := by
  intro i z y
  fin_cases i <;> fin_cases z <;> fin_cases y <;>
    norm_num [opeBoolPotential]

/-- The induced target kernels have the claimed invariant PMFs. -/
theorem opeBoolStationary_invariant (i : Bool) :
    IsInvariantPMF
      (targetPolicyKernel opeBoolEnvironment (opeBoolTargetPolicy i))
      (opeBoolStationary i) := by
  have hpreferredNN :
      (2 / 3 : NNReal) * (3 / 4) + (1 / 3) * (1 / 2) = 2 / 3 := by
    norm_num
  have hpreferred :
      ((2 / 3 : NNReal) : ENNReal) * ((3 / 4 : NNReal) : ENNReal) +
          ((1 / 3 : NNReal) : ENNReal) * ((1 / 2 : NNReal) : ENNReal) =
        ((2 / 3 : NNReal) : ENNReal) := by
    simpa only [ENNReal.coe_add, ENNReal.coe_mul] using
      congrArg (fun q : NNReal ↦ (q : ENNReal)) hpreferredNN
  have hotherNN :
      (2 / 3 : NNReal) * (1 / 4) + (1 / 3) * (1 / 2) = 1 / 3 := by
    norm_num
  have hother :
      ((2 / 3 : NNReal) : ENNReal) * ((1 / 4 : NNReal) : ENNReal) +
          ((1 / 3 : NNReal) : ENNReal) * ((1 / 2 : NNReal) : ENNReal) =
        ((1 / 3 : NNReal) : ENNReal) := by
    simpa only [ENNReal.coe_add, ENNReal.coe_mul] using
      congrArg (fun q : NNReal ↦ (q : ENNReal)) hotherNN
  unfold IsInvariantPMF targetPolicyKernel
  apply PMF.ext
  intro y
  fin_cases i <;> fin_cases y
  · simpa [opeBoolEnvironment, opeBoolTargetPolicy, opeBoolStationary,
      PMF.bind_apply, tsum_fintype, PMF.ofFintype_apply,
      Fintype.sum_bool, add_comm, mul_comm] using hpreferred
  · simpa [opeBoolEnvironment, opeBoolTargetPolicy, opeBoolStationary,
      PMF.bind_apply, tsum_fintype, PMF.ofFintype_apply,
      Fintype.sum_bool, add_comm, mul_comm] using hother
  · simpa [opeBoolEnvironment, opeBoolTargetPolicy, opeBoolStationary,
      PMF.bind_apply, tsum_fintype, PMF.ofFintype_apply,
      Fintype.sum_bool, add_comm, mul_comm] using hother
  · simpa [opeBoolEnvironment, opeBoolTargetPolicy, opeBoolStationary,
      PMF.bind_apply, tsum_fintype, PMF.ofFintype_apply,
      Fintype.sum_bool, add_comm, mul_comm] using hpreferred

/-- Both target policies have stationary loss `1/3`. -/
theorem opeBool_stationaryRisk (i : Bool) :
    stationaryTargetPolicyRisk opeBoolEnvironment (opeBoolTargetPolicy i)
        (opeBoolStationary i) (opeBoolScore i) = 1 / 3 := by
  fin_cases i <;>
    norm_num [stationaryTargetPolicyRisk, targetPolicyRowRisk,
      opeBoolEnvironment, opeBoolTargetPolicy, opeBoolStationary,
      opeBoolScore, PMF.ofFintype_apply, Fintype.sum_bool]

/-- Both nonconstant potentials solve their target-policy Poisson equations. -/
theorem opeBoolPotential_exact (i : Bool) :
    IsExactTargetPolicyPoissonSolution
      opeBoolEnvironment (opeBoolTargetPolicy i) (opeBoolStationary i)
        (opeBoolScore i) (opeBoolPotential i) := by
  intro z
  fin_cases i <;> fin_cases z <;>
    norm_num [IsExactTargetPolicyPoissonSolution,
      targetPolicyRowRisk, targetPolicyPotentialMean,
      stationaryTargetPolicyRisk, opeBoolEnvironment,
      opeBoolTargetPolicy, opeBoolStationary, opeBoolScore,
      opeBoolPotential, PMF.ofFintype_apply, Fintype.sum_bool]

theorem opeUniformBehavior_overlap (i : Bool) :
    ControlledPolicyOverlap opeUniformBehavior
      (markovTargetPolicyAsHistory (opeBoolTargetPolicy i)) := by
  intro n u a hzero
  norm_num [opeUniformBehavior, opeFairBoolPMF,
    PMF.ofFintype_apply] at hzero

/-- The common cap `C=3/2` is sharp for the preferred self-action. -/
theorem opeUniformBehavior_ratioBound (i : Bool) :
    ControlledPolicyRatioBound opeUniformBehavior
      (markovTargetPolicyAsHistory (opeBoolTargetPolicy i)) (3 / 2) := by
  intro n u a
  simp only [markovTargetPolicyAsHistory, opeUniformBehavior,
    opeFairBoolPMF, opeBoolTargetPolicy, PMF.ofFintype_apply]
  split_ifs <;> norm_num

/-- At a preferred current state, the two target-to-behavior ratios are
exactly `3/2` and `1/2`. -/
def opeFalsePrefix (n : ℕ) (_k : Finset.Iic n) :
    ControlledObservation Bool Bool := (false, false)

theorem opeImportanceRatio_witness :
    controlledImportanceRatio opeUniformBehavior
        (markovTargetPolicyAsHistory (opeBoolTargetPolicy false))
        0 (opeFalsePrefix 0) false = 3 / 2 ∧
      controlledImportanceRatio opeUniformBehavior
        (markovTargetPolicyAsHistory (opeBoolTargetPolicy false))
        0 (opeFalsePrefix 0) true = 1 / 2 := by
  constructor <;>
    norm_num [controlledImportanceRatio, opeUniformBehavior,
      opeFairBoolPMF, markovTargetPolicyAsHistory,
      opeBoolTargetPolicy, opeFalsePrefix, PMF.ofFintype_apply]

/-- Concrete path whose first two normalized OPE scores are unequal. -/
def opeVarianceWitnessPath (n : ℕ) : ControlledObservation Bool Bool :=
  if n = 1 then (true, true) else (false, false)

theorem opeVarianceWitness_scores :
    stationaryTargetPolicyObservedScore opeUniformBehavior
        (opeBoolTargetPolicy false) (opeBoolScore false)
        (opeBoolPotential false) (1 / 3) (3 / 2)
        0 opeVarianceWitnessPath = 1 / 3 ∧
      stationaryTargetPolicyObservedScore opeUniformBehavior
        (opeBoolTargetPolicy false) (opeBoolScore false)
        (opeBoolPotential false) (1 / 3) (3 / 2)
        1 opeVarianceWitnessPath = 0 := by
  constructor <;>
    norm_num [stationaryTargetPolicyObservedScore,
      controlledObservedImportanceScore, observedTrajectoryScore,
      controlledNormalizedImportanceScore, controlledImportanceRatio,
      targetPolicyPoissonControlledScore, markovTargetPolicyAsHistory,
      opeUniformBehavior, opeFairBoolPMF, opeBoolTargetPolicy,
      opeBoolScore, opeBoolPotential, opeVarianceWitnessPath,
      Preorder.frestrictLe_apply, PMF.ofFintype_apply]

/-- The displayed behavior path has strictly positive observed Bessel
quadratic variation. -/
theorem opeVarianceWitness_positive :
    0 < forwardBesselQ
      (fun k ↦ stationaryTargetPolicyObservedScore opeUniformBehavior
        (opeBoolTargetPolicy false) (opeBoolScore false)
        (opeBoolPotential false) (1 / 3) (3 / 2)
        k opeVarianceWitnessPath) 2 := by
  rcases opeVarianceWitness_scores with ⟨hzero, hone⟩
  norm_num [forwardBesselQ, forwardPrefixMean, hzero, hone,
    Finset.sum_range_succ]

/-- The behavior-law conditional mean is the constant `4/15` for both target
policies, although the observed importance-weighted scores vary. -/
theorem opeBoolPredictableMean (i : Bool) (n : ℕ)
    (x : ℕ → ControlledObservation Bool Bool) :
    stationaryTargetPolicyPredictableMean
        opeBoolEnvironment (opeBoolTargetPolicy i) (opeBoolScore i)
          (opeBoolPotential i) (1 / 3) (3 / 2) n x = 4 / 15 := by
  rw [stationaryTargetPolicyPredictableMean_eq
    opeBoolEnvironment (opeBoolTargetPolicy i) (opeBoolStationary i)
      (opeBoolScore i) (opeBoolPotential i)
      (by norm_num) (by norm_num) (opeBoolPotential_exact i),
    opeBool_stationaryRisk]
  norm_num

def opeBoolUniformPrior (_i : Bool) : ℝ := 1 / 2

theorem opeBoolUniformPrior_isFullSupportPMF :
    IsFullSupportPMF opeBoolUniformPrior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> norm_num [opeBoolUniformPrior]
  · norm_num [opeBoolUniformPrior, Fintype.sum_bool]
  · intro i
    fin_cases i <;> norm_num [opeBoolUniformPrior]

def opeBoolTiltWeight (_j : Bool) : ℝ := 1 / 2

theorem opeBoolTiltWeight_isFullSupportPMF :
    IsFullSupportPMF opeBoolTiltWeight := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro j
    fin_cases j <;> norm_num [opeBoolTiltWeight]
  · norm_num [opeBoolTiltWeight, Fintype.sum_bool]
  · intro j
    fin_cases j <;> norm_num [opeBoolTiltWeight]

def opeBoolTilts (j : Bool) : ℝ := if j then 1 / 4 else 1 / 5

theorem opeBoolTilts_pos (j : Bool) : 0 < opeBoolTilts j := by
  fin_cases j <;> norm_num [opeBoolTilts]

theorem opeBoolTilts_lt_one (j : Bool) : opeBoolTilts j < 1 := by
  fin_cases j <;> norm_num [opeBoolTilts]

/-- Concrete all-time, all-posterior, all-declared-tilt stationary target
policy OPE certificate under the known behavior propensities. -/
theorem opeBool_stationaryTargetPolicy_certificate :
    ∃ goodEvent : Set (ℕ → ControlledObservation Bool Bool),
      (controlledTrajectoryMeasure opeBoolEnvironment opeUniformBehavior
          (false, false)).real goodEventᶜ ≤ 1 / 20 ∧
        ∀ x ∈ goodEvent, ∀ j : Bool,
          ∀ posterior : Bool → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              stationaryTargetPolicyPosteriorRisk
                  opeBoolEnvironment opeBoolTargetPolicy opeBoolStationary
                    opeBoolScore posterior <
                stationaryTargetPolicyOPEBoundary
                  opeBoolUniformPrior opeBoolTiltWeight opeBoolTilts
                    opeUniformBehavior opeBoolTargetPolicy opeBoolScore
                      opeBoolPotential (1 / 3) (3 / 2)
                        posterior (1 / 20) j n x := by
  exact exists_stationaryTargetPolicyOPE_event
    (ι := Bool) (τ := Bool)
    opeBoolEnvironment opeUniformBehavior (false, false)
    opeBoolTargetPolicy opeBoolStationary opeBoolStationary_invariant
    opeBoolScore opeBoolScore_mem_Icc opeBoolPotential
    (by norm_num) (by norm_num) opeBoolPotential_span
    opeBoolPotential_exact opeUniformBehavior_overlap
    opeUniformBehavior_ratioBound
    opeBoolUniformPrior_isFullSupportPMF
    opeBoolTiltWeight_isFullSupportPMF
    (lam := opeBoolTilts) (delta := (1 / 20 : ℝ))
    (by norm_num) opeBoolTilts_pos opeBoolTilts_lt_one

/-! Public theorem and receipt audit. -/

#check targetPolicyKernel
#check targetPolicyPotentialMean_eq_inducedKernel
#check stationaryTargetPolicyRisk
#check IsExactTargetPolicyPoissonSolution
#check stationaryTargetPolicyObservedScore_condExp
#check posteriorAverage_forwardPrefixMean_stationaryTargetPolicyPredictableMean
#check exists_stationaryTargetPolicyOPE_event
#check stationaryTargetPolicyOPE_selected_of_simultaneous

#print axioms stationaryTargetPolicyObservedScore_condExp
#print axioms targetPolicyPotentialMean_eq_inducedKernel
#print axioms posteriorAverage_forwardPrefixMean_stationaryTargetPolicyPredictableMean
#print axioms exists_stationaryTargetPolicyOPE_event
#print axioms stationaryTargetPolicyOPE_selected_of_simultaneous

#check opeBoolStationary_invariant
#check opeBoolPotential_exact
#check opeImportanceRatio_witness
#check opeVarianceWitness_positive
#check opeBoolPredictableMean
#check opeBool_stationaryTargetPolicy_certificate

#print axioms opeBoolStationary_invariant
#print axioms opeBoolPotential_exact
#print axioms opeVarianceWitness_positive
#print axioms opeBool_stationaryTargetPolicy_certificate

end

end FormalSLT.Examples.CheckStationaryTargetPolicyOPE
