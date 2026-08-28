import FormalSLT.PACBayes.StabilityBridge
import FormalSLT.StochasticDynamics.FiniteTrajectorySleepingOrdinaryRiskPACBayes
import Mathlib.Tactic

/-!
# Finite wake-selected trajectory certificate checks

The Boolean witness below is deliberately small enough to replay exactly.  It
uses an explicit finite transition table, deterministic-probability forecasts,
squared (Brier) loss, a nonzero wake time, and a point posterior against a
uniform full-support prior.  Its boundary is strictly below the trivial loss
ceiling `1`.

This is an arithmetic proof-of-life for the finite certificate API, not a
scientific benchmark.  The public theorem itself permits arbitrary bounded
scores and prefix-dependent finite transition rows.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.AllocationLogLog
open FormalSLT.PACBayesKL

namespace FormalSLT.Examples.CheckFiniteTrajectorySleepingOrdinaryRiskPACBayes

open FormalSLT.StochasticDynamics

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Real encoding of a Boolean outcome. -/
def boolValue : Bool -> Real
  | false => 0
  | true => 1

/-- Squared probabilistic loss for the two deterministic Boolean forecasts. -/
def boolBrierScore (forecast : Bool) : TrajectoryScore Bool :=
  fun _n _u y => (boolValue forecast - boolValue y) ^ 2

theorem boolBrierScore_mem_Icc :
    forall forecast n u y,
      boolBrierScore forecast n u y ∈ Set.Icc (0 : Real) 1 := by
  intro forecast n u y
  fin_cases forecast <;> fin_cases y <;>
    norm_num [boolBrierScore, boolValue]

/-- Every transition is deterministically `false`, expressed as an explicit
real-valued finite PMF row. -/
def deterministicFalseRows (_n : Nat) (_u : (i : Finset.Iic _n) -> Bool)
    (y : Bool) : Real :=
  if y = false then 1 else 0

theorem deterministicFalseRows_isPMF (n : Nat)
    (u : (i : Finset.Iic n) -> Bool) :
    IsPMF (deterministicFalseRows n u) := by
  constructor
  · intro y
    fin_cases y <;> norm_num [deterministicFalseRows]
  · rw [Fintype.sum_bool]
    norm_num [deterministicFalseRows]

def allFalsePath (_n : Nat) : Bool := false

def uniformBoolPrior (_forecast : Bool) : Real := 1 / 2

theorem uniformBoolPrior_isFullSupportPMF :
    IsFullSupportPMF uniformBoolPrior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro forecast
    norm_num [uniformBoolPrior]
  · rw [Fintype.sum_bool]
    norm_num [uniformBoolPrior]
  · intro forecast
    norm_num [uniformBoolPrior]

def selectedPosterior : Bool -> Real :=
  FormalSLT.PACBayes.StabilityBridge.diracPosterior false

theorem selectedPosterior_isPMF : IsPMF selectedPosterior := by
  exact FormalSLT.PACBayes.StabilityBridge.diracPosterior_isPMF false

def halfTilt (_j : Nat) : Real := 1 / 2

theorem halfTilt_pos (j : Nat) : 0 < halfTilt j := by
  norm_num [halfTilt]

theorem halfTilt_le (j : Nat) : halfTilt j <= (1 / 2 : Real) := by
  norm_num [halfTilt]

theorem observed_selectedBrier_zero (k : Nat) :
    observedTrajectoryScore (boolBrierScore false) k allFalsePath = 0 := by
  norm_num [observedTrajectoryScore, boolBrierScore, boolValue, allFalsePath]

theorem selectedBrier_forwardPredictor_zero {k : Nat} (hk : 0 < k) :
    forwardPredictorProcess
        (observedTrajectoryScore (boolBrierScore false)) k allFalsePath = 0 := by
  simp [forwardPredictorProcess, forwardPredictor, hk.ne', forwardPrefixMean,
    observed_selectedBrier_zero]

theorem selectedPosterior_kl_eq_log_two :
    klDiv selectedPosterior uniformBoolPrior = Real.log 2 := by
  rw [show selectedPosterior =
      FormalSLT.PACBayes.StabilityBridge.diracPosterior false from rfl]
  rw [FormalSLT.PACBayes.StabilityBridge.diracPosterior_klDiv_eq_neg_log_prior
    uniformBoolPrior false (by norm_num [uniformBoolPrior])]
  rw [show uniformBoolPrior false = (1 : Real) / 2 by
    norm_num [uniformBoolPrior]]
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
  ring

theorem selected_empiricalSuffixRisk_eq_zero :
    finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
        boolBrierScore selectedPosterior 1 50 allFalsePath = 0 := by
  unfold finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
    posteriorAverage selectedPosterior
  rw [Fintype.sum_bool]
  simp [FormalSLT.PACBayes.StabilityBridge.diracPosterior,
    observed_selectedBrier_zero]

theorem selected_predictorPenalty_eq_zero :
    finiteTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
        boolBrierScore selectedPosterior halfTilt 1 50 allFalsePath = 0 := by
  unfold finiteTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
    posteriorAverage selectedPosterior
  rw [Fintype.sum_bool]
  simp only [FormalSLT.PACBayes.StabilityBridge.diracPosterior,
    Bool.true_eq_false, if_false, zero_mul, if_true, one_mul, zero_add]
  apply Finset.sum_eq_zero
  intro k hk
  have hkpos : 0 < k := (Finset.mem_Ico.mp hk).1
  rw [observed_selectedBrier_zero,
    selectedBrier_forwardPredictor_zero hkpos]
  ring

theorem selected_conditionalSuffixRisk_eq_zero :
    finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
        deterministicFalseRows boolBrierScore selectedPosterior
        1 50 allFalsePath = 0 := by
  unfold finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
    posteriorAverage selectedPosterior
  rw [Fintype.sum_bool]
  simp [FormalSLT.PACBayes.StabilityBridge.diracPosterior,
    deterministicFalseRows, boolBrierScore, boolValue]

theorem selected_logBudget_eq_log_twenty :
    Real.log (1 / ((1 : Real) / 20)) = Real.log 20 := by
  norm_num

theorem selected_wakeCost_eq_log_six :
    -Real.log (polynomialEpochWeight 1) = Real.log 6 := by
  rw [polynomialSleepingSelectionCost]
  norm_num
  rw [← Real.log_mul (by norm_num : (2 : Real) ≠ 0)
    (by norm_num : (3 : Real) ≠ 0)]
  norm_num

/-- Exact formula for the concrete deterministic boundary witness. -/
theorem selectedBrierBoundary_eq :
    finiteTrajectorySleepingConstantTiltSuffixBoundary
        uniformBoolPrior selectedPosterior boolBrierScore halfTilt
        ((1 : Real) / 20) 1 50 allFalsePath =
      2 * Real.log 240 / 49 := by
  unfold finiteTrajectorySleepingConstantTiltSuffixBoundary
  rw [selected_empiricalSuffixRisk_eq_zero,
    selectedPosterior_kl_eq_log_two,
    selected_logBudget_eq_log_twenty,
    selected_predictorPenalty_eq_zero]
  rw [sub_eq_add_neg, selected_wakeCost_eq_log_six]
  have hlogs :
      Real.log (2 : Real) + Real.log 20 + Real.log 6 = Real.log 240 := by
    rw [← Real.log_mul (by norm_num : (2 : Real) ≠ 0)
      (by norm_num : (20 : Real) ≠ 0)]
    norm_num
    rw [← Real.log_mul (by norm_num : (40 : Real) ≠ 0)
      (by norm_num : (6 : Real) ≠ 0)]
    norm_num
  norm_num [halfTilt]
  rw [← hlogs]
  ring

/-- The deterministic boundary witness is nonvacuous: its endpoint is below
the trivial Brier-loss ceiling. -/
theorem selectedBrierBoundary_lt_one :
    finiteTrajectorySleepingConstantTiltSuffixBoundary
        uniformBoolPrior selectedPosterior boolBrierScore halfTilt
        ((1 : Real) / 20) 1 50 allFalsePath < 1 := by
  rw [selectedBrierBoundary_eq]
  have hfactor :
      Real.log (240 : Real) =
        4 * Real.log 2 + Real.log 3 + Real.log 5 := by
    calc
      Real.log (240 : Real) =
          Real.log (((2 : Real) ^ 4 * 3) * 5) := by norm_num
      _ = Real.log ((2 : Real) ^ 4 * 3) + Real.log 5 := by
        rw [Real.log_mul (by positivity) (by norm_num)]
      _ = (Real.log ((2 : Real) ^ 4) + Real.log 3) +
          Real.log 5 := by
        rw [Real.log_mul (by positivity) (by norm_num)]
      _ = 4 * Real.log 2 + Real.log 3 + Real.log 5 := by
        rw [Real.log_pow]
        ring
  have hlog : Real.log (240 : Real) < 6 := by
    rw [hfactor]
    nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
      Real.log_five_lt_d9]
  linarith

/-- The explicitly summed target is strictly below its explicitly evaluated
boundary.  This deterministic statement does not assert membership in the
statistical theorem's good event. -/
theorem selectedBrierTarget_lt_boundary :
    finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
        deterministicFalseRows boolBrierScore selectedPosterior
        1 50 allFalsePath <
      finiteTrajectorySleepingConstantTiltSuffixBoundary
        uniformBoolPrior selectedPosterior boolBrierScore halfTilt
        ((1 : Real) / 20) 1 50 allFalsePath := by
  rw [selected_conditionalSuffixRisk_eq_zero, selectedBrierBoundary_eq]
  have hlog : 0 < Real.log (240 : Real) := Real.log_pos (by norm_num)
  positivity

/-- Deterministic nonvacuity witness: the explicitly summed conditional Brier
target is below a finite endpoint that is itself strictly below one. -/
theorem selectedBrierNonvacuousReceipt :
    finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
        deterministicFalseRows boolBrierScore selectedPosterior
        1 50 allFalsePath = 0 ∧
      finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
          deterministicFalseRows boolBrierScore selectedPosterior
          1 50 allFalsePath <
        finiteTrajectorySleepingConstantTiltSuffixBoundary
          uniformBoolPrior selectedPosterior boolBrierScore halfTilt
          ((1 : Real) / 20) 1 50 allFalsePath ∧
      finiteTrajectorySleepingConstantTiltSuffixBoundary
          uniformBoolPrior selectedPosterior boolBrierScore halfTilt
          ((1 : Real) / 20) 1 50 allFalsePath =
        2 * Real.log 240 / 49 ∧
      finiteTrajectorySleepingConstantTiltSuffixBoundary
          uniformBoolPrior selectedPosterior boolBrierScore halfTilt
          ((1 : Real) / 20) 1 50 allFalsePath < 1 :=
  ⟨selected_conditionalSuffixRisk_eq_zero,
    selectedBrierTarget_lt_boundary, selectedBrierBoundary_eq,
    selectedBrierBoundary_lt_one⟩

/-- The finite theorem applies directly to the explicit Boolean transition
table, all finite posteriors, every reporting time, and every nonempty suffix. -/
theorem finiteBoolBrierSuffixCertificate :
    ∃ goodEvent : Set (Nat -> Bool),
      (trajectoryMeasure
          (finiteTrajectoryKernel deterministicFalseRows
            deterministicFalseRows_isPMF) false).real goodEventᶜ <=
          (1 : Real) / 20 ∧
        forall x, x ∈ goodEvent ->
          forall posterior : Bool -> Real, IsPMF posterior ->
            forall j n : Nat, j < n ->
              finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
                  deterministicFalseRows boolBrierScore posterior j n x <
                finiteTrajectorySleepingConstantTiltSuffixBoundary
                  uniformBoolPrior posterior boolBrierScore halfTilt
                  ((1 : Real) / 20) j n x := by
  exact exists_finitePMFTrajectorySleepingConstantTiltPACBayes_suffixRisk_event
    deterministicFalseRows deterministicFalseRows_isPMF false
    boolBrierScore boolBrierScore_mem_Icc halfTilt
    halfTilt_pos halfTilt_le (by norm_num)
    uniformBoolPrior_isFullSupportPMF (by norm_num)

#check finiteTrajectoryKernel
#check conditionalTrajectoryRisk_finiteTrajectoryKernel_eq_sum
#check finiteTrajectoryPosteriorAverageConditionalSuffixRisk
#check finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
#check finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
#check finiteTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
#check finiteTrajectorySleepingConstantTiltSuffixBoundary
#check exists_finiteTrajectorySleepingConstantTiltPACBayes_suffixRisk_event
#check exists_finitePMFTrajectorySleepingConstantTiltPACBayes_suffixRisk_event
#check selectedBrierNonvacuousReceipt
#check selectedBrierTarget_lt_boundary
#check selectedBrierBoundary_lt_one
#check finiteBoolBrierSuffixCertificate

#print axioms conditionalTrajectoryRisk_finiteTrajectoryKernel_eq_sum
#print axioms finiteTrajectoryPosteriorAverageConditionalSuffixRisk_finiteTrajectoryKernel
#print axioms continuousTrajectorySleepingConstantTiltSuffixBoundary_toPMF
#print axioms exists_finiteTrajectorySleepingConstantTiltPACBayes_suffixRisk_event
#print axioms exists_finitePMFTrajectorySleepingConstantTiltPACBayes_suffixRisk_event
#print axioms selectedBrierBoundary_eq
#print axioms selectedBrierBoundary_lt_one
#print axioms selectedBrierNonvacuousReceipt
#print axioms selectedBrierTarget_lt_boundary
#print axioms finiteBoolBrierSuffixCertificate

end

end FormalSLT.Examples.CheckFiniteTrajectorySleepingOrdinaryRiskPACBayes
