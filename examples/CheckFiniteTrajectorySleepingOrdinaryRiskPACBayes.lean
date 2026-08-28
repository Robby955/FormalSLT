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

/-! ### Nonconstant exact Brier receipt

The earlier all-false witness is intentionally minimal, but its selected loss
is identically zero.  The witness below closes a stronger finite receipt.  A
forecast of `1/4` meets one deterministic positive outcome and then 63
deterministic negative outcomes.  Its Brier losses therefore change from
`9/16` to `1/16`, and its exact monitored conditional risk is the nonzero
value `9/128`.

The probability statement remains the theorem-produced good-event guarantee.
The deterministic arithmetic below does not claim that the named realized
path can itself be proved to belong to that event.
-/

/-- The deterministic outcome at transition `n`: one initial positive outcome,
then negative outcomes. -/
def oneShockOutcome (n : Nat) : Bool :=
  if n = 0 then true else false

/-- Explicit finite transition rows for the one-shock path. -/
def oneShockRows (n : Nat) (_u : (i : Finset.Iic n) -> Bool)
    (y : Bool) : Real :=
  if y = oneShockOutcome n then 1 else 0

theorem oneShockRows_isPMF (n : Nat)
    (u : (i : Finset.Iic n) -> Bool) :
    IsPMF (oneShockRows n u) := by
  constructor
  · intro y
    simp only [oneShockRows]
    split_ifs <;> norm_num
  · rw [Fintype.sum_bool]
    by_cases hn : n = 0 <;>
      simp [oneShockRows, oneShockOutcome, hn]

/-- The named path generated by `oneShockRows`, including its initial state. -/
def oneShockPath (n : Nat) : Bool :=
  if n = 1 then true else false

theorem oneShockPath_succ (k : Nat) :
    oneShockPath (k + 1) = oneShockOutcome k := by
  by_cases hk : k = 0
  · subst k
    norm_num [oneShockPath, oneShockOutcome]
  · simp [oneShockPath, oneShockOutcome, hk]

/-- Two rational forecasts; the selected hypothesis `false` forecasts `1/4`. -/
def quarterForecast (h : Bool) : Real :=
  if h then 3 / 4 else 1 / 4

/-- Brier score for the rational forecast catalog. -/
def quarterBrierScore (h : Bool) : TrajectoryScore Bool :=
  fun _n _u y => (quarterForecast h - boolValue y) ^ 2

theorem quarterBrierScore_mem_Icc :
    forall h n u y,
      quarterBrierScore h n u y ∈ Set.Icc (0 : Real) 1 := by
  intro h n u y
  fin_cases h <;> fin_cases y <;>
    norm_num [quarterBrierScore, quarterForecast, boolValue]

theorem oneShock_observed_selected_loss (k : Nat) :
    observedTrajectoryScore (quarterBrierScore false) k oneShockPath =
      if k = 0 then (9 : Real) / 16 else (1 : Real) / 16 := by
  simp only [observedTrajectoryScore, quarterBrierScore, quarterForecast,
    Bool.false_eq_true, if_false]
  rw [oneShockPath_succ]
  by_cases hk : k = 0 <;>
    simp [oneShockOutcome, hk, boolValue] <;> norm_num

theorem oneShock_first_loss :
    observedTrajectoryScore (quarterBrierScore false) 0 oneShockPath =
      (9 : Real) / 16 := by
  rw [oneShock_observed_selected_loss]
  norm_num

theorem oneShock_second_loss :
    observedTrajectoryScore (quarterBrierScore false) 1 oneShockPath =
      (1 : Real) / 16 := by
  rw [oneShock_observed_selected_loss]
  norm_num

theorem oneShock_losses_vary :
    observedTrajectoryScore (quarterBrierScore false) 0 oneShockPath ≠
      observedTrajectoryScore (quarterBrierScore false) 1 oneShockPath := by
  rw [oneShock_first_loss, oneShock_second_loss]
  norm_num

theorem oneShock_conditional_selected_loss (k : Nat)
    (u : (i : Finset.Iic k) -> Bool) :
    (∑ y,
        oneShockRows k u y * quarterBrierScore false k u y) =
      if k = 0 then (9 : Real) / 16 else (1 : Real) / 16 := by
  rw [Fintype.sum_bool]
  by_cases hk : k = 0 <;>
    simp [oneShockRows, oneShockOutcome, quarterBrierScore,
      quarterForecast, boolValue, hk] <;> norm_num

theorem oneShock_empiricalSuffixRisk_eq :
    finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
        quarterBrierScore selectedPosterior 0 64 oneShockPath =
      (9 : Real) / 128 := by
  unfold finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
    posteriorAverage selectedPosterior
  rw [Fintype.sum_bool]
  simp only [FormalSLT.PACBayes.StabilityBridge.diracPosterior,
    Bool.true_eq_false, if_false, zero_mul, if_true, one_mul, zero_add]
  norm_num [oneShock_observed_selected_loss, Finset.sum_range_succ]

theorem oneShock_conditionalSuffixRisk_eq :
    finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
        oneShockRows quarterBrierScore selectedPosterior
        0 64 oneShockPath = (9 : Real) / 128 := by
  unfold finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
    posteriorAverage selectedPosterior
  rw [Fintype.sum_bool]
  simp only [FormalSLT.PACBayes.StabilityBridge.diracPosterior,
    Bool.true_eq_false, if_false, zero_mul, if_true, one_mul, zero_add]
  simp_rw [oneShock_conditional_selected_loss]
  norm_num [Finset.sum_range_succ]

theorem oneShock_forwardBesselQ_eq :
    forwardBesselQ
        (fun k => observedTrajectoryScore
          (quarterBrierScore false) k oneShockPath) 64 =
      (63 : Real) / 256 := by
  norm_num [forwardBesselQ, forwardPrefixMean,
    oneShock_observed_selected_loss, Finset.sum_range_succ]

theorem oneShock_predictableQuadratic_le_one :
    (∑ k ∈ Finset.Ico 0 64,
        (observedTrajectoryScore (quarterBrierScore false) k oneShockPath -
          forwardPredictorProcess
            (observedTrajectoryScore (quarterBrierScore false))
            k oneShockPath) ^ 2) ≤ (1 : Real) := by
  let loss : Nat → Real := fun k =>
    observedTrajectoryScore (quarterBrierScore false) k oneShockPath
  have hloss : ∀ i < 64, 0 ≤ loss i ∧ loss i ≤ 1 := by
    intro i hi
    rw [show loss i = observedTrajectoryScore
      (quarterBrierScore false) i oneShockPath from rfl,
      oneShock_observed_selected_loss]
    split_ifs <;> norm_num
  have hquadratic :=
    forwardPredictableQuadratic_le_half_add_three_halves_besselQ
      loss (n := 64) (by norm_num) hloss
  have hbessel : forwardBesselQ loss 64 = (63 : Real) / 256 := by
    exact oneShock_forwardBesselQ_eq
  rw [hbessel] at hquadratic
  have hle : forwardPredictableQuadratic loss 64 ≤ (1 : Real) := by
    nlinarith
  simpa [loss, forwardPredictableQuadratic, forwardPredictorProcess] using hle

theorem oneShock_predictorPenalty_le_half :
    finiteTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
        quarterBrierScore selectedPosterior halfTilt
        0 64 oneShockPath ≤ (1 : Real) / 2 := by
  unfold finiteTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
    posteriorAverage selectedPosterior
  rw [Fintype.sum_bool]
  simp only [FormalSLT.PACBayes.StabilityBridge.diracPosterior,
    Bool.true_eq_false, if_false, zero_mul, if_true, one_mul, zero_add]
  rw [← Finset.mul_sum]
  have hpsi0 :
      0 ≤ forwardEmpiricalBernsteinPsi (halfTilt 0) :=
    forwardEmpiricalBernsteinPsi_nonneg (by norm_num [halfTilt])
      (by norm_num [halfTilt])
  have hpsi :
      forwardEmpiricalBernsteinPsi (halfTilt 0) ≤ (1 : Real) / 2 := by
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos
        (show (0 : Real) < 2 by norm_num)
      norm_num at h ⊢
      exact h
    have hlogHalf : Real.log (1 / 2 : Real) = -Real.log 2 := by
      rw [show (1 / 2 : Real) = (2 : Real)⁻¹ by norm_num, Real.log_inv]
    unfold forwardEmpiricalBernsteinPsi
    norm_num [halfTilt]
    rw [hlogHalf]
    linarith
  have hquadratic := oneShock_predictableQuadratic_le_one
  have hquadratic0 :
      0 ≤
        (∑ k ∈ Finset.Ico 0 64,
          (observedTrajectoryScore (quarterBrierScore false) k oneShockPath -
            forwardPredictorProcess
              (observedTrajectoryScore (quarterBrierScore false))
              k oneShockPath) ^ 2) := by
    positivity
  nlinarith

theorem oneShock_logBudget :
    Real.log (1 / ((1 : Real) / 160)) =
      5 * Real.log 2 + Real.log 5 := by
  norm_num
  calc
    Real.log (160 : Real) = Real.log ((2 : Real) ^ 5 * 5) := by norm_num
    _ = Real.log ((2 : Real) ^ 5) + Real.log 5 := by
      rw [Real.log_mul (by positivity) (by norm_num)]
    _ = 5 * Real.log 2 + Real.log 5 := by
      rw [Real.log_pow]
      norm_num

theorem oneShock_wakeCost :
    -Real.log (polynomialEpochWeight 0) = Real.log 2 := by
  rw [polynomialSleepingSelectionCost]
  norm_num

/-- The nonconstant exact receipt has an endpoint below `2/5`. -/
theorem oneShock_boundary_lt_two_fifths :
    finiteTrajectorySleepingConstantTiltSuffixBoundary
        uniformBoolPrior selectedPosterior quarterBrierScore halfTilt
        ((1 : Real) / 160) 0 64 oneShockPath < (2 : Real) / 5 := by
  unfold finiteTrajectorySleepingConstantTiltSuffixBoundary
  rw [oneShock_empiricalSuffixRisk_eq,
    selectedPosterior_kl_eq_log_two, oneShock_logBudget]
  rw [sub_eq_add_neg, oneShock_wakeCost]
  have hpenalty := oneShock_predictorPenalty_le_half
  have hlog2 := Real.log_two_lt_d9
  have hlog5 := Real.log_five_lt_d9
  norm_num [halfTilt] at hpenalty ⊢
  nlinarith

/-- The finite theorem supplies the coverage event for the nonconstant
one-shock Brier process, every finite posterior, and every nonempty suffix. -/
theorem oneShockBrierSuffixCertificate :
    ∃ goodEvent : Set (Nat → Bool),
      (trajectoryMeasure
          (finiteTrajectoryKernel oneShockRows oneShockRows_isPMF) false).real
          goodEventᶜ ≤ (1 : Real) / 160 ∧
        ∀ x, x ∈ goodEvent →
          ∀ posterior : Bool → Real, IsPMF posterior →
            ∀ j n : Nat, j < n →
              finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
                  oneShockRows quarterBrierScore posterior j n x <
                finiteTrajectorySleepingConstantTiltSuffixBoundary
                  uniformBoolPrior posterior quarterBrierScore halfTilt
                  ((1 : Real) / 160) j n x := by
  exact exists_finitePMFTrajectorySleepingConstantTiltPACBayes_suffixRisk_event
    oneShockRows oneShockRows_isPMF false
    quarterBrierScore quarterBrierScore_mem_Icc halfTilt
    halfTilt_pos halfTilt_le (by norm_num)
    uniformBoolPrior_isFullSupportPMF (by norm_num)

/-- Fully discharged coverage theorem linked to a nonconstant, nonzero exact
finite receipt.  Membership of the named path remains an explicit premise of
the final pathwise inequality, while the event's probability guarantee is
proved without such a premise. -/
theorem oneShockBrierFullyDischargedReceipt :
    ∃ goodEvent : Set (Nat → Bool),
      (trajectoryMeasure
          (finiteTrajectoryKernel oneShockRows oneShockRows_isPMF) false).real
          goodEventᶜ ≤ (1 : Real) / 160 ∧
        (∀ x, x ∈ goodEvent →
          ∀ posterior : Bool → Real, IsPMF posterior →
            ∀ j n : Nat, j < n →
              finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
                  oneShockRows quarterBrierScore posterior j n x <
                finiteTrajectorySleepingConstantTiltSuffixBoundary
                  uniformBoolPrior posterior quarterBrierScore halfTilt
                  ((1 : Real) / 160) j n x) ∧
        observedTrajectoryScore (quarterBrierScore false) 0 oneShockPath =
          (9 : Real) / 16 ∧
        observedTrajectoryScore (quarterBrierScore false) 1 oneShockPath =
          (1 : Real) / 16 ∧
        observedTrajectoryScore (quarterBrierScore false) 0 oneShockPath ≠
          observedTrajectoryScore (quarterBrierScore false) 1 oneShockPath ∧
        finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
            oneShockRows quarterBrierScore selectedPosterior
            0 64 oneShockPath = (9 : Real) / 128 ∧
        finiteTrajectorySleepingConstantTiltSuffixBoundary
            uniformBoolPrior selectedPosterior quarterBrierScore halfTilt
            ((1 : Real) / 160) 0 64 oneShockPath < (2 : Real) / 5 ∧
        (oneShockPath ∈ goodEvent →
          finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
              oneShockRows quarterBrierScore selectedPosterior
              0 64 oneShockPath <
            finiteTrajectorySleepingConstantTiltSuffixBoundary
              uniformBoolPrior selectedPosterior quarterBrierScore halfTilt
              ((1 : Real) / 160) 0 64 oneShockPath) := by
  rcases oneShockBrierSuffixCertificate with ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, hgood, oneShock_first_loss,
    oneShock_second_loss, oneShock_losses_vary,
    oneShock_conditionalSuffixRisk_eq, oneShock_boundary_lt_two_fifths, ?_⟩
  intro hpath
  exact hgood oneShockPath hpath selectedPosterior selectedPosterior_isPMF
    0 64 (by norm_num)

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
#check oneShockBrierFullyDischargedReceipt

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
#print axioms oneShockBrierFullyDischargedReceipt

end

end FormalSLT.Examples.CheckFiniteTrajectorySleepingOrdinaryRiskPACBayes
