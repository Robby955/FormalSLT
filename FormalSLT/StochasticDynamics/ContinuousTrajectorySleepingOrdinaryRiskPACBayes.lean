/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.ContinuousTrajectorySleepingPredictableTiltPACBayes

/-!
# Ordinary monitored risk from the continuous sleeping trajectory master

This module specializes the countable sleeping predictable-strategy theorem
to constant positive post-wake tilts. For every atom, normalization cancels the
common tilt and yields the ordinary posterior-averaged conditional risk on the
suffix beginning at that atom's wake time.

The target remains a prequential conditional-risk average.  It is not future,
stationary, population, or deployment risk without an additional bridge.
The suffix window restarts the risk average, while each forward predictor may
use the full history before its prediction time. A fixed positive tilt does
not by itself imply a vanishing-width certificate.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.AllocationLogLog
open FormalSLT.PACBayes.ContinuousSleepingPredictableTiltPACBayes
open scoped BigOperators

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Theta Z : Type*} [MeasurableSpace Theta]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- Atom `j` uses the constant tilt `eta j` after it wakes at time `j`.
The catalog is fixed before the trajectory is observed. -/
def countableConstantTrajectoryTiltCatalog (eta : Nat -> Real) :
    Nat -> TrajectoryPredictableTilt Z :=
  fun j _n _u => eta j

/-- Posterior-averaged conditional risk over the suffix `[j,n)` encountered
along one trajectory.  Division is total; theorem endpoints assume `j < n`. -/
def continuousTrajectoryPosteriorAverageConditionalSuffixRisk
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (j n : Nat) (x : Nat -> Z) : Real :=
  ∫ theta,
    (∑ k ∈ Finset.Ico j n,
      conditionalTrajectoryRisk K (score theta) k x) / (n - j : Nat)
    ∂posterior

/-- Posterior-averaged observed score over the suffix `[j,n)`. -/
def continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (j n : Nat) (x : Nat -> Z) : Real :=
  ∫ theta,
    (∑ k ∈ Finset.Ico j n,
      observedTrajectoryScore (score theta) k x) / (n - j : Nat)
    ∂posterior

omit [MeasurableSpace Theta] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
private theorem sum_sleeping_countableConstantTrajectoryTiltCatalog
    (eta : Nat -> Real) (Y : Nat -> Real) {j n : Nat} (hjn : j <= n)
    (x : Nat -> Z) :
    (∑ k ∈ Finset.range n,
      sleepingStrategy
          (observedTrajectoryPredictableStrategyCatalog
            (countableConstantTrajectoryTiltCatalog eta)) j k x * Y k) =
      eta j * ∑ k ∈ Finset.Ico j n, Y k := by
  unfold observedTrajectoryPredictableStrategyCatalog
    observedTrajectoryPredictableTilt
    countableConstantTrajectoryTiltCatalog
    sleepingStrategy
  rw [← Finset.sum_range_add_sum_Ico
    (fun k => (if j <= k then eta j else 0) * Y k) hjn]
  have hbefore :
      (∑ k ∈ Finset.range j,
        (if j <= k then eta j else 0) * Y k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [not_le.mpr (Finset.mem_range.mp hk)]
  rw [hbefore, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [(Finset.mem_Ico.mp hk).1]

omit [MeasurableSpace Theta] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
private theorem sum_psi_sleeping_countableConstantTrajectoryTiltCatalog
    (eta : Nat -> Real) (Y : Nat -> Real) {j n : Nat} (hjn : j <= n)
    (x : Nat -> Z) :
    (∑ k ∈ Finset.range n,
      forwardEmpiricalBernsteinPsi
          (sleepingStrategy
            (observedTrajectoryPredictableStrategyCatalog
              (countableConstantTrajectoryTiltCatalog eta)) j k x) * Y k) =
      ∑ k ∈ Finset.Ico j n,
        forwardEmpiricalBernsteinPsi (eta j) * Y k := by
  unfold observedTrajectoryPredictableStrategyCatalog
    observedTrajectoryPredictableTilt
    countableConstantTrajectoryTiltCatalog
    sleepingStrategy
  rw [← Finset.sum_range_add_sum_Ico
    (fun k => forwardEmpiricalBernsteinPsi
      (if j <= k then eta j else 0) * Y k) hjn]
  have hbefore :
      (∑ k ∈ Finset.range j,
        forwardEmpiricalBernsteinPsi
          (if j <= k then eta j else 0) * Y k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [not_le.mpr (Finset.mem_range.mp hk),
      forwardEmpiricalBernsteinPsi]
  rw [hbefore, zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  simp [(Finset.mem_Ico.mp hk).1]

omit [MeasurableSpace Theta] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
@[simp]
theorem continuousTrajectorySleepingExposure_countableConstant
    (eta : Nat -> Real) {j n : Nat} (hjn : j <= n) (x : Nat -> Z) :
    continuousSleepingPredictableTiltExposure
      (observedTrajectoryPredictableStrategyCatalog
          (countableConstantTrajectoryTiltCatalog eta)) j n x =
      ((n - j : Nat) : Real) * eta j := by
  unfold continuousSleepingPredictableTiltExposure
  calc
    (∑ k ∈ Finset.range n,
        sleepingStrategy
          (observedTrajectoryPredictableStrategyCatalog
            (countableConstantTrajectoryTiltCatalog eta)) j k x) =
        ∑ k ∈ Finset.range n,
          sleepingStrategy
            (observedTrajectoryPredictableStrategyCatalog
              (countableConstantTrajectoryTiltCatalog eta)) j k x * 1 := by
          simp
    _ = eta j * ∑ _k ∈ Finset.Ico j n, (1 : Real) :=
      sum_sleeping_countableConstantTrajectoryTiltCatalog
        eta (fun _ => 1) hjn x
    _ = ((n - j : Nat) : Real) * eta j := by
      simp [Nat.card_Ico, nsmul_eq_mul]
      ring

omit [MeasurableSpace Theta] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
theorem continuousSleepingWeightedConditionalMeanAt_countableConstant
    (mean : Theta -> Nat -> (Nat -> Z) -> Real)
    (eta : Nat -> Real) (theta : Theta) {j n : Nat} (hjn : j <= n)
    (x : Nat -> Z) :
    continuousSleepingWeightedConditionalMeanAt mean
        (observedTrajectoryPredictableStrategyCatalog
          (countableConstantTrajectoryTiltCatalog eta)) theta j n x =
      eta j * ∑ k ∈ Finset.Ico j n, mean theta k x := by
  unfold continuousSleepingWeightedConditionalMeanAt
  exact sum_sleeping_countableConstantTrajectoryTiltCatalog
    eta (fun k => mean theta k x) hjn x

omit [MeasurableSpace Theta] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
theorem continuousSleepingWeightedObservationAt_countableConstant
    (X : Theta -> Nat -> (Nat -> Z) -> Real)
    (eta : Nat -> Real) (theta : Theta) {j n : Nat} (hjn : j <= n)
    (x : Nat -> Z) :
    continuousSleepingWeightedObservationAt X
        (observedTrajectoryPredictableStrategyCatalog
          (countableConstantTrajectoryTiltCatalog eta)) theta j n x =
      eta j * ∑ k ∈ Finset.Ico j n, X theta k x := by
  unfold continuousSleepingWeightedObservationAt
  exact sum_sleeping_countableConstantTrajectoryTiltCatalog
    eta (fun k => X theta k x) hjn x

omit [MeasurableSpace Theta] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
theorem continuousSleepingPredictorQuadraticPenaltyAt_countableConstant
    (X : Theta -> Nat -> (Nat -> Z) -> Real)
    (eta : Nat -> Real) (theta : Theta) {j n : Nat} (hjn : j <= n)
    (x : Nat -> Z) :
    continuousSleepingPredictorQuadraticPenaltyAt X
        (observedTrajectoryPredictableStrategyCatalog
          (countableConstantTrajectoryTiltCatalog eta)) theta j n x =
      ∑ k ∈ Finset.Ico j n,
        forwardEmpiricalBernsteinPsi (eta j) *
          (X theta k x - forwardPredictorProcess (X theta) k x) ^ 2 := by
  unfold continuousSleepingPredictorQuadraticPenaltyAt
  exact sum_psi_sleeping_countableConstantTrajectoryTiltCatalog eta
    (fun k => (X theta k x - forwardPredictorProcess (X theta) k x) ^ 2)
    hjn x

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
theorem continuousSleepingPosteriorWeightedConditionalMean_countableConstant
    (posterior : Measure Theta)
    (mean : Theta -> Nat -> (Nat -> Z) -> Real)
    (eta : Nat -> Real) {j n : Nat} (hjn : j <= n) (x : Nat -> Z) :
    continuousSleepingPosteriorWeightedConditionalMean posterior mean
        (observedTrajectoryPredictableStrategyCatalog
          (countableConstantTrajectoryTiltCatalog eta)) j n x =
      eta j *
        ∫ theta, (∑ k ∈ Finset.Ico j n, mean theta k x) ∂posterior := by
  unfold continuousSleepingPosteriorWeightedConditionalMean
  simp_rw [continuousSleepingWeightedConditionalMeanAt_countableConstant
    mean eta _ hjn x]
  exact integral_const_mul (eta j)
    (fun theta => ∑ k ∈ Finset.Ico j n, mean theta k x)

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
theorem continuousSleepingPosteriorWeightedObservation_countableConstant
    (posterior : Measure Theta)
    (X : Theta -> Nat -> (Nat -> Z) -> Real)
    (eta : Nat -> Real) {j n : Nat} (hjn : j <= n) (x : Nat -> Z) :
    continuousSleepingPosteriorWeightedObservation posterior X
        (observedTrajectoryPredictableStrategyCatalog
          (countableConstantTrajectoryTiltCatalog eta)) j n x =
      eta j *
        ∫ theta, (∑ k ∈ Finset.Ico j n, X theta k x) ∂posterior := by
  unfold continuousSleepingPosteriorWeightedObservation
  simp_rw [continuousSleepingWeightedObservationAt_countableConstant
    X eta _ hjn x]
  exact integral_const_mul (eta j)
    (fun theta => ∑ k ∈ Finset.Ico j n, X theta k x)

/-- Posterior integral of the observable prediction-residual penalty on
`[j,n)`. The predictor at time `k` may use the full history before `k`. -/
def continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (eta : Nat -> Real) (j n : Nat) (x : Nat -> Z) : Real :=
  ∫ theta,
    ∑ k ∈ Finset.Ico j n,
      forwardEmpiricalBernsteinPsi (eta j) *
        (observedTrajectoryScore (score theta) k x -
          forwardPredictorProcess
            (observedTrajectoryScore (score theta)) k x) ^ 2
    ∂posterior

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
theorem continuousSleepingPosteriorPredictorQuadraticPenalty_countableConstant
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (eta : Nat -> Real) {j n : Nat} (hjn : j <= n) (x : Nat -> Z) :
    continuousSleepingPosteriorPredictorQuadraticPenalty posterior
        (fun theta => observedTrajectoryScore (score theta))
        (observedTrajectoryPredictableStrategyCatalog
          (countableConstantTrajectoryTiltCatalog eta)) j n x =
      continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
        score posterior eta j n x := by
  unfold continuousSleepingPosteriorPredictorQuadraticPenalty
    continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
  simp_rw [continuousSleepingPredictorQuadraticPenaltyAt_countableConstant
    (fun theta => observedTrajectoryScore (score theta)) eta _ hjn x]

omit [Fintype Z] [MeasurableSingletonClass Z] in
/-- A positive constant post-wake tilt cancels from the normalized target,
leaving the ordinary posterior-averaged conditional risk on `[j,n)`. -/
theorem
    continuousTrajectorySleepingPosteriorNormalizedConditionalRisk_countableConstant
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (eta : Nat -> Real) {j n : Nat} (hjn : j < n)
    (heta : 0 < eta j) (x : Nat -> Z) :
    continuousTrajectorySleepingPosteriorNormalizedConditionalRisk K score
        (countableConstantTrajectoryTiltCatalog eta) posterior j n x =
      continuousTrajectoryPosteriorAverageConditionalSuffixRisk
        K score posterior j n x := by
  unfold continuousTrajectorySleepingPosteriorNormalizedConditionalRisk
    continuousSleepingPosteriorNormalizedConditionalMean
    continuousTrajectoryPosteriorAverageConditionalSuffixRisk
  rw [continuousSleepingPosteriorWeightedConditionalMean_countableConstant
      posterior (fun theta => conditionalTrajectoryRisk K (score theta))
      eta hjn.le x,
    continuousTrajectorySleepingExposure_countableConstant eta hjn.le x,
    integral_div]
  rw [mul_comm (eta j), mul_div_mul_right _ _ heta.ne']

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The corresponding normalized observation is exactly the ordinary
posterior-averaged empirical score on `[j,n)`. -/
theorem
    continuousTrajectorySleepingPosteriorNormalizedEmpiricalRisk_countableConstant
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (eta : Nat -> Real) {j n : Nat} (hjn : j < n)
    (heta : 0 < eta j) (x : Nat -> Z) :
    continuousTrajectorySleepingPosteriorNormalizedEmpiricalRisk score
        (countableConstantTrajectoryTiltCatalog eta) posterior j n x =
      continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
        score posterior j n x := by
  unfold continuousTrajectorySleepingPosteriorNormalizedEmpiricalRisk
    continuousSleepingPosteriorNormalizedObservation
    continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
  rw [continuousSleepingPosteriorWeightedObservation_countableConstant
      posterior (fun theta => observedTrajectoryScore (score theta))
      eta hjn.le x,
    continuousTrajectorySleepingExposure_countableConstant eta hjn.le x,
    integral_div]
  rw [mul_comm (eta j), mul_div_mul_right _ _ heta.ne']

/-- Observable upper boundary for the ordinary posterior-averaged suffix risk.
The wake time and its associated constant tilt are selected through the same
catalog atom, so the term `-log (polynomialEpochWeight j)` pays for selecting
among the predeclared `(wake time, tilt)` pairs. -/
def continuousTrajectorySleepingConstantTiltSuffixBoundary
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) (eta : Nat -> Real)
    (delta : Real) (j n : Nat) (x : Nat -> Z) : Real :=
  continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
      score posterior j n x +
    ((InformationTheory.klDiv posterior prior).toReal +
        Real.log (1 / delta) - Real.log (polynomialEpochWeight j) +
        continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
          score posterior eta j n x) /
      (((n - j : Nat) : Real) * eta j)

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
theorem continuousTrajectorySleepingPredictableTiltBoundary_countableConstant
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) (eta : Nat -> Real)
    (delta : Real) {j n : Nat} (hjn : j < n)
    (heta : 0 < eta j) (x : Nat -> Z) :
    continuousTrajectorySleepingPredictableTiltBoundary prior posterior score
        (countableConstantTrajectoryTiltCatalog eta) delta j n x =
      continuousTrajectorySleepingConstantTiltSuffixBoundary
        prior posterior score eta delta j n x := by
  unfold continuousTrajectorySleepingPredictableTiltBoundary
    continuousSleepingPredictableTiltBoundary
    continuousTrajectorySleepingConstantTiltSuffixBoundary
  have hemp :=
    continuousTrajectorySleepingPosteriorNormalizedEmpiricalRisk_countableConstant
      score posterior eta hjn heta x
  unfold continuousTrajectorySleepingPosteriorNormalizedEmpiricalRisk at hemp
  rw [hemp,
    continuousSleepingPosteriorPredictorQuadraticPenalty_countableConstant
      score posterior eta hjn.le x,
    continuousTrajectorySleepingExposure_countableConstant eta hjn.le x]

/-- One outer-mass event controls ordinary posterior-averaged conditional risk
on every nonempty suffix `[j,n)`.  The reporting time, suffix start (the
betting wake time), and eligible posterior on the measurable hypothesis space
may all be selected after observing the path.
The fixed catalog couples wake time `j` to its predeclared constant tilt
`eta j`; this is not parameter-free strategy selection.

The target is the conditional risk encountered along the monitored suffix.
It is not future, stationary, population, or deployment risk. -/
theorem
    exists_continuousTrajectorySleepingConstantTiltPACBayes_suffixRisk_event_of_parameterMeasurable
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    (eta : Nat -> Real) {L : Real}
    (heta_pos : forall j, 0 < eta j)
    (heta_upper : forall j, eta j <= L) (hL1 : L < 1)
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {delta : Real} (hdelta : 0 < delta) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta ∧
        forall x, x ∈ goodEvent ->
          forall posterior : Measure Theta,
            IsProbabilityMeasure posterior -> posterior ≪ prior ->
            Integrable (llr posterior prior) posterior ->
            forall j n : Nat, j < n ->
              continuousTrajectoryPosteriorAverageConditionalSuffixRisk
                  K score posterior j n x <
                continuousTrajectorySleepingConstantTiltSuffixBoundary
                  prior posterior score eta delta j n x := by
  rcases
      exists_continuousTrajectorySleepingPredictableTiltPACBayes_normalized_event_of_parameterMeasurable
        K x0 score hscore hscore_parameter
        (countableConstantTrajectoryTiltCatalog eta) hL1
        (fun j _n _u => ⟨(heta_pos j).le, heta_upper j⟩)
        prior hdelta with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx posterior hposterior hposterior_prior hllr j n hjn
  have hexposure : 0 < continuousSleepingPredictableTiltExposure
      (observedTrajectoryPredictableStrategyCatalog
        (countableConstantTrajectoryTiltCatalog eta)) j n x := by
    rw [continuousTrajectorySleepingExposure_countableConstant
      eta hjn.le x]
    exact mul_pos (Nat.cast_pos.mpr (Nat.sub_pos_of_lt hjn)) (heta_pos j)
  have hbound := hgood x hx posterior hposterior hposterior_prior hllr
    j n hjn hexposure
  rw [continuousTrajectorySleepingPosteriorNormalizedConditionalRisk_countableConstant
        K score posterior eta hjn (heta_pos j) x,
      continuousTrajectorySleepingPredictableTiltBoundary_countableConstant
        prior posterior score eta delta hjn (heta_pos j) x] at hbound
  exact hbound

omit [Fintype Z] [MeasurableSingletonClass Z] in
@[simp]
theorem continuousTrajectoryPosteriorAverageConditionalSuffixRisk_zero
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (n : Nat) (x : Nat -> Z) :
    continuousTrajectoryPosteriorAverageConditionalSuffixRisk
        K score posterior 0 n x =
      continuousTrajectoryPosteriorAverageConditionalRisk
        K score posterior n x := by
  unfold continuousTrajectoryPosteriorAverageConditionalSuffixRisk
    continuousTrajectoryPosteriorAverageConditionalRisk
    trajectoryAverageConditionalRisk runningMean runningSum
  rw [Nat.Ico_zero_eq_range]
  simp

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
@[simp]
theorem continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk_zero
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (n : Nat) (x : Nat -> Z) :
    continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
        score posterior 0 n x =
      continuousTrajectoryPosteriorEmpiricalPrequentialRisk
        score posterior n x := by
  unfold continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
    continuousTrajectoryPosteriorEmpiricalPrequentialRisk
    trajectoryEmpiricalPrequentialRisk runningMean runningSum
  rw [Nat.Ico_zero_eq_range]
  simp

/-- The full-prefix boundary is the wake-selected suffix boundary at
`j = 0`. -/
def continuousTrajectorySleepingConstantTiltPrefixBoundary
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) (eta : Nat -> Real)
    (delta : Real) (n : Nat) (x : Nat -> Z) : Real :=
  continuousTrajectorySleepingConstantTiltSuffixBoundary
    prior posterior score eta delta 0 n x

/-- Full-prefix convenience corollary of the wake-selected suffix event. -/
theorem
    exists_continuousTrajectorySleepingConstantTiltPACBayes_prefixRisk_event_of_parameterMeasurable
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    (eta : Nat -> Real) {L : Real}
    (heta_pos : forall j, 0 < eta j)
    (heta_upper : forall j, eta j <= L) (hL1 : L < 1)
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {delta : Real} (hdelta : 0 < delta) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta ∧
        forall x, x ∈ goodEvent ->
          forall posterior : Measure Theta,
            IsProbabilityMeasure posterior -> posterior ≪ prior ->
            Integrable (llr posterior prior) posterior ->
            forall n : Nat, 0 < n ->
              continuousTrajectoryPosteriorAverageConditionalRisk
                  K score posterior n x <
                continuousTrajectorySleepingConstantTiltPrefixBoundary
                  prior posterior score eta delta n x := by
  rcases
      exists_continuousTrajectorySleepingConstantTiltPACBayes_suffixRisk_event_of_parameterMeasurable
        K x0 score hscore hscore_parameter eta heta_pos heta_upper hL1
        prior hdelta with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx posterior hposterior hposterior_prior hllr n hn
  have hbound := hgood x hx posterior hposterior hposterior_prior hllr
    0 n hn
  simpa [continuousTrajectorySleepingConstantTiltPrefixBoundary] using hbound

end

end FormalSLT.StochasticDynamics
