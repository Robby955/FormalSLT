/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.ContinuousTrajectorySleepingOrdinaryRiskPACBayes

/-!
# Ordinary suffix risk for time-varying predictable tilts

The sleeping predictable-tilt theorem controls a normalized, tilt-weighted
conditional-risk average. This module compares that target with the ordinary
uniform average on the same suffix. The comparison cost is the total variation
distance between the uniform suffix weights and the realized normalized tilt
weights.

For losses in `[0,1]`, the conditional-risk and empirical-risk comparisons each
cost at most this discrepancy. Consequently, the existing weighted PAC-Bayes
certificate implies an ordinary encountered suffix-risk certificate with an
explicit `2 * discrepancy` surcharge. Constant positive post-wake tilts have
zero discrepancy and recover the exact constant-tilt specialization.

The strategy catalog is still fixed before observing the trajectory, and each
strategy remains predictable. The target is encountered conditional risk on
the monitored suffix, not future, stationary, population, or deployment risk.
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

/-! ## A reusable finite total-variation comparison -/

/-- Half the finite `L1` distance between a uniform distribution on `s` and
weights `weight / exposure`. The definition is total; comparison theorems
assume that `s` is nonempty and that `exposure` is the sum of the weights. -/
def finiteUniformNormalizedWeightDiscrepancy {Alpha : Type*}
    (s : Finset Alpha) (weight : Alpha -> Real) (exposure : Real) : Real :=
  (1 / 2 : Real) *
    ∑ i ∈ s, |((s.card : Real)⁻¹) - weight i / exposure|

omit [MeasurableSpace Theta] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
/-- A `[0,1]`-valued function changes by at most half the `L1` distance
between two finite unit-mass weight vectors. Nonnegativity of the vectors is
not needed for this deterministic inequality. -/
theorem abs_weightedSum_sub_weightedSum_le_half_l1
    {Alpha : Type*} (s : Finset Alpha)
    (p q value : Alpha -> Real)
    (hp : (∑ i ∈ s, p i) = 1)
    (hq : (∑ i ∈ s, q i) = 1)
    (hvalue : forall i, i ∈ s -> value i ∈ Set.Icc (0 : Real) 1) :
    |(∑ i ∈ s, p i * value i) -
        ∑ i ∈ s, q i * value i| <=
      (1 / 2 : Real) * ∑ i ∈ s, |p i - q i| := by
  have hmass : (∑ i ∈ s, (p i - q i)) = 0 := by
    rw [Finset.sum_sub_distrib, hp, hq]
    norm_num
  have hdiff :
      (∑ i ∈ s, p i * value i) -
          ∑ i ∈ s, q i * value i =
        ∑ i ∈ s, (p i - q i) * value i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hcenter :
      (∑ i ∈ s, (p i - q i) * value i) =
        ∑ i ∈ s, (p i - q i) * (value i - (1 / 2 : Real)) := by
    calc
      (∑ i ∈ s, (p i - q i) * value i) =
          ∑ i ∈ s,
            ((p i - q i) * (value i - (1 / 2 : Real)) +
              (1 / 2 : Real) * (p i - q i)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = (∑ i ∈ s,
              (p i - q i) * (value i - (1 / 2 : Real))) +
            (1 / 2 : Real) * ∑ i ∈ s, (p i - q i) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ i ∈ s,
          (p i - q i) * (value i - (1 / 2 : Real)) := by
        rw [hmass]
        ring
  rw [hdiff, hcenter]
  calc
    |∑ i ∈ s, (p i - q i) * (value i - (1 / 2 : Real))| <=
        ∑ i ∈ s, |(p i - q i) * (value i - (1 / 2 : Real))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ i ∈ s, (1 / 2 : Real) * |p i - q i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      have habs : |value i - (1 / 2 : Real)| <= (1 / 2 : Real) := by
        rw [abs_le]
        constructor <;> linarith [(hvalue i hi).1, (hvalue i hi).2]
      calc
        |p i - q i| * |value i - (1 / 2 : Real)| <=
            |p i - q i| * (1 / 2 : Real) :=
          mul_le_mul_of_nonneg_left habs (abs_nonneg _)
        _ = (1 / 2 : Real) * |p i - q i| := by ring
    _ = (1 / 2 : Real) * ∑ i ∈ s, |p i - q i| := by
      rw [Finset.mul_sum]

omit [MeasurableSpace Theta] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
/-- A normalized weighted average of `[0,1]` values differs from their
uniform average by at most `finiteUniformNormalizedWeightDiscrepancy`. -/
theorem abs_uniformAverage_sub_normalizedWeightedAverage_le_discrepancy
    {Alpha : Type*} (s : Finset Alpha) (hs : s.Nonempty)
    (weight value : Alpha -> Real) {exposure : Real}
    (hexposure : exposure ≠ 0)
    (hsum : (∑ i ∈ s, weight i) = exposure)
    (hvalue : forall i, i ∈ s -> value i ∈ Set.Icc (0 : Real) 1) :
    |(∑ i ∈ s, value i) / (s.card : Real) -
        (∑ i ∈ s, weight i * value i) / exposure| <=
      finiteUniformNormalizedWeightDiscrepancy s weight exposure := by
  let p : Alpha -> Real := fun _ => ((s.card : Real)⁻¹)
  let q : Alpha -> Real := fun i => weight i / exposure
  have hcard : (s.card : Real) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hs)
  have hp : (∑ i ∈ s, p i) = 1 := by
    simp only [p]
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcard
  have hq : (∑ i ∈ s, q i) = 1 := by
    simp only [q]
    rw [← Finset.sum_div, hsum, div_self hexposure]
  have htv := abs_weightedSum_sub_weightedSum_le_half_l1
    s p q value hp hq hvalue
  have huniform :
      (∑ i ∈ s, p i * value i) =
        (∑ i ∈ s, value i) / (s.card : Real) := by
    simp only [p]
    rw [← Finset.mul_sum]
    simp only [div_eq_mul_inv]
    ring
  have hweighted :
      (∑ i ∈ s, q i * value i) =
        (∑ i ∈ s, weight i * value i) / exposure := by
    simp only [q]
    calc
      (∑ i ∈ s, (weight i / exposure) * value i) =
          ∑ i ∈ s, (weight i * value i) / exposure := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = (∑ i ∈ s, weight i * value i) / exposure := by
        rw [Finset.sum_div]
  rw [huniform, hweighted] at htv
  simpa only [finiteUniformNormalizedWeightDiscrepancy, p, q] using htv

/-! ## Suffix weights and discrepancy -/

/-- Realized total-variation discrepancy between uniform weights on `[j,n)`
and the normalized weights of sleeping atom `j`. -/
def continuousTrajectorySleepingPredictableTiltUniformDiscrepancy
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (j n : Nat) (x : Nat -> Z) : Real :=
  finiteUniformNormalizedWeightDiscrepancy (Finset.Ico j n)
    (fun k => observedTrajectoryPredictableTilt (strategy j) k x)
    (continuousSleepingPredictableTiltExposure
      (observedTrajectoryPredictableStrategyCatalog strategy) j n x)

omit [MeasurableSpace Theta] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
private theorem sum_sleepingStrategy_eq_sum_Ico
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (Y : Nat -> Real) {j n : Nat} (hjn : j <= n) (x : Nat -> Z) :
    (∑ k ∈ Finset.range n,
      sleepingStrategy
          (observedTrajectoryPredictableStrategyCatalog strategy) j k x *
        Y k) =
      ∑ k ∈ Finset.Ico j n,
        observedTrajectoryPredictableTilt (strategy j) k x * Y k := by
  rw [← Finset.sum_range_add_sum_Ico
    (fun k => sleepingStrategy
      (observedTrajectoryPredictableStrategyCatalog strategy) j k x * Y k)
    hjn]
  have hbefore :
      (∑ k ∈ Finset.range j,
        sleepingStrategy
            (observedTrajectoryPredictableStrategyCatalog strategy) j k x *
          Y k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [sleepingStrategy, not_le.mpr (Finset.mem_range.mp hk)]
  rw [hbefore, zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  simp [sleepingStrategy, (Finset.mem_Ico.mp hk).1,
    observedTrajectoryPredictableStrategyCatalog]

omit [MeasurableSpace Theta] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
theorem continuousTrajectorySleepingPredictableTiltExposure_eq_sum_Ico
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    {j n : Nat} (hjn : j <= n) (x : Nat -> Z) :
    continuousSleepingPredictableTiltExposure
        (observedTrajectoryPredictableStrategyCatalog strategy) j n x =
      ∑ k ∈ Finset.Ico j n,
        observedTrajectoryPredictableTilt (strategy j) k x := by
  unfold continuousSleepingPredictableTiltExposure
  calc
    (∑ k ∈ Finset.range n,
        sleepingStrategy
          (observedTrajectoryPredictableStrategyCatalog strategy) j k x) =
        ∑ k ∈ Finset.range n,
          sleepingStrategy
              (observedTrajectoryPredictableStrategyCatalog strategy) j k x *
            1 := by simp
    _ = ∑ k ∈ Finset.Ico j n,
          observedTrajectoryPredictableTilt (strategy j) k x * 1 :=
      sum_sleepingStrategy_eq_sum_Ico strategy (fun _ => 1) hjn x
    _ = ∑ k ∈ Finset.Ico j n,
          observedTrajectoryPredictableTilt (strategy j) k x := by simp

omit [MeasurableSpace Theta] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
private theorem
    continuousSleepingWeightedConditionalMeanAt_eq_sum_Ico
    (mean : Theta -> Nat -> (Nat -> Z) -> Real)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (theta : Theta) {j n : Nat} (hjn : j <= n) (x : Nat -> Z) :
    continuousSleepingWeightedConditionalMeanAt mean
        (observedTrajectoryPredictableStrategyCatalog strategy)
        theta j n x =
      ∑ k ∈ Finset.Ico j n,
        observedTrajectoryPredictableTilt (strategy j) k x * mean theta k x := by
  unfold continuousSleepingWeightedConditionalMeanAt
  exact sum_sleepingStrategy_eq_sum_Ico strategy
    (fun k => mean theta k x) hjn x

omit [MeasurableSpace Theta] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
private theorem continuousSleepingWeightedObservationAt_eq_sum_Ico
    (X : Theta -> Nat -> (Nat -> Z) -> Real)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (theta : Theta) {j n : Nat} (hjn : j <= n) (x : Nat -> Z) :
    continuousSleepingWeightedObservationAt X
        (observedTrajectoryPredictableStrategyCatalog strategy)
        theta j n x =
      ∑ k ∈ Finset.Ico j n,
        observedTrajectoryPredictableTilt (strategy j) k x * X theta k x := by
  unfold continuousSleepingWeightedObservationAt
  exact sum_sleepingStrategy_eq_sum_Ico strategy
    (fun k => X theta k x) hjn x

omit [MeasurableSpace Theta] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
/-- Pointwise conditional-risk comparison between the ordinary suffix average
and the normalized time-varying predictable-tilt average. -/
theorem
    abs_trajectoryConditionalSuffixAverage_sub_sleepingNormalizedConditionalMeanAt_le
    (mean : Theta -> Nat -> (Nat -> Z) -> Real)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (theta : Theta) {j n : Nat} (hjn : j < n) (x : Nat -> Z)
    (hexposure : 0 < continuousSleepingPredictableTiltExposure
      (observedTrajectoryPredictableStrategyCatalog strategy) j n x)
    (hmean : forall k, k ∈ Finset.Ico j n ->
      mean theta k x ∈ Set.Icc (0 : Real) 1) :
    |(∑ k ∈ Finset.Ico j n, mean theta k x) / (n - j : Nat) -
        continuousSleepingWeightedConditionalMeanAt mean
            (observedTrajectoryPredictableStrategyCatalog strategy)
            theta j n x /
          continuousSleepingPredictableTiltExposure
            (observedTrajectoryPredictableStrategyCatalog strategy) j n x| <=
      continuousTrajectorySleepingPredictableTiltUniformDiscrepancy
        strategy j n x := by
  rw [continuousSleepingWeightedConditionalMeanAt_eq_sum_Ico
    mean strategy theta hjn.le x]
  have hs : (Finset.Ico j n).Nonempty := by
    exact ⟨j, Finset.mem_Ico.mpr ⟨le_rfl, hjn⟩⟩
  have hsum := continuousTrajectorySleepingPredictableTiltExposure_eq_sum_Ico
    strategy hjn.le x
  simpa [continuousTrajectorySleepingPredictableTiltUniformDiscrepancy,
    Nat.card_Ico] using
      (abs_uniformAverage_sub_normalizedWeightedAverage_le_discrepancy
        (Finset.Ico j n) hs
        (fun k => observedTrajectoryPredictableTilt (strategy j) k x)
        (fun k => mean theta k x) hexposure.ne' hsum.symm hmean)

omit [MeasurableSpace Theta] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
/-- Pointwise empirical-risk comparison for the same realized predictable
weights. -/
theorem
    abs_trajectoryEmpiricalSuffixAverage_sub_sleepingNormalizedObservationAt_le
    (X : Theta -> Nat -> (Nat -> Z) -> Real)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (theta : Theta) {j n : Nat} (hjn : j < n) (x : Nat -> Z)
    (hexposure : 0 < continuousSleepingPredictableTiltExposure
      (observedTrajectoryPredictableStrategyCatalog strategy) j n x)
    (hX : forall k, k ∈ Finset.Ico j n ->
      X theta k x ∈ Set.Icc (0 : Real) 1) :
    |(∑ k ∈ Finset.Ico j n, X theta k x) / (n - j : Nat) -
        continuousSleepingWeightedObservationAt X
            (observedTrajectoryPredictableStrategyCatalog strategy)
            theta j n x /
          continuousSleepingPredictableTiltExposure
            (observedTrajectoryPredictableStrategyCatalog strategy) j n x| <=
      continuousTrajectorySleepingPredictableTiltUniformDiscrepancy
        strategy j n x := by
  rw [continuousSleepingWeightedObservationAt_eq_sum_Ico
    X strategy theta hjn.le x]
  have hs : (Finset.Ico j n).Nonempty := by
    exact ⟨j, Finset.mem_Ico.mpr ⟨le_rfl, hjn⟩⟩
  have hsum := continuousTrajectorySleepingPredictableTiltExposure_eq_sum_Ico
    strategy hjn.le x
  simpa [continuousTrajectorySleepingPredictableTiltUniformDiscrepancy,
    Nat.card_Ico] using
      (abs_uniformAverage_sub_normalizedWeightedAverage_le_discrepancy
        (Finset.Ico j n) hs
        (fun k => observedTrajectoryPredictableTilt (strategy j) k x)
        (fun k => X theta k x) hexposure.ne' hsum.symm hX)

/-! ## Posterior deviations and the PAC-Bayes bridge -/

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
private theorem abs_integral_sub_integral_le_of_abs_sub_le_const
    (posterior : Measure Theta) [IsProbabilityMeasure posterior]
    (f g : Theta -> Real) {D : Real}
    (hf : Integrable f posterior) (hg : Integrable g posterior)
    (hpoint : forall theta, |f theta - g theta| <= D) :
    |(∫ theta, f theta ∂posterior) - ∫ theta, g theta ∂posterior| <= D := by
  have hpoint_norm : forall theta, ‖f theta - g theta‖ <= D := by
    intro theta
    simpa only [Real.norm_eq_abs] using hpoint theta
  rw [← integral_sub hf hg, ← Real.norm_eq_abs]
  calc
    ‖∫ theta, f theta - g theta ∂posterior‖ <=
        ∫ theta, ‖f theta - g theta‖ ∂posterior :=
      by
        simpa using
          (norm_integral_le_integral_norm (μ := posterior)
            (fun theta => f theta - g theta))
    _ <= ∫ _theta, D ∂posterior := by
      exact integral_mono (hf.sub hg).norm (integrable_const D) hpoint_norm
    _ = D := by simp

omit [Fintype Z] [MeasurableSingletonClass Z] in
/-- Posterior-level conditional-risk deviation. The explicit integrability
premises make this lemma reusable independently of the trajectory master. -/
theorem
    abs_continuousTrajectoryPosteriorAverageConditionalSuffixRisk_sub_normalized_le
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    [IsProbabilityMeasure posterior]
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    {j n : Nat} (hjn : j < n) (x : Nat -> Z)
    (hexposure : 0 < continuousSleepingPredictableTiltExposure
      (observedTrajectoryPredictableStrategyCatalog strategy) j n x)
    (hscore : forall theta k,
      conditionalTrajectoryRisk K (score theta) k x ∈ Set.Icc (0 : Real) 1)
    (hordinary : Integrable (fun theta =>
      (∑ k ∈ Finset.Ico j n,
        conditionalTrajectoryRisk K (score theta) k x) / (n - j : Nat))
      posterior)
    (hweighted : Integrable (fun theta =>
      continuousSleepingWeightedConditionalMeanAt
          (fun theta => conditionalTrajectoryRisk K (score theta))
          (observedTrajectoryPredictableStrategyCatalog strategy)
          theta j n x /
        continuousSleepingPredictableTiltExposure
          (observedTrajectoryPredictableStrategyCatalog strategy) j n x)
      posterior) :
    |continuousTrajectoryPosteriorAverageConditionalSuffixRisk
          K score posterior j n x -
        continuousTrajectorySleepingPosteriorNormalizedConditionalRisk
          K score strategy posterior j n x| <=
      continuousTrajectorySleepingPredictableTiltUniformDiscrepancy
        strategy j n x := by
  unfold continuousTrajectoryPosteriorAverageConditionalSuffixRisk
    continuousTrajectorySleepingPosteriorNormalizedConditionalRisk
    continuousSleepingPosteriorNormalizedConditionalMean
    continuousSleepingPosteriorWeightedConditionalMean
  rw [← integral_div]
  exact abs_integral_sub_integral_le_of_abs_sub_le_const posterior _ _
    hordinary hweighted fun theta =>
      abs_trajectoryConditionalSuffixAverage_sub_sleepingNormalizedConditionalMeanAt_le
        (fun theta => conditionalTrajectoryRisk K (score theta)) strategy
        theta hjn x hexposure (fun k _hk => hscore theta k)

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- Posterior-level empirical-risk deviation under the same realized weights. -/
theorem
    abs_continuousTrajectoryPosteriorEmpiricalSuffixRisk_sub_normalized_le
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    [IsProbabilityMeasure posterior]
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    {j n : Nat} (hjn : j < n) (x : Nat -> Z)
    (hexposure : 0 < continuousSleepingPredictableTiltExposure
      (observedTrajectoryPredictableStrategyCatalog strategy) j n x)
    (hscore : forall theta k,
      observedTrajectoryScore (score theta) k x ∈ Set.Icc (0 : Real) 1)
    (hordinary : Integrable (fun theta =>
      (∑ k ∈ Finset.Ico j n,
        observedTrajectoryScore (score theta) k x) / (n - j : Nat))
      posterior)
    (hweighted : Integrable (fun theta =>
      continuousSleepingWeightedObservationAt
          (fun theta => observedTrajectoryScore (score theta))
          (observedTrajectoryPredictableStrategyCatalog strategy)
          theta j n x /
        continuousSleepingPredictableTiltExposure
          (observedTrajectoryPredictableStrategyCatalog strategy) j n x)
      posterior) :
    |continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
          score posterior j n x -
        continuousTrajectorySleepingPosteriorNormalizedEmpiricalRisk
          score strategy posterior j n x| <=
      continuousTrajectorySleepingPredictableTiltUniformDiscrepancy
        strategy j n x := by
  unfold continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
    continuousTrajectorySleepingPosteriorNormalizedEmpiricalRisk
    continuousSleepingPosteriorNormalizedObservation
    continuousSleepingPosteriorWeightedObservation
  rw [← integral_div]
  exact abs_integral_sub_integral_le_of_abs_sub_le_const posterior _ _
    hordinary hweighted fun theta =>
      abs_trajectoryEmpiricalSuffixAverage_sub_sleepingNormalizedObservationAt_le
        (fun theta => observedTrajectoryScore (score theta)) strategy
        theta hjn x hexposure (fun k _hk => hscore theta k)

/-- The complexity and observable predictor-variance term of the normalized
sleeping predictable-tilt boundary, excluding empirical risk. -/
def continuousTrajectorySleepingPredictableTiltExcess
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (delta : Real) (j n : Nat) (x : Nat -> Z) : Real :=
  ((InformationTheory.klDiv posterior prior).toReal +
      Real.log (1 / delta) - Real.log (polynomialEpochWeight j) +
      continuousSleepingPosteriorPredictorQuadraticPenalty posterior
        (fun theta => observedTrajectoryScore (score theta))
        (observedTrajectoryPredictableStrategyCatalog strategy) j n x) /
    continuousSleepingPredictableTiltExposure
      (observedTrajectoryPredictableStrategyCatalog strategy) j n x

/-- Observable ordinary suffix-risk endpoint for a general nonnegative
time-varying predictable tilt. -/
def continuousTrajectorySleepingPredictableTiltOrdinarySuffixBoundary
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (delta : Real) (j n : Nat) (x : Nat -> Z) : Real :=
  continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
      score posterior j n x +
    continuousTrajectorySleepingPredictableTiltExcess
      prior posterior score strategy delta j n x +
    2 * continuousTrajectorySleepingPredictableTiltUniformDiscrepancy
      strategy j n x

omit [Fintype Z] [MeasurableSingletonClass Z] in
/-- Deterministic composition of a weighted PAC-Bayes inequality with the two
total-variation comparisons. -/
theorem continuousTrajectorySleepingPredictableTilt_ordinaryRisk_of_weighted
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z) (posterior prior : Measure Theta)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (delta : Real) (j n : Nat) (x : Nat -> Z)
    (hweighted :
      continuousTrajectorySleepingPosteriorNormalizedConditionalRisk
          K score strategy posterior j n x <
        continuousTrajectorySleepingPredictableTiltBoundary
          prior posterior score strategy delta j n x)
    (hconditional :
      |continuousTrajectoryPosteriorAverageConditionalSuffixRisk
            K score posterior j n x -
          continuousTrajectorySleepingPosteriorNormalizedConditionalRisk
            K score strategy posterior j n x| <=
        continuousTrajectorySleepingPredictableTiltUniformDiscrepancy
          strategy j n x)
    (hempirical :
      |continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
            score posterior j n x -
          continuousTrajectorySleepingPosteriorNormalizedEmpiricalRisk
            score strategy posterior j n x| <=
        continuousTrajectorySleepingPredictableTiltUniformDiscrepancy
          strategy j n x) :
    continuousTrajectoryPosteriorAverageConditionalSuffixRisk
        K score posterior j n x <
      continuousTrajectorySleepingPredictableTiltOrdinarySuffixBoundary
        prior posterior score strategy delta j n x := by
  unfold continuousTrajectorySleepingPredictableTiltBoundary
    continuousSleepingPredictableTiltBoundary
    continuousTrajectorySleepingPredictableTiltOrdinarySuffixBoundary
    continuousTrajectorySleepingPredictableTiltExcess
    continuousTrajectorySleepingPosteriorNormalizedEmpiricalRisk
    continuousSleepingPosteriorNormalizedObservation at *
  have hcond_upper := (abs_le.mp hconditional).2
  have hemp_upper := (abs_le.mp hempirical).1
  linarith

/-! ## Common-event ordinary-risk theorem -/

/-- One outer-mass event controls ordinary encountered conditional risk on
every nonempty path-selected suffix, for every eligible path-selected
posterior and every predeclared nonnegative predictable strategy atom.

The price for using nonuniform realized time weights is exactly twice the
finite total-variation discrepancy. This theorem does not select a strategy
outside the fixed catalog and is not a strategy-mixture or coin-betting
result. -/
theorem
    exists_continuousTrajectorySleepingPredictableTiltPACBayes_ordinarySuffixRisk_event_of_parameterMeasurable
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    {L : Real} (hL1 : L < 1)
    (hstrategy_range : forall j n u,
      strategy j n u ∈ Set.Icc (0 : Real) L)
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {delta : Real} (hdelta : 0 < delta) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta ∧
        forall x, x ∈ goodEvent ->
          forall posterior : Measure Theta,
            IsProbabilityMeasure posterior -> posterior ≪ prior ->
            Integrable (llr posterior prior) posterior ->
            forall j n : Nat, j < n ->
              0 < continuousSleepingPredictableTiltExposure
                (observedTrajectoryPredictableStrategyCatalog strategy)
                j n x ->
              continuousTrajectoryPosteriorAverageConditionalSuffixRisk
                  K score posterior j n x <
                continuousTrajectorySleepingPredictableTiltOrdinarySuffixBoundary
                  prior posterior score strategy delta j n x := by
  rcases
      exists_continuousTrajectorySleepingPredictableTiltPACBayes_normalized_event_of_parameterMeasurable
        K x0 score hscore hscore_parameter strategy hL1 hstrategy_range
        prior hdelta with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx posterior hposterior hposterior_prior hllr j n hjn hexposure
  letI : IsProbabilityMeasure posterior := hposterior
  have hweighted := hgood x hx posterior hposterior hposterior_prior hllr
    j n hjn hexposure
  have hmean_meas (k : Nat) : StronglyMeasurable
      (fun theta => conditionalTrajectoryRisk K (score theta) k x) :=
    stronglyMeasurable_conditionalTrajectoryRisk_parameter
      K score hscore_parameter k x
  have hX_meas (k : Nat) : StronglyMeasurable
      (fun theta => observedTrajectoryScore (score theta) k x) := by
    simpa only [observedTrajectoryScore] using
      hscore_parameter k (Preorder.frestrictLe k x) (x (k + 1))
  have hmean_unit (theta : Theta) (k : Nat) :
      conditionalTrajectoryRisk K (score theta) k x ∈ Set.Icc (0 : Real) 1 :=
    conditionalTrajectoryRisk_mem_Icc K (hscore theta) k x
  have hX_unit (theta : Theta) (k : Nat) :
      observedTrajectoryScore (score theta) k x ∈ Set.Icc (0 : Real) 1 :=
    observedTrajectoryScore_mem_Icc (hscore theta) k x
  have hmean_int (k : Nat) : Integrable
      (fun theta => conditionalTrajectoryRisk K (score theta) k x) posterior := by
    refine Integrable.of_bound (hmean_meas k).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun theta => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hmean_unit theta k).1]
      exact (hmean_unit theta k).2
  have hX_int (k : Nat) : Integrable
      (fun theta => observedTrajectoryScore (score theta) k x) posterior := by
    refine Integrable.of_bound (hX_meas k).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun theta => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX_unit theta k).1]
      exact (hX_unit theta k).2
  have hordinaryConditional : Integrable (fun theta =>
      (∑ k ∈ Finset.Ico j n,
        conditionalTrajectoryRisk K (score theta) k x) / (n - j : Nat))
      posterior := by
    apply Integrable.div_const
    have hsum : Integrable
        (∑ k ∈ Finset.Ico j n, fun theta =>
          conditionalTrajectoryRisk K (score theta) k x) posterior := by
      apply integrable_finsetSum'
      intro k _hk
      exact hmean_int k
    convert hsum using 1
    funext theta
    simp only [Finset.sum_apply]
  have hordinaryEmpirical : Integrable (fun theta =>
      (∑ k ∈ Finset.Ico j n,
        observedTrajectoryScore (score theta) k x) / (n - j : Nat))
      posterior := by
    apply Integrable.div_const
    have hsum : Integrable
        (∑ k ∈ Finset.Ico j n, fun theta =>
          observedTrajectoryScore (score theta) k x) posterior := by
      apply integrable_finsetSum'
      intro k _hk
      exact hX_int k
    convert hsum using 1
    funext theta
    simp only [Finset.sum_apply]
  have hweightedConditionalAt : Integrable (fun theta =>
      continuousSleepingWeightedConditionalMeanAt
        (fun theta => conditionalTrajectoryRisk K (score theta))
        (observedTrajectoryPredictableStrategyCatalog strategy)
        theta j n x) posterior := by
    unfold continuousSleepingWeightedConditionalMeanAt
    have hsum : Integrable
        (∑ k ∈ Finset.range n, fun theta =>
          sleepingStrategy
              (observedTrajectoryPredictableStrategyCatalog strategy) j k x *
            conditionalTrajectoryRisk K (score theta) k x) posterior := by
      apply integrable_finsetSum'
      intro k _hk
      exact (hmean_int k).const_mul
        (sleepingStrategy
          (observedTrajectoryPredictableStrategyCatalog strategy) j k x)
    convert hsum using 1
    funext theta
    simp only [Finset.sum_apply]
  have hweightedEmpiricalAt : Integrable (fun theta =>
      continuousSleepingWeightedObservationAt
        (fun theta => observedTrajectoryScore (score theta))
        (observedTrajectoryPredictableStrategyCatalog strategy)
        theta j n x) posterior := by
    unfold continuousSleepingWeightedObservationAt
    have hsum : Integrable
        (∑ k ∈ Finset.range n, fun theta =>
          sleepingStrategy
              (observedTrajectoryPredictableStrategyCatalog strategy) j k x *
            observedTrajectoryScore (score theta) k x) posterior := by
      apply integrable_finsetSum'
      intro k _hk
      exact (hX_int k).const_mul
        (sleepingStrategy
          (observedTrajectoryPredictableStrategyCatalog strategy) j k x)
    convert hsum using 1
    funext theta
    simp only [Finset.sum_apply]
  have hweightedConditional : Integrable (fun theta =>
      continuousSleepingWeightedConditionalMeanAt
          (fun theta => conditionalTrajectoryRisk K (score theta))
          (observedTrajectoryPredictableStrategyCatalog strategy)
          theta j n x /
        continuousSleepingPredictableTiltExposure
          (observedTrajectoryPredictableStrategyCatalog strategy) j n x)
      posterior := hweightedConditionalAt.div_const _
  have hweightedEmpirical : Integrable (fun theta =>
      continuousSleepingWeightedObservationAt
          (fun theta => observedTrajectoryScore (score theta))
          (observedTrajectoryPredictableStrategyCatalog strategy)
          theta j n x /
        continuousSleepingPredictableTiltExposure
          (observedTrajectoryPredictableStrategyCatalog strategy) j n x)
      posterior := hweightedEmpiricalAt.div_const _
  have hconditional :=
    abs_continuousTrajectoryPosteriorAverageConditionalSuffixRisk_sub_normalized_le
      K score posterior strategy hjn x hexposure
      (fun theta k => hmean_unit theta k)
      hordinaryConditional hweightedConditional
  have hempirical :=
    abs_continuousTrajectoryPosteriorEmpiricalSuffixRisk_sub_normalized_le
      score posterior strategy hjn x hexposure
      (fun theta k => hX_unit theta k)
      hordinaryEmpirical hweightedEmpirical
  exact continuousTrajectorySleepingPredictableTilt_ordinaryRisk_of_weighted
    K score posterior prior strategy delta j n x hweighted
      hconditional hempirical

omit [MeasurableSpace Theta] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
/-- Constant positive post-wake tilts have exactly zero uniform-weight
discrepancy. -/
@[simp]
theorem continuousTrajectorySleepingPredictableTiltUniformDiscrepancy_countableConstant
    (eta : Nat -> Real) {j n : Nat} (hjn : j < n)
    (heta : 0 < eta j) (x : Nat -> Z) :
    continuousTrajectorySleepingPredictableTiltUniformDiscrepancy
        (countableConstantTrajectoryTiltCatalog eta) j n x = 0 := by
  unfold continuousTrajectorySleepingPredictableTiltUniformDiscrepancy
    finiteUniformNormalizedWeightDiscrepancy
  rw [continuousTrajectorySleepingExposure_countableConstant eta hjn.le x]
  have hm : (0 : Real) < (n - j : Nat) :=
    Nat.cast_pos.mpr (Nat.sub_pos_of_lt hjn)
  have hm_ne : ((n - j : Nat) : Real) ≠ 0 := hm.ne'
  have heta_ne : eta j ≠ 0 := heta.ne'
  have hterm : forall k, k ∈ Finset.Ico j n ->
      ((Finset.Ico j n).card : Real)⁻¹ -
          observedTrajectoryPredictableTilt
              (countableConstantTrajectoryTiltCatalog eta j) k x /
            (((n - j : Nat) : Real) * eta j) = 0 := by
    intro k _hk
    simp only [Nat.card_Ico, observedTrajectoryPredictableTilt,
      countableConstantTrajectoryTiltCatalog]
    field_simp [hm_ne, heta_ne]
    ring
  have hsumzero :
      (∑ k ∈ Finset.Ico j n,
        |((Finset.Ico j n).card : Real)⁻¹ -
          observedTrajectoryPredictableTilt
              (countableConstantTrajectoryTiltCatalog eta j) k x /
            (((n - j : Nat) : Real) * eta j)|) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [abs_eq_zero]
    exact hterm k hk
  rw [hsumzero]
  norm_num

end

end FormalSLT.StochasticDynamics
