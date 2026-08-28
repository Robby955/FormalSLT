/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.TrajectorySleepingStrategyPACBayes
import FormalSLT.StochasticDynamics.FiniteTrajectorySleepingOrdinaryRiskPACBayes
import FormalSLT.StochasticDynamics.ContinuousTrajectorySleepingPredictableTiltOrdinaryRisk

/-!
# Ordinary suffix risk for finite sleeping-strategy posteriors

`TrajectorySleepingStrategyPACBayes` permits the reporting rule to choose both
a model posterior and a soft posterior over a finite catalog of predictable
strategies after observing the path. Its direct endpoint is normalized by the
posterior-averaged predictable tilt.

This module gives that endpoint an ordinary encountered-suffix interpretation
when every catalog strategy has one common wake time fixed before observation.
The strategy posterior induces one effective time-weight vector on the suffix.
For losses in `[0,1]`, replacing that vector by uniform suffix weights costs at
most its finite total-variation discrepancy for conditional risk and once more
for empirical risk. The resulting common-event theorem keeps the separate
model- and strategy-selection KL terms from the finite product-prior master.

The conclusion concerns conditional loss encountered on the monitored suffix.
It is not future, stationary, population, or deployment risk. The common wake
is fixed before the path is observed; this module does not provide post-data
wake selection, a countable active-prefix posterior, or coin betting.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardPredictableStrategyPACBayes
open scoped BigOperators

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {ι κ Z : Type*}
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-! ## Posterior-induced suffix weights -/

/-- The time-`k` predictable tilt averaged under a finite strategy posterior. -/
def finiteStrategyPosteriorEffectiveTrajectoryWeight
    (strategyPosterior : κ -> Real)
    (strategy : κ -> TrajectoryPredictableTilt Z)
    (k : Nat) (x : Nat -> Z) : Real :=
  posteriorAverage strategyPosterior fun a =>
    observedTrajectoryPredictableTilt (strategy a) k x

/-- Total posterior-averaged exposure on the common-wake suffix `[w,n)`. -/
def finiteStrategyPosteriorSleepingExposure
    (strategyPosterior : κ -> Real)
    (strategy : κ -> TrajectoryPredictableTilt Z)
    (w n : Nat) (x : Nat -> Z) : Real :=
  ∑ k ∈ Finset.Ico w n,
    finiteStrategyPosteriorEffectiveTrajectoryWeight
      strategyPosterior strategy k x

/-- Realized discrepancy between uniform suffix weights and the normalized
time weights induced by the selected finite strategy posterior. -/
def finiteStrategyPosteriorSleepingUniformDiscrepancy
    (strategyPosterior : κ -> Real)
    (strategy : κ -> TrajectoryPredictableTilt Z)
    (w n : Nat) (x : Nat -> Z) : Real :=
  finiteUniformNormalizedWeightDiscrepancy (Finset.Ico w n)
    (fun k => finiteStrategyPosteriorEffectiveTrajectoryWeight
      strategyPosterior strategy k x)
    (finiteStrategyPosteriorSleepingExposure
      strategyPosterior strategy w n x)

/-- Put one trajectory strategy to sleep until a common, predeclared wake. -/
private def commonWakeTrajectoryStrategy
    (w : Nat) (strategy : TrajectoryPredictableTilt Z) :
    TrajectoryPredictableTilt Z :=
  fun k u => if w <= k then strategy k u else 0

omit [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
@[simp]
private theorem sleepingTrajectoryStrategyCatalog_commonWake
    (w : Nat) (strategy : κ -> TrajectoryPredictableTilt Z)
    (a : κ) (i : ι) :
    sleepingTrajectoryStrategyCatalog (fun _ : κ => w) strategy a i =
      commonWakeTrajectoryStrategy w (strategy a) := by
  rfl

/-- Conditional suffix risk under the posterior-induced normalized time
weights. The model and strategy posteriors remain factorized. -/
def finiteTrajectorySleepingStrategyPosteriorNormalizedConditionalSuffixRisk
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : ι -> TrajectoryScore Z)
    (modelPosterior : ι -> Real) (strategyPosterior : κ -> Real)
    (strategy : κ -> TrajectoryPredictableTilt Z)
    (w n : Nat) (x : Nat -> Z) : Real :=
  (∑ k ∈ Finset.Ico w n,
      finiteStrategyPosteriorEffectiveTrajectoryWeight
          strategyPosterior strategy k x *
        posteriorAverage modelPosterior (fun i =>
          conditionalTrajectoryRisk K (score i) k x)) /
    finiteStrategyPosteriorSleepingExposure
      strategyPosterior strategy w n x

/-- Empirical suffix risk under the same posterior-induced normalized time
weights. -/
def finiteTrajectorySleepingStrategyPosteriorNormalizedEmpiricalSuffixRisk
    (score : ι -> TrajectoryScore Z)
    (modelPosterior : ι -> Real) (strategyPosterior : κ -> Real)
    (strategy : κ -> TrajectoryPredictableTilt Z)
    (w n : Nat) (x : Nat -> Z) : Real :=
  (∑ k ∈ Finset.Ico w n,
      finiteStrategyPosteriorEffectiveTrajectoryWeight
          strategyPosterior strategy k x *
        posteriorAverage modelPosterior (fun i =>
          observedTrajectoryScore (score i) k x)) /
    finiteStrategyPosteriorSleepingExposure
      strategyPosterior strategy w n x

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
private theorem posteriorAverage_finsetSum
    {Alpha Beta : Type*} [Fintype Alpha]
    (posterior : Alpha -> Real) (s : Finset Beta)
    (f : Alpha -> Beta -> Real) :
    posteriorAverage posterior (fun a => ∑ b ∈ s, f a b) =
      ∑ b ∈ s, posteriorAverage posterior (fun a => f a b) := by
  unfold posteriorAverage
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
private theorem posteriorAverage_finsetAverage
    {Alpha Beta : Type*} [Fintype Alpha]
    (posterior : Alpha -> Real) (s : Finset Beta)
    (f : Alpha -> Beta -> Real) (denominator : Real) :
    posteriorAverage posterior
        (fun a => (∑ b ∈ s, f a b) / denominator) =
      (∑ b ∈ s, posteriorAverage posterior (fun a => f a b)) /
        denominator := by
  calc
    posteriorAverage posterior
        (fun a => (∑ b ∈ s, f a b) / denominator) =
      posteriorAverage posterior (fun a => ∑ b ∈ s, f a b) /
        denominator := by
          unfold posteriorAverage
          calc
            (∑ a, posterior a * ((∑ b ∈ s, f a b) / denominator)) =
                ∑ a, (posterior a * (∑ b ∈ s, f a b)) / denominator := by
              apply Finset.sum_congr rfl
              intro a _ha
              ring
            _ = (∑ a, posterior a * (∑ b ∈ s, f a b)) /
                denominator := by rw [Finset.sum_div]
    _ = _ := by rw [posteriorAverage_finsetSum]

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
private theorem posteriorAverage_mem_Icc_of_isPMF
    {Alpha : Type*} [Fintype Alpha]
    {posterior : Alpha -> Real} (hposterior : IsPMF posterior)
    {f : Alpha -> Real} (hf : forall a, f a ∈ Set.Icc (0 : Real) 1) :
    posteriorAverage posterior f ∈ Set.Icc (0 : Real) 1 := by
  constructor
  · unfold posteriorAverage
    exact Finset.sum_nonneg fun a _ha =>
      mul_nonneg (hposterior.nonneg a) (hf a).1
  · calc
      posteriorAverage posterior f <=
          ∑ a : Alpha, posterior a * 1 := by
        unfold posteriorAverage
        exact Finset.sum_le_sum fun a _ha =>
          mul_le_mul_of_nonneg_left (hf a).2 (hposterior.nonneg a)
      _ = 1 := by simpa using hposterior.sum_one

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
private theorem posteriorAverage_modelStrategy_commonWakeWeightedSum_eq
    (modelPosterior : ι -> Real) (strategyPosterior : κ -> Real)
    (strategy : κ -> TrajectoryPredictableTilt Z)
    (Y : ι -> Nat -> (Nat -> Z) -> Real)
    {w n : Nat} (hwn : w <= n) (x : Nat -> Z) :
    posteriorAverage
        (modelStrategyProductPrior modelPosterior strategyPosterior)
        (fun p : ι × κ =>
          ∑ k ∈ Finset.range n,
            observedTrajectoryPredictableTilt
                (sleepingTrajectoryStrategyCatalog
                  (fun _ : κ => w) strategy p.2 p.1) k x *
              Y p.1 k x) =
      ∑ k ∈ Finset.Ico w n,
        finiteStrategyPosteriorEffectiveTrajectoryWeight
            strategyPosterior strategy k x *
          posteriorAverage modelPosterior (fun i => Y i k x) := by
  have hsum := posteriorAverage_finsetSum
    (modelStrategyProductPrior modelPosterior strategyPosterior)
    (Finset.range n)
    (fun p : ι × κ => fun k =>
      observedTrajectoryPredictableTilt
          (sleepingTrajectoryStrategyCatalog
            (fun _ : κ => w) strategy p.2 p.1) k x *
        Y p.1 k x)
  rw [hsum]
  have hpoint (k : Nat) :
      posteriorAverage
          (modelStrategyProductPrior modelPosterior strategyPosterior)
          (fun p : ι × κ =>
            observedTrajectoryPredictableTilt
                (sleepingTrajectoryStrategyCatalog
                  (fun _ : κ => w) strategy p.2 p.1) k x *
              Y p.1 k x) =
        posteriorAverage modelPosterior (fun i => Y i k x) *
          posteriorAverage strategyPosterior (fun a =>
            observedTrajectoryPredictableTilt
              (commonWakeTrajectoryStrategy w (strategy a)) k x) := by
    simpa only [sleepingTrajectoryStrategyCatalog_commonWake, mul_comm] using
      (posteriorAverage_modelStrategyProductPrior_separable
        modelPosterior strategyPosterior
        (fun i => Y i k x)
        (fun a => observedTrajectoryPredictableTilt
          (commonWakeTrajectoryStrategy w (strategy a)) k x))
  simp_rw [hpoint]
  rw [← Finset.sum_range_add_sum_Ico
    (fun k =>
        posteriorAverage modelPosterior (fun i => Y i k x) *
          posteriorAverage strategyPosterior (fun a =>
            observedTrajectoryPredictableTilt
              (commonWakeTrajectoryStrategy w (strategy a)) k x)) hwn]
  have hbefore :
      (∑ k ∈ Finset.range w,
        posteriorAverage modelPosterior (fun i => Y i k x) *
          posteriorAverage strategyPosterior (fun a =>
            observedTrajectoryPredictableTilt
              (commonWakeTrajectoryStrategy w (strategy a)) k x)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkw : k < w := Finset.mem_range.mp hk
    simp [commonWakeTrajectoryStrategy,
      observedTrajectoryPredictableTilt, not_le.mpr hkw, posteriorAverage]
  rw [hbefore, zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  have hwk : w <= k := (Finset.mem_Ico.mp hk).1
  simp [commonWakeTrajectoryStrategy,
    observedTrajectoryPredictableTilt, hwk,
    finiteStrategyPosteriorEffectiveTrajectoryWeight, mul_comm]

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- Under a factorized posterior and a common wake, the total tilt in the
existing joint theorem is exactly the posterior-induced suffix exposure. -/
theorem trajectorySleepingStrategyPosteriorTotalWeight_commonWake_factorized
    (modelPosterior : ι -> Real) (strategyPosterior : κ -> Real)
    (hmodelPosterior : IsPMF modelPosterior)
    (strategy : κ -> TrajectoryPredictableTilt Z)
    {w n : Nat} (hwn : w <= n) (x : Nat -> Z) :
    trajectoryPredictableStrategyPosteriorTotalWeight
        (sleepingTrajectoryStrategyCatalog (fun _ : κ => w) strategy)
        (modelStrategyProductPrior modelPosterior strategyPosterior) n x =
      finiteStrategyPosteriorSleepingExposure
        strategyPosterior strategy w n x := by
  have hsum := posteriorAverage_modelStrategy_commonWakeWeightedSum_eq
    modelPosterior strategyPosterior strategy
      (fun _i _k _x => (1 : Real)) hwn x
  simpa [trajectoryPredictableStrategyPosteriorTotalWeight,
    trajectoryPredictableTiltPosteriorTotalWeight,
    FormalSLT.PACBayes.ForwardPredictableTiltPACBayes.forwardPredictableTiltPosteriorTotalWeight,
    finiteStrategyPosteriorSleepingExposure,
    posteriorAverage, hmodelPosterior.sum_one] using hsum

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ]
  [Fintype Z] [MeasurableSingletonClass Z] in
/-- The normalized joint conditional-risk quantity equals the explicit
posterior-induced weighted suffix risk. -/
theorem
    trajectorySleepingStrategyPosteriorNormalizedConditionalRisk_commonWake_factorized
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : ι -> TrajectoryScore Z)
    (modelPosterior : ι -> Real) (strategyPosterior : κ -> Real)
    (hmodelPosterior : IsPMF modelPosterior)
    (strategy : κ -> TrajectoryPredictableTilt Z)
    {w n : Nat} (hwn : w <= n) (x : Nat -> Z) :
    trajectoryPredictableStrategyPosteriorNormalizedConditionalRisk
        K score
        (sleepingTrajectoryStrategyCatalog (fun _ : κ => w) strategy)
        (modelStrategyProductPrior modelPosterior strategyPosterior) n x =
      finiteTrajectorySleepingStrategyPosteriorNormalizedConditionalSuffixRisk
        K score modelPosterior strategyPosterior strategy w n x := by
  have hnum := posteriorAverage_modelStrategy_commonWakeWeightedSum_eq
    modelPosterior strategyPosterior strategy
      (fun i k x => conditionalTrajectoryRisk K (score i) k x) hwn x
  have hden :=
    trajectorySleepingStrategyPosteriorTotalWeight_commonWake_factorized
      modelPosterior strategyPosterior hmodelPosterior strategy hwn x
  have hden' :
      FormalSLT.PACBayes.ForwardPredictableTiltPACBayes.forwardPredictableTiltPosteriorTotalWeight
          (modelStrategyProductPrior modelPosterior strategyPosterior)
          (fun p : ι × κ => observedTrajectoryPredictableTilt
            (sleepingTrajectoryStrategyCatalog
              (fun _ : κ => w) strategy p.2 p.1)) n x =
        finiteStrategyPosteriorSleepingExposure
          strategyPosterior strategy w n x := by
    simpa [trajectoryPredictableStrategyPosteriorTotalWeight,
      trajectoryPredictableTiltPosteriorTotalWeight] using hden
  unfold trajectoryPredictableStrategyPosteriorNormalizedConditionalRisk
    trajectoryPredictableTiltPosteriorNormalizedConditionalRisk
    FormalSLT.PACBayes.ForwardPredictableTiltPACBayes.forwardPredictableTiltPosteriorNormalizedMean
    finiteTrajectorySleepingStrategyPosteriorNormalizedConditionalSuffixRisk
  rw [hnum, hden']

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The normalized joint empirical-risk quantity equals the explicit
posterior-induced weighted suffix risk. -/
theorem
    trajectorySleepingStrategyPosteriorNormalizedEmpiricalRisk_commonWake_factorized
    (score : ι -> TrajectoryScore Z)
    (modelPosterior : ι -> Real) (strategyPosterior : κ -> Real)
    (hmodelPosterior : IsPMF modelPosterior)
    (strategy : κ -> TrajectoryPredictableTilt Z)
    {w n : Nat} (hwn : w <= n) (x : Nat -> Z) :
    trajectoryPredictableStrategyPosteriorNormalizedEmpiricalRisk
        score
        (sleepingTrajectoryStrategyCatalog (fun _ : κ => w) strategy)
        (modelStrategyProductPrior modelPosterior strategyPosterior) n x =
      finiteTrajectorySleepingStrategyPosteriorNormalizedEmpiricalSuffixRisk
        score modelPosterior strategyPosterior strategy w n x := by
  have hnum := posteriorAverage_modelStrategy_commonWakeWeightedSum_eq
    modelPosterior strategyPosterior strategy
      (fun i k x => observedTrajectoryScore (score i) k x) hwn x
  have hden :=
    trajectorySleepingStrategyPosteriorTotalWeight_commonWake_factorized
      modelPosterior strategyPosterior hmodelPosterior strategy hwn x
  have hden' :
      FormalSLT.PACBayes.ForwardPredictableTiltPACBayes.forwardPredictableTiltPosteriorTotalWeight
          (modelStrategyProductPrior modelPosterior strategyPosterior)
          (fun p : ι × κ => observedTrajectoryPredictableTilt
            (sleepingTrajectoryStrategyCatalog
              (fun _ : κ => w) strategy p.2 p.1)) n x =
        finiteStrategyPosteriorSleepingExposure
          strategyPosterior strategy w n x := by
    simpa [trajectoryPredictableStrategyPosteriorTotalWeight,
      trajectoryPredictableTiltPosteriorTotalWeight] using hden
  unfold trajectoryPredictableStrategyPosteriorNormalizedEmpiricalRisk
    trajectoryPredictableTiltPosteriorNormalizedEmpiricalRisk
    FormalSLT.PACBayes.ForwardPredictableTiltPACBayes.forwardPredictableTiltPosteriorNormalizedObservation
    finiteTrajectorySleepingStrategyPosteriorNormalizedEmpiricalSuffixRisk
  rw [hnum, hden']

/-! ## Finite-TV comparisons -/

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ] in
/-- Ordinary posterior conditional suffix risk differs from the normalized
strategy-posterior weighted risk by at most the realized time-weight
discrepancy. -/
theorem
    abs_finiteTrajectoryPosteriorConditionalSuffixRisk_sub_sleepingStrategyPosteriorNormalized_le
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    (score : ι -> TrajectoryScore Z)
    (hscore : forall i n u y, score i n u y ∈ Set.Icc (0 : Real) 1)
    (modelPosterior : ι -> Real) (hmodelPosterior : IsPMF modelPosterior)
    (strategyPosterior : κ -> Real)
    (strategy : κ -> TrajectoryPredictableTilt Z)
    {w n : Nat} (hwn : w < n) (x : Nat -> Z)
    (hexposure : 0 < finiteStrategyPosteriorSleepingExposure
      strategyPosterior strategy w n x) :
    |finiteTrajectoryPosteriorAverageConditionalSuffixRisk
          K score modelPosterior w n x -
        trajectoryPredictableStrategyPosteriorNormalizedConditionalRisk
          K score
          (sleepingTrajectoryStrategyCatalog (fun _ : κ => w) strategy)
          (modelStrategyProductPrior modelPosterior strategyPosterior) n x| <=
      finiteStrategyPosteriorSleepingUniformDiscrepancy
        strategyPosterior strategy w n x := by
  rw [trajectorySleepingStrategyPosteriorNormalizedConditionalRisk_commonWake_factorized
    K score modelPosterior strategyPosterior hmodelPosterior strategy hwn.le x]
  unfold finiteTrajectoryPosteriorAverageConditionalSuffixRisk
    finiteTrajectorySleepingStrategyPosteriorNormalizedConditionalSuffixRisk
    finiteStrategyPosteriorSleepingUniformDiscrepancy
  rw [posteriorAverage_finsetAverage]
  have hs : (Finset.Ico w n).Nonempty :=
    ⟨w, Finset.mem_Ico.mpr ⟨le_rfl, hwn⟩⟩
  simpa [Nat.card_Ico] using
    (abs_uniformAverage_sub_normalizedWeightedAverage_le_discrepancy
      (Finset.Ico w n) hs
      (fun k => finiteStrategyPosteriorEffectiveTrajectoryWeight
        strategyPosterior strategy k x)
      (fun k => posteriorAverage modelPosterior (fun i =>
        conditionalTrajectoryRisk K (score i) k x))
      hexposure.ne' rfl
      (fun k _hk => posteriorAverage_mem_Icc_of_isPMF hmodelPosterior
        (fun i => conditionalTrajectoryRisk_mem_Icc K (hscore i) k x)))

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The analogous finite-TV comparison for posterior empirical suffix risk. -/
theorem
    abs_finiteTrajectoryPosteriorEmpiricalSuffixRisk_sub_sleepingStrategyPosteriorNormalized_le
    (score : ι -> TrajectoryScore Z)
    (hscore : forall i n u y, score i n u y ∈ Set.Icc (0 : Real) 1)
    (modelPosterior : ι -> Real) (hmodelPosterior : IsPMF modelPosterior)
    (strategyPosterior : κ -> Real)
    (strategy : κ -> TrajectoryPredictableTilt Z)
    {w n : Nat} (hwn : w < n) (x : Nat -> Z)
    (hexposure : 0 < finiteStrategyPosteriorSleepingExposure
      strategyPosterior strategy w n x) :
    |finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
          score modelPosterior w n x -
        trajectoryPredictableStrategyPosteriorNormalizedEmpiricalRisk
          score
          (sleepingTrajectoryStrategyCatalog (fun _ : κ => w) strategy)
          (modelStrategyProductPrior modelPosterior strategyPosterior) n x| <=
      finiteStrategyPosteriorSleepingUniformDiscrepancy
        strategyPosterior strategy w n x := by
  rw [trajectorySleepingStrategyPosteriorNormalizedEmpiricalRisk_commonWake_factorized
    score modelPosterior strategyPosterior hmodelPosterior strategy hwn.le x]
  unfold finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
    finiteTrajectorySleepingStrategyPosteriorNormalizedEmpiricalSuffixRisk
    finiteStrategyPosteriorSleepingUniformDiscrepancy
  rw [posteriorAverage_finsetAverage]
  have hs : (Finset.Ico w n).Nonempty :=
    ⟨w, Finset.mem_Ico.mpr ⟨le_rfl, hwn⟩⟩
  simpa [Nat.card_Ico] using
    (abs_uniformAverage_sub_normalizedWeightedAverage_le_discrepancy
      (Finset.Ico w n) hs
      (fun k => finiteStrategyPosteriorEffectiveTrajectoryWeight
        strategyPosterior strategy k x)
      (fun k => posteriorAverage modelPosterior (fun i =>
        observedTrajectoryScore (score i) k x))
      hexposure.ne' rfl
      (fun k _hk => posteriorAverage_mem_Icc_of_isPMF hmodelPosterior
        (fun i => observedTrajectoryScore_mem_Icc (hscore i) k x)))

/-! ## Ordinary-risk boundary and common event -/

/-- Complexity, selection, and observable quadratic terms divided by the
posterior-induced suffix exposure. -/
def finiteTrajectorySleepingStrategyPosteriorExcess
    (modelPrior modelPosterior : ι -> Real)
    (strategyPrior strategyPosterior : κ -> Real)
    (score : ι -> TrajectoryScore Z)
    (strategy : κ -> TrajectoryPredictableTilt Z)
    (delta : Real) (w n : Nat) (x : Nat -> Z) : Real :=
  ((klDiv modelPosterior modelPrior +
        klDiv strategyPosterior strategyPrior) +
      Real.log (1 / delta) +
      trajectoryPredictableStrategyPosteriorQuadraticPenalty score
        (sleepingTrajectoryStrategyCatalog (fun _ : κ => w) strategy)
        (modelStrategyProductPrior modelPosterior strategyPosterior) n x) /
    finiteStrategyPosteriorSleepingExposure
      strategyPosterior strategy w n x

/-- Observable ordinary encountered-suffix endpoint for a path-selected finite
model posterior and finite strategy posterior. -/
def finiteTrajectorySleepingStrategyPosteriorOrdinarySuffixBoundary
    (modelPrior modelPosterior : ι -> Real)
    (strategyPrior strategyPosterior : κ -> Real)
    (score : ι -> TrajectoryScore Z)
    (strategy : κ -> TrajectoryPredictableTilt Z)
    (delta : Real) (w n : Nat) (x : Nat -> Z) : Real :=
  finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
      score modelPosterior w n x +
    finiteTrajectorySleepingStrategyPosteriorExcess
      modelPrior modelPosterior strategyPrior strategyPosterior
      score strategy delta w n x +
    2 * finiteStrategyPosteriorSleepingUniformDiscrepancy
      strategyPosterior strategy w n x

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ] in
/-- Deterministic composition of the finite sleeping-strategy weighted theorem
with the two posterior-level finite-TV comparisons. -/
theorem finiteTrajectorySleepingStrategyPosterior_ordinaryRisk_of_weighted
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    (score : ι -> TrajectoryScore Z)
    (hscore : forall i n u y, score i n u y ∈ Set.Icc (0 : Real) 1)
    (modelPrior modelPosterior : ι -> Real)
    (hmodelPosterior : IsPMF modelPosterior)
    (strategyPrior strategyPosterior : κ -> Real)
    (strategy : κ -> TrajectoryPredictableTilt Z)
    (delta : Real) {w n : Nat} (hwn : w < n) (x : Nat -> Z)
    (hexposure : 0 < finiteStrategyPosteriorSleepingExposure
      strategyPosterior strategy w n x)
    (hweighted :
      trajectoryPredictableStrategyPosteriorNormalizedConditionalRisk
          K score
          (sleepingTrajectoryStrategyCatalog (fun _ : κ => w) strategy)
          (modelStrategyProductPrior modelPosterior strategyPosterior) n x <
        trajectoryPredictableStrategyPosteriorNormalizedEmpiricalRisk
            score
            (sleepingTrajectoryStrategyCatalog (fun _ : κ => w) strategy)
            (modelStrategyProductPrior modelPosterior strategyPosterior) n x +
          ((klDiv modelPosterior modelPrior +
                klDiv strategyPosterior strategyPrior) +
              Real.log (1 / delta) +
              trajectoryPredictableStrategyPosteriorQuadraticPenalty score
                (sleepingTrajectoryStrategyCatalog (fun _ : κ => w) strategy)
                (modelStrategyProductPrior
                  modelPosterior strategyPosterior) n x) /
            finiteStrategyPosteriorSleepingExposure
              strategyPosterior strategy w n x) :
    finiteTrajectoryPosteriorAverageConditionalSuffixRisk
        K score modelPosterior w n x <
      finiteTrajectorySleepingStrategyPosteriorOrdinarySuffixBoundary
        modelPrior modelPosterior strategyPrior strategyPosterior
        score strategy delta w n x := by
  have hconditional :=
    abs_finiteTrajectoryPosteriorConditionalSuffixRisk_sub_sleepingStrategyPosteriorNormalized_le
      K score hscore modelPosterior hmodelPosterior strategyPosterior
      strategy hwn x hexposure
  have hempirical :=
    abs_finiteTrajectoryPosteriorEmpiricalSuffixRisk_sub_sleepingStrategyPosteriorNormalized_le
      score hscore modelPosterior hmodelPosterior strategyPosterior
      strategy hwn x hexposure
  have hconditionalUpper := (abs_le.mp hconditional).2
  have hempiricalUpper := (abs_le.mp hempirical).1
  unfold finiteTrajectorySleepingStrategyPosteriorOrdinarySuffixBoundary
    finiteTrajectorySleepingStrategyPosteriorExcess
  linarith

omit [DecidableEq ι] [DecidableEq κ] in
/-- One trajectory event controls ordinary encountered suffix risk for every
reporting time and the supplied path- and time-selected factorized model and
strategy posteriors. The common wake and finite strategy catalog are fixed
before observation; model and strategy selection pay separate KL terms. -/
theorem
    exists_finiteTrajectorySleepingStrategyPACBayes_factorized_ordinarySuffixRisk_selected_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    {score : ι -> TrajectoryScore Z}
    (hscore : forall i n u y, score i n u y ∈ Set.Icc (0 : Real) 1)
    (w : Nat)
    {strategy : κ -> TrajectoryPredictableTilt Z}
    {L : Real} (hL0 : 0 <= L) (hL1 : L < 1)
    (hstrategy : forall a n u,
      strategy a n u ∈ Set.Icc (0 : Real) L)
    {modelPrior : ι -> Real} (hmodelPrior : IsFullSupportPMF modelPrior)
    {strategyPrior : κ -> Real}
    (hstrategyPrior : IsFullSupportPMF strategyPrior)
    {delta : Real} (hdelta : 0 < delta)
    (modelPosterior : (Nat -> Z) -> Nat -> ι -> Real)
    (hmodelPosterior : forall x n, IsPMF (modelPosterior x n))
    (strategyPosterior : (Nat -> Z) -> Nat -> κ -> Real)
    (hstrategyPosterior : forall x n, IsPMF (strategyPosterior x n)) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta ∧
        forall x, x ∈ goodEvent -> forall n : Nat, w < n ->
          0 < finiteStrategyPosteriorSleepingExposure
              (strategyPosterior x n) strategy w n x ->
            finiteTrajectoryPosteriorAverageConditionalSuffixRisk
                K score (modelPosterior x n) w n x <
              finiteTrajectorySleepingStrategyPosteriorOrdinarySuffixBoundary
                modelPrior (modelPosterior x n)
                strategyPrior (strategyPosterior x n)
                score strategy delta w n x := by
  rcases
      exists_trajectorySleepingStrategyPACBayes_factorized_normalized_selected_event
        K x0 hscore (wake := fun _ : κ => w) hL0 hL1 hstrategy
        hmodelPrior hstrategyPrior hdelta
        modelPosterior hmodelPosterior strategyPosterior hstrategyPosterior with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx n hwn hexposure
  have htotal :=
    trajectorySleepingStrategyPosteriorTotalWeight_commonWake_factorized
      (modelPosterior x n) (strategyPosterior x n)
      (hmodelPosterior x n) strategy hwn.le x
  have htotalPos : 0 <
      trajectoryPredictableStrategyPosteriorTotalWeight
        (sleepingTrajectoryStrategyCatalog (fun _ : κ => w) strategy)
        (modelStrategyProductPrior
          (modelPosterior x n) (strategyPosterior x n)) n x := by
    rwa [htotal]
  have hweighted := hgood x hx n htotalPos
  rw [htotal] at hweighted
  exact finiteTrajectorySleepingStrategyPosterior_ordinaryRisk_of_weighted
    K score hscore modelPrior (modelPosterior x n)
      (hmodelPosterior x n) strategyPrior (strategyPosterior x n)
      strategy delta hwn x hexposure hweighted

end

end FormalSLT.StochasticDynamics
