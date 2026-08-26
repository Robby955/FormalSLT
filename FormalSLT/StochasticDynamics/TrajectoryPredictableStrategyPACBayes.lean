/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.ForwardPredictableStrategyPACBayes
import FormalSLT.StochasticDynamics.TrajectoryPredictableTiltPACBayes

/-!
# Joint model--strategy PAC-Bayes bounds for trajectories

This module exposes the finite joint model--strategy selection theorem on
prefix-dependent finite-state trajectories.  Each declared strategy maps a
model and the prefix available before the next transition to a legal tilt.
After observing the trajectory and time, the reporting rule may select an
arbitrary joint posterior over models and strategies.  The bound charges KL
from that joint posterior to an independent model--strategy product prior.

The general theorem does not permit a strategy to inspect the next state before
its tilt is chosen.  Its risk quantities are normalized tilt-weighted
prequential averages under the trajectory law with deterministic initial state
`x0`.  A factorized corollary recovers ordinary posterior-averaged risk when
each model has a constant one-step conditional risk and the predeclared
predictable strategies are shared across models.  A second, more concrete
corollary handles scalar constant-tilt catalogs and ordinary monitored-prefix
risk.  Both charge model and strategy selection by separate KL terms.  Neither
endpoint is a stationary, future, or population-risk statement without a
separate theorem connecting the stated trajectory conditional risk to that
interpretation.  Only the predeclared catalog members are predictable; the
post-hoc reporting posterior is not a composite predictable e-process.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardPredictableTiltPACBayes
open FormalSLT.PACBayes.ForwardPredictableStrategyPACBayes

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {ι κ Z : Type*}
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- Joint model--strategy weighted conditional-minus-observed gap. -/
def trajectoryPredictableStrategyPosteriorMeanGap
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    (score : ι → TrajectoryScore Z)
    (strategy : κ → ι → TrajectoryPredictableTilt Z)
    (jointPosterior : ι × κ → ℝ) (n : ℕ) (x : ℕ → Z) : ℝ :=
  trajectoryPredictableTiltPosteriorMeanGap K
    (fun p : ι × κ ↦ score p.1)
    (fun p : ι × κ ↦ strategy p.2 p.1) jointPosterior n x

/-- Joint model--strategy observable quadratic penalty. -/
def trajectoryPredictableStrategyPosteriorQuadraticPenalty
    (score : ι → TrajectoryScore Z)
    (strategy : κ → ι → TrajectoryPredictableTilt Z)
    (jointPosterior : ι × κ → ℝ) (n : ℕ) (x : ℕ → Z) : ℝ :=
  trajectoryPredictableTiltPosteriorQuadraticPenalty
    (fun p : ι × κ ↦ score p.1)
    (fun p : ι × κ ↦ strategy p.2 p.1) jointPosterior n x

/-- Accumulated joint-posterior tilt on the monitored trajectory. -/
def trajectoryPredictableStrategyPosteriorTotalWeight
    (strategy : κ → ι → TrajectoryPredictableTilt Z)
    (jointPosterior : ι × κ → ℝ) (n : ℕ) (x : ℕ → Z) : ℝ :=
  trajectoryPredictableTiltPosteriorTotalWeight
    (fun p : ι × κ ↦ strategy p.2 p.1) jointPosterior n x

/-- Normalized joint model--strategy tilt-weighted conditional risk. -/
def trajectoryPredictableStrategyPosteriorNormalizedConditionalRisk
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    (score : ι → TrajectoryScore Z)
    (strategy : κ → ι → TrajectoryPredictableTilt Z)
    (jointPosterior : ι × κ → ℝ) (n : ℕ) (x : ℕ → Z) : ℝ :=
  trajectoryPredictableTiltPosteriorNormalizedConditionalRisk K
    (fun p : ι × κ ↦ score p.1)
    (fun p : ι × κ ↦ strategy p.2 p.1) jointPosterior n x

/-- Normalized joint model--strategy tilt-weighted empirical risk. -/
def trajectoryPredictableStrategyPosteriorNormalizedEmpiricalRisk
    (score : ι → TrajectoryScore Z)
    (strategy : κ → ι → TrajectoryPredictableTilt Z)
    (jointPosterior : ι × κ → ℝ) (n : ℕ) (x : ℕ → Z) : ℝ :=
  trajectoryPredictableTiltPosteriorNormalizedEmpiricalRisk
    (fun p : ι × κ ↦ score p.1)
    (fun p : ι × κ ↦ strategy p.2 p.1) jointPosterior n x

/-! ## Shared and constant-tilt catalogs for ordinary risk -/

/-- Turn a finite catalog of scalar tilts into trajectory strategies that are
fixed across models, times, and paths.  Different catalog entries may use
different constants. -/
def constantTrajectoryTiltCatalog
    (eta : κ → ℝ) : κ → ι → TrajectoryPredictableTilt Z :=
  fun j _i _n _u ↦ eta j

/-- Lift a catalog of trajectory strategies shared across models into the
joint model--strategy interface. -/
def sharedTrajectoryStrategyCatalog
    (strategy : κ → TrajectoryPredictableTilt Z) :
    κ → ι → TrajectoryPredictableTilt Z :=
  fun j _i ↦ strategy j

omit [DecidableEq κ] [Nonempty κ] in
private theorem posteriorAverage_pos_of_isPMF_of_pos
    {posterior : κ → ℝ} (hposterior : IsPMF posterior)
    {f : κ → ℝ} (hf : ∀ j, 0 < f j) :
    0 < posteriorAverage posterior f := by
  classical
  have hexists : ∃ j : κ, 0 < posterior j := by
    by_contra h
    push Not at h
    have hzero : ∀ j : κ, posterior j = 0 := by
      intro j
      exact le_antisymm (h j) (hposterior.nonneg j)
    have hsumzero : (∑ j : κ, posterior j) = 0 := by
      apply Finset.sum_eq_zero
      intro j _hj
      exact hzero j
    rw [hposterior.sum_one] at hsumzero
    norm_num at hsumzero
  rcases hexists with ⟨j, hj⟩
  have hterm : 0 < posterior j * f j := mul_pos hj (hf j)
  have hle : posterior j * f j ≤ ∑ k : κ, posterior k * f k := by
    apply Finset.single_le_sum
      (s := Finset.univ) (f := fun k : κ ↦ posterior k * f k)
    · intro k _hk
      exact mul_nonneg (hposterior.nonneg k) (hf k).le
    · exact Finset.mem_univ j
  exact hterm.trans_le hle

omit [DecidableEq ι] [Nonempty ι] in
private theorem posteriorAverage_runningMean_eq
    {Omega : Type*} (posterior : ι → ℝ)
    (Y : ι → ℕ → Omega → ℝ) (n : ℕ) (omega : Omega) :
    posteriorAverage posterior
        (fun i ↦ runningMean (Y i) n omega) =
      posteriorAverage posterior
          (fun i ↦ runningSum (Y i) n omega) / (n : ℝ) := by
  unfold posteriorAverage runningMean
  calc
    (∑ i : ι, posterior i * (runningSum (Y i) n omega / (n : ℝ))) =
        ∑ i : ι, (posterior i * runningSum (Y i) n omega) / (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = _ := by rw [Finset.sum_div]

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ] in
private theorem
    posteriorAverage_modelStrategyProductPrior_constantTiltWeightedSum
    {Omega : Type*}
    (modelPosterior : ι → ℝ) (strategyPosterior : κ → ℝ)
    (eta : κ → ℝ) (Y : ι → ℕ → Omega → ℝ)
    (n : ℕ) (omega : Omega) :
    posteriorAverage
        (modelStrategyProductPrior modelPosterior strategyPosterior)
        (fun p : ι × κ ↦
          ∑ k ∈ Finset.range n, eta p.2 * Y p.1 k omega) =
      posteriorAverage modelPosterior
          (fun i ↦ runningSum (Y i) n omega) *
        posteriorAverage strategyPosterior eta := by
  calc
    posteriorAverage
        (modelStrategyProductPrior modelPosterior strategyPosterior)
        (fun p : ι × κ ↦
          ∑ k ∈ Finset.range n, eta p.2 * Y p.1 k omega) =
      posteriorAverage
        (modelStrategyProductPrior modelPosterior strategyPosterior)
        (fun p : ι × κ ↦ runningSum (Y p.1) n omega * eta p.2) := by
      unfold posteriorAverage
      apply Finset.sum_congr rfl
      intro p _hp
      have hsum :
          (∑ k ∈ Finset.range n, eta p.2 * Y p.1 k omega) =
            runningSum (Y p.1) n omega * eta p.2 := by
        unfold runningSum
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _hk
        ring
      change modelStrategyProductPrior modelPosterior strategyPosterior p *
          (∑ k ∈ Finset.range n, eta p.2 * Y p.1 k omega) =
        modelStrategyProductPrior modelPosterior strategyPosterior p *
          (runningSum (Y p.1) n omega * eta p.2)
      rw [hsum]
    _ = _ := posteriorAverage_modelStrategyProductPrior_separable
      modelPosterior strategyPosterior
      (fun i ↦ runningSum (Y i) n omega) eta

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ] in
private theorem posteriorAverage_modelStrategyProductPrior_constantTiltSum
    (modelPosterior : ι → ℝ) (strategyPosterior : κ → ℝ)
    (hmodelPosterior : IsPMF modelPosterior) (eta : κ → ℝ)
    (n : ℕ) :
    posteriorAverage
        (modelStrategyProductPrior modelPosterior strategyPosterior)
        (fun p : ι × κ ↦ ∑ _k ∈ Finset.range n, eta p.2) =
      (n : ℝ) * posteriorAverage strategyPosterior eta := by
  calc
    posteriorAverage
        (modelStrategyProductPrior modelPosterior strategyPosterior)
        (fun p : ι × κ ↦ ∑ _k ∈ Finset.range n, eta p.2) =
      posteriorAverage
        (modelStrategyProductPrior modelPosterior strategyPosterior)
        (fun p : ι × κ ↦ (n : ℝ) * eta p.2) := by
      apply Finset.sum_congr rfl
      intro p _hp
      congr 1
      simp [nsmul_eq_mul]
    _ = posteriorAverage modelPosterior (fun _i ↦ (n : ℝ)) *
        posteriorAverage strategyPosterior eta :=
      posteriorAverage_modelStrategyProductPrior_separable
        modelPosterior strategyPosterior (fun _i ↦ (n : ℝ)) eta
    _ = (n : ℝ) * posteriorAverage strategyPosterior eta := by
      unfold posteriorAverage
      simp only
      calc
        (∑ i : ι, modelPosterior i * (n : ℝ)) *
            (∑ j : κ, strategyPosterior j * eta j) =
          ((∑ i : ι, modelPosterior i) * (n : ℝ)) *
            (∑ j : κ, strategyPosterior j * eta j) := by
              rw [← Finset.sum_mul]
        _ = _ := by rw [hmodelPosterior.sum_one]; ring

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ] in
private theorem
    forwardPredictableStrategyPosteriorNormalizedMean_constant_factorized
    {Omega : Type*}
    (modelPosterior : ι → ℝ) (strategyPosterior : κ → ℝ)
    (hmodelPosterior : IsPMF modelPosterior)
    (hstrategyPosterior : IsPMF strategyPosterior)
    (eta : κ → ℝ) (heta : ∀ j, 0 < eta j)
    (Y : ι → ℕ → Omega → ℝ)
    (n : ℕ) (hn : 0 < n) (omega : Omega) :
    forwardPredictableStrategyPosteriorNormalizedMean
        (modelStrategyProductPrior modelPosterior strategyPosterior) Y
        (fun j _i _k _omega ↦ eta j) n omega =
      posteriorAverage modelPosterior
        (fun i ↦ runningMean (Y i) n omega) := by
  have havgPos : 0 < posteriorAverage strategyPosterior eta :=
    posteriorAverage_pos_of_isPMF_of_pos hstrategyPosterior heta
  have hnum :=
    posteriorAverage_modelStrategyProductPrior_constantTiltWeightedSum
      modelPosterior strategyPosterior eta Y n omega
  have hden :=
    posteriorAverage_modelStrategyProductPrior_constantTiltSum
      modelPosterior strategyPosterior hmodelPosterior eta n
  have hrunning := posteriorAverage_runningMean_eq
    modelPosterior Y n omega
  unfold forwardPredictableStrategyPosteriorNormalizedMean
    forwardPredictableTiltPosteriorNormalizedMean
    forwardPredictableTiltPosteriorTotalWeight
    modelStrategyProcess modelStrategyPredictableTilt
  rw [hnum, hden, hrunning]
  field_simp [Nat.cast_ne_zero.mpr hn.ne', havgPos.ne']

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- A constant tilt catalog under a factorized model--strategy posterior has
total weight `n` times the strategy-posterior mean tilt. -/
theorem trajectoryPredictableStrategyPosteriorTotalWeight_constant_factorized
    (eta : κ → ℝ) (modelPosterior : ι → ℝ)
    (strategyPosterior : κ → ℝ)
    (hmodelPosterior : IsPMF modelPosterior)
    (n : ℕ) (x : ℕ → Z) :
    trajectoryPredictableStrategyPosteriorTotalWeight
        (constantTrajectoryTiltCatalog eta)
        (modelStrategyProductPrior modelPosterior strategyPosterior) n x =
      (n : ℝ) * posteriorAverage strategyPosterior eta := by
  unfold trajectoryPredictableStrategyPosteriorTotalWeight
    trajectoryPredictableTiltPosteriorTotalWeight
    forwardPredictableTiltPosteriorTotalWeight
    constantTrajectoryTiltCatalog observedTrajectoryPredictableTilt
  exact posteriorAverage_modelStrategyProductPrior_constantTiltSum
    modelPosterior strategyPosterior hmodelPosterior eta n

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ]
  [Fintype Z] [MeasurableSingletonClass Z] in
/-- For a factorized posterior and positive scalar-tilt catalog, the normalized
conditional quantity is the ordinary posterior-averaged conditional risk along
the monitored stream.  It is not future, stationary, or population risk. -/
theorem
    trajectoryPredictableStrategyPosteriorNormalizedConditionalRisk_constant_factorized
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    (score : ι → TrajectoryScore Z) (eta : κ → ℝ)
    (modelPosterior : ι → ℝ) (strategyPosterior : κ → ℝ)
    (hmodelPosterior : IsPMF modelPosterior)
    (hstrategyPosterior : IsPMF strategyPosterior)
    (heta : ∀ j, 0 < eta j) (n : ℕ) (hn : 0 < n) (x : ℕ → Z) :
    trajectoryPredictableStrategyPosteriorNormalizedConditionalRisk
        K score (constantTrajectoryTiltCatalog eta)
        (modelStrategyProductPrior modelPosterior strategyPosterior) n x =
      trajectoryPosteriorAverageConditionalRisk
        K score modelPosterior n x := by
  unfold trajectoryPredictableStrategyPosteriorNormalizedConditionalRisk
    trajectoryPredictableTiltPosteriorNormalizedConditionalRisk
    trajectoryPosteriorAverageConditionalRisk trajectoryAverageConditionalRisk
    constantTrajectoryTiltCatalog observedTrajectoryPredictableTilt
  exact forwardPredictableStrategyPosteriorNormalizedMean_constant_factorized
    modelPosterior strategyPosterior hmodelPosterior hstrategyPosterior
      eta heta (fun i ↦ conditionalTrajectoryRisk K (score i)) n hn x

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- For a factorized posterior and positive scalar-tilt catalog, the normalized
observed quantity is the ordinary posterior-averaged empirical prequential
risk along the monitored stream. -/
theorem
    trajectoryPredictableStrategyPosteriorNormalizedEmpiricalRisk_constant_factorized
    (score : ι → TrajectoryScore Z) (eta : κ → ℝ)
    (modelPosterior : ι → ℝ) (strategyPosterior : κ → ℝ)
    (hmodelPosterior : IsPMF modelPosterior)
    (hstrategyPosterior : IsPMF strategyPosterior)
    (heta : ∀ j, 0 < eta j) (n : ℕ) (hn : 0 < n) (x : ℕ → Z) :
    trajectoryPredictableStrategyPosteriorNormalizedEmpiricalRisk
        score (constantTrajectoryTiltCatalog eta)
        (modelStrategyProductPrior modelPosterior strategyPosterior) n x =
      trajectoryPosteriorEmpiricalPrequentialRisk
        score modelPosterior n x := by
  unfold trajectoryPredictableStrategyPosteriorNormalizedEmpiricalRisk
    trajectoryPredictableTiltPosteriorNormalizedEmpiricalRisk
    forwardPredictableTiltPosteriorNormalizedObservation
    trajectoryPosteriorEmpiricalPrequentialRisk
    trajectoryEmpiricalPrequentialRisk
    constantTrajectoryTiltCatalog observedTrajectoryPredictableTilt
  exact forwardPredictableStrategyPosteriorNormalizedMean_constant_factorized
    modelPosterior strategyPosterior hmodelPosterior hstrategyPosterior
      eta heta (fun i ↦ observedTrajectoryScore (score i)) n hn x

omit [DecidableEq ι] [DecidableEq κ] in
/-- One trajectory event supports path- and time-dependent joint selection in
the raw predictable-tilt inequality. -/
theorem exists_trajectoryPredictableStrategyPACBayes_selected_event
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (K n)] (x0 : Z)
    {score : ι → TrajectoryScore Z}
    (hscore : ∀ i n u y, score i n u y ∈ Set.Icc (0 : ℝ) 1)
    {strategy : κ → ι → TrajectoryPredictableTilt Z} {L : ℝ}
    (hL1 : L < 1)
    (hstrategy : ∀ j i n u,
      0 ≤ strategy j i n u ∧ strategy j i n u ≤ L)
    {modelPrior : ι → ℝ} (hmodelPrior : IsFullSupportPMF modelPrior)
    {strategyPrior : κ → ℝ}
    (hstrategyPrior : IsFullSupportPMF strategyPrior)
    {delta : ℝ} (hdelta : 0 < delta)
    (jointPosterior : (ℕ → Z) → ℕ → ι × κ → ℝ)
    (hposterior : ∀ x n, IsPMF (jointPosterior x n)) :
    ∃ goodEvent : Set (ℕ → Z),
      (trajectoryMeasure K x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ n : ℕ,
          trajectoryPredictableStrategyPosteriorMeanGap
              K score strategy (jointPosterior x n) n x <
            klDiv (jointPosterior x n)
                (modelStrategyProductPrior modelPrior strategyPrior) +
              Real.log (1 / delta) +
              trajectoryPredictableStrategyPosteriorQuadraticPenalty
                score strategy (jointPosterior x n) n x := by
  rcases exists_trajectoryPredictableTiltPACBayes_selected_event
      (ι := ι × κ) K x0
      (score := fun p : ι × κ ↦ score p.1)
      (fun p n u y ↦ hscore p.1 n u y)
      (tilt := fun p : ι × κ ↦ strategy p.2 p.1)
      hL1 (fun p n u ↦ hstrategy p.2 p.1 n u)
      (prior := modelStrategyProductPrior modelPrior strategyPrior)
      (modelStrategyProductPrior_isFullSupportPMF
        hmodelPrior hstrategyPrior)
      hdelta jointPosterior hposterior with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx n
  simpa only [trajectoryPredictableStrategyPosteriorMeanGap,
    trajectoryPredictableStrategyPosteriorQuadraticPenalty] using
      hgood x hx n

omit [DecidableEq ι] [DecidableEq κ] in
/-- One trajectory event supports path- and time-dependent selection of a
joint posterior on models and predeclared predictable strategies.  The
selection cost is the joint KL against the product prior. -/
theorem exists_trajectoryPredictableStrategyPACBayes_normalized_selected_event
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (K n)] (x0 : Z)
    {score : ι → TrajectoryScore Z}
    (hscore : ∀ i n u y, score i n u y ∈ Set.Icc (0 : ℝ) 1)
    {strategy : κ → ι → TrajectoryPredictableTilt Z} {L : ℝ}
    (hL1 : L < 1)
    (hstrategy : ∀ j i n u,
      0 ≤ strategy j i n u ∧ strategy j i n u ≤ L)
    {modelPrior : ι → ℝ} (hmodelPrior : IsFullSupportPMF modelPrior)
    {strategyPrior : κ → ℝ}
    (hstrategyPrior : IsFullSupportPMF strategyPrior)
    {delta : ℝ} (hdelta : 0 < delta)
    (jointPosterior : (ℕ → Z) → ℕ → ι × κ → ℝ)
    (hposterior : ∀ x n, IsPMF (jointPosterior x n)) :
    ∃ goodEvent : Set (ℕ → Z),
      (trajectoryMeasure K x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ n : ℕ,
          0 < trajectoryPredictableStrategyPosteriorTotalWeight
                strategy (jointPosterior x n) n x →
            trajectoryPredictableStrategyPosteriorNormalizedConditionalRisk
                K score strategy (jointPosterior x n) n x <
              trajectoryPredictableStrategyPosteriorNormalizedEmpiricalRisk
                  score strategy (jointPosterior x n) n x +
                (klDiv (jointPosterior x n)
                      (modelStrategyProductPrior modelPrior strategyPrior) +
                    Real.log (1 / delta) +
                    trajectoryPredictableStrategyPosteriorQuadraticPenalty
                      score strategy (jointPosterior x n) n x) /
                  trajectoryPredictableStrategyPosteriorTotalWeight
                    strategy (jointPosterior x n) n x := by
  rcases exists_trajectoryPredictableTiltPACBayes_normalized_selected_event
      (ι := ι × κ) K x0
      (score := fun p : ι × κ ↦ score p.1)
      (fun p n u y ↦ hscore p.1 n u y)
      (tilt := fun p : ι × κ ↦ strategy p.2 p.1)
      hL1 (fun p n u ↦ hstrategy p.2 p.1 n u)
      (prior := modelStrategyProductPrior modelPrior strategyPrior)
      (modelStrategyProductPrior_isFullSupportPMF
        hmodelPrior hstrategyPrior)
      hdelta jointPosterior hposterior with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx n hweight
  simpa only [trajectoryPredictableStrategyPosteriorTotalWeight,
    trajectoryPredictableStrategyPosteriorNormalizedConditionalRisk,
    trajectoryPredictableStrategyPosteriorNormalizedEmpiricalRisk,
    trajectoryPredictableStrategyPosteriorQuadraticPenalty] using
      hgood x hx n hweight

omit [DecidableEq ι] [DecidableEq κ] in
/-- One trajectory event controls ordinary posterior-averaged risk for every
time, model posterior, and strategy posterior when each model's one-step
conditional trajectory risk is the constant `risk i`.  The finite catalog of
prefix-predictable strategies is shared across models, so its weights cancel
from the normalized conditional mean under a factorized reporting posterior.
Model and strategy selection pay separate KL terms.

The conclusion concerns exactly the supplied constant conditional trajectory
risk.  It is not a stationary, future, population, or deployment-risk theorem
without a separate bridge proving that interpretation. -/
theorem
    exists_trajectoryPredictableStrategyPACBayes_shared_constantConditionalRisk_factorized_ordinaryRisk_event
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (K n)] (x0 : Z)
    {score : ι → TrajectoryScore Z}
    (hscore : ∀ i n u y, score i n u y ∈ Set.Icc (0 : ℝ) 1)
    {strategy : κ → TrajectoryPredictableTilt Z} {L : ℝ}
    (hL1 : L < 1)
    (hstrategy : ∀ j n u,
      0 ≤ strategy j n u ∧ strategy j n u ≤ L)
    {risk : ι → ℝ}
    (hconstantRisk : ∀ i n x,
      conditionalTrajectoryRisk K (score i) n x = risk i)
    {modelPrior : ι → ℝ} (hmodelPrior : IsFullSupportPMF modelPrior)
    {strategyPrior : κ → ℝ}
    (hstrategyPrior : IsFullSupportPMF strategyPrior)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ goodEvent : Set (ℕ → Z),
      (trajectoryMeasure K x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent,
          ∀ modelPosterior : ι → ℝ, IsPMF modelPosterior →
            ∀ strategyPosterior : κ → ℝ, IsPMF strategyPosterior →
              ∀ n : ℕ,
                0 < trajectoryPredictableStrategyPosteriorTotalWeight
                      (sharedTrajectoryStrategyCatalog strategy)
                      (modelStrategyProductPrior
                        modelPosterior strategyPosterior) n x →
                  posteriorAverage modelPosterior risk <
                    trajectoryPredictableStrategyPosteriorNormalizedEmpiricalRisk
                        score (sharedTrajectoryStrategyCatalog strategy)
                        (modelStrategyProductPrior
                          modelPosterior strategyPosterior) n x +
                      ((klDiv modelPosterior modelPrior +
                            klDiv strategyPosterior strategyPrior) +
                          Real.log (1 / delta) +
                          trajectoryPredictableStrategyPosteriorQuadraticPenalty
                            score (sharedTrajectoryStrategyCatalog strategy)
                            (modelStrategyProductPrior
                              modelPosterior strategyPosterior) n x) /
                        trajectoryPredictableStrategyPosteriorTotalWeight
                          (sharedTrajectoryStrategyCatalog strategy)
                          (modelStrategyProductPrior
                            modelPosterior strategyPosterior) n x := by
  rcases
      exists_forwardPredictableStrategyPACBayes_shared_constantMean_factorized_ordinaryRisk_event
        (μ := trajectoryMeasure K x0)
        (ℱ := Filtration.piLE (X := fun _ : ℕ ↦ Z))
        hmodelPrior hstrategyPrior hL1 hdelta
        (X := fun i ↦ observedTrajectoryScore (score i))
        (lambda := fun j ↦ observedTrajectoryPredictableTilt (strategy j))
        (risk := risk)
        (fun i ↦ observedTrajectoryScore_incrementAdapted (score i))
        (fun j ↦ observedTrajectoryPredictableTilt_stronglyAdapted
          (strategy j))
        (fun i k x ↦ observedTrajectoryScore_mem_Icc (hscore i) k x)
        (fun j k x ↦ hstrategy j k (Preorder.frestrictLe k x))
        (fun i k ↦ by
          filter_upwards [observedTrajectoryScore_condExp
            K x0 (score i) (hscore i) k] with x hx
          simpa only [hconstantRisk i k x] using hx) with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx modelPosterior hmodelPosterior
    strategyPosterior hstrategyPosterior n hweight
  exact hgood x hx modelPosterior hmodelPosterior
    strategyPosterior hstrategyPosterior n hweight

omit [DecidableEq ι] [DecidableEq κ] in
/-- One trajectory event supports ordinary monitored-risk reporting after
selecting both a model posterior and a soft posterior over finitely many
constant-tilt strategies.  Both posteriors may depend on the observed path and
reporting time.  The strategy-selection cost is the separate term
`klDiv strategyPosterior strategyPrior`.

The target is the posterior-averaged conditional loss encountered along the
monitored stream.  It is not future, stationary, or population risk. -/
theorem
    exists_trajectoryPredictableStrategyPACBayes_constant_factorized_ordinaryRisk_selected_event
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (K n)] (x0 : Z)
    {score : ι → TrajectoryScore Z}
    (hscore : ∀ i n u y, score i n u y ∈ Set.Icc (0 : ℝ) 1)
    {eta : κ → ℝ} {L : ℝ}
    (hetaPos : ∀ j, 0 < eta j) (hetaUpper : ∀ j, eta j ≤ L)
    (hL1 : L < 1)
    {modelPrior : ι → ℝ} (hmodelPrior : IsFullSupportPMF modelPrior)
    {strategyPrior : κ → ℝ}
    (hstrategyPrior : IsFullSupportPMF strategyPrior)
    {delta : ℝ} (hdelta : 0 < delta)
    (modelPosterior : (ℕ → Z) → ℕ → ι → ℝ)
    (hmodelPosterior : ∀ x n, IsPMF (modelPosterior x n))
    (strategyPosterior : (ℕ → Z) → ℕ → κ → ℝ)
    (hstrategyPosterior : ∀ x n, IsPMF (strategyPosterior x n)) :
    ∃ goodEvent : Set (ℕ → Z),
      (trajectoryMeasure K x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ n : ℕ, 0 < n →
          trajectoryPosteriorAverageConditionalRisk
              K score (modelPosterior x n) n x <
            trajectoryPosteriorEmpiricalPrequentialRisk
                score (modelPosterior x n) n x +
              ((klDiv (modelPosterior x n) modelPrior +
                    klDiv (strategyPosterior x n) strategyPrior) +
                  Real.log (1 / delta) +
                  trajectoryPredictableStrategyPosteriorQuadraticPenalty
                    score (constantTrajectoryTiltCatalog eta)
                    (modelStrategyProductPrior
                      (modelPosterior x n) (strategyPosterior x n)) n x) /
                ((n : ℝ) * posteriorAverage (strategyPosterior x n) eta) := by
  let jointPosterior : (ℕ → Z) → ℕ → ι × κ → ℝ := fun x n ↦
    modelStrategyProductPrior (modelPosterior x n) (strategyPosterior x n)
  have hjointPosterior : ∀ x n, IsPMF (jointPosterior x n) := by
    intro x n
    exact modelStrategyProductPrior_isPMF
      (hmodelPosterior x n) (hstrategyPosterior x n)
  rcases exists_trajectoryPredictableStrategyPACBayes_normalized_selected_event
      K x0 hscore (strategy := constantTrajectoryTiltCatalog eta) hL1
      (fun j _i _n _u ↦ ⟨(hetaPos j).le, hetaUpper j⟩)
      hmodelPrior hstrategyPrior hdelta jointPosterior hjointPosterior with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx n hn
  have havgPos : 0 < posteriorAverage (strategyPosterior x n) eta :=
    posteriorAverage_pos_of_isPMF_of_pos
      (hstrategyPosterior x n) hetaPos
  have hweight :=
    trajectoryPredictableStrategyPosteriorTotalWeight_constant_factorized
      eta (modelPosterior x n) (strategyPosterior x n)
      (hmodelPosterior x n) n x
  have hweightPos : 0 <
      trajectoryPredictableStrategyPosteriorTotalWeight
        (constantTrajectoryTiltCatalog eta) (jointPosterior x n) n x := by
    rw [show jointPosterior x n = modelStrategyProductPrior
        (modelPosterior x n) (strategyPosterior x n) by rfl, hweight]
    exact mul_pos (Nat.cast_pos.mpr hn) havgPos
  have hbound := hgood x hx n hweightPos
  rw [show jointPosterior x n = modelStrategyProductPrior
      (modelPosterior x n) (strategyPosterior x n) by rfl] at hbound
  rw [
    trajectoryPredictableStrategyPosteriorNormalizedConditionalRisk_constant_factorized
      K score eta (modelPosterior x n) (strategyPosterior x n)
      (hmodelPosterior x n) (hstrategyPosterior x n) hetaPos n hn x,
    trajectoryPredictableStrategyPosteriorNormalizedEmpiricalRisk_constant_factorized
      score eta (modelPosterior x n) (strategyPosterior x n)
      (hmodelPosterior x n) (hstrategyPosterior x n) hetaPos n hn x,
    hweight,
    klDiv_modelStrategyProductPrior
      (hmodelPosterior x n) hmodelPrior
      (hstrategyPosterior x n) hstrategyPrior] at hbound
  exact hbound

end

end FormalSLT.StochasticDynamics
