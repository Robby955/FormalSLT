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

The theorem does not permit a strategy to inspect the next state before its
tilt is chosen.  Its risk quantities are normalized tilt-weighted prequential
averages under the trajectory law with deterministic initial state `x0`, not
stationary or ordinary unweighted risks.  Only the predeclared catalog members
are predictable; the post-hoc reporting posterior is not a composite
predictable e-process.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.PACBayesKL
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

end

end FormalSLT.StochasticDynamics
