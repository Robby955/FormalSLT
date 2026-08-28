/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.TrajectoryPredictableStrategyPACBayes

/-!
# Sleeping strategy posteriors for trajectory PAC-Bayes bounds

This module turns a finite catalog of predictable trajectory strategies into
a finite catalog of sleeping strategies.  Catalog atom `a` has its own
predeclared wake time `wake a`; its tilt is zero before that time and follows
`strategy a` afterwards.

The resulting theorem uses the existing single model--strategy product-prior
master.  Thus a path-selected soft posterior over the finite strategy catalog
pays the explicit term `klDiv strategyPosterior strategyPrior`.  This is not
the countable confidence allocation used by the geometric-tilt oracle.

The endpoint is the normalized tilt-weighted conditional risk encountered on
the monitored trajectory.  A soft posterior may mix atoms with different wake
times, so it must not be described as one ordinary suffix average.  A separate
ordinary-risk bridge can compare this weighted endpoint with an unweighted
suffix.  The finite catalog remains fixed before observation; this module is
not coin betting or unrestricted post-hoc strategy invention.
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

/-- Put each declared trajectory strategy to sleep until its predeclared wake
time.  The strategy catalog is shared across models. -/
def sleepingTrajectoryStrategyCatalog
    (wake : κ -> Nat) (strategy : κ -> TrajectoryPredictableTilt Z) :
    κ -> ι -> TrajectoryPredictableTilt Z :=
  fun a _i n u => if wake a <= n then strategy a n u else 0

omit [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
@[simp]
theorem sleepingTrajectoryStrategyCatalog_apply_of_lt
    (wake : κ -> Nat) (strategy : κ -> TrajectoryPredictableTilt Z)
    (a : κ) (i : ι) {n : Nat} (hn : n < wake a)
    (u : (j : Finset.Iic n) -> Z) :
    sleepingTrajectoryStrategyCatalog wake strategy a i n u = 0 := by
  simp [sleepingTrajectoryStrategyCatalog, not_le.mpr hn]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
@[simp]
theorem sleepingTrajectoryStrategyCatalog_apply_of_le
    (wake : κ -> Nat) (strategy : κ -> TrajectoryPredictableTilt Z)
    (a : κ) (i : ι) {n : Nat} (hn : wake a <= n)
    (u : (j : Finset.Iic n) -> Z) :
    sleepingTrajectoryStrategyCatalog wake strategy a i n u =
      strategy a n u := by
  simp [sleepingTrajectoryStrategyCatalog, hn]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- Bounds on each awake strategy imply the same bounds for the sleeping
catalog, provided zero is also admitted by the common range. -/
theorem sleepingTrajectoryStrategyCatalog_mem_Icc
    {wake : κ -> Nat} {strategy : κ -> TrajectoryPredictableTilt Z}
    {L : Real} (hL0 : 0 <= L)
    (hstrategy : forall a n u,
      strategy a n u ∈ Set.Icc (0 : Real) L) :
    forall (a : κ) (i : ι) n u,
      sleepingTrajectoryStrategyCatalog wake strategy a i n u ∈
        Set.Icc (0 : Real) L := by
  intro a i n u
  by_cases h : wake a <= n
  · simpa [sleepingTrajectoryStrategyCatalog, h] using hstrategy a n u
  · simp [sleepingTrajectoryStrategyCatalog, h, hL0]

omit [DecidableEq ι] [DecidableEq κ] in
/-- A single finite model--strategy master controls path- and time-selected
model and sleeping-strategy posteriors.  Model and strategy selection pay
separate KL terms against their predeclared priors.

The posterior factors are reporting rules on the common event.  They need not
be predictable, while every member of `strategy` itself must be predictable
because it is evaluated only from the prefix supplied to
`TrajectoryPredictableTilt`. -/
theorem
    exists_trajectorySleepingStrategyPACBayes_factorized_normalized_selected_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    {score : ι -> TrajectoryScore Z}
    (hscore : forall i n u y, score i n u y ∈ Set.Icc (0 : Real) 1)
    {wake : κ -> Nat} {strategy : κ -> TrajectoryPredictableTilt Z}
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
        forall x, x ∈ goodEvent -> forall n : Nat,
          0 < trajectoryPredictableStrategyPosteriorTotalWeight
                (sleepingTrajectoryStrategyCatalog wake strategy)
                (modelStrategyProductPrior
                  (modelPosterior x n) (strategyPosterior x n)) n x ->
            trajectoryPredictableStrategyPosteriorNormalizedConditionalRisk
                K score (sleepingTrajectoryStrategyCatalog wake strategy)
                (modelStrategyProductPrior
                  (modelPosterior x n) (strategyPosterior x n)) n x <
              trajectoryPredictableStrategyPosteriorNormalizedEmpiricalRisk
                  score (sleepingTrajectoryStrategyCatalog wake strategy)
                  (modelStrategyProductPrior
                    (modelPosterior x n) (strategyPosterior x n)) n x +
                ((klDiv (modelPosterior x n) modelPrior +
                      klDiv (strategyPosterior x n) strategyPrior) +
                    Real.log (1 / delta) +
                    trajectoryPredictableStrategyPosteriorQuadraticPenalty
                      score (sleepingTrajectoryStrategyCatalog wake strategy)
                      (modelStrategyProductPrior
                        (modelPosterior x n) (strategyPosterior x n)) n x) /
                  trajectoryPredictableStrategyPosteriorTotalWeight
                    (sleepingTrajectoryStrategyCatalog wake strategy)
                    (modelStrategyProductPrior
                      (modelPosterior x n) (strategyPosterior x n)) n x := by
  let jointPosterior : (Nat -> Z) -> Nat -> ι × κ -> Real := fun x n =>
    modelStrategyProductPrior (modelPosterior x n) (strategyPosterior x n)
  have hjointPosterior : forall x n, IsPMF (jointPosterior x n) := by
    intro x n
    exact modelStrategyProductPrior_isPMF
      (hmodelPosterior x n) (hstrategyPosterior x n)
  have hsleep : forall (a : κ) (i : ι) n u,
      sleepingTrajectoryStrategyCatalog wake strategy a i n u ∈
        Set.Icc (0 : Real) L :=
    sleepingTrajectoryStrategyCatalog_mem_Icc (ι := ι) hL0 hstrategy
  rcases exists_trajectoryPredictableStrategyPACBayes_normalized_selected_event
      K x0 hscore (strategy := sleepingTrajectoryStrategyCatalog wake strategy)
      hL1 hsleep hmodelPrior hstrategyPrior hdelta
      jointPosterior hjointPosterior with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx n hweight
  have hbound := hgood x hx n hweight
  rw [show jointPosterior x n = modelStrategyProductPrior
      (modelPosterior x n) (strategyPosterior x n) by rfl] at hbound
  rw [klDiv_modelStrategyProductPrior
      (hmodelPosterior x n) hmodelPrior
      (hstrategyPosterior x n) hstrategyPrior] at hbound
  exact hbound

end

end FormalSLT.StochasticDynamics
