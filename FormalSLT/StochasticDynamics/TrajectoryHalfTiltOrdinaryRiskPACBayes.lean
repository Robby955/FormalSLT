/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.TrajectoryPredictableStrategyPACBayes

/-!
# Compact half-tilt trajectory PAC-Bayes certificate

This module specializes the finite model--strategy trajectory theorem to one
predeclared constant strategy, `lambda = 1 / 2`.  The singleton strategy has
zero selection cost.  Its constant positive weight cancels from the normalized
mean, leaving the ordinary posterior-averaged conditional and empirical risks
encountered along the monitored prefix.

The observable penalty is the posterior average of the forward-predictor
quadratic variation.  This is the theorem profile used by compact tabular
Brier certificates: raw rows may be replayed outside Lean while the kernel
checks the statistical theorem and the exact summary arithmetic.

The result is simultaneous over reporting times and model posteriors, including
posteriors selected from the observed path.  It does not permit post-hoc tilt
selection and does not identify encountered conditional risk with future,
stationary, population, or deployment risk.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardPredictableTiltPACBayes
open FormalSLT.PACBayes.ForwardPredictableStrategyPACBayes
open scoped BigOperators

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {ι Z : Type*}
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- The only strategy in the compact certificate profile. -/
def trajectoryHalfTilt (_model : ι) : TrajectoryPredictableTilt Z :=
  fun _n _prefix => 1 / 2

/-- Posterior-averaged observable forward-predictor quadratic variation. -/
def trajectoryPosteriorForwardPredictorQuadraticVariation
    (score : ι → TrajectoryScore Z) (posterior : ι → ℝ)
    (n : ℕ) (x : ℕ → Z) : ℝ :=
  posteriorAverage posterior fun i ↦
    ∑ k ∈ Finset.range n,
      (observedTrajectoryScore (score i) k x -
          forwardPredictorProcess (observedTrajectoryScore (score i)) k x) ^ 2

/-- The singleton strategy prior and posterior used by the compact profile. -/
def trajectorySingletonStrategyPMF (_strategy : Unit) : ℝ := 1

theorem trajectorySingletonStrategyPMF_isFullSupportPMF :
    IsFullSupportPMF trajectorySingletonStrategyPMF := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro strategy
    simp [trajectorySingletonStrategyPMF]
  · simp [trajectorySingletonStrategyPMF]
  · intro strategy
    simp [trajectorySingletonStrategyPMF]

theorem trajectorySingletonStrategyPMF_kl_self :
    klDiv trajectorySingletonStrategyPMF trajectorySingletonStrategyPMF = 0 := by
  simp [klDiv, trajectorySingletonStrategyPMF]

omit [DecidableEq ι] [Nonempty ι]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
theorem trajectorySingletonStrategyPMF_half_average :
    posteriorAverage trajectorySingletonStrategyPMF
      (fun _strategy : Unit ↦ (1 / 2 : ℝ)) = 1 / 2 := by
  simp [posteriorAverage, trajectorySingletonStrategyPMF]

omit [DecidableEq ι] [Nonempty ι]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The singleton half-tilt joint penalty is exactly `psi(1/2)` times the
model-posterior forward-predictor quadratic variation. -/
theorem trajectoryHalfTilt_quadraticPenalty_eq
    (score : ι → TrajectoryScore Z) (posterior : ι → ℝ)
    (n : ℕ) (x : ℕ → Z) :
    trajectoryPredictableStrategyPosteriorQuadraticPenalty score
        (constantTrajectoryTiltCatalog (fun _strategy : Unit ↦ (1 / 2 : ℝ)))
        (modelStrategyProductPrior posterior trajectorySingletonStrategyPMF)
        n x =
      forwardEmpiricalBernsteinPsi (1 / 2 : ℝ) *
        trajectoryPosteriorForwardPredictorQuadraticVariation
          score posterior n x := by
  unfold trajectoryPredictableStrategyPosteriorQuadraticPenalty
    trajectoryPredictableTiltPosteriorQuadraticPenalty
    forwardPredictableTiltPosteriorQuadraticPenalty
    trajectoryPosteriorForwardPredictorQuadraticVariation
    posteriorAverage modelStrategyProductPrior
    constantTrajectoryTiltCatalog observedTrajectoryPredictableTilt
    trajectorySingletonStrategyPMF
  simp only [Fintype.sum_prod_type]
  simp [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro k _hk
  ring

omit [DecidableEq ι] in
/-- One event controls the ordinary posterior-averaged conditional risk at
every positive reporting time for every path-selected model posterior.  The
only inference strategy is the predeclared constant half tilt, so there is no
strategy-selection KL term. -/
theorem exists_trajectoryHalfTiltPACBayes_ordinaryRisk_selected_event
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (K n)] (x0 : Z)
    {score : ι → TrajectoryScore Z}
    (hscore : ∀ i n u y, score i n u y ∈ Set.Icc (0 : ℝ) 1)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {delta : ℝ} (hdelta : 0 < delta)
    (posterior : (ℕ → Z) → ℕ → ι → ℝ)
    (hposterior : ∀ x n, IsPMF (posterior x n)) :
    ∃ goodEvent : Set (ℕ → Z),
      (trajectoryMeasure K x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ n : ℕ, 0 < n →
          trajectoryPosteriorAverageConditionalRisk
              K score (posterior x n) n x <
            trajectoryPosteriorEmpiricalPrequentialRisk
                score (posterior x n) n x +
              (klDiv (posterior x n) prior + Real.log (1 / delta) +
                  forwardEmpiricalBernsteinPsi (1 / 2 : ℝ) *
                    trajectoryPosteriorForwardPredictorQuadraticVariation
                      score (posterior x n) n x) /
                ((1 / 2 : ℝ) * n) := by
  let strategyPosterior : (ℕ → Z) → ℕ → Unit → ℝ :=
    fun _x _n ↦ trajectorySingletonStrategyPMF
  have hstrategyPosterior : ∀ x n, IsPMF (strategyPosterior x n) := by
    intro x n
    exact trajectorySingletonStrategyPMF_isFullSupportPMF.toIsPMF
  rcases
      exists_trajectoryPredictableStrategyPACBayes_constant_factorized_ordinaryRisk_selected_event
        (κ := Unit) K x0 hscore
        (eta := fun _strategy : Unit ↦ (1 / 2 : ℝ))
        (L := (1 / 2 : ℝ)) (fun _strategy ↦ by norm_num)
        (fun _strategy ↦ by norm_num) (by norm_num)
        hprior trajectorySingletonStrategyPMF_isFullSupportPMF hdelta
        posterior hposterior strategyPosterior hstrategyPosterior with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx n hn
  have hbound := hgood x hx n hn
  rw [show strategyPosterior x n = trajectorySingletonStrategyPMF by rfl,
    trajectorySingletonStrategyPMF_kl_self,
    trajectorySingletonStrategyPMF_half_average,
    trajectoryHalfTilt_quadraticPenalty_eq] at hbound
  simpa [mul_comm] using hbound

end

end FormalSLT.StochasticDynamics
