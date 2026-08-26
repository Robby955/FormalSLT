/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.ForwardPredictableTiltPACBayes
import FormalSLT.StochasticDynamics.TrajectoryEmpiricalBernsteinPACBayes

/-!
# Predictable-tilt PAC-Bayes bounds for full-prefix trajectories

This module specializes the finite-hypothesis predictable-tilt PAC-Bayes
theorem to arbitrary prefix-dependent finite-state trajectory kernels.  A tilt
rule may inspect the complete prefix available before the next state is drawn.
The rule is fixed before the path is observed; on one outer-mass event, the
posterior may be selected after observing the path and time.

The core conclusion controls a tilt-weighted conditional-risk minus
observed-score sum.  A derived endpoint normalizes this by positive accumulated
tilt; hypothesis-dependent tilts induce corresponding effective model--time
weights.  It is not an ordinary unweighted average-risk bound and does not
construct an e-process from a post-hoc selected tilt schedule.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardPredictableTiltPACBayes
open scoped BigOperators

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {ι Z : Type*}
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- A predictable trajectory tilt reads exactly the prefix available before
the transition at time `n`. -/
abbrev TrajectoryPredictableTilt (Z : Type*) :=
  (n : ℕ) → ((i : Finset.Iic n) → Z) → ℝ

/-- Evaluation of a prefix-only tilt rule along a complete path. -/
def observedTrajectoryPredictableTilt
    (tilt : TrajectoryPredictableTilt Z) (n : ℕ) (x : ℕ → Z) : ℝ :=
  tilt n (Preorder.frestrictLe n x)

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- A prefix-only tilt rule is predictable for the canonical path filtration. -/
theorem observedTrajectoryPredictableTilt_stronglyAdapted
    (tilt : TrajectoryPredictableTilt Z) :
    StronglyAdapted (Filtration.piLE (X := fun _ : ℕ ↦ Z))
      (observedTrajectoryPredictableTilt tilt) := by
  intro n
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact (measurable_of_countable (tilt n)).stronglyMeasurable.comp_measurable
    (comap_measurable _)

/-- Posterior average of the prefix-predictable weighted conditional-risk
minus observed-score sums. -/
def trajectoryPredictableTiltPosteriorMeanGap
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    (score : ι → TrajectoryScore Z)
    (tilt : ι → TrajectoryPredictableTilt Z)
    (posterior : ι → ℝ) (n : ℕ) (x : ℕ → Z) : ℝ :=
  forwardPredictableTiltPosteriorMeanGap posterior
    (fun i ↦ observedTrajectoryScore (score i))
    (fun i ↦ conditionalTrajectoryRisk K (score i))
    (fun i ↦ observedTrajectoryPredictableTilt (tilt i)) n x

/-- Posterior average of the observed predictable quadratic penalties along
the trajectory. -/
def trajectoryPredictableTiltPosteriorQuadraticPenalty
    (score : ι → TrajectoryScore Z)
    (tilt : ι → TrajectoryPredictableTilt Z)
    (posterior : ι → ℝ) (n : ℕ) (x : ℕ → Z) : ℝ :=
  forwardPredictableTiltPosteriorQuadraticPenalty posterior
    (fun i ↦ observedTrajectoryScore (score i))
    (fun i ↦ observedTrajectoryPredictableTilt (tilt i)) n x

/-- Total posterior-averaged predictable tilt accumulated along a trajectory. -/
def trajectoryPredictableTiltPosteriorTotalWeight
    (tilt : ι → TrajectoryPredictableTilt Z)
    (posterior : ι → ℝ) (n : ℕ) (x : ℕ → Z) : ℝ :=
  forwardPredictableTiltPosteriorTotalWeight posterior
    (fun i ↦ observedTrajectoryPredictableTilt (tilt i)) n x

/-- Normalized posterior tilt-weighted conditional risk along the monitored
trajectory.  Under a PMF posterior, nonnegative tilts, and positive total
weight, its effective model--time weights are proportional to
`posterior i * tilt i k`; hypothesis-dependent tilts therefore reweight the
original posterior. -/
def trajectoryPredictableTiltPosteriorNormalizedConditionalRisk
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    (score : ι → TrajectoryScore Z)
    (tilt : ι → TrajectoryPredictableTilt Z)
    (posterior : ι → ℝ) (n : ℕ) (x : ℕ → Z) : ℝ :=
  forwardPredictableTiltPosteriorNormalizedMean posterior
    (fun i ↦ conditionalTrajectoryRisk K (score i))
    (fun i ↦ observedTrajectoryPredictableTilt (tilt i)) n x

/-- Normalized posterior tilt-weighted observed prequential risk, with the same
effective model--time weights as the conditional-risk quantity above. -/
def trajectoryPredictableTiltPosteriorNormalizedEmpiricalRisk
    (score : ι → TrajectoryScore Z)
    (tilt : ι → TrajectoryPredictableTilt Z)
    (posterior : ι → ℝ) (n : ℕ) (x : ℕ → Z) : ℝ :=
  forwardPredictableTiltPosteriorNormalizedObservation posterior
    (fun i ↦ observedTrajectoryScore (score i))
    (fun i ↦ observedTrajectoryPredictableTilt (tilt i)) n x

omit [DecidableEq ι] in
/-- One outer-mass event controls every time and every posterior for a fixed
finite catalog of scores and prefix-predictable tilt rules. -/
theorem exists_trajectoryPredictableTiltPACBayes_event
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (K n)] (x0 : Z)
    {score : ι → TrajectoryScore Z}
    (hscore : ∀ i n u y, score i n u y ∈ Set.Icc (0 : ℝ) 1)
    {tilt : ι → TrajectoryPredictableTilt Z} {L : ℝ}
    (hL1 : L < 1)
    (htilt : ∀ i n u, 0 ≤ tilt i n u ∧ tilt i n u ≤ L)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ goodEvent : Set (ℕ → Z),
      (trajectoryMeasure K x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ posterior : ι → ℝ, IsPMF posterior →
          ∀ n : ℕ,
            trajectoryPredictableTiltPosteriorMeanGap
                K score tilt posterior n x <
              klDiv posterior prior + Real.log (1 / delta) +
                trajectoryPredictableTiltPosteriorQuadraticPenalty
                  score tilt posterior n x := by
  rcases exists_forwardPredictableTiltPACBayes_event
      (μ := trajectoryMeasure K x0)
      (ℱ := Filtration.piLE (X := fun _ : ℕ ↦ Z))
      (prior := prior) hprior
      (X := fun i ↦ observedTrajectoryScore (score i))
      (mean := fun i ↦ conditionalTrajectoryRisk K (score i))
      (lambda := fun i ↦ observedTrajectoryPredictableTilt (tilt i))
      (L := L) (delta := delta) hL1 hdelta
      (fun i ↦ observedTrajectoryScore_incrementAdapted (score i))
      (fun i ↦ conditionalTrajectoryRisk_stronglyAdapted K (score i))
      (fun i ↦ observedTrajectoryPredictableTilt_stronglyAdapted (tilt i))
      (fun i k x ↦ observedTrajectoryScore_mem_Icc (hscore i) k x)
      (fun i k x ↦ htilt i k (Preorder.frestrictLe k x))
      (fun i k ↦ observedTrajectoryScore_condExp K x0 (score i) (hscore i) k)
    with ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx posterior hposterior n
  simpa only [trajectoryPredictableTiltPosteriorMeanGap,
    trajectoryPredictableTiltPosteriorQuadraticPenalty] using
      hgood x hx posterior hposterior n

omit [DecidableEq ι] in
/-- The common trajectory event permits a path- and time-dependent posterior.
The prefix-predictable tilt rules remain the fixed rules supplied above. -/
theorem exists_trajectoryPredictableTiltPACBayes_selected_event
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (K n)] (x0 : Z)
    {score : ι → TrajectoryScore Z}
    (hscore : ∀ i n u y, score i n u y ∈ Set.Icc (0 : ℝ) 1)
    {tilt : ι → TrajectoryPredictableTilt Z} {L : ℝ}
    (hL1 : L < 1)
    (htilt : ∀ i n u, 0 ≤ tilt i n u ∧ tilt i n u ≤ L)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {delta : ℝ} (hdelta : 0 < delta)
    (posterior : (ℕ → Z) → ℕ → ι → ℝ)
    (hposterior : ∀ x n, IsPMF (posterior x n)) :
    ∃ goodEvent : Set (ℕ → Z),
      (trajectoryMeasure K x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ n : ℕ,
          trajectoryPredictableTiltPosteriorMeanGap
              K score tilt (posterior x n) n x <
            klDiv (posterior x n) prior + Real.log (1 / delta) +
              trajectoryPredictableTiltPosteriorQuadraticPenalty
                score tilt (posterior x n) n x := by
  rcases exists_trajectoryPredictableTiltPACBayes_event
      K x0 hscore hL1 htilt hprior hdelta with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx n
  exact hgood x hx (posterior x n) (hposterior x n) n

omit [DecidableEq ι] in
/-- One outer-mass event controls normalized tilt-weighted conditional risk at
every time and posterior with positive accumulated tilt.  The result remains a
tilt-weighted monitored-trajectory guarantee, not an ordinary unweighted or
stationary-risk statement. -/
theorem exists_trajectoryPredictableTiltPACBayes_normalized_event
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (K n)] (x0 : Z)
    {score : ι → TrajectoryScore Z}
    (hscore : ∀ i n u y, score i n u y ∈ Set.Icc (0 : ℝ) 1)
    {tilt : ι → TrajectoryPredictableTilt Z} {L : ℝ}
    (hL1 : L < 1)
    (htilt : ∀ i n u, 0 ≤ tilt i n u ∧ tilt i n u ≤ L)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ goodEvent : Set (ℕ → Z),
      (trajectoryMeasure K x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ posterior : ι → ℝ, IsPMF posterior →
          ∀ n : ℕ,
            0 < trajectoryPredictableTiltPosteriorTotalWeight
                tilt posterior n x →
              trajectoryPredictableTiltPosteriorNormalizedConditionalRisk
                  K score tilt posterior n x <
                trajectoryPredictableTiltPosteriorNormalizedEmpiricalRisk
                    score tilt posterior n x +
                  (klDiv posterior prior + Real.log (1 / delta) +
                      trajectoryPredictableTiltPosteriorQuadraticPenalty
                        score tilt posterior n x) /
                    trajectoryPredictableTiltPosteriorTotalWeight
                      tilt posterior n x := by
  rcases exists_forwardPredictableTiltPACBayes_normalized_event
      (μ := trajectoryMeasure K x0)
      (ℱ := Filtration.piLE (X := fun _ : ℕ ↦ Z))
      (prior := prior) hprior
      (X := fun i ↦ observedTrajectoryScore (score i))
      (mean := fun i ↦ conditionalTrajectoryRisk K (score i))
      (lambda := fun i ↦ observedTrajectoryPredictableTilt (tilt i))
      (L := L) (delta := delta) hL1 hdelta
      (fun i ↦ observedTrajectoryScore_incrementAdapted (score i))
      (fun i ↦ conditionalTrajectoryRisk_stronglyAdapted K (score i))
      (fun i ↦ observedTrajectoryPredictableTilt_stronglyAdapted (tilt i))
      (fun i k x ↦ observedTrajectoryScore_mem_Icc (hscore i) k x)
      (fun i k x ↦ htilt i k (Preorder.frestrictLe k x))
      (fun i k ↦ observedTrajectoryScore_condExp K x0 (score i) (hscore i) k)
    with ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx posterior hposterior n hweight
  simpa only [trajectoryPredictableTiltPosteriorTotalWeight,
    trajectoryPredictableTiltPosteriorNormalizedConditionalRisk,
    trajectoryPredictableTiltPosteriorNormalizedEmpiricalRisk,
    trajectoryPredictableTiltPosteriorQuadraticPenalty] using
      hgood x hx posterior hposterior n hweight

omit [DecidableEq ι] in
/-- Path- and time-dependent posterior specialization of the normalized
tilt-weighted trajectory theorem. -/
theorem exists_trajectoryPredictableTiltPACBayes_normalized_selected_event
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (K n)] (x0 : Z)
    {score : ι → TrajectoryScore Z}
    (hscore : ∀ i n u y, score i n u y ∈ Set.Icc (0 : ℝ) 1)
    {tilt : ι → TrajectoryPredictableTilt Z} {L : ℝ}
    (hL1 : L < 1)
    (htilt : ∀ i n u, 0 ≤ tilt i n u ∧ tilt i n u ≤ L)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {delta : ℝ} (hdelta : 0 < delta)
    (posterior : (ℕ → Z) → ℕ → ι → ℝ)
    (hposterior : ∀ x n, IsPMF (posterior x n)) :
    ∃ goodEvent : Set (ℕ → Z),
      (trajectoryMeasure K x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ n : ℕ,
          0 < trajectoryPredictableTiltPosteriorTotalWeight
              tilt (posterior x n) n x →
            trajectoryPredictableTiltPosteriorNormalizedConditionalRisk
                K score tilt (posterior x n) n x <
              trajectoryPredictableTiltPosteriorNormalizedEmpiricalRisk
                  score tilt (posterior x n) n x +
                (klDiv (posterior x n) prior + Real.log (1 / delta) +
                    trajectoryPredictableTiltPosteriorQuadraticPenalty
                      score tilt (posterior x n) n x) /
                  trajectoryPredictableTiltPosteriorTotalWeight
                    tilt (posterior x n) n x := by
  rcases exists_trajectoryPredictableTiltPACBayes_normalized_event
      K x0 hscore hL1 htilt hprior hdelta with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx n hweight
  exact hgood x hx (posterior x n) (hposterior x n) n hweight

end

end FormalSLT.StochasticDynamics
