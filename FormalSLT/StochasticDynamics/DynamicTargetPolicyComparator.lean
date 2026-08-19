/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.ControlledTrajectory

/-!
# Dynamic target-policy comparators along behavior trajectories

This file turns the controlled-trajectory conditional-mean identity into an
all-time empirical-Bernstein PAC--Bayes comparator.  Both the behavior policy
and every target policy may depend on the complete observed prefix and on
time.  On one behavior-law event, the result controls the posterior average
of the targets' one-step conditional risks at the histories and states that
the behavior trajectory actually encounters.

The observed score uses one-step target-to-behavior action ratios.  A common
declared ratio cap `C` normalizes every score into `[0,1]`; multiplying the
generic predictable-mean boundary by `C` returns the conclusion to the
original score units.  The event is simultaneous over all times `n >= 2`, all
posterior PMFs, and all atoms of a finite predeclared tilt catalog, so these
choices may be substituted after observing the path.

This is an encountered-state dynamic comparator.  It is not target-law
occupancy evaluation, stationary-value estimation, full-trajectory
importance sampling, or doubly robust off-policy evaluation.  The environment
kernel in this module is known and homogeneous in `(state, action)`; making it
prefix- or time-dependent requires a corresponding extension of the
controlled semantic layer.
-/

open Filter Finset Function MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardPredictableMeanBesselPACBayes
open scoped BigOperators ENNReal NNReal Topology

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Z A ι τ : Type*}
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- The target policy's one-step conditional score at the history and state
encountered by the behavior path.  No target state-occupancy distribution is
introduced. -/
def encounteredTargetConditionalRisk
    (P : Z → A → PMF Z) (pi : TargetPolicy Z A)
    (score : ControlledTransitionScore Z A)
    (n : ℕ) (x : ℕ → ControlledObservation Z A) : ℝ :=
  let u := Preorder.frestrictLe n x
  let currentState := (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
  ∑ a : A,
    (pi n u a).toReal *
      ∑ y : Z, (P currentState a y).toReal * score n u a y

omit [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The normalized controlled conditional mean is exactly the encountered
target risk divided by the declared common ratio cap. -/
theorem controlledTargetConditionalMean_eq_encounteredRisk_div
    (P : Z → A → PMF Z) (pi : TargetPolicy Z A)
    (score : ControlledTransitionScore Z A) (C : ℝ)
    (n : ℕ) (x : ℕ → ControlledObservation Z A) :
    controlledTargetConditionalMean P pi score C n x =
      encounteredTargetConditionalRisk P pi score n x / C := by
  classical
  unfold controlledTargetConditionalMean encounteredTargetConditionalRisk
  simp_rw [← Finset.sum_div]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

/-- Posterior/time average of the target policies' one-step risks along the
behavior-encountered histories and states. -/
def dynamicTargetPolicyPosteriorEncounteredRisk
    [Fintype ι]
    (P : Z → A → PMF Z) (pi : ι → TargetPolicy Z A)
    (score : ι → ControlledTransitionScore Z A)
    (posterior : ι → ℝ) (n : ℕ)
    (x : ℕ → ControlledObservation Z A) : ℝ :=
  posteriorAverage posterior fun i ↦
    forwardPrefixMean
      (fun k ↦ encounteredTargetConditionalRisk
        P (pi i) (score i) k x) n

/-- Posterior empirical mean of normalized one-step importance-weighted
scores observed along the behavior trajectory. -/
def dynamicTargetPolicyPosteriorEmpiricalScore
    [Fintype ι]
    (beta : BehaviorPolicy Z A) (pi : ι → TargetPolicy Z A)
    (score : ι → ControlledTransitionScore Z A) (C : ℝ)
    (posterior : ι → ℝ) (n : ℕ)
    (x : ℕ → ControlledObservation Z A) : ℝ :=
  posteriorAverage posterior fun i ↦
    forwardPrefixMean
      (fun k ↦ controlledObservedImportanceScore
        beta (pi i) (score i) C k x) n

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
private theorem forwardPrefixMean_div
    (f : ℕ → ℝ) (C : ℝ) (n : ℕ) :
    forwardPrefixMean (fun k ↦ f k / C) n =
      forwardPrefixMean f n / C := by
  unfold forwardPrefixMean
  rw [← Finset.sum_div]
  ring

omit [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Scaling identity used by the capstone: the posterior/time average of the
normalized predictable means is the encountered-risk average divided by the
common cap. -/
theorem posteriorAverage_forwardPrefixMean_controlledTargetConditionalMean
    [Fintype ι]
    (P : Z → A → PMF Z) (pi : ι → TargetPolicy Z A)
    (score : ι → ControlledTransitionScore Z A) (C : ℝ)
    (posterior : ι → ℝ) (n : ℕ)
    (x : ℕ → ControlledObservation Z A) :
    posteriorAverage posterior
        (fun i ↦ forwardPrefixMean
          (fun k ↦ controlledTargetConditionalMean
            P (pi i) (score i) C k x) n) =
      dynamicTargetPolicyPosteriorEncounteredRisk
        P pi score posterior n x / C := by
  classical
  unfold dynamicTargetPolicyPosteriorEncounteredRisk posteriorAverage
  simp_rw [controlledTargetConditionalMean_eq_encounteredRisk_div,
    forwardPrefixMean_div]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Complete dynamic-comparator right-hand side for one declared tilt.  The
quantity in parentheses is in normalized importance-score units, and the
outer factor `C` restores the original target-score units. -/
def dynamicTargetPolicyComparatorBoundary
    [Fintype ι] [Fintype τ]
    (prior : ι → ℝ) (weight : τ → ℝ) (lam : τ → ℝ)
    (beta : BehaviorPolicy Z A) (pi : ι → TargetPolicy Z A)
    (score : ι → ControlledTransitionScore Z A) (C : ℝ)
    (posterior : ι → ℝ) (delta : ℝ) (j : τ) (n : ℕ)
    (x : ℕ → ControlledObservation Z A) : ℝ :=
  C *
    (dynamicTargetPolicyPosteriorEmpiricalScore
        beta pi score C posterior n x +
      forwardPredictableMeanBesselPACBayesBoundary
        prior weight lam
          (fun i ↦ controlledObservedImportanceScore
            beta (pi i) (score i) C)
          posterior delta j n x)

/-- All-time empirical-Bernstein PAC--Bayes comparator for a finite catalog
of history- and time-dependent target policies.

The controlled conditional means are evaluated at behavior-encountered
histories and states.  One outer event supports every time `n >= 2`, every
post-data posterior PMF, and every atom of the finite declared tilt catalog. -/
theorem exists_dynamicTargetPolicyComparator_event
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (P : Z → A → PMF Z) (beta : BehaviorPolicy Z A)
    (initial : ControlledObservation Z A)
    (pi : ι → TargetPolicy Z A)
    (score : ι → ControlledTransitionScore Z A)
    (hscore : ∀ i n u a y, score i n u a y ∈ Set.Icc (0 : ℝ) 1)
    {C : ℝ} (hC : 0 < C)
    (hoverlap : ∀ i, ControlledPolicyOverlap beta (pi i))
    (hratio : ∀ i, ControlledPolicyRatioBound beta (pi i) C)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : τ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : τ → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_one : ∀ j, lam j < 1) :
    ∃ goodEvent : Set (ℕ → ControlledObservation Z A),
      (controlledTrajectoryMeasure P beta initial).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : τ,
          ∀ posterior : ι → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              dynamicTargetPolicyPosteriorEncounteredRisk
                  P pi score posterior n x <
                dynamicTargetPolicyComparatorBoundary
                  prior weight lam beta pi score C
                    posterior delta j n x := by
  have hinterfaces := controlledImportanceCatalog_predictableMean_interfaces
    P beta initial pi score (fun _i ↦ C)
      hoverlap hratio (fun _i ↦ hC) hscore
  rcases hinterfaces with ⟨hXadapted, hmeanadapted, hXunit, hcond⟩
  rcases exists_forwardPredictableMeanBesselPACBayes_event
      (μ := controlledTrajectoryMeasure P beta initial)
      (ℱ := Filtration.piLE
        (X := fun _ : ℕ ↦ ControlledObservation Z A))
      hprior hweight hdelta hlam hlam_one
      hXadapted hmeanadapted hXunit hcond with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx j posterior hposterior n hn
  have hbase :
      posteriorAverage posterior
          (fun i ↦ forwardPrefixMean
            (fun k ↦ controlledTargetConditionalMean
              P (pi i) (score i) C k x) n) <
        dynamicTargetPolicyPosteriorEmpiricalScore
            beta pi score C posterior n x +
          forwardPredictableMeanBesselPACBayesBoundary
            prior weight lam
              (fun i ↦ controlledObservedImportanceScore
                beta (pi i) (score i) C)
              posterior delta j n x := by
    simpa only [dynamicTargetPolicyPosteriorEmpiricalScore] using
      hgood x hx j posterior hposterior n hn
  rw [posteriorAverage_forwardPrefixMean_controlledTargetConditionalMean
    P pi score C posterior n x] at hbase
  unfold dynamicTargetPolicyComparatorBoundary
  calc
    dynamicTargetPolicyPosteriorEncounteredRisk P pi score posterior n x =
        C * (dynamicTargetPolicyPosteriorEncounteredRisk
          P pi score posterior n x / C) := by
      field_simp [hC.ne']
    _ < C *
        (dynamicTargetPolicyPosteriorEmpiricalScore
            beta pi score C posterior n x +
          forwardPredictableMeanBesselPACBayesBoundary
            prior weight lam
              (fun i ↦ controlledObservedImportanceScore
                beta (pi i) (score i) C)
              posterior delta j n x) :=
      mul_lt_mul_of_pos_left hbase hC

omit [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Explicit path/time/posterior/tilt substitution into a simultaneous
dynamic-comparator conclusion.  It does not construct or validate a selected
stochastic process. -/
theorem dynamicTargetPolicyComparator_selected_of_simultaneous
    [Fintype ι] [Fintype τ]
    (P : Z → A → PMF Z) (beta : BehaviorPolicy Z A)
    (pi : ι → TargetPolicy Z A)
    (score : ι → ControlledTransitionScore Z A)
    (C : ℝ) (prior : ι → ℝ) (weight : τ → ℝ)
    (lam : τ → ℝ) (delta : ℝ)
    (x : ℕ → ControlledObservation Z A)
    (hall : ∀ j : τ, ∀ posterior : ι → ℝ, IsPMF posterior →
      ∀ n : ℕ, 2 ≤ n →
        dynamicTargetPolicyPosteriorEncounteredRisk
            P pi score posterior n x <
          dynamicTargetPolicyComparatorBoundary
            prior weight lam beta pi score C posterior delta j n x)
    (posterior : (ℕ → ControlledObservation Z A) → ℕ → ι → ℝ)
    (hposterior : ∀ x n, IsPMF (posterior x n))
    (select : (ℕ → ControlledObservation Z A) →
      ℕ → (ι → ℝ) → τ)
    (n : ℕ) (hn : 2 ≤ n) :
    dynamicTargetPolicyPosteriorEncounteredRisk
        P pi score (posterior x n) n x <
      dynamicTargetPolicyComparatorBoundary
        prior weight lam beta pi score C (posterior x n) delta
          (select x n (posterior x n)) n x :=
  hall (select x n (posterior x n)) (posterior x n)
    (hposterior x n) n hn

end

end FormalSLT.StochasticDynamics
