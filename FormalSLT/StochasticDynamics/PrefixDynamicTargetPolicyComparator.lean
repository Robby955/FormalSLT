/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.DynamicTargetPolicyComparator

/-!
# Prefix-dependent controlled environments and dynamic comparators

This module extends the controlled-trajectory semantic bridge from a
homogeneous environment row `P(state, action)` to a known environment kernel
which may inspect the complete completed prefix and the current time.  The
behavior and target policies already have this information pattern.  The
one-step importance ratio still changes only the action distribution: the
behavior and target conditional scores use the same prefix-dependent
environment row.

The capstone is an all-time empirical-Bernstein PAC--Bayes comparator for a
finite catalog of history/time-dependent target policies under a
history/time-dependent behavior policy and a history/time-dependent known
environment.  Its estimand remains the running average of target one-step
risks at behavior-encountered prefixes.  It is not target-law occupancy value,
full-trajectory importance sampling, a stationary result, or a doubly robust
estimator.
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

/-- A known environment continuation row which may inspect time and the full
completed controlled prefix before mapping the newly chosen action to a PMF
of next states. -/
abbrev PrefixControlledEnvironment (Z A : Type*) :=
  (n : ℕ) →
    ((i : Finset.Iic n) → ControlledObservation Z A) →
    A → PMF Z

/-- Embed a homogeneous state/action environment into the prefix-dependent
interface. -/
def homogeneousPrefixControlledEnvironment
    (P : Z → A → PMF Z) : PrefixControlledEnvironment Z A :=
  fun n u a ↦ P (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 a

/-- Joint next-action/next-state continuation under a prefix-dependent
environment and behavior policy. -/
def prefixControlledContinuationPMF
    (Q : PrefixControlledEnvironment Z A) (beta : BehaviorPolicy Z A)
    (n : ℕ) (u : (i : Finset.Iic n) → ControlledObservation Z A) :
    PMF (ControlledObservation Z A) :=
  (beta n u).bind fun a ↦
    (Q n u a).map fun y ↦ (a, y)

omit [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma prefixControlledContinuationPMF_apply
    (Q : PrefixControlledEnvironment Z A) (beta : BehaviorPolicy Z A)
    (n : ℕ) (u : (i : Finset.Iic n) → ControlledObservation Z A)
    (a : A) (y : Z) :
    prefixControlledContinuationPMF Q beta n u (a, y) =
      beta n u a * Q n u a y := by
  classical
  simp only [prefixControlledContinuationPMF, PMF.bind_apply, PMF.map_apply,
    tsum_fintype]
  rw [Finset.sum_eq_single a]
  · simp
  · intro a' _ ha'
    simp [Ne.symm ha']
  · simp

/-- Prefix kernel induced by the dynamic environment and behavior policy. -/
def prefixControlledPrefixKernel
    (Q : PrefixControlledEnvironment Z A) (beta : BehaviorPolicy Z A)
    (n : ℕ) :
    Kernel (((i : Finset.Iic n) → ControlledObservation Z A))
      (ControlledObservation Z A) :=
  Kernel.ofFunOfCountable fun u ↦
    (prefixControlledContinuationPMF Q beta n u).toMeasure

instance prefixControlledPrefixKernel.instIsMarkovKernel
    (Q : PrefixControlledEnvironment Z A) (beta : BehaviorPolicy Z A)
    (n : ℕ) :
    IsMarkovKernel (prefixControlledPrefixKernel Q beta n) :=
  ⟨fun u ↦ by
    change IsProbabilityMeasure
      (prefixControlledContinuationPMF Q beta n u).toMeasure
    infer_instance⟩

/-- Behavior-law trajectory under the dynamic controlled environment. -/
def prefixControlledTrajectoryMeasure
    (Q : PrefixControlledEnvironment Z A) (beta : BehaviorPolicy Z A)
    (initial : ControlledObservation Z A) :
    Measure (ℕ → ControlledObservation Z A) :=
  trajectoryMeasure (prefixControlledPrefixKernel Q beta) initial

instance prefixControlledTrajectoryMeasure.instIsProbabilityMeasure
    (Q : PrefixControlledEnvironment Z A) (beta : BehaviorPolicy Z A)
    (initial : ControlledObservation Z A) :
    IsProbabilityMeasure (prefixControlledTrajectoryMeasure Q beta initial) := by
  unfold prefixControlledTrajectoryMeasure
  infer_instance

/-- Normalized target one-step conditional mean at a realized prefix under
the prefix-dependent environment. -/
def prefixControlledTargetConditionalMean
    (Q : PrefixControlledEnvironment Z A) (pi : TargetPolicy Z A)
    (score : ControlledTransitionScore Z A) (C : ℝ)
    (n : ℕ) (x : ℕ → ControlledObservation Z A) : ℝ :=
  let u := Preorder.frestrictLe n x
  ∑ a : A,
    (pi n u a).toReal *
      ∑ y : Z, (Q n u a y).toReal * score n u a y / C

/-- One-step target/behavior cancellation remains exact because both policies
use the same prefix-dependent environment row after the action is chosen. -/
theorem conditionalTrajectoryRisk_prefixControlledNormalizedImportanceScore
    (Q : PrefixControlledEnvironment Z A) (beta : BehaviorPolicy Z A)
    (pi : TargetPolicy Z A) (score : ControlledTransitionScore Z A)
    (C : ℝ) (hoverlap : ControlledPolicyOverlap beta pi)
    (n : ℕ) (x : ℕ → ControlledObservation Z A) :
    conditionalTrajectoryRisk (prefixControlledPrefixKernel Q beta)
        (controlledNormalizedImportanceScore beta pi score C) n x =
      prefixControlledTargetConditionalMean Q pi score C n x := by
  classical
  let u := Preorder.frestrictLe n x
  change
    (∫ next,
        controlledNormalizedImportanceScore beta pi score C n u next
      ∂(prefixControlledContinuationPMF Q beta n u).toMeasure) = _
  rw [PMF.integral_eq_sum]
  rw [Fintype.sum_prod_type]
  unfold prefixControlledTargetConditionalMean
  simp only [u, prefixControlledContinuationPMF_apply, ENNReal.toReal_mul,
    controlledNormalizedImportanceScore, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _hy
  have hcancel :
      (beta n u a).toReal *
          controlledImportanceRatio beta pi n u a =
        (pi n u a).toReal := by
    by_cases hq : (beta n u a).toReal = 0
    · have hp := hoverlap n u a hq
      simp [controlledImportanceRatio, hq, hp]
    · unfold controlledImportanceRatio
      field_simp
  rw [show
      (beta n u a).toReal * (Q n u a y).toReal *
          (controlledImportanceRatio beta pi n u a * score n u a y / C) =
        ((beta n u a).toReal *
            controlledImportanceRatio beta pi n u a) *
          ((Q n u a y).toReal * score n u a y / C) by ring]
  rw [hcancel]

/-- Exact dynamic-environment conditional-expectation interface. -/
theorem prefixControlledObservedImportanceScore_condExp
    (Q : PrefixControlledEnvironment Z A) (beta : BehaviorPolicy Z A)
    (initial : ControlledObservation Z A)
    (pi : TargetPolicy Z A) (score : ControlledTransitionScore Z A)
    (C : ℝ)
    (hoverlap : ControlledPolicyOverlap beta pi)
    (hratio : ControlledPolicyRatioBound beta pi C)
    (hC : 0 < C)
    (hscore : ∀ n u a y, score n u a y ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) :
    (prefixControlledTrajectoryMeasure Q beta initial)[
        controlledObservedImportanceScore beta pi score C n |
        Filtration.piLE
          (X := fun _ : ℕ ↦ ControlledObservation Z A) n] =ᵐ[
      prefixControlledTrajectoryMeasure Q beta initial]
        prefixControlledTargetConditionalMean Q pi score C n := by
  have hcond := observedTrajectoryScore_condExp
    (prefixControlledPrefixKernel Q beta) initial
    (controlledNormalizedImportanceScore beta pi score C)
    (controlledNormalizedImportanceScore_mem_Icc
      hoverlap hratio hC hscore) n
  change
    (trajectoryMeasure (prefixControlledPrefixKernel Q beta) initial)[
        observedTrajectoryScore
          (controlledNormalizedImportanceScore beta pi score C) n |
        Filtration.piLE
          (X := fun _ : ℕ ↦ ControlledObservation Z A) n] =ᵐ[
      trajectoryMeasure (prefixControlledPrefixKernel Q beta) initial]
        prefixControlledTargetConditionalMean Q pi score C n
  filter_upwards [hcond] with x hx
  rw [hx]
  exact conditionalTrajectoryRisk_prefixControlledNormalizedImportanceScore
    Q beta pi score C hoverlap n x

/-- The dynamic target conditional mean is predictable from the completed
prefix. -/
theorem prefixControlledTargetConditionalMean_stronglyAdapted
    (Q : PrefixControlledEnvironment Z A) (beta : BehaviorPolicy Z A)
    (pi : TargetPolicy Z A) (score : ControlledTransitionScore Z A)
    (C : ℝ) (hoverlap : ControlledPolicyOverlap beta pi) :
    StronglyAdapted
      (Filtration.piLE
        (X := fun _ : ℕ ↦ ControlledObservation Z A))
      (prefixControlledTargetConditionalMean Q pi score C) := by
  intro n
  have hmeas := stronglyMeasurable_conditionalTrajectoryRisk
    (prefixControlledPrefixKernel Q beta)
    (controlledNormalizedImportanceScore beta pi score C) n
  have heq :
      prefixControlledTargetConditionalMean Q pi score C n =
        conditionalTrajectoryRisk (prefixControlledPrefixKernel Q beta)
          (controlledNormalizedImportanceScore beta pi score C) n := by
    funext x
    exact (conditionalTrajectoryRisk_prefixControlledNormalizedImportanceScore
      Q beta pi score C hoverlap n x).symm
  rw [heq]
  exact hmeas

/-- Catalog interfaces for the predictable-mean empirical-Bernstein theorem
under a prefix-dependent controlled environment. -/
theorem prefixControlledImportanceCatalog_predictableMean_interfaces
    [Fintype ι]
    (Q : PrefixControlledEnvironment Z A) (beta : BehaviorPolicy Z A)
    (initial : ControlledObservation Z A)
    (pi : ι → TargetPolicy Z A)
    (score : ι → ControlledTransitionScore Z A)
    (C : ℝ)
    (hoverlap : ∀ i, ControlledPolicyOverlap beta (pi i))
    (hratio : ∀ i, ControlledPolicyRatioBound beta (pi i) C)
    (hC : 0 < C)
    (hscore : ∀ i n u a y, score i n u a y ∈ Set.Icc (0 : ℝ) 1) :
    (∀ i, IncrementAdapted
        (Filtration.piLE
          (X := fun _ : ℕ ↦ ControlledObservation Z A))
        (controlledObservedImportanceScore beta (pi i) (score i) C)) ∧
      (∀ i, StronglyAdapted
        (Filtration.piLE
          (X := fun _ : ℕ ↦ ControlledObservation Z A))
        (prefixControlledTargetConditionalMean Q (pi i) (score i) C)) ∧
      (∀ i n x,
        0 ≤ controlledObservedImportanceScore
            beta (pi i) (score i) C n x ∧
          controlledObservedImportanceScore
            beta (pi i) (score i) C n x ≤ 1) ∧
      (∀ i n,
        (prefixControlledTrajectoryMeasure Q beta initial)[
            controlledObservedImportanceScore beta (pi i) (score i) C n |
            Filtration.piLE
              (X := fun _ : ℕ ↦ ControlledObservation Z A) n] =ᵐ[
          prefixControlledTrajectoryMeasure Q beta initial]
            prefixControlledTargetConditionalMean Q (pi i) (score i) C n) := by
  refine ⟨fun i ↦ controlledObservedImportanceScore_incrementAdapted
      beta (pi i) (score i) C, ?_, ?_, ?_⟩
  · exact fun i ↦ prefixControlledTargetConditionalMean_stronglyAdapted
      Q beta (pi i) (score i) C (hoverlap i)
  · intro i n x
    exact observedTrajectoryScore_mem_Icc
      (controlledNormalizedImportanceScore_mem_Icc
        (hoverlap i) (hratio i) hC (hscore i)) n x
  · exact fun i n ↦ prefixControlledObservedImportanceScore_condExp
      Q beta initial (pi i) (score i) C
      (hoverlap i) (hratio i) hC (hscore i) n

/-- Unnormalized target one-step risk at a behavior-encountered prefix under
the dynamic environment. -/
def prefixEncounteredTargetConditionalRisk
    (Q : PrefixControlledEnvironment Z A) (pi : TargetPolicy Z A)
    (score : ControlledTransitionScore Z A)
    (n : ℕ) (x : ℕ → ControlledObservation Z A) : ℝ :=
  let u := Preorder.frestrictLe n x
  ∑ a : A,
    (pi n u a).toReal *
      ∑ y : Z, (Q n u a y).toReal * score n u a y

omit [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem prefixControlledTargetConditionalMean_eq_risk_div
    (Q : PrefixControlledEnvironment Z A) (pi : TargetPolicy Z A)
    (score : ControlledTransitionScore Z A) (C : ℝ)
    (n : ℕ) (x : ℕ → ControlledObservation Z A) :
    prefixControlledTargetConditionalMean Q pi score C n x =
      prefixEncounteredTargetConditionalRisk Q pi score n x / C := by
  classical
  unfold prefixControlledTargetConditionalMean
    prefixEncounteredTargetConditionalRisk
  simp_rw [← Finset.sum_div]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

/-- Posterior/time encountered-risk average under the dynamic environment. -/
def prefixDynamicTargetPolicyPosteriorEncounteredRisk
    [Fintype ι]
    (Q : PrefixControlledEnvironment Z A) (pi : ι → TargetPolicy Z A)
    (score : ι → ControlledTransitionScore Z A)
    (posterior : ι → ℝ) (n : ℕ)
    (x : ℕ → ControlledObservation Z A) : ℝ :=
  posteriorAverage posterior fun i ↦
    forwardPrefixMean
      (fun k ↦ prefixEncounteredTargetConditionalRisk
        Q (pi i) (score i) k x) n

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
private theorem prefixForwardPrefixMean_div
    (f : ℕ → ℝ) (C : ℝ) (n : ℕ) :
    forwardPrefixMean (fun k ↦ f k / C) n =
      forwardPrefixMean f n / C := by
  unfold forwardPrefixMean
  rw [← Finset.sum_div]
  ring

omit [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem posteriorAverage_forwardPrefixMean_prefixControlledTargetMean
    [Fintype ι]
    (Q : PrefixControlledEnvironment Z A) (pi : ι → TargetPolicy Z A)
    (score : ι → ControlledTransitionScore Z A) (C : ℝ)
    (posterior : ι → ℝ) (n : ℕ)
    (x : ℕ → ControlledObservation Z A) :
    posteriorAverage posterior
        (fun i ↦ forwardPrefixMean
          (fun k ↦ prefixControlledTargetConditionalMean
            Q (pi i) (score i) C k x) n) =
      prefixDynamicTargetPolicyPosteriorEncounteredRisk
        Q pi score posterior n x / C := by
  classical
  unfold prefixDynamicTargetPolicyPosteriorEncounteredRisk posteriorAverage
  simp_rw [prefixControlledTargetConditionalMean_eq_risk_div,
    prefixForwardPrefixMean_div]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Dynamic-environment comparator right-hand side. -/
def prefixDynamicTargetPolicyComparatorBoundary
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

/-- All-time empirical-Bernstein PAC--Bayes comparator under a known
prefix/time-dependent environment. -/
theorem exists_prefixDynamicTargetPolicyComparator_event
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (Q : PrefixControlledEnvironment Z A) (beta : BehaviorPolicy Z A)
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
      (prefixControlledTrajectoryMeasure Q beta initial).real
          goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : τ,
          ∀ posterior : ι → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              prefixDynamicTargetPolicyPosteriorEncounteredRisk
                  Q pi score posterior n x <
                prefixDynamicTargetPolicyComparatorBoundary
                  prior weight lam beta pi score C
                    posterior delta j n x := by
  have hinterfaces :=
    prefixControlledImportanceCatalog_predictableMean_interfaces
      Q beta initial pi score C hoverlap hratio hC hscore
  rcases hinterfaces with ⟨hXadapted, hmeanadapted, hXunit, hcond⟩
  rcases exists_forwardPredictableMeanBesselPACBayes_event
      (μ := prefixControlledTrajectoryMeasure Q beta initial)
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
            (fun k ↦ prefixControlledTargetConditionalMean
              Q (pi i) (score i) C k x) n) <
        dynamicTargetPolicyPosteriorEmpiricalScore
            beta pi score C posterior n x +
          forwardPredictableMeanBesselPACBayesBoundary
            prior weight lam
              (fun i ↦ controlledObservedImportanceScore
                beta (pi i) (score i) C)
              posterior delta j n x := by
    simpa only [dynamicTargetPolicyPosteriorEmpiricalScore] using
      hgood x hx j posterior hposterior n hn
  rw [posteriorAverage_forwardPrefixMean_prefixControlledTargetMean
    Q pi score C posterior n x] at hbase
  unfold prefixDynamicTargetPolicyComparatorBoundary
  calc
    prefixDynamicTargetPolicyPosteriorEncounteredRisk
        Q pi score posterior n x =
      C * (prefixDynamicTargetPolicyPosteriorEncounteredRisk
        Q pi score posterior n x / C) := by
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
/-- Path/time/posterior/tilt substitution for the prefix-dynamic result. -/
theorem prefixDynamicTargetPolicyComparator_selected_of_simultaneous
    [Fintype ι] [Fintype τ]
    (Q : PrefixControlledEnvironment Z A) (beta : BehaviorPolicy Z A)
    (pi : ι → TargetPolicy Z A)
    (score : ι → ControlledTransitionScore Z A)
    (C : ℝ) (prior : ι → ℝ) (weight : τ → ℝ)
    (lam : τ → ℝ) (delta : ℝ)
    (x : ℕ → ControlledObservation Z A)
    (hall : ∀ j : τ, ∀ posterior : ι → ℝ, IsPMF posterior →
      ∀ n : ℕ, 2 ≤ n →
        prefixDynamicTargetPolicyPosteriorEncounteredRisk
            Q pi score posterior n x <
          prefixDynamicTargetPolicyComparatorBoundary
            prior weight lam beta pi score C posterior delta j n x)
    (posterior : (ℕ → ControlledObservation Z A) → ℕ → ι → ℝ)
    (hposterior : ∀ x n, IsPMF (posterior x n))
    (select : (ℕ → ControlledObservation Z A) →
      ℕ → (ι → ℝ) → τ)
    (n : ℕ) (hn : 2 ≤ n) :
    prefixDynamicTargetPolicyPosteriorEncounteredRisk
        Q pi score (posterior x n) n x <
      prefixDynamicTargetPolicyComparatorBoundary
        prior weight lam beta pi score C (posterior x n) delta
          (select x n (posterior x n)) n x :=
  hall (select x n (posterior x n)) (posterior x n)
    (hposterior x n) n hn

end

end FormalSLT.StochasticDynamics
