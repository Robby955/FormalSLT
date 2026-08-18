/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.TrajectoryRisk
import FormalSLT.PACBayes.ForwardPredictableMeanBesselPACBayes

/-!
# Controlled finite trajectories under a history-dependent behavior policy

This file supplies the semantic layer needed to apply the predictable-mean
PAC--Bayes machinery to controlled trajectories.  A path coordinate is a
decision--outcome pair `(A_t, S_{t+1})`.  Given the prefix through time `t`,
the behavior policy first draws `A_{t+1}` after observing the current state
`S_{t+1}`, and then the environment draws `S_{t+2}` from
`P(S_{t+1}, A_{t+1})`.  Thus there is no ambiguity about whether an action is
chosen before or after a transition.

For a finite catalog of predeclared target policies, an importance-weighted
bounded transition score is normalized by a declared overlap cap.  Its exact
conditional mean under the behavior path law is the corresponding target
policy transition score, with the same normalization.  The resulting observed
score and conditional mean discharge the `IncrementAdapted`,
`StronglyAdapted`, and conditional-expectation interfaces used by
`ForwardPredictableMeanBesselPACBayes`.

This is only a semantic prerequisite.  It does not identify a stationary
target-policy value, compare target and behavior state-occupancy laws, or
provide an off-policy evaluation theorem for a target trajectory law.
-/

open Filter Finset Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Z A ι : Type*}
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- One coordinate records an action and the state revealed after that action.
The final coordinate in a prefix therefore exposes the current state for the
next decision. -/
abbrev ControlledObservation (Z A : Type*) := A × Z

/-- After the prefix through `(A_t,S_{t+1})`, the behavior policy chooses
`A_{t+1}`.  It may inspect the entire completed decision--outcome history;
the current state is the second component of its final coordinate. -/
abbrev BehaviorPolicy (Z A : Type*) :=
  (n : ℕ) →
    ((i : Finset.Iic n) → ControlledObservation Z A) →
    PMF A

/-- A predeclared target policy has the same information pattern as the
behavior policy. -/
abbrev TargetPolicy (Z A : Type*) := BehaviorPolicy Z A

/-- A bounded score for the controlled transition from the final pair in the
prefix to the newly sampled action--outcome pair. -/
abbrev ControlledTransitionScore (Z A : Type*) :=
  (n : ℕ) →
    ((i : Finset.Iic n) → ControlledObservation Z A) →
    A → Z → ℝ

/-- The joint continuation PMF.  Conditional on the prefix through time `n`,
sample the next action from the behavior policy at the current state, then
sample its outcome from the selected environment row. -/
def controlledContinuationPMF
    (P : Z → A → PMF Z) (β : BehaviorPolicy Z A)
    (n : ℕ) (u : (i : Finset.Iic n) → ControlledObservation Z A) :
    PMF (ControlledObservation Z A) :=
  let currentState := (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
  (β n u).bind fun a ↦
    (P currentState a).map fun y ↦ (a, y)

omit [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma controlledContinuationPMF_apply
    (P : Z → A → PMF Z) (β : BehaviorPolicy Z A)
    (n : ℕ) (u : (i : Finset.Iic n) → ControlledObservation Z A)
    (a : A) (y : Z) :
    controlledContinuationPMF P β n u (a, y) =
      β n u a *
        P (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 a y := by
  classical
  simp only [controlledContinuationPMF, PMF.bind_apply, PMF.map_apply,
    tsum_fintype]
  rw [Finset.sum_eq_single a]
  · simp
  · intro a' _ ha'
    simp [Ne.symm ha']
  · simp

/-- Prefix kernel on the augmented state--action space. -/
def controlledPrefixKernel
    (P : Z → A → PMF Z) (β : BehaviorPolicy Z A)
    (n : ℕ) :
    Kernel (((i : Finset.Iic n) → ControlledObservation Z A))
      (ControlledObservation Z A) :=
  Kernel.ofFunOfCountable fun u ↦ (controlledContinuationPMF P β n u).toMeasure

instance controlledPrefixKernel.instIsMarkovKernel
    (P : Z → A → PMF Z) (β : BehaviorPolicy Z A) (n : ℕ) :
    IsMarkovKernel (controlledPrefixKernel P β n) :=
  ⟨fun u ↦ by
    change IsProbabilityMeasure (controlledContinuationPMF P β n u).toMeasure
    infer_instance⟩

/-- Behavior-law trajectory, conditional on a supplied initial action--outcome
pair.  The first coordinate is fixed; every later action is sampled from `β`
after the preceding outcome state is observed. -/
def controlledTrajectoryMeasure
    (P : Z → A → PMF Z) (β : BehaviorPolicy Z A)
    (initial : ControlledObservation Z A) :
    Measure (ℕ → ControlledObservation Z A) :=
  trajectoryMeasure (controlledPrefixKernel P β) initial

instance controlledTrajectoryMeasure.instIsProbabilityMeasure
    (P : Z → A → PMF Z) (β : BehaviorPolicy Z A)
    (initial : ControlledObservation Z A) :
    IsProbabilityMeasure (controlledTrajectoryMeasure P β initial) := by
  unfold controlledTrajectoryMeasure
  infer_instance

/-- Real-valued target-to-behavior action likelihood ratio.  A separate
overlap hypothesis below makes the zero-denominator branch identifiable. -/
def controlledImportanceRatio
    (β : BehaviorPolicy Z A) (π : TargetPolicy Z A)
    (n : ℕ) (u : (i : Finset.Iic n) → ControlledObservation Z A)
    (a : A) : ℝ :=
  (π n u a).toReal / (β n u a).toReal

/-- Pointwise finite-space overlap: the target assigns no mass to an action
which the behavior policy makes impossible at the same history and state. -/
def ControlledPolicyOverlap
  (β : BehaviorPolicy Z A) (π : TargetPolicy Z A) : Prop :=
  ∀ n u a,
    (β n u a).toReal = 0 → (π n u a).toReal = 0

/-- A declared cap on every target-to-behavior likelihood ratio, expressed
without division so it remains meaningful at zero behavior mass. -/
def ControlledPolicyRatioBound
  (β : BehaviorPolicy Z A) (π : TargetPolicy Z A) (cap : ℝ) : Prop :=
  ∀ n u a,
    (π n u a).toReal ≤ cap * (β n u a).toReal

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
private lemma mul_ratio_eq_of_zero_imp_zero
    {p q : ℝ} (hzero : q = 0 → p = 0) :
    q * (p / q) = p := by
  by_cases hq : q = 0
  · simp [hq, hzero hq]
  · field_simp

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma controlledImportanceRatio_nonneg
    (β : BehaviorPolicy Z A) (π : TargetPolicy Z A)
    (n : ℕ) (u : (i : Finset.Iic n) → ControlledObservation Z A)
    (a : A) :
    0 ≤ controlledImportanceRatio β π n u a := by
  exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma controlledImportanceRatio_le_cap
    {β : BehaviorPolicy Z A} {π : TargetPolicy Z A} {cap : ℝ}
    (hoverlap : ControlledPolicyOverlap β π)
    (hcap : ControlledPolicyRatioBound β π cap)
    (hcap0 : 0 ≤ cap)
    (n : ℕ) (u : (i : Finset.Iic n) → ControlledObservation Z A)
    (a : A) :
    controlledImportanceRatio β π n u a ≤ cap := by
  let q := (β n u a).toReal
  let p := (π n u a).toReal
  by_cases hq : q = 0
  · have hp : p = 0 := hoverlap n u a hq
    simpa [controlledImportanceRatio, q, p, hq, hp] using hcap0
  · have hqpos : 0 < q := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hq)
    exact (div_le_iff₀ hqpos).2 (hcap n u a)

/-- The importance-weighted transition score, divided by a declared likelihood
ratio cap so that it remains in `[0,1]`. -/
def controlledNormalizedImportanceScore
    (β : BehaviorPolicy Z A) (π : TargetPolicy Z A)
    (score : ControlledTransitionScore Z A) (cap : ℝ) :
    TrajectoryScore (ControlledObservation Z A) :=
  fun n u next ↦
    controlledImportanceRatio β π n u next.1 *
        score n u next.1 next.2 / cap

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma controlledNormalizedImportanceScore_mem_Icc
    {β : BehaviorPolicy Z A} {π : TargetPolicy Z A}
    {score : ControlledTransitionScore Z A} {cap : ℝ}
    (hoverlap : ControlledPolicyOverlap β π)
    (hratio : ControlledPolicyRatioBound β π cap)
    (hcap : 0 < cap)
    (hscore : ∀ n u a y, score n u a y ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (u : (i : Finset.Iic n) → ControlledObservation Z A)
    (next : ControlledObservation Z A) :
    controlledNormalizedImportanceScore β π score cap n u next ∈
      Set.Icc (0 : ℝ) 1 := by
  let ratio := controlledImportanceRatio β π n u next.1
  have hratio0 : 0 ≤ ratio :=
    controlledImportanceRatio_nonneg β π n u next.1
  have hratiocap : ratio ≤ cap :=
    controlledImportanceRatio_le_cap hoverlap hratio hcap.le
      n u next.1
  have hs := hscore n u next.1 next.2
  constructor
  · exact div_nonneg (mul_nonneg hratio0 hs.1) hcap.le
  · change ratio * score n u next.1 next.2 / cap ≤ 1
    rw [div_le_iff₀ hcap]
    simpa using mul_le_mul hratiocap hs.2 hs.1 hcap.le

/-- The target-policy conditional transition score, normalized by `cap`, but
still averaged over environment outcomes from the actually encountered current
state. -/
def controlledTargetConditionalMean
    (P : Z → A → PMF Z) (π : TargetPolicy Z A)
    (score : ControlledTransitionScore Z A) (cap : ℝ)
    (n : ℕ) (x : ℕ → ControlledObservation Z A) : ℝ :=
  let u := Preorder.frestrictLe n x
  let currentState := (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
  ∑ a : A,
    (π n u a).toReal *
      ∑ y : Z, (P currentState a y).toReal * score n u a y / cap

/-- Under overlap, behavior weighting cancels exactly and the generic
prefix-kernel conditional risk is the normalized target-policy transition
score at the encountered history. -/
theorem conditionalTrajectoryRisk_controlledNormalizedImportanceScore
    (P : Z → A → PMF Z) (β : BehaviorPolicy Z A)
    (π : TargetPolicy Z A) (score : ControlledTransitionScore Z A)
    (cap : ℝ) (hoverlap : ControlledPolicyOverlap β π)
    (n : ℕ) (x : ℕ → ControlledObservation Z A) :
    conditionalTrajectoryRisk (controlledPrefixKernel P β)
        (controlledNormalizedImportanceScore β π score cap) n x =
      controlledTargetConditionalMean P π score cap n x := by
  classical
  let u := Preorder.frestrictLe n x
  change
    (∫ next,
        controlledNormalizedImportanceScore β π score cap n u next
      ∂(controlledContinuationPMF P β n u).toMeasure) = _
  rw [PMF.integral_eq_sum]
  rw [Fintype.sum_prod_type]
  unfold controlledTargetConditionalMean
  simp only [u, controlledContinuationPMF_apply, ENNReal.toReal_mul,
    controlledNormalizedImportanceScore, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  have hcancel :
      (β n u a).toReal *
          controlledImportanceRatio β π n u a =
        (π n u a).toReal := by
    exact mul_ratio_eq_of_zero_imp_zero (hoverlap n u a)
  rw [show
      (β n u a).toReal *
          (P (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 a y).toReal *
            (controlledImportanceRatio β π n u a *
              score n u a y / cap) =
        ((β n u a).toReal *
            controlledImportanceRatio β π n u a) *
          ((P (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 a y).toReal *
              score n u a y / cap) by ring]
  rw [hcancel]

/-- Importance-weighted score actually observed from the behavior trajectory. -/
def controlledObservedImportanceScore
    (β : BehaviorPolicy Z A) (π : TargetPolicy Z A)
    (score : ControlledTransitionScore Z A) (cap : ℝ)
    (n : ℕ) (x : ℕ → ControlledObservation Z A) : ℝ :=
  observedTrajectoryScore
    (controlledNormalizedImportanceScore β π score cap) n x

lemma measurable_controlledObservedImportanceScore
    (β : BehaviorPolicy Z A) (π : TargetPolicy Z A)
    (score : ControlledTransitionScore Z A) (cap : ℝ) (n : ℕ) :
    Measurable (controlledObservedImportanceScore β π score cap n) := by
  exact measurable_observedTrajectoryScore
    (controlledNormalizedImportanceScore β π score cap) n

theorem integrable_controlledObservedImportanceScore
    (P : Z → A → PMF Z) (β : BehaviorPolicy Z A)
    (initial : ControlledObservation Z A)
    (π : TargetPolicy Z A) (score : ControlledTransitionScore Z A)
    (cap : ℝ)
    (hoverlap : ControlledPolicyOverlap β π)
    (hratio : ControlledPolicyRatioBound β π cap)
    (hcap : 0 < cap)
    (hscore : ∀ n u a y, score n u a y ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) :
    Integrable (controlledObservedImportanceScore β π score cap n)
      (controlledTrajectoryMeasure P β initial) := by
  exact integrable_observedTrajectoryScore
    (κ := controlledPrefixKernel P β) (x0 := initial)
    (controlledNormalizedImportanceScore_mem_Icc
      hoverlap hratio hcap hscore) n

/-- Exact off-policy one-step identity under the behavior law.  It identifies
only the target action distribution at the behavior-encountered history and
state distribution. -/
theorem controlledObservedImportanceScore_condExp
    (P : Z → A → PMF Z) (β : BehaviorPolicy Z A)
    (initial : ControlledObservation Z A)
    (π : TargetPolicy Z A) (score : ControlledTransitionScore Z A)
    (cap : ℝ)
    (hoverlap : ControlledPolicyOverlap β π)
    (hratio : ControlledPolicyRatioBound β π cap)
    (hcap : 0 < cap)
    (hscore : ∀ n u a y, score n u a y ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) :
    (controlledTrajectoryMeasure P β initial)[
        controlledObservedImportanceScore β π score cap n |
        Filtration.piLE
          (X := fun _ : ℕ ↦ ControlledObservation Z A) n] =ᵐ[
      controlledTrajectoryMeasure P β initial]
        controlledTargetConditionalMean P π score cap n := by
  have hcond := observedTrajectoryScore_condExp
    (controlledPrefixKernel P β) initial
    (controlledNormalizedImportanceScore β π score cap)
    (controlledNormalizedImportanceScore_mem_Icc
      hoverlap hratio hcap hscore) n
  change
    (trajectoryMeasure (controlledPrefixKernel P β) initial)[
        observedTrajectoryScore
          (controlledNormalizedImportanceScore β π score cap) n |
        Filtration.piLE
          (X := fun _ : ℕ ↦ ControlledObservation Z A) n] =ᵐ[
      trajectoryMeasure (controlledPrefixKernel P β) initial]
        controlledTargetConditionalMean P π score cap n
  filter_upwards [hcond] with x hx
  rw [hx]
  exact conditionalTrajectoryRisk_controlledNormalizedImportanceScore
    P β π score cap hoverlap n x

/-- The observed importance-weighted score is revealed at the next augmented
path coordinate. -/
theorem controlledObservedImportanceScore_incrementAdapted
    (β : BehaviorPolicy Z A) (π : TargetPolicy Z A)
    (score : ControlledTransitionScore Z A) (cap : ℝ) :
    AnytimeValid.IncrementAdapted
      (Filtration.piLE
        (X := fun _ : ℕ ↦ ControlledObservation Z A))
      (controlledObservedImportanceScore β π score cap) := by
  intro n
  exact stronglyMeasurable_observedTrajectoryScore_succ
    (controlledNormalizedImportanceScore β π score cap) n

/-- The exact normalized target-policy conditional score is predictable from
the current augmented prefix. -/
theorem controlledTargetConditionalMean_stronglyAdapted
    (P : Z → A → PMF Z) (β : BehaviorPolicy Z A)
    (π : TargetPolicy Z A) (score : ControlledTransitionScore Z A)
    (cap : ℝ) (hoverlap : ControlledPolicyOverlap β π) :
    StronglyAdapted
      (Filtration.piLE
        (X := fun _ : ℕ ↦ ControlledObservation Z A))
      (controlledTargetConditionalMean P π score cap) := by
  intro n
  have hmeas := stronglyMeasurable_conditionalTrajectoryRisk
    (controlledPrefixKernel P β)
    (controlledNormalizedImportanceScore β π score cap) n
  have heq :
      controlledTargetConditionalMean P π score cap n =
        conditionalTrajectoryRisk (controlledPrefixKernel P β)
          (controlledNormalizedImportanceScore β π score cap) n := by
    funext x
    exact (conditionalTrajectoryRisk_controlledNormalizedImportanceScore
      P β π score cap hoverlap n x).symm
  rw [heq]
  exact hmeas

/-- Catalog-level interface consumed directly by the finite-hypothesis
predictable-mean PAC--Bayes theorem. -/
theorem controlledImportanceCatalog_predictableMean_interfaces
    [Fintype ι]
    (P : Z → A → PMF Z) (β : BehaviorPolicy Z A)
    (initial : ControlledObservation Z A)
    (π : ι → TargetPolicy Z A)
    (score : ι → ControlledTransitionScore Z A)
    (cap : ι → ℝ)
    (hoverlap : ∀ i, ControlledPolicyOverlap β (π i))
    (hratio : ∀ i, ControlledPolicyRatioBound β (π i) (cap i))
    (hcap : ∀ i, 0 < cap i)
    (hscore : ∀ i n u a y, score i n u a y ∈ Set.Icc (0 : ℝ) 1) :
    (∀ i, AnytimeValid.IncrementAdapted
        (Filtration.piLE
          (X := fun _ : ℕ ↦ ControlledObservation Z A))
        (controlledObservedImportanceScore β (π i) (score i) (cap i))) ∧
      (∀ i, StronglyAdapted
        (Filtration.piLE
          (X := fun _ : ℕ ↦ ControlledObservation Z A))
        (controlledTargetConditionalMean P (π i) (score i) (cap i))) ∧
      (∀ i n x,
        0 ≤ controlledObservedImportanceScore β (π i) (score i) (cap i) n x ∧
          controlledObservedImportanceScore β (π i) (score i) (cap i) n x ≤ 1) ∧
      (∀ i n,
        (controlledTrajectoryMeasure P β initial)[
            controlledObservedImportanceScore β (π i) (score i) (cap i) n |
            Filtration.piLE
              (X := fun _ : ℕ ↦ ControlledObservation Z A) n] =ᵐ[
          controlledTrajectoryMeasure P β initial]
            controlledTargetConditionalMean P (π i) (score i) (cap i) n) := by
  refine ⟨fun i ↦ controlledObservedImportanceScore_incrementAdapted
      β (π i) (score i) (cap i), ?_, ?_, ?_⟩
  · exact fun i ↦ controlledTargetConditionalMean_stronglyAdapted
      P β (π i) (score i) (cap i) (hoverlap i)
  · intro i n x
    exact observedTrajectoryScore_mem_Icc
      (controlledNormalizedImportanceScore_mem_Icc
        (hoverlap i) (hratio i) (hcap i) (hscore i)) n x
  · exact fun i n ↦ controlledObservedImportanceScore_condExp
      P β initial (π i) (score i) (cap i)
      (hoverlap i) (hratio i) (hcap i) (hscore i) n


end

end FormalSLT.StochasticDynamics
