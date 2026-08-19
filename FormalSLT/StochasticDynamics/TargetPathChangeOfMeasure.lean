/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.PrefixDynamicTargetPolicyComparator

/-!
# Finite-horizon target-path change of measure

This file gives the target-law counterpart to the encountered-prefix dynamic
comparator.  A history/time-dependent target policy is run through the same
known prefix-dependent environment as the behavior policy.  At a finite
horizon, its prefix expectation is exactly the behavior-prefix expectation
weighted by the product of target-to-behavior action likelihood ratios.

The result is finite-horizon and finite-state/action.  It does not assert an
anytime-valid full-trajectory importance-sampling bound: under a one-step
ratio cap `C`, the cumulative weight has the explicit worst-case range
inflation `C ^ n`.
-/

open Finset Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Z A : Type*}
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- Extend a controlled prefix through time `n` by one action--outcome
coordinate at time `n + 1`. -/
def controlledPrefixSnoc {n : ℕ}
    (u : (i : Finset.Iic n) → ControlledObservation Z A)
    (next : ControlledObservation Z A) :
    (i : Finset.Iic (n + 1)) → ControlledObservation Z A :=
  fun i ↦ if h : i.1 ≤ n then u ⟨i.1, Finset.mem_Iic.mpr h⟩ else next

/-- Restrict a constant-type controlled prefix along `k ≤ n`.  This wrapper
avoids exposing the dependent-family argument of `Preorder.frestrictLe₂` in
the public controlled API. -/
def controlledPrefixRestrict {k n : ℕ} (h : k ≤ n)
    (u : (i : Finset.Iic n) → ControlledObservation Z A) :
    (i : Finset.Iic k) → ControlledObservation Z A :=
  fun i ↦ u ⟨i.1, Finset.mem_Iic.mpr ((Finset.mem_Iic.mp i.2).trans h)⟩

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
@[simp]
lemma controlledPrefixRestrict_refl {n : ℕ}
    (u : (i : Finset.Iic n) → ControlledObservation Z A) :
    controlledPrefixRestrict (le_rfl : n ≤ n) u = u := by
  funext i
  rfl

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
@[simp]
lemma controlledPrefixSnoc_last {n : ℕ}
    (u : (i : Finset.Iic n) → ControlledObservation Z A)
    (next : ControlledObservation Z A) :
    controlledPrefixSnoc u next
        ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ = next := by
  simp [controlledPrefixSnoc]

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
@[simp]
lemma controlledPrefixRestrict_snoc {k n : ℕ} (h : k ≤ n)
    (u : (i : Finset.Iic n) → ControlledObservation Z A)
    (next : ControlledObservation Z A) :
    controlledPrefixRestrict (h.trans (Nat.le_succ n))
        (controlledPrefixSnoc u next) =
      controlledPrefixRestrict h u := by
  funext i
  simp [controlledPrefixRestrict, controlledPrefixSnoc,
    (Finset.mem_Iic.mp i.2).trans h]

/-- The infinite target trajectory law under the same prefix-dependent
environment as the behavior law. -/
def prefixControlledTargetTrajectoryMeasure
    (Q : PrefixControlledEnvironment Z A) (pi : TargetPolicy Z A)
    (initial : ControlledObservation Z A) :
    Measure (ℕ → ControlledObservation Z A) :=
  prefixControlledTrajectoryMeasure Q pi initial

instance prefixControlledTargetTrajectoryMeasure.instIsProbabilityMeasure
    (Q : PrefixControlledEnvironment Z A) (pi : TargetPolicy Z A)
    (initial : ControlledObservation Z A) :
    IsProbabilityMeasure
      (prefixControlledTargetTrajectoryMeasure Q pi initial) := by
  unfold prefixControlledTargetTrajectoryMeasure
  infer_instance

/-- Exact finite-prefix expectation generated recursively by the policy and
the prefix-dependent environment.  The horizon-`n` prefix contains
coordinates `0,...,n`; coordinate zero is the supplied deterministic initial
action--outcome pair, and the recursion makes `n` policy decisions.

Every function on this finite prefix type is bounded and measurable. -/
def controlledFinitePrefixExpectation
    (Q : PrefixControlledEnvironment Z A) (policy : TargetPolicy Z A)
    (initial : ControlledObservation Z A) :
    (n : ℕ) →
      (((i : Finset.Iic n) → ControlledObservation Z A) → ℝ) → ℝ
  | 0, f => f (fun _ ↦ initial)
  | n + 1, f =>
      controlledFinitePrefixExpectation Q policy initial n fun u ↦
        ∑ next : ControlledObservation Z A,
          (prefixControlledContinuationPMF Q policy n u next).toReal *
            f (controlledPrefixSnoc u next)

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
private lemma controlledPrefixSnoc_frestrictLe
    {n : ℕ} (x : ℕ → ControlledObservation Z A) :
    controlledPrefixSnoc (Preorder.frestrictLe n x) (x (n + 1)) =
      Preorder.frestrictLe (n + 1) x := by
  funext i
  by_cases hi : i.1 ≤ n
  · simp [Preorder.frestrictLe_apply, controlledPrefixSnoc, hi]
  · have hieq : i.1 = n + 1 := by
      have hi_le : i.1 ≤ n + 1 := Finset.mem_Iic.mp i.2
      omega
    simp [Preorder.frestrictLe_apply, controlledPrefixSnoc, hieq]

/-- Turn a function of the terminal finite prefix into a generic trajectory
score.  Only its value at the declared terminal step is used below. -/
private def controlledTerminalPrefixScore
    (n : ℕ)
    (f : ((i : Finset.Iic (n + 1)) → ControlledObservation Z A) → ℝ) :
    TrajectoryScore (ControlledObservation Z A) :=
  fun k u next ↦
    if h : k = n then
      f (cast
        (congrArg
          (fun m : ℕ ↦
            (i : Finset.Iic (m + 1)) → ControlledObservation Z A) h)
        (controlledPrefixSnoc u next))
    else 0

/-- A one-step continuation integral under `Kernel.traj` is the explicit
finite sum used by `controlledFinitePrefixExpectation`. -/
private theorem integral_prefix_succ_traj_eq_sum
    (Q : PrefixControlledEnvironment Z A) (policy : TargetPolicy Z A)
    (n : ℕ) (u : (i : Finset.Iic n) → ControlledObservation Z A)
    (f : ((i : Finset.Iic (n + 1)) → ControlledObservation Z A) → ℝ) :
    (∫ x,
        f (Preorder.frestrictLe (n + 1) x)
      ∂Kernel.traj
        (X := fun _ : ℕ ↦ ControlledObservation Z A)
        (prefixControlledPrefixKernel Q policy) n u) =
      ∑ next : ControlledObservation Z A,
        (prefixControlledContinuationPMF Q policy n u next).toReal *
          f (controlledPrefixSnoc u next) := by
  classical
  let score := controlledTerminalPrefixScore n f
  have hscore_at (v : (i : Finset.Iic n) → ControlledObservation Z A)
      (next : ControlledObservation Z A) :
      score n v next = f (controlledPrefixSnoc v next) := by
    simp [score, controlledTerminalPrefixScore]
  have hobserved :
      (fun x : ℕ → ControlledObservation Z A ↦
        f (Preorder.frestrictLe (n + 1) x)) =
      observedTrajectoryScore score n := by
    funext x
    rw [show observedTrajectoryScore score n x =
        score n (Preorder.frestrictLe n x) (x (n + 1)) by rfl,
      hscore_at, controlledPrefixSnoc_frestrictLe]
  calc
    (∫ x, f (Preorder.frestrictLe (n + 1) x)
      ∂Kernel.traj
        (X := fun _ : ℕ ↦ ControlledObservation Z A)
        (prefixControlledPrefixKernel Q policy) n u) =
        ∫ x, observedTrajectoryScore score n x
          ∂Kernel.traj
            (X := fun _ : ℕ ↦ ControlledObservation Z A)
            (prefixControlledPrefixKernel Q policy) n u := by
          rw [hobserved]
    _ = ∫ next, score n u next
        ∂prefixControlledPrefixKernel Q policy n u :=
      integral_observedTrajectoryScore_traj
        (prefixControlledPrefixKernel Q policy) score n u
    _ = ∫ next, f (controlledPrefixSnoc u next)
        ∂prefixControlledPrefixKernel Q policy n u := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun next ↦ hscore_at u next
    _ = ∑ next : ControlledObservation Z A,
        (prefixControlledContinuationPMF Q policy n u next).toReal *
          f (controlledPrefixSnoc u next) := by
      change
        (∫ next, f (controlledPrefixSnoc u next)
          ∂(prefixControlledContinuationPMF Q policy n u).toMeasure) = _
      simpa only [smul_eq_mul] using
        (PMF.integral_eq_sum
          (prefixControlledContinuationPMF Q policy n u)
          (fun next ↦ f (controlledPrefixSnoc u next)))

/-- Restricting the one-step trajectory continuation to its completed prefix
turns the preceding infinite-trajectory integral into the corresponding
`partialTraj` integral. -/
private theorem integral_prefix_succ_partialTraj_eq_sum
    (Q : PrefixControlledEnvironment Z A) (policy : TargetPolicy Z A)
    (n : ℕ) (u : (i : Finset.Iic n) → ControlledObservation Z A)
    (f : ((i : Finset.Iic (n + 1)) → ControlledObservation Z A) → ℝ) :
    (∫ v, f v
      ∂Kernel.partialTraj
        (X := fun _ : ℕ ↦ ControlledObservation Z A)
        (prefixControlledPrefixKernel Q policy) n (n + 1) u) =
      ∑ next : ControlledObservation Z A,
        (prefixControlledContinuationPMF Q policy n u next).toReal *
          f (controlledPrefixSnoc u next) := by
  rw [← Kernel.traj_map_frestrictLe_apply
    (X := fun _ : ℕ ↦ ControlledObservation Z A)
    (κ := prefixControlledPrefixKernel Q policy) n (n + 1) u]
  have hf : Integrable f
      ((Kernel.traj
        (X := fun _ : ℕ ↦ ControlledObservation Z A)
        (prefixControlledPrefixKernel Q policy) n u).map
          (Preorder.frestrictLe (n + 1))) :=
    Integrable.of_finite
  rw [MeasureTheory.integral_map
    (Preorder.measurable_frestrictLe (X := fun _ : ℕ ↦ ControlledObservation Z A)
      (n + 1)).aemeasurable hf.aestronglyMeasurable]
  exact integral_prefix_succ_traj_eq_sum Q policy n u f

/-- The recursive finite-prefix expectation is exactly integration against
mathlib's finite Ionescu--Tulcea marginal `Kernel.partialTraj`. -/
theorem controlledFinitePrefixExpectation_eq_partialTrajIntegral
    (Q : PrefixControlledEnvironment Z A) (policy : TargetPolicy Z A)
    (initial : ControlledObservation Z A) (n : ℕ)
    (f : ((i : Finset.Iic n) → ControlledObservation Z A) → ℝ) :
    controlledFinitePrefixExpectation Q policy initial n f =
      ∫ u, f u
        ∂Kernel.partialTraj
          (X := fun _ : ℕ ↦ ControlledObservation Z A)
          (prefixControlledPrefixKernel Q policy) 0 n
          (fun _ ↦ initial) := by
  induction n with
  | zero =>
      simp [controlledFinitePrefixExpectation, Kernel.id]
  | succ n ih =>
      unfold controlledFinitePrefixExpectation
      rw [ih]
      rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n)]
      rw [Kernel.integral_comp (Integrable.of_finite :
        Integrable f
          ((Kernel.partialTraj
              (X := fun _ : ℕ ↦ ControlledObservation Z A)
              (prefixControlledPrefixKernel Q policy) n (n + 1) ∘ₖ
            Kernel.partialTraj
              (X := fun _ : ℕ ↦ ControlledObservation Z A)
              (prefixControlledPrefixKernel Q policy) 0 n)
            (fun _ ↦ initial)))]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u ↦
        (integral_prefix_succ_partialTraj_eq_sum Q policy n u f).symm

/-- Every finite-prefix expectation is the corresponding cylinder-function
integral under the actual infinite Ionescu--Tulcea target law. -/
theorem controlledFinitePrefixExpectation_eq_trajectoryIntegral
    (Q : PrefixControlledEnvironment Z A) (policy : TargetPolicy Z A)
    (initial : ControlledObservation Z A) (n : ℕ)
    (f : ((i : Finset.Iic n) → ControlledObservation Z A) → ℝ) :
    controlledFinitePrefixExpectation Q policy initial n f =
      ∫ x, f (Preorder.frestrictLe n x)
        ∂prefixControlledTargetTrajectoryMeasure Q policy initial := by
  rw [controlledFinitePrefixExpectation_eq_partialTrajIntegral]
  unfold prefixControlledTargetTrajectoryMeasure
    prefixControlledTrajectoryMeasure trajectoryMeasure
  rw [← Kernel.traj_map_frestrictLe_apply
    (X := fun _ : ℕ ↦ ControlledObservation Z A)
    (κ := prefixControlledPrefixKernel Q policy) 0 n (fun _ ↦ initial)]
  have hf : Integrable f
      ((Kernel.traj
        (X := fun _ : ℕ ↦ ControlledObservation Z A)
        (prefixControlledPrefixKernel Q policy) 0 (fun _ ↦ initial)).map
          (Preorder.frestrictLe n)) :=
    Integrable.of_finite
  exact MeasureTheory.integral_map
    (Preorder.measurable_frestrictLe (X := fun _ : ℕ ↦ ControlledObservation Z A)
      n).aemeasurable hf.aestronglyMeasurable

private theorem sum_pmf_toReal_eq_one
    {Omega : Type*} [Fintype Omega] (p : PMF Omega) :
    ∑ omega : Omega, (p omega).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun omega _homega ↦ p.apply_ne_top omega)]
  have hsum : ∑ omega : Omega, p omega = 1 := by
    simpa only [tsum_fintype] using p.tsum_coe
  rw [hsum, ENNReal.toReal_one]

omit [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The recursively generated finite-prefix law is normalized at every
horizon. -/
theorem controlledFinitePrefixExpectation_one
    (Q : PrefixControlledEnvironment Z A) (policy : TargetPolicy Z A)
    (initial : ControlledObservation Z A) (n : ℕ) :
    controlledFinitePrefixExpectation Q policy initial n (fun _u ↦ 1) = 1 := by
  classical
  induction n with
  | zero => simp [controlledFinitePrefixExpectation]
  | succ n ih =>
      unfold controlledFinitePrefixExpectation
      have hinner :
          (fun u : (i : Finset.Iic n) → ControlledObservation Z A ↦
            ∑ next : ControlledObservation Z A,
              (prefixControlledContinuationPMF Q policy n u next).toReal *
                (fun _u ↦ (1 : ℝ)) (controlledPrefixSnoc u next)) =
            fun _u ↦ 1 := by
        funext u
        simpa using sum_pmf_toReal_eq_one
          (prefixControlledContinuationPMF Q policy n u)
      rw [hinner, ih]

/-- Product of target-to-behavior action likelihood ratios along a completed
finite prefix.  Environment probabilities cancel because target and behavior
use the same prefix-dependent environment row after each action. -/
def controlledFinitePrefixLikelihoodRatio
    (beta : BehaviorPolicy Z A) (pi : TargetPolicy Z A)
    (n : ℕ) (u : (i : Finset.Iic n) → ControlledObservation Z A) : ℝ :=
  ∏ k ∈ Finset.range n,
    if hk : k < n then
      controlledImportanceRatio beta pi k
        (controlledPrefixRestrict (Nat.le_of_lt hk) u)
        (u ⟨k + 1, Finset.mem_Iic.mpr hk⟩).1
    else 1

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Appending one coordinate multiplies the previous prefix weight by the
new one-step action likelihood ratio. -/
theorem controlledFinitePrefixLikelihoodRatio_snoc
    (beta : BehaviorPolicy Z A) (pi : TargetPolicy Z A)
    {n : ℕ} (u : (i : Finset.Iic n) → ControlledObservation Z A)
    (next : ControlledObservation Z A) :
    controlledFinitePrefixLikelihoodRatio beta pi (n + 1)
        (controlledPrefixSnoc u next) =
      controlledFinitePrefixLikelihoodRatio beta pi n u *
        controlledImportanceRatio beta pi n u next.1 := by
  classical
  unfold controlledFinitePrefixLikelihoodRatio
  rw [Finset.prod_range_succ]
  have hprod :
      (∏ k ∈ Finset.range n,
          if hk : k < n + 1 then
            controlledImportanceRatio beta pi k
              (controlledPrefixRestrict (Nat.le_of_lt hk)
                (controlledPrefixSnoc u next))
              ((controlledPrefixSnoc u next)
                ⟨k + 1, Finset.mem_Iic.mpr hk⟩).1
          else 1) =
        ∏ k ∈ Finset.range n,
          if hk : k < n then
            controlledImportanceRatio beta pi k
              (controlledPrefixRestrict (Nat.le_of_lt hk) u)
              (u ⟨k + 1, Finset.mem_Iic.mpr hk⟩).1
          else 1 := by
    apply Finset.prod_congr rfl
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    rw [dif_pos hkn, dif_pos (hkn.trans (Nat.lt_succ_self n))]
    have hprefix := controlledPrefixRestrict_snoc
      (Nat.le_of_lt hkn) u next
    rw [hprefix]
    simp [controlledPrefixSnoc, hkn]
  rw [hprod, dif_pos (Nat.lt_succ_self n)]
  have hlastPrefix :
      controlledPrefixRestrict (Nat.le_of_lt (Nat.lt_succ_self n))
          (controlledPrefixSnoc u next) = u := by
    exact controlledPrefixRestrict_snoc (le_rfl : n ≤ n) u next
  rw [hlastPrefix, controlledPrefixSnoc_last]

omit [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- One-step target expectation equals the likelihood-weighted behavior
expectation.  This is the local cancellation used in the pathwise induction. -/
theorem prefixControlledContinuation_expectation_changeOfMeasure
    (Q : PrefixControlledEnvironment Z A)
    (beta : BehaviorPolicy Z A) (pi : TargetPolicy Z A)
    (hoverlap : ControlledPolicyOverlap beta pi)
    (n : ℕ) (u : (i : Finset.Iic n) → ControlledObservation Z A)
    (f : ControlledObservation Z A → ℝ) :
    (∑ next : ControlledObservation Z A,
        (prefixControlledContinuationPMF Q pi n u next).toReal * f next) =
      ∑ next : ControlledObservation Z A,
        (prefixControlledContinuationPMF Q beta n u next).toReal *
          (controlledImportanceRatio beta pi n u next.1 * f next) := by
  classical
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro y _hy
  simp only [prefixControlledContinuationPMF_apply, ENNReal.toReal_mul]
  have hcancel :
      (beta n u a).toReal * controlledImportanceRatio beta pi n u a =
        (pi n u a).toReal := by
    exact mul_ratio_eq_of_zero_imp_zero (hoverlap n u a)
  rw [← hcancel]
  ring

omit [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Finite-horizon path change of measure.  For every real function of the
completed prefix through time `n`, target expectation equals behavior
expectation weighted by the cumulative action likelihood ratio. -/
theorem controlledFinitePrefixExpectation_changeOfMeasure
    (Q : PrefixControlledEnvironment Z A)
    (beta : BehaviorPolicy Z A) (pi : TargetPolicy Z A)
    (initial : ControlledObservation Z A)
    (hoverlap : ControlledPolicyOverlap beta pi)
    (n : ℕ)
    (f : ((i : Finset.Iic n) → ControlledObservation Z A) → ℝ) :
    controlledFinitePrefixExpectation Q pi initial n f =
      controlledFinitePrefixExpectation Q beta initial n fun u ↦
        controlledFinitePrefixLikelihoodRatio beta pi n u * f u := by
  classical
  induction n with
  | zero =>
      simp [controlledFinitePrefixExpectation,
        controlledFinitePrefixLikelihoodRatio]
  | succ n ih =>
      unfold controlledFinitePrefixExpectation
      rw [ih]
      apply congrArg
        (controlledFinitePrefixExpectation Q beta initial n)
      funext u
      rw [prefixControlledContinuation_expectation_changeOfMeasure
        Q beta pi hoverlap n u
          (fun next ↦ f (controlledPrefixSnoc u next))]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro next _hnext
      change
        controlledFinitePrefixLikelihoodRatio beta pi n u *
            ((prefixControlledContinuationPMF Q beta n u next).toReal *
              (controlledImportanceRatio beta pi n u next.1 *
                f (controlledPrefixSnoc u next))) =
          (prefixControlledContinuationPMF Q beta n u next).toReal *
            (controlledFinitePrefixLikelihoodRatio beta pi (n + 1)
                (controlledPrefixSnoc u next) *
              f (controlledPrefixSnoc u next))
      rw [controlledFinitePrefixLikelihoodRatio_snoc]
      ring

/-- Actual infinite-trajectory form of finite-horizon change of measure.  The
integrands inspect only coordinates through `n`, but both sides integrate
against the infinite Ionescu--Tulcea path laws. -/
theorem prefixControlledTargetTrajectory_integral_changeOfMeasure
    (Q : PrefixControlledEnvironment Z A)
    (beta : BehaviorPolicy Z A) (pi : TargetPolicy Z A)
    (initial : ControlledObservation Z A)
    (hoverlap : ControlledPolicyOverlap beta pi)
    (n : ℕ)
    (f : ((i : Finset.Iic n) → ControlledObservation Z A) → ℝ) :
    (∫ x, f (Preorder.frestrictLe n x)
      ∂prefixControlledTargetTrajectoryMeasure Q pi initial) =
      ∫ x,
        controlledFinitePrefixLikelihoodRatio beta pi n
            (Preorder.frestrictLe n x) *
          f (Preorder.frestrictLe n x)
        ∂prefixControlledTrajectoryMeasure Q beta initial := by
  calc
    (∫ x, f (Preorder.frestrictLe n x)
      ∂prefixControlledTargetTrajectoryMeasure Q pi initial) =
        controlledFinitePrefixExpectation Q pi initial n f :=
      (controlledFinitePrefixExpectation_eq_trajectoryIntegral
        Q pi initial n f).symm
    _ = controlledFinitePrefixExpectation Q beta initial n fun u ↦
          controlledFinitePrefixLikelihoodRatio beta pi n u * f u :=
      controlledFinitePrefixExpectation_changeOfMeasure
        Q beta pi initial hoverlap n f
    _ = ∫ x,
          controlledFinitePrefixLikelihoodRatio beta pi n
              (Preorder.frestrictLe n x) *
            f (Preorder.frestrictLe n x)
          ∂prefixControlledTargetTrajectoryMeasure Q beta initial :=
      controlledFinitePrefixExpectation_eq_trajectoryIntegral
        Q beta initial n (fun u ↦
          controlledFinitePrefixLikelihoodRatio beta pi n u * f u)
    _ = ∫ x,
          controlledFinitePrefixLikelihoodRatio beta pi n
              (Preorder.frestrictLe n x) *
            f (Preorder.frestrictLe n x)
          ∂prefixControlledTrajectoryMeasure Q beta initial := rfl

/-- The cylinder in the infinite controlled path space determined by a set of
completed prefixes through time `n`. -/
def controlledTrajectoryCylinder
    (n : ℕ)
    (event : Set ((i : Finset.Iic n) → ControlledObservation Z A)) :
    Set (ℕ → ControlledObservation Z A) :=
  {x | Preorder.frestrictLe n x ∈ event}

theorem measurableSet_controlledTrajectoryCylinder
    (n : ℕ)
    (event : Set ((i : Finset.Iic n) → ControlledObservation Z A)) :
    MeasurableSet (controlledTrajectoryCylinder n event) := by
  exact (Set.toFinite event).measurableSet.preimage
    (Preorder.measurable_frestrictLe
      (X := fun _ : ℕ ↦ ControlledObservation Z A) n)

/-- Cylinder-event version of the actual infinite-trajectory change of
measure theorem. -/
theorem prefixControlledTargetTrajectory_cylinder_changeOfMeasure
    (Q : PrefixControlledEnvironment Z A)
    (beta : BehaviorPolicy Z A) (pi : TargetPolicy Z A)
    (initial : ControlledObservation Z A)
    (hoverlap : ControlledPolicyOverlap beta pi)
    (n : ℕ)
    (event : Set ((i : Finset.Iic n) → ControlledObservation Z A)) :
    (prefixControlledTargetTrajectoryMeasure Q pi initial).real
        (controlledTrajectoryCylinder n event) =
      ∫ x,
        controlledFinitePrefixLikelihoodRatio beta pi n
            (Preorder.frestrictLe n x) *
          Set.indicator event (fun _u ↦ 1)
            (Preorder.frestrictLe n x)
        ∂prefixControlledTrajectoryMeasure Q beta initial := by
  calc
    (prefixControlledTargetTrajectoryMeasure Q pi initial).real
        (controlledTrajectoryCylinder n event) =
        ∫ x,
          Set.indicator (controlledTrajectoryCylinder n event)
            (fun _x ↦ (1 : ℝ)) x
          ∂prefixControlledTargetTrajectoryMeasure Q pi initial := by
            symm
            rw [show (fun _x : ℕ → ControlledObservation Z A ↦
                (1 : ℝ)) = (1 : (ℕ → ControlledObservation Z A) → ℝ) by
              funext _x
              rfl]
            exact integral_indicator_one
              (measurableSet_controlledTrajectoryCylinder n event)
    _ = ∫ x,
          Set.indicator event (fun _u ↦ (1 : ℝ))
            (Preorder.frestrictLe n x)
          ∂prefixControlledTargetTrajectoryMeasure Q pi initial := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x ↦ by
              simp [controlledTrajectoryCylinder, Set.indicator]
    _ = ∫ x,
          controlledFinitePrefixLikelihoodRatio beta pi n
              (Preorder.frestrictLe n x) *
            Set.indicator event (fun _u ↦ 1)
              (Preorder.frestrictLe n x)
          ∂prefixControlledTrajectoryMeasure Q beta initial :=
      prefixControlledTargetTrajectory_integral_changeOfMeasure
        Q beta pi initial hoverlap n
          (Set.indicator event fun _u ↦ 1)

/-- Finite-horizon path risk for an arbitrary real terminal-prefix loss. -/
def controlledFiniteHorizonRisk
    (Q : PrefixControlledEnvironment Z A) (policy : TargetPolicy Z A)
    (initial : ControlledObservation Z A) (n : ℕ)
    (loss : ((i : Finset.Iic n) → ControlledObservation Z A) → ℝ) : ℝ :=
  controlledFinitePrefixExpectation Q policy initial n loss

omit [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Exact finite-horizon target-risk identity under behavior-path weighting. -/
theorem controlledFiniteHorizonRisk_changeOfMeasure
    (Q : PrefixControlledEnvironment Z A)
    (beta : BehaviorPolicy Z A) (pi : TargetPolicy Z A)
    (initial : ControlledObservation Z A)
    (hoverlap : ControlledPolicyOverlap beta pi)
    (n : ℕ)
    (loss : ((i : Finset.Iic n) → ControlledObservation Z A) → ℝ) :
    controlledFiniteHorizonRisk Q pi initial n loss =
      controlledFinitePrefixExpectation Q beta initial n fun u ↦
        controlledFinitePrefixLikelihoodRatio beta pi n u * loss u :=
  controlledFinitePrefixExpectation_changeOfMeasure
    Q beta pi initial hoverlap n loss

/-- Finite-prefix event probability under a policy. -/
def controlledFinitePrefixEventProbability
    (Q : PrefixControlledEnvironment Z A) (policy : TargetPolicy Z A)
    (initial : ControlledObservation Z A) (n : ℕ)
    (event : Set ((i : Finset.Iic n) → ControlledObservation Z A)) : ℝ :=
  controlledFinitePrefixExpectation Q policy initial n
    (Set.indicator event fun _u ↦ 1)

omit [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Cylinder/event form of finite-horizon change of measure. -/
theorem controlledFinitePrefixEventProbability_changeOfMeasure
    (Q : PrefixControlledEnvironment Z A)
    (beta : BehaviorPolicy Z A) (pi : TargetPolicy Z A)
    (initial : ControlledObservation Z A)
    (hoverlap : ControlledPolicyOverlap beta pi)
    (n : ℕ)
    (event : Set ((i : Finset.Iic n) → ControlledObservation Z A)) :
    controlledFinitePrefixEventProbability Q pi initial n event =
      controlledFinitePrefixExpectation Q beta initial n fun u ↦
        controlledFinitePrefixLikelihoodRatio beta pi n u *
          Set.indicator event (fun _u ↦ 1) u := by
  exact controlledFinitePrefixExpectation_changeOfMeasure
    Q beta pi initial hoverlap n _

/-- The recursively defined finite-prefix event probability is the actual
probability of its cylinder under the infinite target trajectory law. -/
theorem controlledFinitePrefixEventProbability_eq_trajectoryCylinderProbability
    (Q : PrefixControlledEnvironment Z A) (policy : TargetPolicy Z A)
    (initial : ControlledObservation Z A) (n : ℕ)
    (event : Set ((i : Finset.Iic n) → ControlledObservation Z A)) :
    controlledFinitePrefixEventProbability Q policy initial n event =
      (prefixControlledTargetTrajectoryMeasure Q policy initial).real
        (controlledTrajectoryCylinder n event) := by
  unfold controlledFinitePrefixEventProbability
  rw [controlledFinitePrefixExpectation_eq_trajectoryIntegral]
  calc
    (∫ x,
        Set.indicator event (fun _u ↦ (1 : ℝ))
          (Preorder.frestrictLe n x)
      ∂prefixControlledTargetTrajectoryMeasure Q policy initial) =
        ∫ x,
          Set.indicator (controlledTrajectoryCylinder n event)
            (fun _x ↦ (1 : ℝ)) x
          ∂prefixControlledTargetTrajectoryMeasure Q policy initial := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x ↦ by
              simp [controlledTrajectoryCylinder, Set.indicator]
    _ = (prefixControlledTargetTrajectoryMeasure Q policy initial).real
        (controlledTrajectoryCylinder n event) := by
          rw [show (fun _x : ℕ → ControlledObservation Z A ↦
              (1 : ℝ)) = (1 : (ℕ → ControlledObservation Z A) → ℝ) by
            funext _x
            rfl]
          exact integral_indicator_one
            (measurableSet_controlledTrajectoryCylinder n event)

/-- Probability that the state component at time `n` equals `z`. -/
def controlledFiniteHorizonStateOccupancy
    (Q : PrefixControlledEnvironment Z A) (policy : TargetPolicy Z A)
    (initial : ControlledObservation Z A) (n : ℕ) (z : Z) : ℝ :=
  controlledFinitePrefixEventProbability Q policy initial n
    {u | (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 = z}

omit [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Exact target occupancy identity under behavior-path weighting. -/
theorem controlledFiniteHorizonStateOccupancy_changeOfMeasure
    (Q : PrefixControlledEnvironment Z A)
    (beta : BehaviorPolicy Z A) (pi : TargetPolicy Z A)
    (initial : ControlledObservation Z A)
    (hoverlap : ControlledPolicyOverlap beta pi)
    (n : ℕ) (z : Z) :
    controlledFiniteHorizonStateOccupancy Q pi initial n z =
      controlledFinitePrefixExpectation Q beta initial n fun u ↦
        controlledFinitePrefixLikelihoodRatio beta pi n u *
          Set.indicator
            {u | (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 = z}
            (fun _u ↦ 1) u := by
  exact controlledFinitePrefixEventProbability_changeOfMeasure
    Q beta pi initial hoverlap n _

/-- Actual infinite-trajectory probability that the state component at time
`n` equals `z`.  The event is written as a finite-prefix cylinder so its
measurability is explicit. -/
def prefixControlledTargetTrajectoryStateOccupancy
    (Q : PrefixControlledEnvironment Z A) (policy : TargetPolicy Z A)
    (initial : ControlledObservation Z A) (n : ℕ) (z : Z) : ℝ :=
  (prefixControlledTargetTrajectoryMeasure Q policy initial).real
    (controlledTrajectoryCylinder n
      {u | (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 = z})

/-- The actual infinite-trajectory occupancy agrees with the recursively
generated finite-horizon occupancy. -/
theorem prefixControlledTargetTrajectoryStateOccupancy_eq_finite
    (Q : PrefixControlledEnvironment Z A) (policy : TargetPolicy Z A)
    (initial : ControlledObservation Z A) (n : ℕ) (z : Z) :
    prefixControlledTargetTrajectoryStateOccupancy
        Q policy initial n z =
      controlledFiniteHorizonStateOccupancy
        Q policy initial n z := by
  unfold prefixControlledTargetTrajectoryStateOccupancy
    controlledFiniteHorizonStateOccupancy
  exact (controlledFinitePrefixEventProbability_eq_trajectoryCylinderProbability
    Q policy initial n _).symm

/-- Exact target state-occupancy identity on the actual infinite path law,
expressed as a likelihood-weighted behavior-path integral. -/
theorem prefixControlledTargetTrajectoryStateOccupancy_changeOfMeasure
    (Q : PrefixControlledEnvironment Z A)
    (beta : BehaviorPolicy Z A) (pi : TargetPolicy Z A)
    (initial : ControlledObservation Z A)
    (hoverlap : ControlledPolicyOverlap beta pi)
    (n : ℕ) (z : Z) :
    prefixControlledTargetTrajectoryStateOccupancy Q pi initial n z =
      ∫ x,
        controlledFinitePrefixLikelihoodRatio beta pi n
            (Preorder.frestrictLe n x) *
          Set.indicator
            {u | (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 = z}
            (fun _u ↦ 1) (Preorder.frestrictLe n x)
        ∂prefixControlledTrajectoryMeasure Q beta initial := by
  unfold prefixControlledTargetTrajectoryStateOccupancy
  exact prefixControlledTargetTrajectory_cylinder_changeOfMeasure
    Q beta pi initial hoverlap n _

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- A common one-step ratio cap inflates the worst-case range of a horizon-`n`
importance weight by `C ^ n`. -/
theorem controlledFinitePrefixLikelihoodRatio_le_pow
    {beta : BehaviorPolicy Z A} {pi : TargetPolicy Z A} {C : ℝ}
    (hoverlap : ControlledPolicyOverlap beta pi)
    (hratio : ControlledPolicyRatioBound beta pi C)
    (hC : 0 ≤ C)
    (n : ℕ) (u : (i : Finset.Iic n) → ControlledObservation Z A) :
    0 ≤ controlledFinitePrefixLikelihoodRatio beta pi n u ∧
      controlledFinitePrefixLikelihoodRatio beta pi n u ≤ C ^ n := by
  classical
  unfold controlledFinitePrefixLikelihoodRatio
  constructor
  · exact Finset.prod_nonneg fun k hk ↦ by
      have hkn : k < n := Finset.mem_range.mp hk
      rw [dif_pos hkn]
      exact controlledImportanceRatio_nonneg beta pi _ _ _
  · calc
      (∏ k ∈ Finset.range n,
          if hk : k < n then
              controlledImportanceRatio beta pi k
              (controlledPrefixRestrict (Nat.le_of_lt hk) u)
              (u ⟨k + 1, Finset.mem_Iic.mpr hk⟩).1
          else 1) ≤
          ∏ _k ∈ Finset.range n, C := by
            apply Finset.prod_le_prod
            · intro k hk
              have hkn : k < n := Finset.mem_range.mp hk
              rw [dif_pos hkn]
              exact controlledImportanceRatio_nonneg beta pi _ _ _
            · intro k hk
              have hkn : k < n := Finset.mem_range.mp hk
              rw [dif_pos hkn]
              exact controlledImportanceRatio_le_cap hoverlap hratio hC
                k (controlledPrefixRestrict (Nat.le_of_lt hkn) u)
                  (u ⟨k + 1, Finset.mem_Iic.mpr hkn⟩).1
      _ = C ^ n := by simp

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Explicit `C ^ n` range receipt for a likelihood-weighted payoff in
`[0,1]`.  This is the range inflation a fixed-horizon concentration theorem
would have to pay without additional structure. -/
theorem controlledWeightedPrefixPayoff_mem_Icc
    {beta : BehaviorPolicy Z A} {pi : TargetPolicy Z A} {C : ℝ}
    (hoverlap : ControlledPolicyOverlap beta pi)
    (hratio : ControlledPolicyRatioBound beta pi C)
    (hC : 0 ≤ C)
    (n : ℕ) (u : (i : Finset.Iic n) → ControlledObservation Z A)
    {f : ((i : Finset.Iic n) → ControlledObservation Z A) → ℝ}
    (hf : f u ∈ Set.Icc (0 : ℝ) 1) :
    controlledFinitePrefixLikelihoodRatio beta pi n u * f u ∈
      Set.Icc (0 : ℝ) (C ^ n) := by
  rcases controlledFinitePrefixLikelihoodRatio_le_pow
      hoverlap hratio hC n u with ⟨hW0, hWC⟩
  constructor
  · exact mul_nonneg hW0 hf.1
  · exact (mul_le_mul hWC hf.2 hf.1 (pow_nonneg hC n)).trans_eq
      (mul_one (C ^ n))

end

end FormalSLT.StochasticDynamics
