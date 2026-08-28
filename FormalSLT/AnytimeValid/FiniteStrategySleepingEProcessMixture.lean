/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.AnytimeValid.CountableSleepingEProcessMixture

/-!
# Finite strategy mixtures with countably many sleeping wakes

This module builds the two-axis master needed to distinguish strategy
selection from wake-time selection.  For a finite strategy prior `q`, the
master is a finite mixture of exact countable sleeping-wake mixtures:

`sum_a q(a) * (tail(n) + sum_{w<n} p(w) E(a,w,n))`.

When `q` is normalized, this is exactly

`tail(n) + sum_{w<n} p(w) * sum_a q(a) E(a,w,n)`.

Thus each finite-time value admits an exact finite-sum formula plus a
closed-form wake tail despite the countable wake axis.  One master competes
with every active `(strategy, wake)` component in the supplied finite catalog
and pays the exact product-prior log cost.  This is a genuine process mixture,
not a confidence-allocation union bound.  The strategy catalog is still finite
and predeclared; no coin-betting or parameter-free claim is made here.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid.AllocationLogLog
open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

variable {A Omega : Type*}

/-- A finite strategy mixture whose component for each strategy is the exact
polynomial-tail mixture over countably many sleeping wake times. -/
def finiteStrategySleepingProcessMixture [Fintype A]
    (strategyWeight : A -> Real)
    (E : A -> Nat -> Nat -> Omega -> Real) : Nat -> Omega -> Real :=
  finiteWeightedProcess strategyWeight
    (fun a => countableSleepingProcessMixture (E a))

/-- The expanded exact finite-time formula. -/
theorem finiteStrategySleepingProcessMixture_eq
    [Fintype A]
    (strategyWeight : A -> Real)
    (E : A -> Nat -> Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) :
    finiteStrategySleepingProcessMixture strategyWeight E n omega =
      ∑ a : A, strategyWeight a *
        (polynomialSleepingTail n +
          ∑ w ∈ Finset.range n,
            polynomialEpochWeight w * E a w n omega) := by
  rfl

/-- With normalized strategy weights, the nested implementation is exactly a
single polynomial wake tail plus a finite active-wake sum of finite strategy
mixtures. -/
theorem finiteStrategySleepingProcessMixture_eq_tail_add_sum
    [Fintype A]
    (strategyWeight : A -> Real)
    (hweight_sum_one : ∑ a : A, strategyWeight a = 1)
    (E : A -> Nat -> Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) :
    finiteStrategySleepingProcessMixture strategyWeight E n omega =
      polynomialSleepingTail n +
        ∑ w ∈ Finset.range n, polynomialEpochWeight w *
          ∑ a : A, strategyWeight a * E a w n omega := by
  classical
  unfold finiteStrategySleepingProcessMixture finiteWeightedProcess
    countableSleepingProcessMixture
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  calc
    (∑ a : A, strategyWeight a * polynomialSleepingTail n) +
          ∑ a : A, strategyWeight a *
            ∑ w ∈ Finset.range n,
              polynomialEpochWeight w * E a w n omega =
        polynomialSleepingTail n +
          ∑ a : A, strategyWeight a *
            ∑ w ∈ Finset.range n,
              polynomialEpochWeight w * E a w n omega := by
      rw [← Finset.sum_mul, hweight_sum_one, one_mul]
    _ = polynomialSleepingTail n +
          ∑ a : A, ∑ w ∈ Finset.range n,
            strategyWeight a *
              (polynomialEpochWeight w * E a w n omega) := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
    _ = polynomialSleepingTail n +
          ∑ w ∈ Finset.range n, ∑ a : A,
            strategyWeight a *
              (polynomialEpochWeight w * E a w n omega) := by
      congr 1
      rw [Finset.sum_comm]
    _ = polynomialSleepingTail n +
          ∑ w ∈ Finset.range n, polynomialEpochWeight w *
            ∑ a : A, strategyWeight a * E a w n omega := by
      congr 1
      apply Finset.sum_congr rfl
      intro w _hw
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      ring

/-- Pointwise nonnegativity of the two-axis master. -/
theorem finiteStrategySleepingProcessMixture_nonneg
    [Fintype A]
    {strategyWeight : A -> Real}
    (hweight : forall a, 0 <= strategyWeight a)
    {E : A -> Nat -> Nat -> Omega -> Real}
    (hE : forall a w n omega, 0 <= E a w n omega) :
    0 <= finiteStrategySleepingProcessMixture strategyWeight E := by
  intro n omega
  unfold finiteStrategySleepingProcessMixture finiteWeightedProcess
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg (hweight a)
      (countableSleepingProcessMixture_nonneg (hE a) n omega)

variable {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
  {F : Filtration Nat mOmega}

/-- A normalized finite strategy mixture of exact sleeping-wake e-processes is
itself one e-process. -/
theorem finiteStrategySleepingProcessMixture_eProcess
    [Fintype A] [DecidableEq A] [IsFiniteMeasure mu]
    {strategyWeight : A -> Real}
    (hweight_nonneg : forall a, 0 <= strategyWeight a)
    (hweight_sum_one : ∑ a : A, strategyWeight a = 1)
    {E : A -> Nat -> Nat -> Omega -> Real}
    (hE : forall a w, EProcess mu F (E a w))
    (hsleep : forall a w n omega, n <= w -> E a w n omega = 1) :
    EProcess mu F
      (finiteStrategySleepingProcessMixture strategyWeight E) := by
  unfold finiteStrategySleepingProcessMixture
  apply finiteWeightedProcess_eProcess hweight_nonneg hweight_sum_one
  intro a
  exact countableSleepingProcessMixture_eProcess
    (hE a) (hsleep a)

/-- Every active strategy--wake atom is dominated by the single two-axis
master after multiplication by its product-prior weight. -/
theorem finiteStrategySleepingProcessMixture_competes
    [Fintype A] [DecidableEq A]
    {strategyWeight : A -> Real}
    (hweight : forall a, 0 <= strategyWeight a)
    {E : A -> Nat -> Nat -> Omega -> Real}
    (hE : forall a w n omega, 0 <= E a w n omega)
    (a : A) {w n : Nat} (hwn : w < n) (omega : Omega) :
    strategyWeight a * polynomialEpochWeight w * E a w n omega <=
      finiteStrategySleepingProcessMixture strategyWeight E n omega := by
  have hinner :
      polynomialEpochWeight w * E a w n omega <=
        countableSleepingProcessMixture (E a) n omega :=
    countableSleepingProcessMixture_competes_of_lt (hE a) hwn omega
  have hweighted :
      strategyWeight a *
          (polynomialEpochWeight w * E a w n omega) <=
        strategyWeight a *
          countableSleepingProcessMixture (E a) n omega :=
    mul_le_mul_of_nonneg_left hinner (hweight a)
  have hsingle :
      strategyWeight a *
          countableSleepingProcessMixture (E a) n omega <=
        ∑ b : A, strategyWeight b *
          countableSleepingProcessMixture (E b) n omega := by
    exact Finset.single_le_sum
      (fun b _ => mul_nonneg (hweight b)
        (countableSleepingProcessMixture_nonneg (hE b) n omega))
      (Finset.mem_univ a)
  calc
    strategyWeight a * polynomialEpochWeight w * E a w n omega =
        strategyWeight a *
          (polynomialEpochWeight w * E a w n omega) := by ring
    _ <= strategyWeight a *
        countableSleepingProcessMixture (E a) n omega := hweighted
    _ <= finiteStrategySleepingProcessMixture strategyWeight E n omega := by
      simpa [finiteStrategySleepingProcessMixture,
        finiteWeightedProcess] using hsingle

/-- Log-wealth regret against an active positive atom is the sum of the
strategy and wake log-prior costs. -/
theorem finiteStrategySleepingProcessMixture_logWealth_regret_le
    [Fintype A] [DecidableEq A]
    {strategyWeight : A -> Real}
    (hweight : forall a, 0 <= strategyWeight a)
    {E : A -> Nat -> Nat -> Omega -> Real}
    (hE : forall a w n omega, 0 <= E a w n omega)
    (a : A) (hweight_pos : 0 < strategyWeight a)
    {w n : Nat} (hwn : w < n) {omega : Omega}
    (hcomponent : 0 < E a w n omega) :
    Real.log (E a w n omega) -
        Real.log
          (finiteStrategySleepingProcessMixture
            strategyWeight E n omega) <=
      -Real.log (strategyWeight a) -
        Real.log (polynomialEpochWeight w) := by
  have hwake : 0 < polynomialEpochWeight w := polynomialEpochWeight_pos w
  have hleft :
      0 < strategyWeight a * polynomialEpochWeight w * E a w n omega :=
    mul_pos (mul_pos hweight_pos hwake) hcomponent
  have hcomp := finiteStrategySleepingProcessMixture_competes
    hweight hE a hwn omega
  have hlog := Real.log_le_log hleft hcomp
  rw [Real.log_mul (mul_pos hweight_pos hwake).ne' hcomponent.ne',
    Real.log_mul hweight_pos.ne' hwake.ne'] at hlog
  linarith

end

end FormalSLT.AnytimeValid
