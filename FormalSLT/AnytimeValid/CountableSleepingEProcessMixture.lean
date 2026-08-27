/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.AnytimeValid.CountableSleepingPredictableBettingMixture
import FormalSLT.AnytimeValid.ForwardPredictableTiltEmpiricalBernstein
import FormalSLT.AnytimeValid.AllocationLogLog

/-!
# Exact sleeping mixtures of arbitrary e-processes

This module separates the exact finite-tail construction from the
algebraic betting factors used to introduce it.  If component `j` remains
identically one through time `j`, then at time `n` every component `j >= n`
still has value one.  The telescoping polynomial allocation is therefore
exactly a finite active-prefix sum plus the closed-form tail `1 / (n + 1)`.
Its selection price is logarithmic in the wake time, rather than linear.

The final section instantiates this generic construction with FormalSLT's
time-varying predictable-mean empirical-Bernstein process.  Its score uses the
observable forward-predictor residual, rather than the unknown conditional
mean residual appearing in an algebraic betting wealth.  This distinction is
load-bearing: the two squared residuals are not ordered pointwise.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid.AllocationLogLog
open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

variable {Omega : Type*}

/-! ## Exact polynomial-tail process mixture -/

/-- Remaining mass after the first `n` telescoping polynomial weights. -/
def polynomialSleepingTail (n : Nat) : Real :=
  1 / ((n : Real) + 1)

theorem polynomialSleepingTail_pos (n : Nat) :
    0 < polynomialSleepingTail n := by
  unfold polynomialSleepingTail
  positivity

/-- Exact finite representation of a polynomially weighted countable process
mixture when all indices outside the active prefix are still equal to one. -/
def countableSleepingProcessMixture
    (E : Nat -> Nat -> Omega -> Real) (n : Nat) (omega : Omega) : Real :=
  polynomialSleepingTail n +
    ∑ j ∈ Finset.range n, polynomialEpochWeight j * E j n omega

@[simp]
theorem countableSleepingProcessMixture_zero
    (E : Nat -> Nat -> Omega -> Real) (omega : Omega) :
    countableSleepingProcessMixture E 0 omega = 1 := by
  simp [countableSleepingProcessMixture, polynomialSleepingTail]

/-- Pointwise nonnegativity of the exact finite-tail mixture. -/
theorem countableSleepingProcessMixture_nonneg
    {E : Nat -> Nat -> Omega -> Real}
    (hE : forall j n omega, 0 <= E j n omega) :
    0 <= countableSleepingProcessMixture E := by
  intro n omega
  unfold countableSleepingProcessMixture
  exact add_nonneg (polynomialSleepingTail_pos n).le
    (Finset.sum_nonneg fun j _ =>
      mul_nonneg (polynomialEpochWeight_pos j).le (hE j n omega))

/-- The unused polynomial tail makes the finite-tail mixture strictly positive. -/
theorem countableSleepingProcessMixture_pos
    {E : Nat -> Nat -> Omega -> Real}
    (hE : forall j n omega, 0 <= E j n omega)
    (n : Nat) (omega : Omega) :
    0 < countableSleepingProcessMixture E n omega := by
  unfold countableSleepingProcessMixture
  exact add_pos_of_pos_of_nonneg (polynomialSleepingTail_pos n)
    (Finset.sum_nonneg fun j _ =>
      mul_nonneg (polynomialEpochWeight_pos j).le (hE j n omega))

/-- Every component in the active prefix is dominated by the exact mixture
after multiplication by its polynomial prior weight. -/
theorem countableSleepingProcessMixture_competes_of_lt
    {E : Nat -> Nat -> Omega -> Real}
    (hE : forall j n omega, 0 <= E j n omega)
    {j n : Nat} (hjn : j < n) (omega : Omega) :
    polynomialEpochWeight j * E j n omega <=
      countableSleepingProcessMixture E n omega := by
  have hsingle :
      polynomialEpochWeight j * E j n omega <=
        ∑ i ∈ Finset.range n, polynomialEpochWeight i * E i n omega := by
    exact Finset.single_le_sum
      (fun i _ => mul_nonneg (polynomialEpochWeight_pos i).le (hE i n omega))
      (Finset.mem_range.mpr hjn)
  unfold countableSleepingProcessMixture
  exact hsingle.trans (le_add_of_nonneg_left (polynomialSleepingTail_pos n).le)

/-- Log-wealth regret against any positive active component is at most the
negative log of that component's polynomial prior weight. -/
theorem countableSleepingProcessMixture_logWealth_regret_le
    {E : Nat -> Nat -> Omega -> Real}
    (hE : forall j n omega, 0 <= E j n omega)
    {j n : Nat} (hjn : j < n) {omega : Omega}
    (hEj : 0 < E j n omega) :
    Real.log (E j n omega) -
        Real.log (countableSleepingProcessMixture E n omega) <=
      -Real.log (polynomialEpochWeight j) := by
  have hweight : 0 < polynomialEpochWeight j :=
    polynomialEpochWeight_pos j
  have hcomp := countableSleepingProcessMixture_competes_of_lt hE hjn omega
  have hlog := Real.log_le_log (mul_pos hweight hEj) hcomp
  rw [Real.log_mul hweight.ne' hEj.ne'] at hlog
  linarith

/-- The wake-time selection price of the polynomial allocation is logarithmic. -/
theorem polynomialSleepingSelectionCost (j : Nat) :
    -Real.log (polynomialEpochWeight j) =
      Real.log ((j : Real) + 1) + Real.log ((j : Real) + 2) := by
  rw [← polynomialEpochWeight_log_cost]
  rw [one_div, Real.log_inv]

/-- The exact finite-prefix formula equals the mathematical countable
mixture whenever every not-yet-active component is still one. -/
theorem countableSleepingProcessMixture_eq_tsum
    (E : Nat -> Nat -> Omega -> Real)
    (hsleep : forall j n omega, n <= j -> E j n omega = 1)
    (n : Nat) (omega : Omega) :
    countableSleepingProcessMixture E n omega =
      ∑' j : Nat, polynomialEpochWeight j * E j n omega := by
  let f : Nat -> Real := fun j => polynomialEpochWeight j * E j n omega
  have hweight_summable : Summable
      (fun j : Nat => polynomialEpochWeight j) :=
    polynomialEpochWeight_summable
  have htail_eq (i : Nat) :
      f (i + n) = polynomialEpochWeight (i + n) := by
    unfold f
    rw [hsleep (i + n) n omega (Nat.le_add_left n i), mul_one]
  have hshift_summable : Summable (fun i => f (i + n)) := by
    exact ((summable_nat_add_iff n).2 hweight_summable).congr
      (fun i => (htail_eq i).symm)
  have hf : Summable f := (summable_nat_add_iff n).1 hshift_summable
  have hweight_tail :
      (∑' i : Nat, polynomialEpochWeight (i + n)) =
        polynomialSleepingTail n := by
    have hsplit := polynomialEpochWeight_summable.sum_add_tsum_nat_add n
    rw [polynomialEpochWeight_sum_range,
      polynomialEpochWeight_tsum] at hsplit
    unfold polynomialSleepingTail
    linarith
  have htail_tsum :
      (∑' i : Nat, f (i + n)) = polynomialSleepingTail n := by
    calc
      (∑' i : Nat, f (i + n)) =
          ∑' i : Nat, polynomialEpochWeight (i + n) := by
            apply tsum_congr
            exact htail_eq
      _ = polynomialSleepingTail n := hweight_tail
  unfold countableSleepingProcessMixture
  change polynomialSleepingTail n + (∑ j ∈ Finset.range n, f j) = ∑' j, f j
  rw [add_comm, ← htail_tsum]
  exact hf.sum_add_tsum_nat_add n

/-- The exact finite-tail mixture is the generic countable weighted process. -/
theorem countableSleepingProcessMixture_eq_countableWeightedProcess
    (E : Nat -> Nat -> Omega -> Real)
    (hsleep : forall j n omega, n <= j -> E j n omega = 1) :
    countableSleepingProcessMixture E =
      countableWeightedProcess polynomialEpochWeight E := by
  funext n omega
  exact countableSleepingProcessMixture_eq_tsum E hsleep n omega

/-! ## E-process closure -/

variable {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
  {F : Filtration Nat mOmega}

/-- Strong adaptedness is a finite-prefix calculation for the exact
mixture. -/
theorem countableSleepingProcessMixture_stronglyAdapted
    {E : Nat -> Nat -> Omega -> Real}
    (hE : forall j, EProcess mu F (E j)) :
    StronglyAdapted F (countableSleepingProcessMixture E) := by
  intro n
  unfold countableSleepingProcessMixture
  have hsum : StronglyMeasurable[F n]
      (∑ j ∈ Finset.range n,
        fun omega => polynomialEpochWeight j * E j n omega) :=
    Finset.stronglyMeasurable_sum (Finset.range n) fun j _ =>
      ((hE j).supermartingale.stronglyAdapted n).const_mul
        (polynomialEpochWeight j)
  have hadd : StronglyMeasurable[F n]
      ((fun _ : Omega => polynomialSleepingTail n) +
        ∑ j ∈ Finset.range n,
          fun omega => polynomialEpochWeight j * E j n omega) :=
    stronglyMeasurable_const.add hsum
  convert hadd using 1
  funext omega
  simp only [Pi.add_apply, Finset.sum_apply]

/-- Fixed-time integrability is also a finite-prefix calculation. -/
theorem countableSleepingProcessMixture_integrable
    [IsFiniteMeasure mu]
    {E : Nat -> Nat -> Omega -> Real}
    (hE : forall j, EProcess mu F (E j))
    (n : Nat) :
    Integrable (countableSleepingProcessMixture E n) mu := by
  unfold countableSleepingProcessMixture
  have hsum : Integrable
      (∑ j ∈ Finset.range n,
        fun omega => polynomialEpochWeight j * E j n omega) mu :=
    integrable_finsetSum' (Finset.range n) fun j _ =>
      ((hE j).supermartingale.integrable n).const_mul
        (polynomialEpochWeight j)
  have hadd : Integrable
      ((fun _ : Omega => polynomialSleepingTail n) +
        ∑ j ∈ Finset.range n,
          fun omega => polynomialEpochWeight j * E j n omega) mu :=
    (integrable_const _).add hsum
  convert hadd using 1
  funext omega
  simp only [Pi.add_apply, Finset.sum_apply]

/-- The set-integral norm series is summable because every component after
the active prefix is exactly one and the remaining weights are geometric. -/
theorem countableSleepingProcessMixture_integralNorm_summable
    [IsFiniteMeasure mu]
    (E : Nat -> Nat -> Omega -> Real)
    (hsleep : forall j n omega, n <= j -> E j n omega = 1)
    (n : Nat) (s : Set Omega) (_hs : MeasurableSet s) :
    Summable fun j =>
      ∫ omega in s, ‖polynomialEpochWeight j * E j n omega‖ ∂mu := by
  let g : Nat -> Real := fun j =>
    ∫ omega in s, ‖polynomialEpochWeight j * E j n omega‖ ∂mu
  have htail_eq (i : Nat) :
      g (i + n) =
        polynomialEpochWeight (i + n) * mu.real s := by
    unfold g
    simp_rw [hsleep (i + n) n _ (Nat.le_add_left n i)]
    rw [mul_one, Real.norm_eq_abs,
      abs_of_pos (polynomialEpochWeight_pos (i + n))]
    simp [mul_comm]
  have hweight_shift : Summable
      (fun i => polynomialEpochWeight (i + n)) :=
    (summable_nat_add_iff n).2 polynomialEpochWeight_summable
  have hshift : Summable (fun i => g (i + n)) := by
    exact (hweight_shift.mul_right (mu.real s)).congr
      (fun i => (htail_eq i).symm)
  exact (summable_nat_add_iff n).1 hshift

/-- A polynomially weighted sleeping mixture of e-processes is an e-process.  The exact
finite-tail representation discharges the countable interchange obligations. -/
theorem countableSleepingProcessMixture_eProcess
    [IsFiniteMeasure mu]
    {E : Nat -> Nat -> Omega -> Real}
    (hE : forall j, EProcess mu F (E j))
    (hsleep : forall j n omega, n <= j -> E j n omega = 1) :
    EProcess mu F (countableSleepingProcessMixture E) := by
  have heq := countableSleepingProcessMixture_eq_countableWeightedProcess
    E hsleep
  rw [heq]
  apply countableWeightedProcess_eProcess
    (fun j => (polynomialEpochWeight_pos j).le)
    polynomialEpochWeight_hasSum hE
  · rw [← heq]
    exact countableSleepingProcessMixture_stronglyAdapted hE
  · intro n
    rw [← heq]
    exact countableSleepingProcessMixture_integrable hE n
  · exact countableSleepingProcessMixture_integralNorm_summable E hsleep

/-! ## Observable predictable-mean empirical-Bernstein instantiation -/

/-- A sleeping predictable strategy is strongly adapted whenever its awake
strategy is strongly adapted. -/
theorem sleepingStrategy_stronglyAdapted
    (strategy : Nat -> Nat -> Omega -> Real)
    (hstrategy : forall j, StronglyAdapted F (strategy j)) (j : Nat) :
    StronglyAdapted F (sleepingStrategy strategy j) := by
  intro k
  by_cases hjk : j <= k
  · have heq : sleepingStrategy strategy j k = strategy j k := by
      funext omega
      exact sleepingStrategy_of_le strategy hjk omega
    rw [heq]
    exact hstrategy j k
  · have hkj : k < j := Nat.lt_of_not_ge hjk
    have heq : sleepingStrategy strategy j k = fun _ => 0 := by
      funext omega
      exact sleepingStrategy_of_lt strategy hkj omega
    rw [heq]
    exact stronglyMeasurable_const

/-- Sleeping preserves a common `[0,L]` range. -/
theorem sleepingStrategy_mem_Icc
    {strategy : Nat -> Nat -> Omega -> Real} {L : Real}
    (hstrategy : forall j k omega, strategy j k omega ∈ Set.Icc 0 L)
    (j k : Nat) (omega : Omega) :
    sleepingStrategy strategy j k omega ∈ Set.Icc 0 L := by
  by_cases hjk : j <= k
  · simpa [sleepingStrategy, hjk] using hstrategy j k omega
  · have hL : 0 <= L := (hstrategy j k omega).1.trans
        (hstrategy j k omega).2
    simp [sleepingStrategy, hjk, hL]

/-- A not-yet-awake predictable-tilt lower process is exactly one. -/
theorem
    forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_sleeping_of_time_le
    (X mean : Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    {n j : Nat} (hnj : n <= j) (omega : Omega) :
    forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess X mean
        (sleepingStrategy strategy j) n omega = 1 := by
  rw [forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_eq]
  have hsum :
      (∑ k ∈ Finset.range n,
        (sleepingStrategy strategy j k omega * (mean k omega - X k omega) -
          forwardEmpiricalBernsteinPsi
              (sleepingStrategy strategy j k omega) *
            (X k omega - forwardPredictorProcess X k omega) ^ 2)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : k < j :=
      lt_of_lt_of_le (Finset.mem_range.mp hk) hnj
    rw [sleepingStrategy_of_lt strategy hkj omega]
    simp [forwardEmpiricalBernsteinPsi]
  rw [hsum, Real.exp_zero]

/-- Exact finite-prefix polynomial master over a countable catalog of predictable
empirical-Bernstein strategies.  At time `n`, only `n` components are evaluated. -/
def countableSleepingForwardPredictableMeanMasterProcess
    (X mean : Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real) : Nat -> Omega -> Real :=
  countableSleepingProcessMixture fun j =>
    forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess X mean
      (sleepingStrategy strategy j)

/-- The finite-prefix predictable-mean sleeping master is an e-process under the
same boundedness and predictability assumptions as each component. -/
theorem countableSleepingForwardPredictableMeanMasterProcess_eProcess_of_bounded
    [IsProbabilityMeasure mu]
    {X mean : Nat -> Omega -> Real}
    {strategy : Nat -> Nat -> Omega -> Real} {L : Real}
    (hL1 : L < 1)
    (hX_adapted : IncrementAdapted F X)
    (hmean_adapted : StronglyAdapted F mean)
    (hstrategy_adapted : forall j, StronglyAdapted F (strategy j))
    (hX_unit : forall k omega, X k omega ∈ Set.Icc (0 : Real) 1)
    (hstrategy_range : forall j k omega,
      strategy j k omega ∈ Set.Icc (0 : Real) L)
    (hmean : forall k, mu[X k | F k] =ᵐ[mu] mean k) :
    EProcess mu F
      (countableSleepingForwardPredictableMeanMasterProcess
        X mean strategy) := by
  unfold countableSleepingForwardPredictableMeanMasterProcess
  apply countableSleepingProcessMixture_eProcess
  · intro j
    exact
      forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_eProcess_of_bounded
        hL1 hX_adapted hmean_adapted
          (sleepingStrategy_stronglyAdapted strategy hstrategy_adapted j)
          hX_unit
          (fun k omega => sleepingStrategy_mem_Icc hstrategy_range j k omega)
          hmean
  · intro j n omega hnj
    exact
      forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_sleeping_of_time_le
        X mean strategy hnj omega

/-- The exact observable predictor-residual score of any active strategy is
bounded by the log of the finite-prefix master plus its logarithmic selection cost. -/
theorem forwardPredictableMeanScore_le_log_countableSleepingMaster_sub_logWeight
    (X mean : Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    {j n : Nat} (hjn : j < n) (omega : Omega) :
    (∑ k ∈ Finset.range n,
      (sleepingStrategy strategy j k omega * (mean k omega - X k omega) -
        forwardEmpiricalBernsteinPsi
            (sleepingStrategy strategy j k omega) *
          (X k omega - forwardPredictorProcess X k omega) ^ 2)) <=
      Real.log
          (countableSleepingForwardPredictableMeanMasterProcess
            X mean strategy n omega) -
        Real.log (polynomialEpochWeight j) := by
  let E : Nat -> Nat -> Omega -> Real := fun i =>
    forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess X mean
      (sleepingStrategy strategy i)
  have hE : forall i k xi, 0 <= E i k xi := by
    intro i k xi
    exact (Real.exp_pos _).le
  have hEj : 0 < E j n omega := Real.exp_pos _
  have hregret :=
    countableSleepingProcessMixture_logWealth_regret_le hE hjn hEj
  have hprocess :=
    forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_eq
      X mean (sleepingStrategy strategy j) n omega
  change
    (∑ k ∈ Finset.range n,
      (sleepingStrategy strategy j k omega * (mean k omega - X k omega) -
        forwardEmpiricalBernsteinPsi
            (sleepingStrategy strategy j k omega) *
          (X k omega - forwardPredictorProcess X k omega) ^ 2)) <=
      Real.log (countableSleepingProcessMixture E n omega) -
        Real.log (polynomialEpochWeight j)
  dsimp [E] at hregret
  rw [hprocess, Real.log_exp] at hregret
  linarith

end

end FormalSLT.AnytimeValid
