/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Statistics.CramerRao
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Finite exponential families

This module adds the finite one-parameter exponential-family companion to the
Fisher-information and Cramer-Rao layer.

For a finite sample space with positive base weights `h` and statistic `T`, the
normalizer is

`Z(theta) = sum_x h x * exp(theta * T x)`

and the log-partition is `A(theta) = log Z(theta)`. The normalized mass function
is `p_theta(x) = h x * exp(theta * T x - A(theta))`.

The main results are the finite-sum textbook identities:

* `A'(theta) = E_theta[T]`;
* the derivative of `E_theta[T]` is `Var_theta(T)`, so `A''(theta) = Var_theta(T)`;
* the natural-parameter Fisher information equals that same variance.

The Bernoulli witness uses `Bool`, statistic `1{true}`, base weights `1`, and
`theta = 0`, giving `A'(0) = 1/2`, `A''(0) = 1/4`, and Fisher information `1/4`.
-/

open scoped BigOperators
open Finset

namespace FormalSLT.Statistics
namespace ExponentialFamily

noncomputable section

open ClassicalEstimation
open FisherInformation

/-! ### Finite exponential-family primitives -/

/-- The finite partition sum `Z(theta)`. -/
def finitePartition {Ω : Type*} [Fintype Ω] (h T : Ω -> ℝ) (theta : ℝ) : ℝ :=
  ∑ x, h x * Real.exp (theta * T x)

/-- The log-partition function `A(theta) = log Z(theta)`. -/
def finiteLogPartition {Ω : Type*} [Fintype Ω] (h T : Ω -> ℝ) (theta : ℝ) : ℝ :=
  Real.log (finitePartition h T theta)

/-- The natural-parameter finite exponential-family mass function. -/
def finiteExponentialPMF {Ω : Type*} [Fintype Ω]
    (h T : Ω -> ℝ) (theta : ℝ) (x : Ω) : ℝ :=
  h x * Real.exp (theta * T x - finiteLogPartition h T theta)

/-- The natural-parameter derivative of the finite exponential-family mass. -/
def finiteExponentialPMFDeriv {Ω : Type*} [Fintype Ω]
    (h T : Ω -> ℝ) (theta : ℝ) (x : Ω) : ℝ :=
  finiteExponentialPMF h T theta x *
    (T x - weightedExpectation (finiteExponentialPMF h T theta) T)

/-- Positivity of the finite partition sum under positive base weights. -/
theorem finitePartition_pos {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {h T : Ω -> ℝ} (hpos : ∀ x, 0 < h x) (theta : ℝ) :
    0 < finitePartition h T theta := by
  unfold finitePartition
  exact Finset.sum_pos (fun x _ => mul_pos (hpos x) (Real.exp_pos _))
    (Finset.univ_nonempty)

/-- The normalized exponential-family masses sum to one. -/
theorem finiteExponentialPMF_sum_one {Ω : Type*} [Fintype Ω]
    {h T : Ω -> ℝ} {theta : ℝ}
    (hZ : 0 < finitePartition h T theta) :
    ∑ x, finiteExponentialPMF h T theta x = 1 := by
  have hZ_exp :
      Real.exp (Real.log (∑ y, h y * Real.exp (theta * T y))) =
        ∑ y, h y * Real.exp (theta * T y) := by
    simpa [finitePartition] using Real.exp_log hZ
  have hZ_ne : (∑ y, h y * Real.exp (theta * T y)) ≠ 0 := by
    simpa [finitePartition] using ne_of_gt hZ
  unfold finiteExponentialPMF finiteLogPartition finitePartition
  calc
    ∑ x, h x * Real.exp (theta * T x - Real.log (∑ y, h y * Real.exp (theta * T y)))
        =
      ∑ x, (h x * Real.exp (theta * T x)) / (∑ y, h y * Real.exp (theta * T y)) := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          rw [Real.exp_sub, hZ_exp]
          ring
    _ = (∑ x, h x * Real.exp (theta * T x)) /
          (∑ y, h y * Real.exp (theta * T y)) := by
          rw [Finset.sum_div]
    _ = 1 := by
          field_simp [hZ_ne]

/-- Exponential-family masses are positive under positive base weights. -/
theorem finiteExponentialPMF_pos {Ω : Type*} [Fintype Ω]
    {h T : Ω -> ℝ} {theta : ℝ}
    (hpos : ∀ x, 0 < h x) :
    ∀ x, 0 < finiteExponentialPMF h T theta x := by
  intro x
  unfold finiteExponentialPMF
  exact mul_pos (hpos x) (Real.exp_pos _)

/-- Differentiating the finite partition sum termwise. -/
theorem finitePartition_hasDerivAt {Ω : Type*} [Fintype Ω]
    (h T : Ω -> ℝ) (theta : ℝ) :
    HasDerivAt (fun u => finitePartition h T u)
      (∑ x, h x * Real.exp (theta * T x) * T x)
      theta := by
  unfold finitePartition
  have hsum := HasDerivAt.sum (u := (Finset.univ : Finset Ω)) fun x _ =>
    ((Real.hasDerivAt_exp (theta * T x)).comp theta
      ((hasDerivAt_id theta).mul_const (T x))).const_mul (h x)
  convert hsum using 1
  · ext u
    simp
  · ring_nf

/-- The normalized expectation is the logarithmic derivative numerator divided by `Z`. -/
theorem finiteExponentialFamily_mean_eq_logPartition_deriv {Ω : Type*} [Fintype Ω]
    {h T : Ω -> ℝ} {theta : ℝ}
    (hZ : 0 < finitePartition h T theta) :
    weightedExpectation (finiteExponentialPMF h T theta) T =
      (∑ x, h x * Real.exp (theta * T x) * T x) / finitePartition h T theta := by
  have hZ_exp :
      Real.exp (Real.log (∑ y, h y * Real.exp (theta * T y))) =
        ∑ y, h y * Real.exp (theta * T y) := by
    simpa [finitePartition] using Real.exp_log hZ
  unfold weightedExpectation finiteExponentialPMF finiteLogPartition finitePartition
  calc
    ∑ x, (h x * Real.exp (theta * T x - Real.log (∑ y, h y * Real.exp (theta * T y)))) * T x
        =
      ∑ x, (h x * Real.exp (theta * T x) * T x) /
        (∑ y, h y * Real.exp (theta * T y)) := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          rw [Real.exp_sub, hZ_exp]
          ring
    _ = (∑ x, h x * Real.exp (theta * T x) * T x) /
        (∑ y, h y * Real.exp (theta * T y)) := by
          rw [Finset.sum_div]

/-- **Log-partition derivative identity.**

For a finite exponential family, the derivative of `A(theta)` is the finite
expectation of the sufficient statistic. -/
theorem finiteLogPartition_hasDerivAt {Ω : Type*} [Fintype Ω]
    {h T : Ω -> ℝ} {theta : ℝ}
    (hZ : 0 < finitePartition h T theta) :
    HasDerivAt (fun u => finiteLogPartition h T u)
      (weightedExpectation (finiteExponentialPMF h T theta) T)
      theta := by
  have hpart := finitePartition_hasDerivAt h T theta
  have hlog := hpart.log (ne_of_gt hZ)
  simpa [finiteLogPartition, finiteExponentialFamily_mean_eq_logPartition_deriv hZ] using hlog

/-- Textbook positive-base form of the log-partition derivative identity. -/
theorem finiteLogPartition_hasDerivAt_of_positiveBase {Ω : Type*}
    [Fintype Ω] [Nonempty Ω]
    {h T : Ω -> ℝ} {theta : ℝ}
    (hpos : ∀ x, 0 < h x) :
    HasDerivAt (fun u => finiteLogPartition h T u)
      (weightedExpectation (finiteExponentialPMF h T theta) T)
      theta :=
  finiteLogPartition_hasDerivAt (h := h) (T := T) (finitePartition_pos hpos theta)

/-! ### Curvature and variance -/

/-- The derivative of the finite exponential-family mass. -/
theorem finiteExponentialPMF_hasDerivAt {Ω : Type*} [Fintype Ω]
    {h T : Ω -> ℝ} {theta : ℝ}
    (hZ : 0 < finitePartition h T theta) (x : Ω) :
    HasDerivAt (fun u => finiteExponentialPMF h T u x)
      (finiteExponentialPMFDeriv h T theta x)
      theta := by
  unfold finiteExponentialPMFDeriv finiteExponentialPMF
  have hlin : HasDerivAt (fun u => u * T x - finiteLogPartition h T u)
      (T x - weightedExpectation (finiteExponentialPMF h T theta) T) theta := by
    simpa using (((hasDerivAt_id theta).mul_const (T x)).sub
      (finiteLogPartition_hasDerivAt (h := h) (T := T) hZ))
  have hexp := hlin.exp
  simpa [finiteExponentialPMF, finiteExponentialPMFDeriv, weightedExpectation,
    mul_assoc, mul_left_comm, mul_comm] using hexp.const_mul (h x)

/-- Differentiating the finite mean gives the centered second moment. -/
theorem finiteMean_hasDerivAt {Ω : Type*} [Fintype Ω]
    {h T : Ω -> ℝ} {theta : ℝ}
    (hZ : 0 < finitePartition h T theta) :
    HasDerivAt
      (fun u => weightedExpectation (finiteExponentialPMF h T u) T)
      (∑ x,
        finiteExponentialPMF h T theta x *
          (T x - weightedExpectation (finiteExponentialPMF h T theta) T) * T x)
      theta := by
  exact hasDerivAt_weightedExpectation_param
    (pmf := fun u => finiteExponentialPMF h T u)
    (pmfDeriv := fun u => finiteExponentialPMFDeriv h T u)
    (T := T)
    (theta := theta)
    (fun x => finiteExponentialPMF_hasDerivAt (h := h) (T := T) hZ x)

/-- The centered second-moment derivative is the finite variance. -/
theorem finiteMean_deriv_eq_variance {Ω : Type*} [Fintype Ω]
    {h T : Ω -> ℝ} {theta : ℝ}
    (hZ : 0 < finitePartition h T theta) :
    (∑ x,
        finiteExponentialPMF h T theta x *
          (T x - weightedExpectation (finiteExponentialPMF h T theta) T) * T x)
      = weightedVariance (finiteExponentialPMF h T theta) T := by
  let m := weightedExpectation (finiteExponentialPMF h T theta) T
  have hsum : ∑ x, finiteExponentialPMF h T theta x = 1 :=
    finiteExponentialPMF_sum_one hZ
  have hcenter :
      ∑ x, finiteExponentialPMF h T theta x * (T x - m) = 0 := by
    calc
      ∑ x, finiteExponentialPMF h T theta x * (T x - m)
          = ∑ x, (finiteExponentialPMF h T theta x * T x
              - m * finiteExponentialPMF h T theta x) := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            ring
      _ = ∑ x, finiteExponentialPMF h T theta x * T x
              - ∑ x, m * finiteExponentialPMF h T theta x := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ x, finiteExponentialPMF h T theta x * T x
              - m * ∑ x, finiteExponentialPMF h T theta x := by
            rw [Finset.mul_sum]
      _ = 0 := by
            simp [m, weightedExpectation, hsum]
  unfold weightedVariance
  change _ = ∑ x, finiteExponentialPMF h T theta x * (T x - m) ^ 2
  calc
    ∑ x, finiteExponentialPMF h T theta x * (T x - m) * T x
        =
      ∑ x, finiteExponentialPMF h T theta x * (T x - m) * ((T x - m) + m) := by
        refine Finset.sum_congr rfl ?_
        intro x _hx
        ring
    _ =
      ∑ x, finiteExponentialPMF h T theta x * (T x - m) ^ 2
        + m * ∑ x, finiteExponentialPMF h T theta x * (T x - m) := by
        calc
          ∑ x, finiteExponentialPMF h T theta x * (T x - m) * ((T x - m) + m)
              =
            ∑ x, (finiteExponentialPMF h T theta x * (T x - m) ^ 2
              + m * (finiteExponentialPMF h T theta x * (T x - m))) := by
              refine Finset.sum_congr rfl ?_
              intro x _hx
              ring
          _ =
            ∑ x, finiteExponentialPMF h T theta x * (T x - m) ^ 2
              + ∑ x, m * (finiteExponentialPMF h T theta x * (T x - m)) := by
              rw [Finset.sum_add_distrib]
          _ =
            ∑ x, finiteExponentialPMF h T theta x * (T x - m) ^ 2
              + m * ∑ x, finiteExponentialPMF h T theta x * (T x - m) := by
              rw [Finset.mul_sum]
    _ = ∑ x, finiteExponentialPMF h T theta x * (T x - m) ^ 2 := by
        rw [hcenter]
        ring

/-- **Log-partition curvature identity.**

For a finite exponential family, differentiating the mean gives the variance of
the sufficient statistic. This is the one-dimensional Hessian identity
`A''(theta) = Var_theta(T)`. -/
theorem finiteLogPartition_hasSecondDerivAt {Ω : Type*} [Fintype Ω]
    {h T : Ω -> ℝ} {theta : ℝ}
    (hZ : 0 < finitePartition h T theta) :
    HasDerivAt
      (fun u => weightedExpectation (finiteExponentialPMF h T u) T)
      (weightedVariance (finiteExponentialPMF h T theta) T)
      theta := by
  convert finiteMean_hasDerivAt (h := h) (T := T) hZ using 1
  exact (finiteMean_deriv_eq_variance (h := h) (T := T) hZ).symm

/-- Textbook positive-base form of the log-partition curvature identity. -/
theorem finiteLogPartition_hasSecondDerivAt_of_positiveBase {Ω : Type*}
    [Fintype Ω] [Nonempty Ω]
    {h T : Ω -> ℝ} {theta : ℝ}
    (hpos : ∀ x, 0 < h x) :
    HasDerivAt
      (fun u => weightedExpectation (finiteExponentialPMF h T u) T)
      (weightedVariance (finiteExponentialPMF h T theta) T)
      theta :=
  finiteLogPartition_hasSecondDerivAt (h := h) (T := T) (finitePartition_pos hpos theta)

/-- A named equality form of the curvature identity. -/
theorem finiteExponentialFamily_variance_eq_logPartition_secondDeriv {Ω : Type*} [Fintype Ω]
    {h T : Ω -> ℝ} {theta : ℝ}
    (hZ : 0 < finitePartition h T theta) :
    HasDerivAt
      (fun u => weightedExpectation (finiteExponentialPMF h T u) T)
      (weightedVariance (finiteExponentialPMF h T theta) T)
      theta :=
  finiteLogPartition_hasSecondDerivAt (h := h) (T := T) hZ

/-! ### Fisher information connection -/

/-- The natural-parameter score is `T - E_theta[T]`. -/
theorem finiteExponentialFamily_score_eq_centered {Ω : Type*} [Fintype Ω]
    {h T : Ω -> ℝ} {theta : ℝ}
    (hpos : ∀ x, 0 < h x) :
    ∀ x,
      scoreFunction (fun u => finiteExponentialPMF h T u)
        (fun u => finiteExponentialPMFDeriv h T u) theta x =
        T x - weightedExpectation (finiteExponentialPMF h T theta) T := by
  intro x
  unfold scoreFunction finiteExponentialPMFDeriv
  have hp : finiteExponentialPMF h T theta x ≠ 0 :=
    ne_of_gt (finiteExponentialPMF_pos (h := h) (T := T) (theta := theta) hpos x)
  field_simp [hp]

/-- **Fisher information equals exponential-family curvature and variance.** -/
theorem finiteExponentialFamily_fisherInformation_eq_variance {Ω : Type*}
    [Fintype Ω] [Nonempty Ω]
    {h T : Ω -> ℝ} {theta : ℝ}
    (hpos : ∀ x, 0 < h x) :
    fisherInformation (fun u => finiteExponentialPMF h T u)
        (fun u => finiteExponentialPMFDeriv h T u) theta =
      weightedVariance (finiteExponentialPMF h T theta) T := by
  have hZ : 0 < finitePartition h T theta := finitePartition_pos hpos theta
  unfold fisherInformation weightedVariance weightedExpectation
  refine Finset.sum_congr rfl ?_
  intro x _hx
  simp [weightedExpectation, finiteExponentialFamily_score_eq_centered
    (h := h) (T := T) hpos x]

/-- Direct form of `I(theta) = A''(theta)` for a positive finite exponential family. -/
theorem finiteExponentialFamily_logPartition_secondDeriv_eq_fisherInformation {Ω : Type*}
    [Fintype Ω] [Nonempty Ω]
    {h T : Ω -> ℝ} {theta : ℝ}
    (hpos : ∀ x, 0 < h x) :
    HasDerivAt
      (fun u => weightedExpectation (finiteExponentialPMF h T u) T)
      (fisherInformation (fun u => finiteExponentialPMF h T u)
        (fun u => finiteExponentialPMFDeriv h T u) theta)
      theta := by
  convert finiteLogPartition_hasSecondDerivAt_of_positiveBase
    (h := h) (T := T) hpos using 1
  exact finiteExponentialFamily_fisherInformation_eq_variance
    (h := h) (T := T) hpos

/-! ### Bernoulli natural-parameter witness -/

/-- Bernoulli natural-family base weights on `Bool`. -/
def bernoulliNaturalBase : Bool -> ℝ := fun _ => 1

/-- Bernoulli natural sufficient statistic `1{true}`. -/
def bernoulliNaturalStatistic : Bool -> ℝ := fun b => if b then 1 else 0

/-- The Bernoulli natural-parameter partition sum is `1 + exp(theta)`. -/
theorem bernoulliNatural_partition (theta : ℝ) :
    finitePartition bernoulliNaturalBase bernoulliNaturalStatistic theta =
      1 + Real.exp theta := by
  unfold finitePartition bernoulliNaturalBase bernoulliNaturalStatistic
  rw [Fintype.sum_bool]
  simp
  ring

/-- At `theta = 0`, the Bernoulli natural log-partition is `log 2`. -/
theorem bernoulliNatural_logPartition_zero :
    finiteLogPartition bernoulliNaturalBase bernoulliNaturalStatistic 0 =
      Real.log 2 := by
  unfold finiteLogPartition
  rw [bernoulliNatural_partition]
  norm_num

/-- At `theta = 0`, the Bernoulli natural-family success probability is `1/2`. -/
theorem bernoulliNatural_mean_zero :
    weightedExpectation
        (finiteExponentialPMF bernoulliNaturalBase bernoulliNaturalStatistic 0)
        bernoulliNaturalStatistic =
      (1 : ℝ) / 2 := by
  have hZ : 0 < finitePartition bernoulliNaturalBase bernoulliNaturalStatistic 0 := by
    rw [bernoulliNatural_partition]
    norm_num
  rw [finiteExponentialFamily_mean_eq_logPartition_deriv (h := bernoulliNaturalBase)
    (T := bernoulliNaturalStatistic) hZ]
  unfold finitePartition bernoulliNaturalBase bernoulliNaturalStatistic
  rw [Fintype.sum_bool]
  norm_num

/-- `A'(0) = 1/2` for the Bernoulli natural family. -/
theorem bernoulliNatural_logPartition_deriv_zero :
    HasDerivAt
      (fun u => finiteLogPartition bernoulliNaturalBase bernoulliNaturalStatistic u)
      ((1 : ℝ) / 2)
      0 := by
  have hZ : 0 < finitePartition bernoulliNaturalBase bernoulliNaturalStatistic 0 := by
    rw [bernoulliNatural_partition]
    norm_num
  convert finiteLogPartition_hasDerivAt
    (h := bernoulliNaturalBase) (T := bernoulliNaturalStatistic) hZ using 1
  exact bernoulliNatural_mean_zero.symm

/-- At `theta = 0`, both Bernoulli natural-family atoms have mass `1/2`. -/
theorem bernoulliNatural_pmf_zero (b : Bool) :
    finiteExponentialPMF bernoulliNaturalBase bernoulliNaturalStatistic 0 b =
      (1 : ℝ) / 2 := by
  have hexp : Real.exp (-Real.log 2) = (1 : ℝ) / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  cases b <;>
    norm_num [finiteExponentialPMF, finiteLogPartition, finitePartition,
      bernoulliNaturalBase, bernoulliNaturalStatistic, Fintype.sum_bool,
      Real.exp_log (by norm_num : (0 : ℝ) < 2), hexp]

/-- At `theta = 0`, Bernoulli natural-family variance is `1/4`. -/
theorem bernoulliNatural_variance_zero :
    weightedVariance
        (finiteExponentialPMF bernoulliNaturalBase bernoulliNaturalStatistic 0)
        bernoulliNaturalStatistic =
      (1 : ℝ) / 4 := by
  unfold weightedVariance
  rw [bernoulliNatural_mean_zero, Fintype.sum_bool]
  simp [bernoulliNatural_pmf_zero, bernoulliNaturalStatistic]
  norm_num

/-- `A''(0) = 1/4` for the Bernoulli natural family. -/
theorem bernoulliNatural_logPartition_secondDeriv_zero :
    HasDerivAt
      (fun u =>
        weightedExpectation
          (finiteExponentialPMF bernoulliNaturalBase bernoulliNaturalStatistic u)
          bernoulliNaturalStatistic)
      ((1 : ℝ) / 4)
      0 := by
  have hZ : 0 < finitePartition bernoulliNaturalBase bernoulliNaturalStatistic 0 := by
    rw [bernoulliNatural_partition]
    norm_num
  convert finiteLogPartition_hasSecondDerivAt
    (h := bernoulliNaturalBase) (T := bernoulliNaturalStatistic) hZ using 1
  exact bernoulliNatural_variance_zero.symm

/-- At `theta = 0`, Bernoulli natural-family Fisher information is `1/4`. -/
theorem bernoulliNatural_fisher_zero :
    fisherInformation
        (fun u => finiteExponentialPMF bernoulliNaturalBase bernoulliNaturalStatistic u)
        (fun u => finiteExponentialPMFDeriv bernoulliNaturalBase bernoulliNaturalStatistic u)
        0 =
      (1 : ℝ) / 4 := by
  have hpos : ∀ x, 0 < bernoulliNaturalBase x := by
    intro x
    norm_num [bernoulliNaturalBase]
  rw [finiteExponentialFamily_fisherInformation_eq_variance
    (h := bernoulliNaturalBase) (T := bernoulliNaturalStatistic) hpos]
  exact bernoulliNatural_variance_zero

/-- Bernoulli natural-family Fisher information equals variance at `theta = 0`. -/
theorem bernoulliNatural_fisher_eq_variance_zero :
    fisherInformation
        (fun u => finiteExponentialPMF bernoulliNaturalBase bernoulliNaturalStatistic u)
        (fun u => finiteExponentialPMFDeriv bernoulliNaturalBase bernoulliNaturalStatistic u)
        0 =
      weightedVariance
        (finiteExponentialPMF bernoulliNaturalBase bernoulliNaturalStatistic 0)
        bernoulliNaturalStatistic := by
  have hpos : ∀ x, 0 < bernoulliNaturalBase x := by
    intro x
    norm_num [bernoulliNaturalBase]
  exact finiteExponentialFamily_fisherInformation_eq_variance
    (h := bernoulliNaturalBase) (T := bernoulliNaturalStatistic) hpos

/-- Concrete Bernoulli witness at `theta = 0`:
`A'(0) = 1/2`, `A''(0) = 1/4`, and `I(0) = Var(T) = 1/4`. -/
theorem bernoulliNatural_witness :
    weightedExpectation
        (finiteExponentialPMF bernoulliNaturalBase bernoulliNaturalStatistic 0)
        bernoulliNaturalStatistic = (1 : ℝ) / 2 ∧
      weightedVariance
        (finiteExponentialPMF bernoulliNaturalBase bernoulliNaturalStatistic 0)
        bernoulliNaturalStatistic = (1 : ℝ) / 4 ∧
      fisherInformation
        (fun u => finiteExponentialPMF bernoulliNaturalBase bernoulliNaturalStatistic u)
        (fun u => finiteExponentialPMFDeriv bernoulliNaturalBase bernoulliNaturalStatistic u)
        0 = (1 : ℝ) / 4 := by
  exact ⟨bernoulliNatural_mean_zero, bernoulliNatural_variance_zero,
    bernoulliNatural_fisher_zero⟩

end

end ExponentialFamily
end FormalSLT.Statistics
