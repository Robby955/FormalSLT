/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.AnytimeValid.SingularFractionBesselMixture

/-!
# Explicit observable LIL-order corollary for the singular-fraction mixture

This file chooses an admissible fraction from the observed hybrid-Bessel
penalty and substitutes it into the all-fraction theorem.  The chosen fraction
is a deterministic function of the reported prefix, so no new stochastic
selection step or exceptional event is introduced.

For a nonnegative penalty `Q`, define

* `V = max Q (exp 2)` and `R = log V`;
* `A = log (R * (R + 2) / (4 * delta))` and `C = max 1 A`;
* `M = max V (exp 2 * C)`;
* `lambda = sqrt (C / M)`.

The scalar construction makes `0 < lambda <= exp (-1)` and bounds the exact
singular-window price by `C`.  Substitution yields the observable LIL-order
deviation radius `(1 + exp 1) * sqrt (M * C)`.  No optimality or asymptotic
sharpness claim is made.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}

/-- Positive floor for the observable hybrid-Bessel penalty. -/
def singularFractionObservablePenaltyFloor (Q : Real) : Real :=
  max Q (Real.exp 2)

/-- Logarithm of the floored observable penalty. -/
def singularFractionObservableLogPenaltyFloor (Q : Real) : Real :=
  Real.log (singularFractionObservablePenaltyFloor Q)

/-- Raw logarithmic price of the singular-fraction window. -/
def singularFractionObservableRawCost (Q delta : Real) : Real :=
  let R := singularFractionObservableLogPenaltyFloor Q
  Real.log (R * (R + 2) / (4 * delta))

/-- Observable price floored at one. -/
def singularFractionObservableCost (Q delta : Real) : Real :=
  max 1 (singularFractionObservableRawCost Q delta)

/-- Scale enlarged enough to make the tuned fraction admissible. -/
def singularFractionObservableScale (Q delta : Real) : Real :=
  max (singularFractionObservablePenaltyFloor Q)
    (Real.exp 2 * singularFractionObservableCost Q delta)

/-- Explicit data-dependent fraction used inside the already simultaneous
all-fraction event. -/
def singularFractionObservableTunedLambda (Q delta : Real) : Real :=
  Real.sqrt
    (singularFractionObservableCost Q delta /
      singularFractionObservableScale Q delta)

/-- Parameter-free observable LIL-order deviation radius. -/
def singularFractionObservableLILBoundary (Q delta : Real) : Real :=
  (1 + Real.exp 1) *
    Real.sqrt
      (singularFractionObservableScale Q delta *
        singularFractionObservableCost Q delta)

/-- The floored observable penalty dominates the original penalty. -/
theorem le_singularFractionObservablePenaltyFloor (Q : Real) :
    Q <= singularFractionObservablePenaltyFloor Q := by
  exact le_max_left _ _

/-- The observable penalty floor is at least `exp 2`. -/
theorem exp_two_le_singularFractionObservablePenaltyFloor (Q : Real) :
    Real.exp 2 <= singularFractionObservablePenaltyFloor Q := by
  exact le_max_right _ _

/-- The observable penalty floor is strictly positive. -/
theorem singularFractionObservablePenaltyFloor_pos (Q : Real) :
    0 < singularFractionObservablePenaltyFloor Q :=
  (Real.exp_pos 2).trans_le
    (exp_two_le_singularFractionObservablePenaltyFloor Q)

/-- The logarithm of the penalty floor is at least two. -/
theorem two_le_singularFractionObservableLogPenaltyFloor (Q : Real) :
    2 <= singularFractionObservableLogPenaltyFloor Q := by
  unfold singularFractionObservableLogPenaltyFloor
  have hlog := Real.log_le_log (Real.exp_pos 2)
    (exp_two_le_singularFractionObservablePenaltyFloor Q)
  simpa using hlog

/-- Under a probability-level confidence budget, the raw cost is positive. -/
theorem singularFractionObservableRawCost_pos
    {Q delta : Real} (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    0 < singularFractionObservableRawCost Q delta := by
  let R := singularFractionObservableLogPenaltyFloor Q
  have hR : 2 <= R := by
    simpa [R] using two_le_singularFractionObservableLogPenaltyFloor Q
  have hratio : 1 < R * (R + 2) / (4 * delta) := by
    have htwo : 2 <= R * (R + 2) / (4 * delta) := by
      apply (le_div_iff₀ (mul_pos (by norm_num) hdelta)).2
      nlinarith
    linarith
  unfold singularFractionObservableRawCost
  dsimp only
  exact Real.log_pos hratio

/-- The observable cost is at least one. -/
theorem one_le_singularFractionObservableCost (Q delta : Real) :
    1 <= singularFractionObservableCost Q delta := by
  exact le_max_left _ _

/-- The raw logarithmic price is no larger than the floored cost. -/
theorem singularFractionObservableRawCost_le_cost (Q delta : Real) :
    singularFractionObservableRawCost Q delta <=
      singularFractionObservableCost Q delta := by
  exact le_max_right _ _

/-- The observable cost is strictly positive. -/
theorem singularFractionObservableCost_pos (Q delta : Real) :
    0 < singularFractionObservableCost Q delta :=
  zero_lt_one.trans_le (one_le_singularFractionObservableCost Q delta)

/-- The enlarged scale dominates the floored observable penalty. -/
theorem singularFractionObservablePenaltyFloor_le_scale (Q delta : Real) :
    singularFractionObservablePenaltyFloor Q <=
      singularFractionObservableScale Q delta := by
  exact le_max_left _ _

/-- The enlarged scale dominates `exp 2` times the cost. -/
theorem exp_two_mul_cost_le_singularFractionObservableScale
    (Q delta : Real) :
    Real.exp 2 * singularFractionObservableCost Q delta <=
      singularFractionObservableScale Q delta := by
  exact le_max_right _ _

/-- The enlarged scale is strictly positive. -/
theorem singularFractionObservableScale_pos (Q delta : Real) :
    0 < singularFractionObservableScale Q delta :=
  (singularFractionObservablePenaltyFloor_pos Q).trans_le
    (singularFractionObservablePenaltyFloor_le_scale Q delta)

/-- The scale-to-cost ratio remains below the observable penalty floor. -/
theorem singularFractionObservableScale_div_cost_le_penaltyFloor
    (Q delta : Real) :
    singularFractionObservableScale Q delta /
        singularFractionObservableCost Q delta <=
      singularFractionObservablePenaltyFloor Q := by
  let V := singularFractionObservablePenaltyFloor Q
  let C := singularFractionObservableCost Q delta
  let M := singularFractionObservableScale Q delta
  have hV0 : 0 <= V := (singularFractionObservablePenaltyFloor_pos Q).le
  have hC1 : 1 <= C := by
    simpa [C] using one_le_singularFractionObservableCost Q delta
  have hC0 : 0 <= C := zero_le_one.trans hC1
  have hexpV : Real.exp 2 <= V := by
    simpa [V] using exp_two_le_singularFractionObservablePenaltyFloor Q
  have hM : M <= V * C := by
    dsimp [M, singularFractionObservableScale]
    apply max_le
    · simpa using mul_le_mul_of_nonneg_left hC1 hV0
    · exact mul_le_mul_of_nonneg_right hexpV hC0
  apply (div_le_iff₀ (singularFractionObservableCost_pos Q delta)).2
  simpa [V, C, M] using hM

/-- The tuned fraction is strictly positive. -/
theorem singularFractionObservableTunedLambda_pos (Q delta : Real) :
    0 < singularFractionObservableTunedLambda Q delta := by
  unfold singularFractionObservableTunedLambda
  exact Real.sqrt_pos.mpr
    (div_pos (singularFractionObservableCost_pos Q delta)
      (singularFractionObservableScale_pos Q delta))

/-- Exact square of the tuned fraction. -/
theorem singularFractionObservableTunedLambda_sq (Q delta : Real) :
    singularFractionObservableTunedLambda Q delta ^ 2 =
      singularFractionObservableCost Q delta /
        singularFractionObservableScale Q delta := by
  unfold singularFractionObservableTunedLambda
  exact Real.sq_sqrt
    (div_nonneg (singularFractionObservableCost_pos Q delta).le
      (singularFractionObservableScale_pos Q delta).le)

/-- The tuned fraction lies in the singular-mixture admissible range. -/
theorem singularFractionObservableTunedLambda_le_exp_neg_one
    (Q delta : Real) :
    singularFractionObservableTunedLambda Q delta <= Real.exp (-1) := by
  let C := singularFractionObservableCost Q delta
  let M := singularFractionObservableScale Q delta
  have hC0 : 0 <= C := (singularFractionObservableCost_pos Q delta).le
  have hM0 : 0 <= M := (singularFractionObservableScale_pos Q delta).le
  have hfloor : Real.exp 2 * C <= M := by
    simpa [C, M] using
      exp_two_mul_cost_le_singularFractionObservableScale Q delta
  have hratio : C / M <= Real.exp (-2) := by
    apply (div_le_iff₀ (singularFractionObservableScale_pos Q delta)).2
    have hscaled := mul_le_mul_of_nonneg_left hfloor (Real.exp_pos (-2)).le
    calc
      C = Real.exp (-2) * (Real.exp 2 * C) := by
        symm
        calc
          Real.exp (-2) * (Real.exp 2 * C) =
              (Real.exp (-2) * Real.exp 2) * C := by ring
          _ = Real.exp (-2 + 2) * C := by rw [Real.exp_add]
          _ = C := by norm_num
      _ <= Real.exp (-2) * M := hscaled
  have hsquares : singularFractionObservableTunedLambda Q delta ^ 2 <=
      (Real.exp (-1)) ^ 2 := by
    rw [singularFractionObservableTunedLambda_sq]
    calc
      C / M <= Real.exp (-2) := hratio
      _ = (Real.exp (-1)) ^ 2 := by
        rw [pow_two, ← Real.exp_add]
        norm_num
  exact (sq_le_sq₀ (singularFractionObservableTunedLambda_pos Q delta).le
    (Real.exp_pos (-1)).le).mp hsquares

/-- Exact logarithmic scale of the tuned fraction. -/
theorem singularFractionLogScale_tunedLambda_eq
    (Q delta : Real) :
    singularFractionLogScale
        (singularFractionObservableTunedLambda Q delta) =
      Real.log
          (singularFractionObservableScale Q delta /
            singularFractionObservableCost Q delta) /
        2 := by
  have hratio : 0 <=
      singularFractionObservableCost Q delta /
        singularFractionObservableScale Q delta :=
    div_nonneg (singularFractionObservableCost_pos Q delta).le
      (singularFractionObservableScale_pos Q delta).le
  unfold singularFractionLogScale singularFractionObservableTunedLambda
  rw [Real.log_sqrt hratio]
  rw [Real.log_div (singularFractionObservableCost_pos Q delta).ne'
    (singularFractionObservableScale_pos Q delta).ne']
  rw [Real.log_div (singularFractionObservableScale_pos Q delta).ne'
    (singularFractionObservableCost_pos Q delta).ne']
  ring

/-- The tuned logarithmic scale is at most half the logarithm of the penalty
floor. -/
theorem singularFractionLogScale_tunedLambda_le_half_logPenaltyFloor
    (Q delta : Real) :
    singularFractionLogScale
        (singularFractionObservableTunedLambda Q delta) <=
      singularFractionObservableLogPenaltyFloor Q / 2 := by
  rw [singularFractionLogScale_tunedLambda_eq]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact Real.log_le_log
    (div_pos (singularFractionObservableScale_pos Q delta)
      (singularFractionObservableCost_pos Q delta))
    (singularFractionObservableScale_div_cost_le_penaltyFloor Q delta)

/-- The exact logarithmic singular-window price at the tuned fraction is
bounded by the observable cost. -/
theorem singularFraction_tunedLambda_logWindowCost_le
    {Q delta : Real} (hdelta : 0 < delta) (_hdelta_one : delta <= 1) :
    Real.log
        (singularFractionLogScale
              (singularFractionObservableTunedLambda Q delta) *
            (singularFractionLogScale
                (singularFractionObservableTunedLambda Q delta) + 1) /
          delta) <=
      singularFractionObservableCost Q delta := by
  let L := singularFractionLogScale
    (singularFractionObservableTunedLambda Q delta)
  let R := singularFractionObservableLogPenaltyFloor Q
  have hlam_pos := singularFractionObservableTunedLambda_pos Q delta
  have hlam := singularFractionObservableTunedLambda_le_exp_neg_one Q delta
  have hL : 1 <= L := by
    simpa [L] using one_le_singularFractionLogScale hlam_pos hlam
  have hR : 2 <= R := by
    simpa [R] using two_le_singularFractionObservableLogPenaltyFloor Q
  have hLR : L <= R / 2 := by
    simpa [L, R] using
      singularFractionLogScale_tunedLambda_le_half_logPenaltyFloor Q delta
  have hpoly : L * (L + 1) <= R * (R + 2) / 4 := by
    have hfactor : 0 <= (R / 2 - L) * (R / 2 + L + 1) := by
      apply mul_nonneg
      · linarith
      · linarith
    nlinarith
  have hratio : L * (L + 1) / delta <=
      R * (R + 2) / (4 * delta) := by
    calc
      L * (L + 1) / delta <= (R * (R + 2) / 4) / delta :=
        div_le_div_of_nonneg_right hpoly hdelta.le
      _ = R * (R + 2) / (4 * delta) := by ring
  have hleft_pos : 0 < L * (L + 1) / delta := by positivity
  calc
    Real.log (L * (L + 1) / delta) <=
        Real.log (R * (R + 2) / (4 * delta)) :=
      Real.log_le_log hleft_pos hratio
    _ = singularFractionObservableRawCost Q delta := by
      rfl
    _ <= singularFractionObservableCost Q delta :=
      singularFractionObservableRawCost_le_cost Q delta

/-- Substituting the tuned fraction into the exact all-fraction boundary is
bounded by the explicit observable LIL-order radius. -/
theorem singularFraction_tunedBoundary_le_observableLIL
    {Q delta : Real} (_hQ : 0 <= Q)
    (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    singularFractionObservableTunedLambda Q delta * Q +
        Real.exp 1 / singularFractionObservableTunedLambda Q delta *
          Real.log
            (singularFractionLogScale
                  (singularFractionObservableTunedLambda Q delta) *
                (singularFractionLogScale
                    (singularFractionObservableTunedLambda Q delta) + 1) /
              delta) <=
      singularFractionObservableLILBoundary Q delta := by
  let C := singularFractionObservableCost Q delta
  let M := singularFractionObservableScale Q delta
  let lam := singularFractionObservableTunedLambda Q delta
  let B := Real.sqrt (M * C)
  have hC : 0 < C := by
    simpa [C] using singularFractionObservableCost_pos Q delta
  have hM : 0 < M := by
    simpa [M] using singularFractionObservableScale_pos Q delta
  have hlam : 0 < lam := by
    simpa [lam] using singularFractionObservableTunedLambda_pos Q delta
  have hMC : 0 <= M * C := mul_nonneg hM.le hC.le
  have hB : 0 <= B := by simp [B]
  have hlam_sq : lam ^ 2 = C / M := by
    simpa [lam, C, M] using
      singularFractionObservableTunedLambda_sq Q delta
  have hlam_sq_mul : lam ^ 2 * M = C := by
    rw [hlam_sq]
    exact div_mul_cancel₀ C hM.ne'
  have hlamM_sq : (lam * M) ^ 2 = M * C := by
    calc
      (lam * M) ^ 2 = (lam ^ 2 * M) * M := by ring
      _ = C * M := by rw [hlam_sq_mul]
      _ = M * C := by ring
  have hB_sq : B ^ 2 = M * C := by
    simpa [B] using Real.sq_sqrt hMC
  have hlamM_eq : lam * M = B := by
    have hlamM0 : 0 <= lam * M := mul_nonneg hlam.le hM.le
    nlinarith
  have hQ_le_M : Q <= M := by
    exact (le_singularFractionObservablePenaltyFloor Q).trans
      (singularFractionObservablePenaltyFloor_le_scale Q delta)
  have hlinear : lam * Q <= B := by
    calc
      lam * Q <= lam * M := mul_le_mul_of_nonneg_left hQ_le_M hlam.le
      _ = B := hlamM_eq
  have hlog := singularFraction_tunedLambda_logWindowCost_le
    (Q := Q) hdelta hdelta_one
  have hC_div_lam : C / lam = B := by
    calc
      C / lam = lam * M := by
        apply (div_eq_iff hlam.ne').2
        nlinarith
      _ = B := hlamM_eq
  have hprice : Real.exp 1 / lam *
        Real.log
          (singularFractionLogScale lam *
              (singularFractionLogScale lam + 1) / delta) <=
      Real.exp 1 * B := by
    calc
      Real.exp 1 / lam *
          Real.log
            (singularFractionLogScale lam *
                (singularFractionLogScale lam + 1) / delta) <=
          Real.exp 1 / lam * C :=
        mul_le_mul_of_nonneg_left (by simpa [lam, C] using hlog) (by positivity)
      _ = Real.exp 1 * (C / lam) := by ring
      _ = Real.exp 1 * B := by rw [hC_div_lam]
  unfold singularFractionObservableLILBoundary
  change lam * Q + Real.exp 1 / lam *
      Real.log
        (singularFractionLogScale lam *
            (singularFractionLogScale lam + 1) / delta) <=
    (1 + Real.exp 1) * B
  nlinarith

/-- Ordinary monitored-mean form of the sharper exact all-fraction boundary.
The same event supports every reporting time and every admissible target
fraction. -/
theorem singularFractionLowerMixture_all_fraction_mean
    {X : Nat → Omega → Real} {mean delta : Real}
    (hX_unit : ∀ k omega, X k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : mean ∈ Set.Icc (0 : Real) 1)
    (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    {omega : Omega}
    (homega : omega ∉
      singularFractionLowerMixtureExceptionalEvent X mean delta) :
    ∀ n : Nat, 2 <= n → ∀ lam : Real,
      0 < lam → lam <= Real.exp (-1) →
      mean < forwardPrefixMean (fun k => X k omega) n +
        singularFractionForwardBesselBoundary X lam delta n omega /
          (n : Real) := by
  intro n hn lam hlam_pos hlam
  have hsum := singularFractionLowerMixture_all_fraction_boundary
    hX_unit hmean_unit hdelta hdelta_one homega n hn lam hlam_pos hlam
  have hidentity := sum_mean_sub_eq_mul_sub_forwardPrefixMean
    (fun k => X k omega) mean (show 0 < n by omega)
  rw [hidentity] at hsum
  have hnpos : 0 < (n : Real) := Nat.cast_pos.mpr (by omega)
  have hdiv : mean - forwardPrefixMean (fun k => X k omega) n <
      singularFractionForwardBesselBoundary X lam delta n omega /
        (n : Real) := by
    apply (lt_div_iff₀ hnpos).2
    nlinarith
  linarith

/-- End-to-end one-event ordinary monitored-mean form of the exact
all-fraction theorem. -/
theorem singularFractionLowerMixture_timeUniform_all_fraction_mean
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration Nat mOmega} {X : Nat → Omega → Real}
    {mean delta : Real}
    (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (hX_adapted : IncrementAdapted F X)
    (hX_unit : ∀ k omega, X k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : mean ∈ Set.Icc (0 : Real) 1)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] fun _ => mean) :
    mu.real (singularFractionLowerMixtureExceptionalEvent X mean delta) <=
        delta ∧
      ∀ omega ∉ singularFractionLowerMixtureExceptionalEvent X mean delta,
        ∀ n : Nat, 2 <= n → ∀ lam : Real,
          0 < lam → lam <= Real.exp (-1) →
          mean < forwardPrefixMean (fun k => X k omega) n +
            singularFractionForwardBesselBoundary X lam delta n omega /
              (n : Real) := by
  constructor
  · exact singularFractionLowerMixtureExceptionalEvent_mass_le_delta
      hdelta hX_adapted hX_unit hmean_unit hmean
  · intro omega homega
    exact singularFractionLowerMixture_all_fraction_mean
      hX_unit hmean_unit hdelta hdelta_one homega

/-- Outside the original singular-mixture event, the parameter-free
observable LIL-order deviation bound holds at every time `n >= 2`. -/
theorem singularFractionLowerMixture_observableLIL_boundary
    {X : Nat → Omega → Real} {mean delta : Real}
    (hX_unit : ∀ k omega, X k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : mean ∈ Set.Icc (0 : Real) 1)
    (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    {omega : Omega}
    (homega : omega ∉
      singularFractionLowerMixtureExceptionalEvent X mean delta) :
    ∀ n : Nat, 2 <= n →
      (∑ k ∈ Finset.range n, (mean - X k omega)) <
        singularFractionObservableLILBoundary
          (forwardHybridBesselPenalty (fun k => X k omega) n) delta := by
  intro n hn
  let Q := forwardHybridBesselPenalty (fun k => X k omega) n
  let lam := singularFractionObservableTunedLambda Q delta
  have hQ : 0 <= Q := by
    simpa [Q] using forwardHybridBesselPenalty_nonneg_of_two
      (fun k => X k omega) hn
  have hfixed := singularFractionLowerMixture_all_fraction_boundary
    hX_unit hmean_unit hdelta hdelta_one homega n hn lam
      (by simpa [lam, Q] using
        singularFractionObservableTunedLambda_pos Q delta)
      (by simpa [lam, Q] using
        singularFractionObservableTunedLambda_le_exp_neg_one Q delta)
  have henvelope := singularFraction_tunedBoundary_le_observableLIL
    hQ hdelta hdelta_one
  exact hfixed.trans_le (by
    simpa [singularFractionForwardBesselBoundary, lam, Q] using henvelope)

/-- Ordinary monitored-mean form of the observable LIL-order deviation
corollary.  The target is the candidate conditional mean from the model, not
an unlabeled population or future-risk quantity. -/
theorem singularFractionLowerMixture_observableLIL_mean
    {X : Nat → Omega → Real} {mean delta : Real}
    (hX_unit : ∀ k omega, X k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : mean ∈ Set.Icc (0 : Real) 1)
    (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    {omega : Omega}
    (homega : omega ∉
      singularFractionLowerMixtureExceptionalEvent X mean delta) :
    ∀ n : Nat, 2 <= n →
      mean < forwardPrefixMean (fun k => X k omega) n +
        singularFractionObservableLILBoundary
            (forwardHybridBesselPenalty (fun k => X k omega) n) delta /
          (n : Real) := by
  intro n hn
  have hsum := singularFractionLowerMixture_observableLIL_boundary
    hX_unit hmean_unit hdelta hdelta_one homega n hn
  have hidentity := sum_mean_sub_eq_mul_sub_forwardPrefixMean
    (fun k => X k omega) mean (show 0 < n by omega)
  rw [hidentity] at hsum
  have hnpos : 0 < (n : Real) := Nat.cast_pos.mpr (by omega)
  have hdiv : mean - forwardPrefixMean (fun k => X k omega) n <
      singularFractionObservableLILBoundary
          (forwardHybridBesselPenalty (fun k => X k omega) n) delta /
        (n : Real) := by
    apply (lt_div_iff₀ hnpos).2
    nlinarith
  linarith

/-- End-to-end one-event observable LIL-order deviation theorem.  The event is
chosen before the time quantifier and has outer mass at most `delta`. -/
theorem singularFractionLowerMixture_timeUniform_observableLIL
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration Nat mOmega} {X : Nat → Omega → Real}
    {mean delta : Real}
    (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (hX_adapted : IncrementAdapted F X)
    (hX_unit : ∀ k omega, X k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : mean ∈ Set.Icc (0 : Real) 1)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] fun _ => mean) :
    mu.real (singularFractionLowerMixtureExceptionalEvent X mean delta) <=
        delta ∧
      ∀ omega ∉ singularFractionLowerMixtureExceptionalEvent X mean delta,
        ∀ n : Nat, 2 <= n →
          (∑ k ∈ Finset.range n, (mean - X k omega)) <
            singularFractionObservableLILBoundary
              (forwardHybridBesselPenalty (fun k => X k omega) n) delta := by
  constructor
  · exact singularFractionLowerMixtureExceptionalEvent_mass_le_delta
      hdelta hX_adapted hX_unit hmean_unit hmean
  · intro omega homega
    exact singularFractionLowerMixture_observableLIL_boundary
      hX_unit hmean_unit hdelta hdelta_one homega

/-- End-to-end one-event ordinary monitored-mean corollary. -/
theorem singularFractionLowerMixture_timeUniform_observableLIL_mean
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration Nat mOmega} {X : Nat → Omega → Real}
    {mean delta : Real}
    (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (hX_adapted : IncrementAdapted F X)
    (hX_unit : ∀ k omega, X k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : mean ∈ Set.Icc (0 : Real) 1)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] fun _ => mean) :
    mu.real (singularFractionLowerMixtureExceptionalEvent X mean delta) <=
        delta ∧
      ∀ omega ∉ singularFractionLowerMixtureExceptionalEvent X mean delta,
        ∀ n : Nat, 2 <= n →
          mean < forwardPrefixMean (fun k => X k omega) n +
            singularFractionObservableLILBoundary
                (forwardHybridBesselPenalty (fun k => X k omega) n) delta /
              (n : Real) := by
  constructor
  · exact singularFractionLowerMixtureExceptionalEvent_mass_le_delta
      hdelta hX_adapted hX_unit hmean_unit hmean
  · intro omega homega
    exact singularFractionLowerMixture_observableLIL_mean
      hX_unit hmean_unit hdelta hdelta_one homega

end

end FormalSLT.AnytimeValid
