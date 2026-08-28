/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.AnytimeValid.SingularFractionObservableLIL

/-!
# Exact scalar optimization for the singular-fraction observable envelope

The singular-fraction mixture gives the all-fraction numerator

`lambda * Q + exp 1 / lambda * log (L * (L + 1) / delta)`.

The existing observable construction bounds the logarithmic price by a
positive path-dependent cost `C`.  This file optimizes the resulting surrogate

`lambda * Q + exp 1 * C / lambda`

exactly over `0 < lambda <= exp (-1)`.  The capped minimizer is `exp (-1)` when
`Q <= exp 3 * C`, and `sqrt (exp 1 * C / Q)` otherwise.  It is no smaller than
the earlier safe tilt, so the same singular-window cost certificate remains
valid.  The resulting envelope is pointwise no larger than the earlier
`(1 + exp 1) * sqrt (M * C)` envelope.

The argmin is exact for the displayed surrogate, not for the original
logarithmic boundary before its window price is bounded by `C`.  No statistical
or stochastic claim is introduced in the scalar optimization itself.
-/

open MeasureTheory ProbabilityTheory

namespace FormalSLT.AnytimeValid

noncomputable section

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}

/-- The post-window-price scalar surrogate optimized in this file. -/
def singularFractionObservableSurrogate
    (Q delta lam : Real) : Real :=
  lam * Q + Real.exp 1 * singularFractionObservableCost Q delta / lam

/-- Exact capped optimizer of `singularFractionObservableSurrogate` over
`0 < lambda <= exp (-1)`. -/
def singularFractionObservableSharpLambda (Q delta : Real) : Real :=
  let C := singularFractionObservableCost Q delta
  if Q <= Real.exp 3 * C then
    Real.exp (-1)
  else
    Real.sqrt (Real.exp 1 * C / Q)

/-- Observable envelope obtained by evaluating the surrogate at its exact
capped optimizer. -/
def singularFractionObservableSharpLILBoundary (Q delta : Real) : Real :=
  singularFractionObservableSurrogate Q delta
    (singularFractionObservableSharpLambda Q delta)

/-- The exact capped optimizer is strictly positive for every input. -/
theorem singularFractionObservableSharpLambda_pos (Q delta : Real) :
    0 < singularFractionObservableSharpLambda Q delta := by
  let C := singularFractionObservableCost Q delta
  have hC : 0 < C := by
    simpa [C] using singularFractionObservableCost_pos Q delta
  by_cases hsmall : Q <= Real.exp 3 * C
  · simp [singularFractionObservableSharpLambda, C, hsmall, Real.exp_pos]
  · have hQ : 0 < Q := by
      have hlarge : Real.exp 3 * C < Q := lt_of_not_ge hsmall
      exact (mul_pos (Real.exp_pos 3) hC).trans hlarge
    simp only [singularFractionObservableSharpLambda, C, if_neg hsmall]
    exact Real.sqrt_pos.mpr
      (div_pos (mul_pos (Real.exp_pos 1) hC) hQ)

/-- The exact capped optimizer remains in the singular-mixture admissible
fraction range. -/
theorem singularFractionObservableSharpLambda_le_exp_neg_one
    (Q delta : Real) :
    singularFractionObservableSharpLambda Q delta <= Real.exp (-1) := by
  let C := singularFractionObservableCost Q delta
  have hC : 0 < C := by
    simpa [C] using singularFractionObservableCost_pos Q delta
  by_cases hsmall : Q <= Real.exp 3 * C
  · simp [singularFractionObservableSharpLambda, C, hsmall]
  · have hlarge : Real.exp 3 * C < Q := lt_of_not_ge hsmall
    have hQ : 0 < Q := (mul_pos (Real.exp_pos 3) hC).trans hlarge
    have harg : 0 <= Real.exp 1 * C / Q :=
      (div_pos (mul_pos (Real.exp_pos 1) hC) hQ).le
    have hratio : Real.exp 1 * C / Q <= Real.exp (-2) := by
      apply le_of_lt
      apply (div_lt_iff₀ hQ).2
      have hscaled := mul_lt_mul_of_pos_left hlarge (Real.exp_pos (-2))
      calc
        Real.exp 1 * C = Real.exp (-2) * (Real.exp 3 * C) := by
          rw [show Real.exp 1 = Real.exp (-2) * Real.exp 3 by
            rw [← Real.exp_add]
            norm_num]
          ring
        _ < Real.exp (-2) * Q := hscaled
    simp only [singularFractionObservableSharpLambda, C, if_neg hsmall]
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.exp_pos (-1)).le).mp
    rw [Real.sq_sqrt harg]
    calc
      Real.exp 1 * C / Q <= Real.exp (-2) := hratio
      _ = (Real.exp (-1)) ^ 2 := by
        rw [pow_two, ← Real.exp_add]
        norm_num

/-- The earlier safe observable tilt is no larger than the exact capped
surrogate optimizer.  Consequently the sharper tilt stays inside the same
certified log-window region. -/
theorem singularFractionObservableTunedLambda_le_sharpLambda
    {Q : Real} (hQ : 0 <= Q) (delta : Real) :
    singularFractionObservableTunedLambda Q delta <=
      singularFractionObservableSharpLambda Q delta := by
  let C := singularFractionObservableCost Q delta
  let M := singularFractionObservableScale Q delta
  have hC : 0 < C := by
    simpa [C] using singularFractionObservableCost_pos Q delta
  have hM : 0 < M := by
    simpa [M] using singularFractionObservableScale_pos Q delta
  by_cases hsmall : Q <= Real.exp 3 * C
  · rw [show singularFractionObservableSharpLambda Q delta =
        Real.exp (-1) by
      simp [singularFractionObservableSharpLambda, C, hsmall]]
    exact singularFractionObservableTunedLambda_le_exp_neg_one Q delta
  · have hlarge : Real.exp 3 * C < Q := lt_of_not_ge hsmall
    have hQpos : 0 < Q := (mul_pos (Real.exp_pos 3) hC).trans hlarge
    have hQM : Q <= M := by
      exact (le_singularFractionObservablePenaltyFloor Q).trans
        (singularFractionObservablePenaltyFloor_le_scale Q delta)
    have hold_sq : singularFractionObservableTunedLambda Q delta ^ 2 = C / M := by
      simpa [C, M] using singularFractionObservableTunedLambda_sq Q delta
    have hsharp_sq : singularFractionObservableSharpLambda Q delta ^ 2 =
        Real.exp 1 * C / Q := by
      rw [show singularFractionObservableSharpLambda Q delta =
          Real.sqrt (Real.exp 1 * C / Q) by
        simp [singularFractionObservableSharpLambda, C, hsmall]]
      exact Real.sq_sqrt
        (div_nonneg (mul_nonneg (Real.exp_pos 1).le hC.le) hQpos.le)
    have hdiv : C / M <= C / Q :=
      div_le_div_of_nonneg_left hC.le hQpos hQM
    have hone : (1 : Real) <= Real.exp 1 :=
      Real.one_le_exp (by norm_num)
    have hscale : C / Q <= Real.exp 1 * C / Q := by
      apply div_le_div_of_nonneg_right _ hQpos.le
      nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hone)]
    apply (sq_le_sq₀
      (singularFractionObservableTunedLambda_pos Q delta).le
      (singularFractionObservableSharpLambda_pos Q delta).le).mp
    rw [hold_sq, hsharp_sq]
    exact hdiv.trans hscale

/-- The existing observable log-window cost bound remains valid at the larger
exact surrogate optimizer. -/
theorem singularFraction_sharpLambda_logWindowCost_le
    {Q delta : Real} (hQ : 0 <= Q)
    (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    Real.log
        (singularFractionLogScale
              (singularFractionObservableSharpLambda Q delta) *
            (singularFractionLogScale
                (singularFractionObservableSharpLambda Q delta) + 1) /
          delta) <=
      singularFractionObservableCost Q delta := by
  let oldLam := singularFractionObservableTunedLambda Q delta
  let sharpLam := singularFractionObservableSharpLambda Q delta
  let oldL := singularFractionLogScale oldLam
  let sharpL := singularFractionLogScale sharpLam
  have hold_pos : 0 < oldLam := by
    simpa [oldLam] using singularFractionObservableTunedLambda_pos Q delta
  have hsharp_pos : 0 < sharpLam := by
    simpa [sharpLam] using singularFractionObservableSharpLambda_pos Q delta
  have hold_le : oldLam <= sharpLam := by
    simpa [oldLam, sharpLam] using
      singularFractionObservableTunedLambda_le_sharpLambda hQ delta
  have hold_cap : oldLam <= Real.exp (-1) := by
    simpa [oldLam] using
      singularFractionObservableTunedLambda_le_exp_neg_one Q delta
  have hsharp_cap : sharpLam <= Real.exp (-1) := by
    simpa [sharpLam] using
      singularFractionObservableSharpLambda_le_exp_neg_one Q delta
  have hlog_order : Real.log oldLam <= Real.log sharpLam :=
    Real.log_le_log hold_pos hold_le
  have hscale_order : sharpL <= oldL := by
    dsimp [sharpL, oldL, singularFractionLogScale]
    linarith
  have holdL : 1 <= oldL := by
    simpa [oldL] using
      one_le_singularFractionLogScale hold_pos hold_cap
  have hsharpL : 1 <= sharpL := by
    simpa [sharpL] using
      one_le_singularFractionLogScale hsharp_pos hsharp_cap
  have hpoly : sharpL * (sharpL + 1) <= oldL * (oldL + 1) := by
    have hfactor : 0 <= (oldL - sharpL) * (oldL + sharpL + 1) := by
      exact mul_nonneg (sub_nonneg.mpr hscale_order) (by linarith)
    nlinarith
  have hratio : sharpL * (sharpL + 1) / delta <=
      oldL * (oldL + 1) / delta :=
    div_le_div_of_nonneg_right hpoly hdelta.le
  have hleft_pos : 0 < sharpL * (sharpL + 1) / delta := by positivity
  have hlog_mono :
      Real.log (sharpL * (sharpL + 1) / delta) <=
        Real.log (oldL * (oldL + 1) / delta) :=
    Real.log_le_log hleft_pos hratio
  have hold_cost := singularFraction_tunedLambda_logWindowCost_le
    (Q := Q) hdelta hdelta_one
  simpa [sharpLam, oldLam, sharpL, oldL] using hlog_mono.trans hold_cost

/-- The capped tilt is the exact global minimizer of the declared observable
surrogate over the whole admissible singular-fraction range. -/
theorem singularFractionObservableSharpLambda_argmin
    {Q : Real} (hQ : 0 <= Q) (delta : Real)
    {lam : Real} (hlam : 0 < lam) (hlam_cap : lam <= Real.exp (-1)) :
    singularFractionObservableSharpLILBoundary Q delta <=
      singularFractionObservableSurrogate Q delta lam := by
  let C := singularFractionObservableCost Q delta
  let a := Real.exp 1 * C
  have hC : 0 < C := by
    simpa [C] using singularFractionObservableCost_pos Q delta
  have ha : 0 < a := mul_pos (Real.exp_pos 1) hC
  by_cases hsmall : Q <= Real.exp 3 * C
  · let s := Real.exp (-1)
    have hs : 0 < s := by simpa [s] using Real.exp_pos (-1)
    have hsharp : singularFractionObservableSharpLambda Q delta = s := by
      simp [singularFractionObservableSharpLambda, C, hsmall, s]
    have hs_sq : s ^ 2 = Real.exp (-2) := by
      dsimp [s]
      rw [pow_two, ← Real.exp_add]
      norm_num
    have hthreshold : Q * s ^ 2 <= a := by
      rw [hs_sq]
      calc
        Q * Real.exp (-2) <= (Real.exp 3 * C) * Real.exp (-2) :=
          mul_le_mul_of_nonneg_right hsmall (Real.exp_pos (-2)).le
        _ = a := by
          dsimp [a]
          rw [show Real.exp 3 * C * Real.exp (-2) =
              (Real.exp 3 * Real.exp (-2)) * C by ring,
            ← Real.exp_add]
          norm_num
    have hlam_s : lam <= s := by simpa [s] using hlam_cap
    have hlam_s_mul : lam * s <= s ^ 2 := by
      simpa [pow_two] using mul_le_mul_of_nonneg_right hlam_s hs.le
    have hproduct : Q * lam * s <= a := by
      calc
        Q * lam * s = Q * (lam * s) := by ring
        _ <= Q * s ^ 2 := mul_le_mul_of_nonneg_left hlam_s_mul hQ
        _ <= a := hthreshold
    have hfactor : 0 <= (s - lam) * (a - Q * lam * s) :=
      mul_nonneg (sub_nonneg.mpr hlam_s) (sub_nonneg.mpr hproduct)
    have hidentity :
        (singularFractionObservableSurrogate Q delta lam -
            singularFractionObservableSurrogate Q delta s) * (lam * s) =
          (s - lam) * (a - Q * lam * s) := by
      unfold singularFractionObservableSurrogate
      dsimp [a, C]
      field_simp [hlam.ne', hs.ne']
      ring
    have hmul : 0 <=
        (singularFractionObservableSurrogate Q delta lam -
            singularFractionObservableSurrogate Q delta s) * (lam * s) := by
      rw [hidentity]
      exact hfactor
    have hdiff : 0 <=
        singularFractionObservableSurrogate Q delta lam -
          singularFractionObservableSurrogate Q delta s :=
      nonneg_of_mul_nonneg_right hmul (mul_pos hlam hs)
    unfold singularFractionObservableSharpLILBoundary
    rw [hsharp]
    exact sub_nonneg.mp hdiff
  · have hlarge : Real.exp 3 * C < Q := lt_of_not_ge hsmall
    have hQpos : 0 < Q := (mul_pos (Real.exp_pos 3) hC).trans hlarge
    let s := Real.sqrt (a / Q)
    have hratio : 0 < a / Q := div_pos ha hQpos
    have hs : 0 < s := by
      dsimp [s]
      exact Real.sqrt_pos.mpr hratio
    have hs_sq : s ^ 2 = a / Q := by
      dsimp [s]
      exact Real.sq_sqrt hratio.le
    have hbalance : Q * s ^ 2 = a := by
      rw [hs_sq]
      field_simp [hQpos.ne']
    have hsharp : singularFractionObservableSharpLambda Q delta = s := by
      simp [singularFractionObservableSharpLambda, C, hsmall, s, a]
    have hidentity :
        (singularFractionObservableSurrogate Q delta lam -
            singularFractionObservableSurrogate Q delta s) * lam =
          Q * (lam - s) ^ 2 := by
      unfold singularFractionObservableSurrogate
      change
        (lam * Q + a / lam - (s * Q + a / s)) * lam =
          Q * (lam - s) ^ 2
      rw [← hbalance]
      field_simp [hlam.ne', hs.ne']
      ring
    have hmul : 0 <=
        (singularFractionObservableSurrogate Q delta lam -
            singularFractionObservableSurrogate Q delta s) * lam := by
      rw [hidentity]
      positivity
    have hdiff : 0 <=
        singularFractionObservableSurrogate Q delta lam -
          singularFractionObservableSurrogate Q delta s :=
      nonneg_of_mul_nonneg_right hmul hlam
    unfold singularFractionObservableSharpLILBoundary
    rw [hsharp]
    exact sub_nonneg.mp hdiff

/-- The exactly optimized surrogate envelope is pointwise no larger than the
earlier observable LIL-order envelope. -/
theorem singularFractionObservableSharpLILBoundary_le_observableLILBoundary
    {Q : Real} (hQ : 0 <= Q) (delta : Real) :
    singularFractionObservableSharpLILBoundary Q delta <=
      singularFractionObservableLILBoundary Q delta := by
  let C := singularFractionObservableCost Q delta
  let M := singularFractionObservableScale Q delta
  let oldLam := singularFractionObservableTunedLambda Q delta
  let B := Real.sqrt (M * C)
  have hC : 0 < C := by
    simpa [C] using singularFractionObservableCost_pos Q delta
  have hM : 0 < M := by
    simpa [M] using singularFractionObservableScale_pos Q delta
  have holdLam : 0 < oldLam := by
    simpa [oldLam] using singularFractionObservableTunedLambda_pos Q delta
  have holdLam_cap : oldLam <= Real.exp (-1) := by
    simpa [oldLam] using
      singularFractionObservableTunedLambda_le_exp_neg_one Q delta
  have hmin := singularFractionObservableSharpLambda_argmin
    hQ delta holdLam holdLam_cap
  have hMC : 0 <= M * C := mul_nonneg hM.le hC.le
  have hB : 0 <= B := by
    dsimp [B]
    exact Real.sqrt_nonneg _
  have hold_sq : oldLam ^ 2 = C / M := by
    simpa [oldLam, C, M] using
      singularFractionObservableTunedLambda_sq Q delta
  have hold_sq_mul : oldLam ^ 2 * M = C := by
    rw [hold_sq]
    exact div_mul_cancel₀ C hM.ne'
  have holdM_sq : (oldLam * M) ^ 2 = M * C := by
    calc
      (oldLam * M) ^ 2 = (oldLam ^ 2 * M) * M := by ring
      _ = C * M := by rw [hold_sq_mul]
      _ = M * C := by ring
  have hB_sq : B ^ 2 = M * C := by
    simpa [B] using Real.sq_sqrt hMC
  have holdM_eq : oldLam * M = B := by
    have holdM0 : 0 <= oldLam * M := mul_nonneg holdLam.le hM.le
    nlinarith
  have hQ_le_M : Q <= M :=
    (le_singularFractionObservablePenaltyFloor Q).trans
      (singularFractionObservablePenaltyFloor_le_scale Q delta)
  have hlinear : oldLam * Q <= B := by
    calc
      oldLam * Q <= oldLam * M :=
        mul_le_mul_of_nonneg_left hQ_le_M holdLam.le
      _ = B := holdM_eq
  have hC_div_lam : C / oldLam = B := by
    calc
      C / oldLam = oldLam * M := by
        apply (div_eq_iff holdLam.ne').2
        nlinarith
      _ = B := holdM_eq
  have hsurrogate_old :
      singularFractionObservableSurrogate Q delta oldLam <=
        singularFractionObservableLILBoundary Q delta := by
    unfold singularFractionObservableSurrogate
      singularFractionObservableLILBoundary
    change oldLam * Q + Real.exp 1 * C / oldLam <=
      (1 + Real.exp 1) * B
    have hprice : Real.exp 1 * C / oldLam = Real.exp 1 * B := by
      calc
        Real.exp 1 * C / oldLam = Real.exp 1 * (C / oldLam) := by ring
        _ = Real.exp 1 * B := by rw [hC_div_lam]
    rw [hprice]
    nlinarith [mul_nonneg (Real.exp_pos 1).le hB]
  exact hmin.trans hsurrogate_old

/-- The original singular-window numerator evaluated at the sharp tilt is
bounded by the sharper observable envelope. -/
theorem singularFraction_sharpTunedBoundary_le_sharpObservableLIL
    {Q delta : Real} (hQ : 0 <= Q)
    (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    singularFractionObservableSharpLambda Q delta * Q +
        Real.exp 1 / singularFractionObservableSharpLambda Q delta *
          Real.log
            (singularFractionLogScale
                  (singularFractionObservableSharpLambda Q delta) *
                (singularFractionLogScale
                    (singularFractionObservableSharpLambda Q delta) + 1) /
              delta) <=
      singularFractionObservableSharpLILBoundary Q delta := by
  let lam := singularFractionObservableSharpLambda Q delta
  let C := singularFractionObservableCost Q delta
  have hlam : 0 < lam := by
    simpa [lam] using singularFractionObservableSharpLambda_pos Q delta
  have hlog := singularFraction_sharpLambda_logWindowCost_le
    hQ hdelta hdelta_one
  have hprice : Real.exp 1 / lam *
        Real.log
          (singularFractionLogScale lam *
              (singularFractionLogScale lam + 1) / delta) <=
      Real.exp 1 * C / lam := by
    calc
      Real.exp 1 / lam *
          Real.log
            (singularFractionLogScale lam *
                (singularFractionLogScale lam + 1) / delta) <=
        Real.exp 1 / lam * C :=
          mul_le_mul_of_nonneg_left
            (by simpa [lam, C] using hlog) (by positivity)
      _ = Real.exp 1 * C / lam := by ring
  unfold singularFractionObservableSharpLILBoundary
    singularFractionObservableSurrogate
  change lam * Q + Real.exp 1 / lam *
      Real.log
        (singularFractionLogScale lam *
            (singularFractionLogScale lam + 1) / delta) <=
    lam * Q + Real.exp 1 * C / lam
  exact add_le_add_left hprice _

/-- Outside the singular-mixture event, the sharper observable numerator
controls every reporting time. -/
theorem singularFractionLowerMixture_sharpObservableLIL_boundary
    {X : Nat → Omega → Real} {mean delta : Real}
    (hX_unit : ∀ k omega, X k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : mean ∈ Set.Icc (0 : Real) 1)
    (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    {omega : Omega}
    (homega : omega ∉
      singularFractionLowerMixtureExceptionalEvent X mean delta) :
    ∀ n : Nat, 2 <= n →
      (∑ k ∈ Finset.range n, (mean - X k omega)) <
        singularFractionObservableSharpLILBoundary
          (forwardHybridBesselPenalty (fun k ↦ X k omega) n) delta := by
  intro n hn
  let Q := forwardHybridBesselPenalty (fun k ↦ X k omega) n
  let lam := singularFractionObservableSharpLambda Q delta
  have hQ : 0 <= Q := by
    simpa [Q] using forwardHybridBesselPenalty_nonneg_of_two
      (fun k ↦ X k omega) hn
  have hfixed := singularFractionLowerMixture_all_fraction_boundary
    hX_unit hmean_unit hdelta hdelta_one homega n hn lam
      (by simpa [lam] using singularFractionObservableSharpLambda_pos Q delta)
      (by simpa [lam] using
        singularFractionObservableSharpLambda_le_exp_neg_one Q delta)
  have henvelope := singularFraction_sharpTunedBoundary_le_sharpObservableLIL
    hQ hdelta hdelta_one
  exact hfixed.trans_le (by
    simpa [singularFractionForwardBesselBoundary, lam, Q] using henvelope)

/-- Ordinary monitored-mean form of the sharper observable corollary. -/
theorem singularFractionLowerMixture_sharpObservableLIL_mean
    {X : Nat → Omega → Real} {mean delta : Real}
    (hX_unit : ∀ k omega, X k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : mean ∈ Set.Icc (0 : Real) 1)
    (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    {omega : Omega}
    (homega : omega ∉
      singularFractionLowerMixtureExceptionalEvent X mean delta) :
    ∀ n : Nat, 2 <= n →
      mean < forwardPrefixMean (fun k ↦ X k omega) n +
        singularFractionObservableSharpLILBoundary
            (forwardHybridBesselPenalty (fun k ↦ X k omega) n) delta /
          (n : Real) := by
  intro n hn
  have hsum := singularFractionLowerMixture_sharpObservableLIL_boundary
    hX_unit hmean_unit hdelta hdelta_one homega n hn
  have hidentity := sum_mean_sub_eq_mul_sub_forwardPrefixMean
    (fun k ↦ X k omega) mean (show 0 < n by omega)
  rw [hidentity] at hsum
  have hnpos : 0 < (n : Real) := Nat.cast_pos.mpr (by omega)
  have hdiv : mean - forwardPrefixMean (fun k ↦ X k omega) n <
      singularFractionObservableSharpLILBoundary
          (forwardHybridBesselPenalty (fun k ↦ X k omega) n) delta /
        (n : Real) := by
    apply (lt_div_iff₀ hnpos).2
    nlinarith
  linarith

/-- End-to-end one-event monitored-mean theorem with the sharper envelope. -/
theorem singularFractionLowerMixture_timeUniform_sharpObservableLIL_mean
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration Nat mOmega} {X : Nat → Omega → Real}
    {mean delta : Real}
    (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (hX_adapted : IncrementAdapted F X)
    (hX_unit : ∀ k omega, X k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : mean ∈ Set.Icc (0 : Real) 1)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] fun _ ↦ mean) :
    mu.real (singularFractionLowerMixtureExceptionalEvent X mean delta) <=
        delta ∧
      ∀ omega ∉ singularFractionLowerMixtureExceptionalEvent X mean delta,
        ∀ n : Nat, 2 <= n →
          mean < forwardPrefixMean (fun k ↦ X k omega) n +
            singularFractionObservableSharpLILBoundary
                (forwardHybridBesselPenalty (fun k ↦ X k omega) n) delta /
              (n : Real) := by
  constructor
  · exact singularFractionLowerMixtureExceptionalEvent_mass_le_delta
      hdelta hX_adapted hX_unit hmean_unit hmean
  · intro omega homega
    exact singularFractionLowerMixture_sharpObservableLIL_mean
      hX_unit hmean_unit hdelta hdelta_one homega

end

end FormalSLT.AnytimeValid
