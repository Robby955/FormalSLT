/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Pointwise Bennett / sub-gamma Taylor inequality

The **load-bearing real-analysis sub-lemma** of the conditional sub-gamma
MGF extractor. For real `x` with `|x| ≤ b`, real `λ ≥ 0`, and `b · λ < 3`:

    exp (λ · x) ≤ 1 + λ · x + (λ² · x²) / (2 · (1 − b · λ / 3))

## Proof strategy

Substitute `v := λ · x`, so `|v| ≤ b · λ < 3`. The Taylor expansion gives

    exp v − 1 − v = v² · ∑'_{n} v^n / (n + 2)!

We bound the tail by

    v^n / (n + 2)!  ≤  |v|^n / (n + 2)!  ≤  (|v| / 3)^n / 2,

where the second inequality uses the elementary fact `2 · 3^n ≤ (n + 2)!`
(established by induction). Summing the geometric series `∑' (|v|/3)^n =
1 / (1 − |v|/3)` and using `|v| ≤ b · λ` gives the bound.

This unified series argument avoids a separate negative-side calculus
lemma: the termwise comparison `v^n ≤ |v|^n` handles both signs of `v`.
-/

open scoped Nat

namespace FormalSLT.Concentration.SubGamma

/-- Elementary factorial growth bound: `2 · 3^k ≤ (k + 2)!` for all `k : ℕ`.

Base case `k = 0`: `2 ≤ 2`. Inductive step uses `k + 3 ≥ 3` so
`(k + 3)! = (k + 3) · (k + 2)! ≥ 3 · (k + 2)! ≥ 3 · 2 · 3^k = 2 · 3^(k+1)`. -/
private lemma factorial_two_three_pow (k : ℕ) : 2 * 3 ^ k ≤ (k + 2)! := by
  induction k with
  | zero => decide
  | succ n ih =>
    calc 2 * 3 ^ (n + 1)
        = 3 * (2 * 3 ^ n) := by ring
      _ ≤ 3 * (n + 2)! := Nat.mul_le_mul_left 3 ih
      _ ≤ (n + 3) * (n + 2)! := Nat.mul_le_mul_right _ (by omega)
      _ = (n + 1 + 2)! := rfl

/-- The core series bound. For any `v c : ℝ` with `|v| ≤ c < 3`,

    exp v − 1 − v  ≤  v² / (2 · (1 − c / 3)).

Proof via the Taylor series `exp v − 1 − v = v² · ∑'_n v^n / (n + 2)!`
combined with the termwise bound `|v|^n / (n + 2)! ≤ (|v|/3)^n / 2`. -/
private lemma exp_sub_one_sub_id_le_bennett {v c : ℝ}
    (h_abs : |v| ≤ c) (hc : c < 3) :
    Real.exp v - 1 - v ≤ v ^ 2 / (2 * (1 - c / 3)) := by
  -- Setup: bounds on c and |v|.
  have habs_v_nonneg : 0 ≤ |v| := abs_nonneg v
  have hc_nonneg : 0 ≤ c := le_trans habs_v_nonneg h_abs
  have habs_v_lt : |v| < 3 := lt_of_le_of_lt h_abs hc
  have hc3_pos : 0 < 1 - c / 3 := by linarith
  have habs3_lt_one : |v| / 3 < 1 := by linarith
  have habs3_nonneg : 0 ≤ |v| / 3 := by positivity
  have habs3_diff_pos : 0 < 1 - |v| / 3 := by linarith
  -- Step 1: Real.exp v = ∑' n, v^n / n!
  have hexp_tsum : Real.exp v = ∑' n : ℕ, v ^ n / (n ! : ℝ) := by
    rw [Real.exp_eq_exp_ℝ]
    exact congrFun (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)) v
  have hsum_exp : Summable (fun n : ℕ => v ^ n / (n ! : ℝ)) :=
    Real.summable_pow_div_factorial v
  -- Step 2: Extract the first two terms via `Summable.sum_add_tsum_nat_add`.
  have hsum_split :
      (∑ i ∈ Finset.range 2, v ^ i / (i ! : ℝ))
        + ∑' i, v ^ (i + 2) / ((i + 2)! : ℝ)
      = ∑' n, v ^ n / (n ! : ℝ) :=
    hsum_exp.sum_add_tsum_nat_add 2
  have hsum2_eq : (∑ i ∈ Finset.range 2, v ^ i / (i ! : ℝ)) = 1 + v := by
    simp [Finset.sum_range_succ]
  have hexp_minus :
      Real.exp v - 1 - v = ∑' i, v ^ (i + 2) / ((i + 2)! : ℝ) := by
    have hrearr : Real.exp v = (1 + v) + ∑' i, v ^ (i + 2) / ((i + 2)! : ℝ) := by
      rw [hexp_tsum, ← hsum_split, hsum2_eq]
    linarith
  -- Step 3: Summability of `fun i => v^i / (i+2)!`.
  have hsum_quotient : Summable (fun i : ℕ => v ^ i / ((i + 2)! : ℝ)) := by
    refine (Real.summable_pow_div_factorial |v|).of_norm_bounded (fun i => ?_)
    rw [Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
    apply div_le_div_of_nonneg_left (pow_nonneg habs_v_nonneg _)
    · exact_mod_cast Nat.factorial_pos i
    · exact_mod_cast Nat.factorial_le (Nat.le_add_right i 2)
  -- Step 4: Factor `v²` out of the tail.
  have hfactor :
      (∑' i, v ^ (i + 2) / ((i + 2)! : ℝ))
        = v ^ 2 * ∑' i, v ^ i / ((i + 2)! : ℝ) := by
    rw [← hsum_quotient.tsum_mul_left (v ^ 2)]
    apply tsum_congr
    intro i
    rw [pow_add]
    ring
  -- Step 5: Summability of `fun i => |v|^i / (i+2)!`.
  have hsum_quotient_abs : Summable (fun i : ℕ => |v| ^ i / ((i + 2)! : ℝ)) := by
    refine (Real.summable_pow_div_factorial |v|).of_norm_bounded (fun i => ?_)
    have h_nonneg : 0 ≤ |v| ^ i / ((i + 2)! : ℝ) :=
      div_nonneg (pow_nonneg habs_v_nonneg _) (Nat.cast_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
    apply div_le_div_of_nonneg_left (pow_nonneg habs_v_nonneg _)
    · exact_mod_cast Nat.factorial_pos i
    · exact_mod_cast Nat.factorial_le (Nat.le_add_right i 2)
  -- Step 6: Termwise `v^i / (i+2)! ≤ |v|^i / (i+2)!`.
  have hbound1 :
      (∑' i, v ^ i / ((i + 2)! : ℝ))
        ≤ ∑' i, |v| ^ i / ((i + 2)! : ℝ) := by
    apply Summable.tsum_le_tsum _ hsum_quotient hsum_quotient_abs
    intro i
    have h_le : v ^ i ≤ |v| ^ i := (le_abs_self _).trans (abs_pow v i).le
    have h_pos : (0 : ℝ) < ((i + 2)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    exact div_le_div_of_nonneg_right h_le h_pos.le
  -- Step 7: Termwise `|v|^i / (i+2)! ≤ (|v|/3)^i / 2`.
  have hsum_geom_half : Summable (fun i : ℕ => (|v| / 3) ^ i / 2) := by
    have hgeom := summable_geometric_of_lt_one habs3_nonneg habs3_lt_one
    exact hgeom.div_const 2
  have hbound2 :
      (∑' i, |v| ^ i / ((i + 2)! : ℝ))
        ≤ ∑' i, (|v| / 3) ^ i / 2 := by
    apply Summable.tsum_le_tsum _ hsum_quotient_abs hsum_geom_half
    intro i
    have hfact_real : (2 : ℝ) * 3 ^ i ≤ ((i + 2)! : ℝ) := by
      exact_mod_cast factorial_two_three_pow i
    have h_pos_23i : (0 : ℝ) < 2 * 3 ^ i := by positivity
    have h_three_pos : (0 : ℝ) < (3 : ℝ) ^ i := pow_pos (by norm_num) _
    have h_step1 : |v| ^ i / ((i + 2)! : ℝ) ≤ |v| ^ i / (2 * 3 ^ i) := by
      apply div_le_div_of_nonneg_left (pow_nonneg habs_v_nonneg _)
      · exact h_pos_23i
      · exact hfact_real
    have h_step2 : |v| ^ i / (2 * 3 ^ i) = (|v| / 3) ^ i / 2 := by
      rw [div_pow, div_div, mul_comm 2 ((3 : ℝ) ^ i)]
    rw [← h_step2]
    exact h_step1
  -- Step 8: Geometric tsum.
  have hgeom_eq :
      ∑' i : ℕ, (|v| / 3) ^ i / 2 = 1 / (2 * (1 - |v| / 3)) := by
    have hgeom := summable_geometric_of_lt_one habs3_nonneg habs3_lt_one
    have heq : (fun i : ℕ => (|v| / 3) ^ i / 2) = fun i => (1 / 2) * (|v| / 3) ^ i := by
      funext i; ring
    rw [heq, hgeom.tsum_mul_left (1 / 2 : ℝ),
      tsum_geometric_of_lt_one habs3_nonneg habs3_lt_one]
    have hne : (1 - |v| / 3 : ℝ) ≠ 0 := habs3_diff_pos.ne'
    field_simp
  -- Step 9: Combine everything.
  have h_sq_nonneg : (0 : ℝ) ≤ v ^ 2 := sq_nonneg v
  have h_tail_le : (∑' i, v ^ i / ((i + 2)! : ℝ)) ≤ 1 / (2 * (1 - |v| / 3)) := by
    calc (∑' i, v ^ i / ((i + 2)! : ℝ))
        ≤ ∑' i, |v| ^ i / ((i + 2)! : ℝ) := hbound1
      _ ≤ ∑' i, (|v| / 3) ^ i / 2 := hbound2
      _ = 1 / (2 * (1 - |v| / 3)) := hgeom_eq
  -- Apply the bound to the v² factor.
  have h_final_pre :
      Real.exp v - 1 - v ≤ v ^ 2 / (2 * (1 - |v| / 3)) := by
    calc Real.exp v - 1 - v
        = ∑' i, v ^ (i + 2) / ((i + 2)! : ℝ) := hexp_minus
      _ = v ^ 2 * ∑' i, v ^ i / ((i + 2)! : ℝ) := hfactor
      _ ≤ v ^ 2 * (1 / (2 * (1 - |v| / 3))) :=
          mul_le_mul_of_nonneg_left h_tail_le h_sq_nonneg
      _ = v ^ 2 / (2 * (1 - |v| / 3)) := by ring
  -- Final monotonicity: weaken from |v| to c.
  have h_denom_le : 2 * (1 - c / 3) ≤ 2 * (1 - |v| / 3) := by
    have : |v| / 3 ≤ c / 3 := by linarith
    linarith
  have h_denom_pos : (0 : ℝ) < 2 * (1 - c / 3) := by linarith
  calc Real.exp v - 1 - v
      ≤ v ^ 2 / (2 * (1 - |v| / 3)) := h_final_pre
    _ ≤ v ^ 2 / (2 * (1 - c / 3)) :=
        div_le_div_of_nonneg_left h_sq_nonneg h_denom_pos h_denom_le

/--
**Pointwise sub-gamma Taylor / Bennett bound.**

For `|x| ≤ b`, `λ ≥ 0`, and `b · λ < 3`, the exponential `exp(λ · x)` is
dominated by its sub-gamma Taylor surrogate

    1 + λ · x + (λ² · x²) / (2 (1 − b · λ / 3)).

This is the pointwise input to the conditional MGF extractor in
`FormalSLT.Concentration.SubGamma.Extractor`. The inequality holds on
*both* signs of `x` via the unified series argument in
`exp_sub_one_sub_id_le_bennett`.
-/
theorem bennett_taylor_bound
    {x b lam : ℝ}
    (_hb_pos : 0 < b)
    (hlam_nonneg : 0 ≤ lam)
    (hblam : b * lam < 3)
    (hx_lo : -b ≤ x)
    (hx_hi : x ≤ b) :
    Real.exp (lam * x) ≤ 1 + lam * x + lam ^ 2 * x ^ 2 / (2 * (1 - b * lam / 3)) := by
  -- Set v := lam * x. Bounds: -(b * lam) ≤ v ≤ b * lam, hence |v| ≤ b * lam < 3.
  set v := lam * x with hv_def
  have habs_v : |v| ≤ b * lam := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have := mul_le_mul_of_nonneg_left hx_lo hlam_nonneg
      nlinarith [hlam_nonneg]
    · have := mul_le_mul_of_nonneg_left hx_hi hlam_nonneg
      nlinarith [hlam_nonneg]
  -- Apply the core series bound with c := b * lam.
  have hbennett : Real.exp v - 1 - v ≤ v ^ 2 / (2 * (1 - b * lam / 3)) :=
    exp_sub_one_sub_id_le_bennett habs_v hblam
  -- Rewrite v² = (lam * x)² = lam² * x².
  have hvsq : v ^ 2 = lam ^ 2 * x ^ 2 := by
    show (lam * x) ^ 2 = lam ^ 2 * x ^ 2; ring
  rw [hvsq] at hbennett
  linarith

end FormalSLT.Concentration.SubGamma
