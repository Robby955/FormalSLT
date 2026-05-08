import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Polynomial form of the Sauer-Shelah growth-function bound

Proves the polynomial upper bound on partial binomial sums:

    ∑_{k=0}^{d} C(n,k) ≤ (en/d)^d

for 1 ≤ d ≤ n. This converts the Sauer-Shelah combinatorial bound
(a sum of binomial coefficients) into the clean closed form used in
VC-dimension sample-complexity theorems.

## Proof strategy

The proof uses the standard method:
1. Multiply each binomial coefficient by `(n/d)^{d-k} ≥ 1`, collecting
   a factor of `(n/d)^d` outside the sum.
2. Extend the partial sum to the full binomial sum (adding non-negative terms).
3. Apply the binomial theorem: `∑_{k≤n} C(n,k) (d/n)^k = (1 + d/n)^n`.
4. Bound `(1 + d/n)^n ≤ exp(d)` using `1 + x ≤ exp(x)`.
5. Combine: `(n/d)^d · exp(d) = (en/d)^d`.

No `sorry`, no `admit`, no custom `axiom`.
-/

open scoped BigOperators
open Finset Real

noncomputable section

namespace FormalSLT.VC.SauerShelah

/-- For `0 < d ≤ n`, the partial binomial sum `∑_{k=0}^d C(n,k)` is bounded by
`(e·n/d)^d`. This is the polynomial form of the Sauer-Shelah growth-function
bound, converting the binomial-sum form into a clean closed-form expression. -/
theorem sauerShelah_polynomial_bound {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) :
    (∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ)) ≤ (Real.exp 1 * ↑n / ↑d) ^ d := by
  have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le hd hdn)
  have hnd : (d : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hdn
  -- The ratio d/n ∈ (0, 1].
  have hdn_ratio_pos : (0 : ℝ) < (d : ℝ) / (n : ℝ) := div_pos hdR hnR
  have hdn_ratio_le : (d : ℝ) / (n : ℝ) ≤ 1 := by
    rw [div_le_one hnR]; exact hnd
  -- The ratio n/d ≥ 1.
  have hnd_ratio_ge : (1 : ℝ) ≤ (n : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hdR]; linarith
  -- Step 1: Each C(n,k) ≤ (n/d)^d · C(n,k) · (d/n)^k for k ≤ d.
  -- Equivalently: 1 ≤ (n/d)^(d-k) for k ≤ d.
  have h_per_term : ∀ k ∈ Finset.range (d + 1),
      (n.choose k : ℝ) ≤ ((n : ℝ) / d) ^ d * ((n.choose k : ℝ) * ((d : ℝ) / n) ^ k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkd : k ≤ d := Nat.lt_succ_iff.mp hk
    have hnd_pos : (0 : ℝ) < ((n : ℝ) / (d : ℝ)) := div_pos hnR hdR
    have hnd_ne : ((n : ℝ) / (d : ℝ)) ≠ 0 := ne_of_gt hnd_pos
    have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hdR
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR
    -- Key identity: (d/n)^k = ((n/d)^k)⁻¹
    have h_inv_k : ((d : ℝ) / (n : ℝ)) ^ k = (((n : ℝ) / (d : ℝ)) ^ k)⁻¹ := by
      rw [← inv_pow, inv_div]
    -- (n/d)^d · (d/n)^k = (n/d)^(d-k)
    have h_ratio : ((n : ℝ) / (d : ℝ)) ^ d * ((d : ℝ) / (n : ℝ)) ^ k
        = ((n : ℝ) / (d : ℝ)) ^ (d - k) := by
      rw [h_inv_k, pow_sub₀ _ hnd_ne hkd]
    -- (n/d)^(d-k) ≥ 1
    have h_ge_one : (1 : ℝ) ≤ ((n : ℝ) / (d : ℝ)) ^ (d - k) := by
      simpa using pow_le_pow_left₀ zero_le_one hnd_ratio_ge (d - k)
    have hC_nn : (0 : ℝ) ≤ (n.choose k : ℝ) := Nat.cast_nonneg _
    -- The RHS equals C(n,k) * (n/d)^(d-k) by algebra + h_ratio.
    have h_eq : ((n : ℝ) / d) ^ d * ((n.choose k : ℝ) * ((d : ℝ) / n) ^ k)
        = (n.choose k : ℝ) * (((n : ℝ) / d) ^ (d - k)) := by
      have h_ring : ((n : ℝ) / d) ^ d * ((n.choose k : ℝ) * ((d : ℝ) / n) ^ k)
          = (n.choose k : ℝ) * (((n : ℝ) / d) ^ d * ((d : ℝ) / n) ^ k) := by ring
      rw [h_ring, h_ratio]
    -- C(n,k) ≤ C(n,k) * (n/d)^(d-k) since (n/d)^(d-k) ≥ 1 and C(n,k) ≥ 0.
    rw [h_eq]
    exact le_mul_of_one_le_right hC_nn h_ge_one
  -- Step 1 applied to the sum.
  have h_step1 : ∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ)
      ≤ ((n : ℝ) / d) ^ d * ∑ k ∈ Finset.range (d + 1), ((n.choose k : ℝ) * ((d : ℝ) / n) ^ k) := by
    calc ∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ)
        ≤ ∑ k ∈ Finset.range (d + 1), (((n : ℝ) / d) ^ d * ((n.choose k : ℝ) * ((d : ℝ) / n) ^ k)) :=
          Finset.sum_le_sum h_per_term
      _ = ((n : ℝ) / d) ^ d * ∑ k ∈ Finset.range (d + 1), ((n.choose k : ℝ) * ((d : ℝ) / n) ^ k) := by
          rw [Finset.mul_sum]
  -- Step 2: Extend the partial sum to the full range (adding non-negative terms).
  have h_step2 : ∑ k ∈ Finset.range (d + 1), ((n.choose k : ℝ) * ((d : ℝ) / n) ^ k)
      ≤ ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℝ) * ((d : ℝ) / n) ^ k) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (by omega)
    · intro k _ _
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt hdn_ratio_pos) k)
  -- Step 3: Binomial theorem: ∑_{k=0}^n C(n,k) · (d/n)^k = (1 + d/n)^n.
  have h_step3 : ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℝ) * ((d : ℝ) / n) ^ k)
      = (1 + (d : ℝ) / n) ^ n := by
    have h_binom := add_pow ((d : ℝ) / n) 1 n
    simp only [one_pow, mul_one] at h_binom
    -- h_binom : (↑d / ↑n + 1) ^ n = ∑ x ∈ range (n + 1), (↑d / ↑n) ^ x * ↑(n.choose x)
    rw [show (1 + (d : ℝ) / n) ^ n = ((d : ℝ) / n + 1) ^ n from by ring, h_binom]
    apply Finset.sum_congr rfl
    intro k _; ring
  -- Step 4: (1 + d/n)^n ≤ exp(d).
  have h_step4 : (1 + (d : ℝ) / n) ^ n ≤ Real.exp d := by
    -- From 1 + x ≤ exp(x) with x = d/n:
    have h_one_exp : 1 + (d : ℝ) / n ≤ Real.exp ((d : ℝ) / n) := by
      have := add_one_le_exp ((d : ℝ) / n)
      linarith
    -- Raise to power n: (1 + d/n)^n ≤ exp(d/n)^n.
    have h_pow : (1 + (d : ℝ) / n) ^ n ≤ Real.exp ((d : ℝ) / n) ^ n :=
      pow_le_pow_left₀ (by linarith [hdn_ratio_pos]) h_one_exp n
    -- exp(d/n)^n = exp(n · (d/n)) = exp(d).
    have h_exp_mul : Real.exp ((d : ℝ) / n) ^ n = Real.exp d := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    linarith
  -- Step 5: Combine and simplify to (en/d)^d.
  have h_combine : ((n : ℝ) / d) ^ d * Real.exp d = (Real.exp 1 * ↑n / ↑d) ^ d := by
    have h_exp_d : Real.exp (d : ℝ) = Real.exp 1 ^ d := by
      rw [← Real.exp_nat_mul]; simp
    rw [h_exp_d, ← mul_pow]
    congr 1
    rw [mul_comm, mul_div_assoc]
  -- Chain everything together.
  calc ∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ)
      ≤ ((n : ℝ) / d) ^ d * ∑ k ∈ Finset.range (d + 1), ((n.choose k : ℝ) * ((d : ℝ) / n) ^ k) :=
        h_step1
    _ ≤ ((n : ℝ) / d) ^ d * ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℝ) * ((d : ℝ) / n) ^ k) := by
        apply mul_le_mul_of_nonneg_left h_step2
        exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) d
    _ = ((n : ℝ) / d) ^ d * (1 + (d : ℝ) / n) ^ n := by rw [h_step3]
    _ ≤ ((n : ℝ) / d) ^ d * Real.exp d := by
        apply mul_le_mul_of_nonneg_left h_step4
        exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) d
    _ = (Real.exp 1 * ↑n / ↑d) ^ d := h_combine

end FormalSLT.VC.SauerShelah
