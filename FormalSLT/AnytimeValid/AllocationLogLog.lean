/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.SelectionCost

/-!
# Countable-allocation and log-log guardrails

This file isolates the elementary obstruction behind confidence allocation
over a countable sequence of geometric epochs.  If nonnegative weights have
total mass at most one, then every integer block `[N, 2N]` contains an atom
with weight at most `1 / (N + 1)`.  For positive weights, the corresponding
logarithmic selection cost is at least `log (N + 1)`.

When epoch `k` is associated with geometric scale `4^(k+1)`, the same statement
forces a `log log`-sized atom cost along an unbounded subsequence, up to an
explicit additive constant.  This is a method-specific obstruction for
countable confidence allocation or union-bound stitching.  It is not a
minimax lower bound for confidence sequences and does not assert a universal
law-of-the-iterated-logarithm lower bound.

The final section gives a concrete receipt: telescoping polynomial weights
`1 / ((k+1)(k+2))` sum to one, while geometric epoch scales turn their exact
selection cost into an explicit iterated-log expression.

Mathematical sources: the pigeonhole principle, summability of nonnegative
series, and the standard weighted Bonferroni/Kraft allocation principle.
-/

namespace FormalSLT.AnytimeValid.AllocationLogLog

open Finset BigOperators
open Filter Topology

noncomputable section

/-! ## Blockwise obstruction for arbitrary countable allocations -/

/-- Every block `[N, 2N]` of a nonnegative countable allocation contains an
atom no larger than the reciprocal block cardinality.  The interval is
inclusive and has exactly `N + 1` elements. -/
theorem exists_small_weight_on_dyadicBlock
    (weight : ℕ → ℝ)
    (hweight_nonneg : ∀ k, 0 ≤ weight k)
    (hweight_summable : Summable weight)
    (hweight_total : ∑' k, weight k ≤ 1)
    (N : ℕ) :
    ∃ k ∈ Finset.Icc N (2 * N),
      weight k ≤ 1 / ((N : ℝ) + 1) := by
  classical
  let block := Finset.Icc N (2 * N)
  have hblock_nonempty : block.Nonempty := by
    refine ⟨N, ?_⟩
    simp only [block, Finset.mem_Icc]
    omega
  by_contra hsmall
  have hstrict_pointwise :
      ∀ k ∈ block, 1 / ((N : ℝ) + 1) < weight k := by
    intro k hk
    exact lt_of_not_ge (fun hle ↦ hsmall ⟨k, hk, hle⟩)
  have hconstant_sum :
      (∑ _k ∈ block, (1 / ((N : ℝ) + 1))) = 1 := by
    dsimp [block]
    rw [Finset.sum_const, Nat.card_Icc]
    have hcard : 2 * N + 1 - N = N + 1 := by omega
    rw [hcard]
    simp [nsmul_eq_mul]
    field_simp
  have hblock_gt_one : 1 < ∑ k ∈ block, weight k := by
    rw [← hconstant_sum]
    exact Finset.sum_lt_sum_of_nonempty hblock_nonempty hstrict_pointwise
  have hblock_le_total : (∑ k ∈ block, weight k) ≤ ∑' k, weight k := by
    exact hweight_summable.sum_le_tsum block
      (fun k _hk ↦ hweight_nonneg k)
  linarith

/-- Positive countable allocations must pay at least `log (N+1)` somewhere in
every inclusive block `[N, 2N]`. -/
theorem exists_logCost_ge_log_blockCard
    (weight : ℕ → ℝ)
    (hweight_pos : ∀ k, 0 < weight k)
    (hweight_summable : Summable weight)
    (hweight_total : ∑' k, weight k ≤ 1)
    (N : ℕ) :
    ∃ k ∈ Finset.Icc N (2 * N),
      Real.log ((N : ℝ) + 1) ≤ Real.log (1 / weight k) := by
  obtain ⟨k, hk, hsmall⟩ := exists_small_weight_on_dyadicBlock
    weight (fun j ↦ (hweight_pos j).le) hweight_summable hweight_total N
  refine ⟨k, hk, ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hmul : ((N : ℝ) + 1) * weight k ≤ 1 := by
    calc
      ((N : ℝ) + 1) * weight k = weight k * ((N : ℝ) + 1) := by ring
      _ ≤ (1 / ((N : ℝ) + 1)) * ((N : ℝ) + 1) := by
        exact mul_le_mul_of_nonneg_right hsmall hNpos.le
      _ = 1 := by field_simp
  have hreciprocal : (N : ℝ) + 1 ≤ 1 / weight k := by
    exact (le_div_iff₀ (hweight_pos k)).2 hmul
  exact Real.log_le_log hNpos hreciprocal

/-- A block witness can be expressed directly in terms of its selected index:
the log cost is at least `log (k+1) - log 2`. -/
theorem exists_logCost_ge_indexLog_sub_log_two
    (weight : ℕ → ℝ)
    (hweight_pos : ∀ k, 0 < weight k)
    (hweight_summable : Summable weight)
    (hweight_total : ∑' k, weight k ≤ 1)
    (N : ℕ) :
    ∃ k ∈ Finset.Icc N (2 * N),
      Real.log ((k : ℝ) + 1) - Real.log 2 ≤
        Real.log (1 / weight k) := by
  obtain ⟨k, hk, hcost⟩ := exists_logCost_ge_log_blockCard
    weight hweight_pos hweight_summable hweight_total N
  refine ⟨k, hk, ?_⟩
  have hk_upper : k ≤ 2 * N := (Finset.mem_Icc.mp hk).2
  have hkcast : (k : ℝ) + 1 ≤ 2 * ((N : ℝ) + 1) := by
    exact_mod_cast (show k + 1 ≤ 2 * (N + 1) by omega)
  have hlog : Real.log ((k : ℝ) + 1) ≤
      Real.log (2 * ((N : ℝ) + 1)) :=
    Real.log_le_log (by positivity) hkcast
  have hsplit : Real.log (2 * ((N : ℝ) + 1)) =
      Real.log 2 + Real.log ((N : ℝ) + 1) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
  rw [hsplit] at hlog
  linarith

/-- The index-scale lower bound occurs frequently at infinity.  This is the
filter-level form of the unbounded-subsequence statement. -/
theorem frequently_logCost_ge_indexLog_sub_log_two
    (weight : ℕ → ℝ)
    (hweight_pos : ∀ k, 0 < weight k)
    (hweight_summable : Summable weight)
    (hweight_total : ∑' k, weight k ≤ 1) :
    ∃ᶠ k : ℕ in Filter.atTop,
      Real.log ((k : ℝ) + 1) - Real.log 2 ≤
        Real.log (1 / weight k) := by
  rw [Filter.frequently_atTop]
  intro K
  let N := max 1 K
  obtain ⟨k, hk, hcost⟩ := exists_logCost_ge_indexLog_sub_log_two
    weight hweight_pos hweight_summable hweight_total N
  refine ⟨k, ?_, hcost⟩
  exact (le_max_right 1 K).trans (Finset.mem_Icc.mp hk).1

/-! ## Translation to geometric epochs -/

/-- Integer sample-size scale associated with geometric epoch `k`. -/
def geometricEpochTime (k : ℕ) : ℕ :=
  4 ^ (k + 1)

/-- Real coercion of the geometric epoch time, used inside logarithms. -/
def geometricEpochScale (k : ℕ) : ℝ :=
  geometricEpochTime k

/-- Iterated natural logarithm of the geometric epoch scale. -/
def geometricEpochIteratedLog (k : ℕ) : ℝ :=
  Real.log (Real.log (geometricEpochScale k))

/-- The base-four logarithm recovers the epoch index exactly. -/
theorem geometricEpochTime_natLog (k : ℕ) :
    Nat.log 4 (geometricEpochTime k) = k + 1 := by
  unfold geometricEpochTime
  exact Nat.log_pow (by norm_num) (k + 1)

theorem geometricEpochScale_log (k : ℕ) :
    Real.log (geometricEpochScale k) =
      ((k : ℝ) + 1) * Real.log 4 := by
  unfold geometricEpochScale
  unfold geometricEpochTime
  push_cast
  rw [Real.log_pow]
  push_cast
  ring

/-- Exact conversion from geometric epoch index to iterated logarithm. -/
theorem geometricEpochIteratedLog_eq (k : ℕ) :
    geometricEpochIteratedLog k =
      Real.log ((k : ℝ) + 1) + Real.log (Real.log 4) := by
  unfold geometricEpochIteratedLog
  rw [geometricEpochScale_log]
  rw [Real.log_mul (by positivity)
    (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 4)))]

/-- **Allocation-based log-log obstruction.** For every block of geometric
epochs, one selected atom pays at least the iterated logarithm of its epoch
scale, up to the displayed universal additive constant. -/
theorem exists_geometricEpoch_loglogCost
    (weight : ℕ → ℝ)
    (hweight_pos : ∀ k, 0 < weight k)
    (hweight_summable : Summable weight)
    (hweight_total : ∑' k, weight k ≤ 1)
    (N : ℕ) :
    ∃ k ∈ Finset.Icc N (2 * N),
      geometricEpochIteratedLog k -
          (Real.log 2 + Real.log (Real.log 4)) ≤
        Real.log (1 / weight k) := by
  obtain ⟨k, hk, hcost⟩ := exists_logCost_ge_indexLog_sub_log_two
    weight hweight_pos hweight_summable hweight_total N
  refine ⟨k, hk, ?_⟩
  rw [geometricEpochIteratedLog_eq]
  linarith

/-- The geometric-epoch log-log obstruction holds along an unbounded
subsequence. -/
theorem frequently_geometricEpoch_loglogCost
    (weight : ℕ → ℝ)
    (hweight_pos : ∀ k, 0 < weight k)
    (hweight_summable : Summable weight)
    (hweight_total : ∑' k, weight k ≤ 1) :
    ∃ᶠ k : ℕ in Filter.atTop,
      geometricEpochIteratedLog k -
          (Real.log 2 + Real.log (Real.log 4)) ≤
        Real.log (1 / weight k) := by
  exact
    (frequently_logCost_ge_indexLog_sub_log_two
      weight hweight_pos hweight_summable hweight_total).mono (by
        intro k hk
        rw [geometricEpochIteratedLog_eq]
        linarith)

/-! ## Polynomial weights on geometric epochs -/

/-- Telescoping polynomial confidence allocation. -/
def polynomialEpochWeight (k : ℕ) : ℝ :=
  1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))

theorem polynomialEpochWeight_pos (k : ℕ) :
    0 < polynomialEpochWeight k := by
  unfold polynomialEpochWeight
  positivity

theorem polynomialEpochWeight_eq_sub (k : ℕ) :
    polynomialEpochWeight k =
      1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) := by
  unfold polynomialEpochWeight
  field_simp
  ring

theorem polynomialEpochWeight_sum_range (K : ℕ) :
    ∑ k ∈ Finset.range K, polynomialEpochWeight k =
      1 - 1 / ((K : ℝ) + 1) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, polynomialEpochWeight_eq_sub]
      push_cast
      ring

/-- The polynomial confidence allocation has total mass exactly one. -/
theorem polynomialEpochWeight_hasSum :
    HasSum polynomialEpochWeight 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun k ↦ (polynomialEpochWeight_pos k).le)]
  simp_rw [polynomialEpochWeight_sum_range]
  have hlim : Tendsto (fun K : ℕ ↦ 1 / ((K : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [sub_zero] using tendsto_const_nhds.sub hlim

theorem polynomialEpochWeight_summable :
    Summable polynomialEpochWeight :=
  polynomialEpochWeight_hasSum.summable

theorem polynomialEpochWeight_tsum :
    ∑' k, polynomialEpochWeight k = 1 :=
  polynomialEpochWeight_hasSum.tsum_eq

/-- Exact log selection price of the polynomial allocation. -/
theorem polynomialEpochWeight_log_cost (k : ℕ) :
    Real.log (1 / polynomialEpochWeight k) =
      Real.log ((k : ℝ) + 1) + Real.log ((k : ℝ) + 2) := by
  have hreciprocal : 1 / polynomialEpochWeight k =
      ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
    unfold polynomialEpochWeight
    field_simp
  rw [hreciprocal, Real.log_mul (by positivity) (by positivity)]

/-- Exact polynomial-weight/geometric-epoch receipt. -/
theorem polynomialGeometricEpoch_log_cost (k : ℕ) :
    Real.log (1 / polynomialEpochWeight k) =
      geometricEpochIteratedLog k - Real.log (Real.log 4) +
        Real.log ((k : ℝ) + 2) := by
  rw [polynomialEpochWeight_log_cost, geometricEpochIteratedLog_eq]
  ring

end

end FormalSLT.AnytimeValid.AllocationLogLog
