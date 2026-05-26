import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import FormalSLT.PACBayesFiniteProductMGF

open scoped BigOperators Nat
open Real
open FormalSLT.PACBayesFiniteProductMGF

namespace FormalSLT.Probability.BernsteinMGF

/-!
# Finite Bennett / Bernstein moment generating function bound

This module proves a **variance-aware** exponential-moment (MGF) bound for a
finite distribution: the Bennett inequality

```
∑ z, p z * exp (lam * X z) ≤ exp ((exp (lam*b) - 1 - lam*b) / b^2 * v)
```

for a centered observable `X` (`∑ p z * X z = 0`) that is bounded above
(`X z ≤ b`) with variance proxy `∑ p z * X z ^ 2 ≤ v`.

Unlike the range-based Hoeffding MGF the localized-Rademacher lane currently
relies on (which feeds the conservative `variance = 1` proxy), this bound carries
the genuine variance `v` in the exponent. For small `lam*b` it behaves like
`exp (lam^2 * v / 2)`. It is the load-bearing piece of the finite Bernstein
variance-localization route to a non-conservative localized fast-rate theorem.

The variance-aware Bennett form and its keystone pointwise inequality are proved
here directly. The keystone `exp_le_quadratic_of_le` splits into an elementary
`x ≤ 0` branch and a termwise exponential-series comparison on `0 ≤ x ≤ b`.
-/

/-- `f y = exp y - (1 + y + y^2/2)` has derivative `exp x - (1 + x)`. -/
lemma hasDerivAt_expSub (x : ℝ) :
    HasDerivAt (fun y => Real.exp y - (1 + y + y ^ 2 / 2)) (Real.exp x - (1 + x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => Real.exp y) (Real.exp x) x := Real.hasDerivAt_exp x
  have h2 : HasDerivAt (fun y : ℝ => 1 + y + y ^ 2 / 2) (1 + x) x := by
    have : HasDerivAt (fun y : ℝ => 1 + y + y ^ 2 / 2) (0 + 1 + (2 * x ^ 1) / 2) x := by
      apply HasDerivAt.add
      · exact (hasDerivAt_const x 1).add (hasDerivAt_id x)
      · simpa using ((hasDerivAt_pow 2 x).div_const 2)
    simpa using this
  exact h1.sub h2

/-- Elementary lower bound `1 + u + u^2/2 ≤ exp u` for `u ≥ 0`. -/
lemma one_add_add_sq_le_exp_of_nonneg {u : ℝ} (hu : 0 ≤ u) :
    1 + u + u ^ 2 / 2 ≤ Real.exp u := by
  have hmono : MonotoneOn (fun y => Real.exp y - (1 + y + y ^ 2 / 2)) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      ((Continuous.sub Real.continuous_exp (by fun_prop)).continuousOn)
      (fun x _ => (hasDerivAt_expSub x).differentiableAt.differentiableWithinAt)
    intro x _
    rw [(hasDerivAt_expSub x).deriv]
    have := Real.add_one_le_exp x; linarith
  have h0 : (fun y => Real.exp y - (1 + y + y ^ 2 / 2)) 0 = 0 := by simp
  have := hmono Set.self_mem_Ici (Set.mem_Ici.mpr hu) hu
  simp only [h0] at this; linarith

/-- Elementary upper bound `exp u ≤ 1 + u + u^2/2` for `u ≤ 0`. -/
lemma exp_le_one_add_add_sq_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    Real.exp u ≤ 1 + u + u ^ 2 / 2 := by
  have hmono : MonotoneOn (fun y => Real.exp y - (1 + y + y ^ 2 / 2)) (Set.Iic 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic 0)
      ((Continuous.sub Real.continuous_exp (by fun_prop)).continuousOn)
      (fun x _ => (hasDerivAt_expSub x).differentiableAt.differentiableWithinAt)
    intro x _
    rw [(hasDerivAt_expSub x).deriv]
    have := Real.add_one_le_exp x; linarith
  have h0 : (fun y => Real.exp y - (1 + y + y ^ 2 / 2)) 0 = 0 := by simp
  have := hmono (Set.mem_Iic.mpr hu) Set.self_mem_Iic hu
  simp only [h0] at this; linarith

/-- The exponential series with the first two terms peeled off:
`exp a - 1 - a = ∑' k, a^(k+2)/(k+2)!`. -/
lemma exp_sub_one_sub_eq_tsum (a : ℝ) :
    Real.exp a - 1 - a = ∑' k : ℕ, a ^ (k + 2) / (k + 2) ! := by
  have hsum : Summable (fun n : ℕ => a ^ n / n !) := Real.summable_pow_div_factorial a
  have hexp : Real.exp a = ∑' n : ℕ, a ^ n / n ! := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [hexp, ← hsum.sum_add_tsum_nat_add 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one, zero_add]
  ring

/-- Bennett comparison `exp a - 1 - a ≤ (exp B - 1 - B) * a^2 / B^2` for `0 < B`
and `a ≤ B`. This is the quotient-monotonicity heart of Bennett's lemma; it is
proved without differentiating the awkward `(exp u - 1 - u)/u^2`, by splitting
into an elementary `a ≤ 0` branch and a termwise power-series comparison on
`0 ≤ a ≤ B`. -/
lemma exp_sub_one_sub_le {B : ℝ} (hB : 0 < B) {a : ℝ} (ha : a ≤ B) :
    Real.exp a - 1 - a ≤ (Real.exp B - 1 - B) * a ^ 2 / B ^ 2 := by
  by_cases hle : a ≤ 0
  · have h1 : Real.exp a - 1 - a ≤ a ^ 2 / 2 := by
      have := exp_le_one_add_add_sq_of_nonpos hle; linarith
    have hlow : 1 + B + B ^ 2 / 2 ≤ Real.exp B := one_add_add_sq_le_exp_of_nonneg hB.le
    have hBsq : (0:ℝ) < B ^ 2 := by positivity
    have hkey : a ^ 2 / 2 ≤ (Real.exp B - 1 - B) * a ^ 2 / B ^ 2 := by
      have ha2 : (0:ℝ) ≤ a ^ 2 := sq_nonneg a
      have hE : B ^ 2 / 2 ≤ Real.exp B - 1 - B := by nlinarith [hlow]
      rw [le_div_iff₀ hBsq]
      nlinarith [mul_nonneg ha2 (sub_nonneg.mpr hE), ha2, hE]
    linarith
  · have hlt : 0 < a := not_le.mp hle
    have ha0 : 0 ≤ a := hlt.le
    have hBne : B ≠ 0 := ne_of_gt hB
    rw [exp_sub_one_sub_eq_tsum a, exp_sub_one_sub_eq_tsum B]
    have hsumB : Summable (fun k : ℕ => B ^ (k + 2) / (k + 2) !) :=
      (summable_nat_add_iff 2).2 (Real.summable_pow_div_factorial B)
    have hsumA : Summable (fun k : ℕ => a ^ (k + 2) / (k + 2) !) :=
      (summable_nat_add_iff 2).2 (Real.summable_pow_div_factorial a)
    rw [div_eq_mul_inv, ← tsum_mul_right, ← tsum_mul_right]
    refine hsumA.tsum_le_tsum (fun k => ?_) ((hsumB.mul_right _).mul_right _)
    have hpow : a ^ k ≤ B ^ k := pow_le_pow_left₀ ha0 ha k
    have hrw : B ^ (k + 2) / (↑(k + 2)) ! * a ^ 2 * (B ^ 2)⁻¹
             = B ^ k * a ^ 2 / (↑(k + 2)) ! := by
      rw [pow_add]; field_simp
    rw [hrw]
    have hnum : a ^ (k + 2) ≤ B ^ k * a ^ 2 := by
      rw [pow_add]; exact mul_le_mul_of_nonneg_right hpow (sq_nonneg a)
    gcongr

/-- **Keystone pointwise Bennett bound.** For `0 < b`, `0 ≤ t`, and `x ≤ b`:
`exp (t*x) ≤ 1 + t*x + ((exp (t*b) - 1 - t*b)/b^2) * x^2`. -/
lemma exp_le_quadratic_of_le {b : ℝ} (hb : 0 < b) {t : ℝ} (ht : 0 ≤ t) {x : ℝ}
    (hx : x ≤ b) :
    Real.exp (t * x) ≤ 1 + t * x + (Real.exp (t * b) - 1 - t * b) / b ^ 2 * x ^ 2 := by
  rcases eq_or_lt_of_le ht with rfl | htpos
  · simp
  · have hB : 0 < t * b := mul_pos htpos hb
    have ha : t * x ≤ t * b := by nlinarith [hx, htpos.le]
    have hkey := exp_sub_one_sub_le hB ha
    have htranslate : (Real.exp (t * b) - 1 - t * b) * (t * x) ^ 2 / (t * b) ^ 2
        = (Real.exp (t * b) - 1 - t * b) / b ^ 2 * x ^ 2 := by
      have htne : t ≠ 0 := ne_of_gt htpos
      have hbne : b ≠ 0 := ne_of_gt hb
      field_simp
    rw [htranslate] at hkey
    linarith

/-- **Finite Bennett MGF.** For a finite PMF `p` and an observable `X` that is
centered (`∑ p z * X z = 0`), bounded above (`X z ≤ b`, `0 < b`), and has
variance proxy `∑ p z * X z ^ 2 ≤ v`, the exponential moment at `0 ≤ lam`
obeys the Bennett bound
`∑ z, p z * exp (lam * X z) ≤ exp ((exp (lam*b) - 1 - lam*b)/b^2 * v)`.

This is variance-aware: the exponent carries `v`, not the range, and for small
`lam*b` behaves like `exp (lam^2 * v / 2)`. -/
lemma bennett_mgf {Z : Type*} [Fintype Z] (p : Z → ℝ) (X : Z → ℝ)
    {b v lam : ℝ} (hb : 0 < b) (hlam : 0 ≤ lam)
    (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum : ∑ z, p z = 1)
    (hcenter : ∑ z, p z * X z = 0)
    (hbound : ∀ z, X z ≤ b)
    (hvar : ∑ z, p z * X z ^ 2 ≤ v) :
    ∑ z, p z * Real.exp (lam * X z)
      ≤ Real.exp ((Real.exp (lam * b) - 1 - lam * b) / b ^ 2 * v) := by
  set C : ℝ := (Real.exp (lam * b) - 1 - lam * b) / b ^ 2 with hC
  have hCnonneg : 0 ≤ C := by
    rw [hC]
    apply div_nonneg _ (by positivity)
    have := Real.add_one_le_exp (lam * b); linarith
  have hpoint : ∀ z, p z * Real.exp (lam * X z)
      ≤ p z * (1 + lam * X z + C * X z ^ 2) := by
    intro z
    apply mul_le_mul_of_nonneg_left _ (hp_nonneg z)
    have := exp_le_quadratic_of_le hb hlam (hbound z)
    rw [hC]; linarith [this]
  have hsum : ∑ z, p z * Real.exp (lam * X z)
      ≤ ∑ z, p z * (1 + lam * X z + C * X z ^ 2) :=
    Finset.sum_le_sum (fun z _ => hpoint z)
  have hexpand : ∑ z, p z * (1 + lam * X z + C * X z ^ 2)
      = (∑ z, p z) + lam * (∑ z, p z * X z) + C * (∑ z, p z * X z ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    ring
  rw [hexpand, hp_sum, hcenter] at hsum
  have hmoment : (1 : ℝ) + lam * 0 + C * (∑ z, p z * X z ^ 2) ≤ 1 + C * v := by
    have := mul_le_mul_of_nonneg_left hvar hCnonneg; linarith
  have hfinal : (1 : ℝ) + C * v ≤ Real.exp (C * v) := by
    have := Real.add_one_le_exp (C * v); linarith
  calc ∑ z, p z * Real.exp (lam * X z)
      ≤ 1 + lam * 0 + C * (∑ z, p z * X z ^ 2) := hsum
    _ ≤ 1 + C * v := hmoment
    _ ≤ Real.exp (C * v) := hfinal

/-- `2 * 3^k ≤ (k+2)!` for all `k`. The factorial growth that converts the
Bennett series into the geometric `1/(1 - s/3)` series. -/
lemma two_mul_three_pow_le_factorial (k : ℕ) : 2 * 3 ^ k ≤ (k + 2)! := by
  induction k with
  | zero => decide
  | succ n ih =>
    have h1 : 2 * 3 ^ (n + 1) = 3 * (2 * 3 ^ n) := by ring
    have h2 : (n + 1 + 2)! = (n + 3) * (n + 2)! := by
      have he : n + 1 + 2 = (n + 2) + 1 := by ring
      rw [he, Nat.factorial_succ]
    rw [h1, h2]
    exact le_trans (Nat.mul_le_mul (le_refl 3) ih) (Nat.mul_le_mul (by omega) (le_refl _))

/-- **Bernstein / sub-Gamma scalar simplification.** For `0 ≤ s < 3`,
`exp s - 1 - s ≤ s^2 / (2 * (1 - s/3))`. This converts the Bennett exponent into
the sub-Gamma denominator form; the `s < 3` hypothesis keeps the denominator
positive. Proved by a termwise comparison of the exponential series
`∑ s^(k+2)/(k+2)!` against the geometric series `∑ s^(k+2)/(2·3^k)`, using
`two_mul_three_pow_le_factorial`. -/
lemma exp_sub_one_sub_le_sq_div {s : ℝ} (hs : 0 ≤ s) (hs3 : s < 3) :
    Real.exp s - 1 - s ≤ s ^ 2 / (2 * (1 - s / 3)) := by
  have hr : (0:ℝ) ≤ s / 3 := by positivity
  have hr1 : s / 3 < 1 := by linarith
  have hgeo : ∑' j : ℕ, (s / 3) ^ j = (1 - s / 3)⁻¹ := tsum_geometric_of_lt_one hr hr1
  have hsummG : Summable (fun j : ℕ => (s / 3) ^ j) := summable_geometric_of_lt_one hr hr1
  have hne : (1:ℝ) - s / 3 ≠ 0 := by linarith
  have hRHS : s ^ 2 / (2 * (1 - s / 3)) = ∑' k : ℕ, s ^ (k + 2) / (2 * 3 ^ k) := by
    have hstep : s ^ 2 / (2 * (1 - s / 3)) = (s ^ 2 / 2) * (∑' j : ℕ, (s / 3) ^ j) := by
      rw [hgeo]; field_simp
    rw [hstep, ← tsum_mul_left]
    refine tsum_congr (fun k => ?_)
    rw [div_pow]; field_simp; ring
  rw [exp_sub_one_sub_eq_tsum s, hRHS]
  have hsummL : Summable (fun k : ℕ => s ^ (k + 2) / (k + 2) !) :=
    (summable_nat_add_iff 2).2 (Real.summable_pow_div_factorial s)
  have hsummR : Summable (fun k : ℕ => s ^ (k + 2) / (2 * 3 ^ k)) := by
    apply (hsummG.mul_left (s ^ 2 / 2)).congr
    intro k
    rw [div_pow]; field_simp; ring
  refine hsummL.tsum_le_tsum (fun k => ?_) hsummR
  have hkey : (2:ℝ) * 3 ^ k ≤ ((k + 2)! : ℝ) := by
    exact_mod_cast two_mul_three_pow_le_factorial k
  have hsk : (0:ℝ) ≤ s ^ (k + 2) := pow_nonneg hs _
  gcongr

/-- **Finite sub-Gamma MGF.** The Bennett MGF (`bennett_mgf`) rewritten in the
Bernstein denominator form: for `0 ≤ lam` with `lam*b < 3` and variance proxy
`0 ≤ v`,
`∑ z, p z * exp (lam * X z) ≤ exp (lam^2 * v / (2 * (1 - lam*b/3)))`.

Kept separate from the raw `bennett_mgf` so callers can use either the exact
Bennett exponent or this sub-Gamma simplification. The denominator positivity is
explicit via `lam*b < 3`. -/
lemma bennett_mgf_subgamma {Z : Type*} [Fintype Z] (p : Z → ℝ) (X : Z → ℝ)
    {b v lam : ℝ} (hb : 0 < b) (hlam : 0 ≤ lam) (hlb : lam * b < 3)
    (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum : ∑ z, p z = 1)
    (hcenter : ∑ z, p z * X z = 0)
    (hbound : ∀ z, X z ≤ b)
    (hvar : ∑ z, p z * X z ^ 2 ≤ v) :
    ∑ z, p z * Real.exp (lam * X z)
      ≤ Real.exp (lam ^ 2 * v / (2 * (1 - lam * b / 3))) := by
  -- `0 ≤ v` is forced by the variance hypothesis, not assumed separately.
  have hv : 0 ≤ v :=
    le_trans (Finset.sum_nonneg fun z _ => mul_nonneg (hp_nonneg z) (sq_nonneg (X z))) hvar
  refine (bennett_mgf p X hb hlam hp_nonneg hp_sum hcenter hbound hvar).trans ?_
  apply Real.exp_le_exp.mpr
  have hsbnonneg : (0:ℝ) ≤ lam * b := by positivity
  have hsc := exp_sub_one_sub_le_sq_div hsbnonneg hlb
  have hbne : b ≠ 0 := ne_of_gt hb
  have hden : (0:ℝ) < 1 - lam * b / 3 := by linarith
  have hCle : (Real.exp (lam * b) - 1 - lam * b) / b ^ 2
      ≤ lam ^ 2 / (2 * (1 - lam * b / 3)) := by
    have hstep : (Real.exp (lam * b) - 1 - lam * b) / b ^ 2
        ≤ (lam * b) ^ 2 / (2 * (1 - lam * b / 3)) / b ^ 2 := by gcongr
    refine hstep.trans (le_of_eq ?_)
    field_simp
  calc (Real.exp (lam * b) - 1 - lam * b) / b ^ 2 * v
      ≤ lam ^ 2 / (2 * (1 - lam * b / 3)) * v := mul_le_mul_of_nonneg_right hCle hv
    _ = lam ^ 2 * v / (2 * (1 - lam * b / 3)) := by ring

/-- Finite weighted Markov upper tail: for `lam ≥ 0` and nonnegative weights,
the weighted mass on `{z | eps ≤ X z}` is at most the exponential moment divided
by `exp (lam * eps)`. The Chernoff/Markov step underneath the Bernstein tail. -/
lemma weighted_upper_tail_le_mgf_div {Z : Type*} [Fintype Z] (p X : Z → ℝ)
    {eps lam : ℝ} (hlam : 0 ≤ lam) (hp_nonneg : ∀ z, 0 ≤ p z) :
    ∑ z ∈ Finset.univ.filter (fun z => eps ≤ X z), p z
      ≤ (∑ z, p z * Real.exp (lam * X z)) / Real.exp (lam * eps) := by
  rw [le_div_iff₀ (Real.exp_pos _)]
  calc (∑ z ∈ Finset.univ.filter (fun z => eps ≤ X z), p z) * Real.exp (lam * eps)
      = ∑ z ∈ Finset.univ.filter (fun z => eps ≤ X z), p z * Real.exp (lam * eps) := by
        rw [Finset.sum_mul]
    _ ≤ ∑ z ∈ Finset.univ.filter (fun z => eps ≤ X z), p z * Real.exp (lam * X z) := by
        refine Finset.sum_le_sum (fun z hz => ?_)
        rw [Finset.mem_filter] at hz
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz.2 hlam)) (hp_nonneg z)
    _ ≤ ∑ z, p z * Real.exp (lam * X z) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro z _ _; exact mul_nonneg (hp_nonneg z) (Real.exp_pos _).le

/-- Raw Bernstein tail at a fixed `lam` (finite Markov + sub-Gamma MGF):
`mass{eps ≤ X} ≤ exp (lam^2 v / (2(1 - lam b/3)) - lam eps)`. Kept separate from
the optimized form so callers can pick their own `lam`. -/
lemma bernstein_tail_mgf {Z : Type*} [Fintype Z] (p X : Z → ℝ)
    {b v lam eps : ℝ} (hb : 0 < b) (hlam : 0 ≤ lam) (hlb : lam * b < 3)
    (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum : ∑ z, p z = 1)
    (hcenter : ∑ z, p z * X z = 0) (hbound : ∀ z, X z ≤ b)
    (hvar : ∑ z, p z * X z ^ 2 ≤ v) :
    ∑ z ∈ Finset.univ.filter (fun z => eps ≤ X z), p z
      ≤ Real.exp (lam ^ 2 * v / (2 * (1 - lam * b / 3)) - lam * eps) := by
  refine (weighted_upper_tail_le_mgf_div p X hlam hp_nonneg).trans ?_
  rw [Real.exp_sub]
  gcongr
  exact bennett_mgf_subgamma p X hb hlam hlb hp_nonneg hp_sum hcenter hbound hvar

/-- **Raw Bernstein tail (optimized `lam`).** For variance proxy `0 < v`, bound
`0 < b`, and `0 ≤ eps`, the weighted upper tail obeys the standard Bernstein
inequality
`mass{eps ≤ X} ≤ exp (-eps^2 / (2 (v + b eps/3)))`.

The `lam`-optimization `lam = eps / (v + b eps/3)` is performed here; at that
`lam` the fixed-`lam` exponent equals the stated bound exactly (the `lam b < 3`
denominator condition reduces to `0 < 3v`). This is the one-sample tail; the
averaged `exp (-n eps^2 / …)` form arises from the iid product/tensorization at
composition time. -/
lemma bernstein_tail {Z : Type*} [Fintype Z] (p X : Z → ℝ)
    {b v eps : ℝ} (hb : 0 < b) (hv : 0 < v) (heps : 0 ≤ eps)
    (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum : ∑ z, p z = 1)
    (hcenter : ∑ z, p z * X z = 0) (hbound : ∀ z, X z ≤ b)
    (hvar : ∑ z, p z * X z ^ 2 ≤ v) :
    ∑ z ∈ Finset.univ.filter (fun z => eps ≤ X z), p z
      ≤ Real.exp (-(eps ^ 2) / (2 * (v + b * eps / 3))) := by
  have hDpos : 0 < v + b * eps / 3 := by positivity
  have hlam0 : 0 ≤ eps / (v + b * eps / 3) := by positivity
  have hlb : eps / (v + b * eps / 3) * b < 3 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hDpos]; nlinarith [hv, heps, hb]
  refine (bernstein_tail_mgf p X hb hlam0 hlb hp_nonneg hp_sum hcenter hbound hvar).trans ?_
  apply Real.exp_le_exp.mpr
  have hkey : (1:ℝ) - eps / (v + b * eps / 3) * b / 3 = v / (v + b * eps / 3) := by
    field_simp; ring
  rw [hkey]
  have hvne : v ≠ 0 := ne_of_gt hv
  have hDne : v + b * eps / 3 ≠ 0 := ne_of_gt hDpos
  apply le_of_eq
  field_simp
  ring

/-- **Averaged (tensorized) Bernstein tail.** For an iid product of `n` draws
from PMF `p`, the population-minus-empirical deviation of hypothesis `i` has the
correct `n · eps^2` Bernstein tail with the *per-coordinate* range bound `b` and
variance proxy `v`.

This is the form used by the finite localized Bernstein theorem: the
one-sample `bernstein_tail` applied to the product would keep an O(1) range
term with no `n` and give the wrong rate. The product MGF is factorized via
`finiteProduct_mgf_empiricalRiskDeviation_eq_pow` into the `n`-th power of the
one-coordinate MGF, which is bounded by `bennett_mgf` at parameter `lam/n`; the
`lam = n · s` optimization then reduces to the same scalar sub-Gamma step
`exp_sub_one_sub_le_sq_div`, scaled by `n`. Requires `0 < v` (so `lam·b < 3`
reduces to `0 < 3v`). -/
lemma averaged_bernstein_tail {ι : Type*} {Z : Type*} [Fintype Z] {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : FormalSLT.PACBayesKL.IsPMF p) (ℓ : ι → Z → ℝ) (i : ι)
    {b v eps : ℝ} (hb : 0 < b) (hv : 0 < v) (heps : 0 ≤ eps)
    (hbound : ∀ z, finitePopulationRisk p ℓ i - ℓ i z ≤ b)
    (hvar : ∑ z, p z * (finitePopulationRisk p ℓ i - ℓ i z) ^ 2 ≤ v) :
    ∑ S ∈ Finset.univ.filter (fun S : Fin n → Z =>
        eps ≤ finitePopulationRisk p ℓ i - finiteEmpiricalRisk ℓ i S),
        finiteProductSampleWeight p S
      ≤ Real.exp (-(n : ℝ) * eps ^ 2 / (2 * (v + b * eps / 3))) := by
  classical
  have hn_pos : (0:ℝ) < n := by exact_mod_cast hn
  have hcenter : ∑ z, p z * (finitePopulationRisk p ℓ i - ℓ i z) = 0 := by
    have hexp : ∑ z, p z * (finitePopulationRisk p ℓ i - ℓ i z)
        = finitePopulationRisk p ℓ i * (∑ z, p z) - ∑ z, p z * ℓ i z := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun z _ => by ring)
    rw [hexp, hp.sum_one]
    unfold finitePopulationRisk; ring
  have hW_nonneg : ∀ S : Fin n → Z, 0 ≤ finiteProductSampleWeight p S := by
    intro S; unfold finiteProductSampleWeight
    exact Finset.prod_nonneg (fun k _ => hp.nonneg (S k))
  have hDpos : 0 < v + b * eps / 3 := by positivity
  set s := eps / (v + b * eps / 3) with hs
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hsb : s * b < 3 := by
    rw [hs, div_mul_eq_mul_div, div_lt_iff₀ hDpos]; nlinarith [hv, heps, hb]
  set lam := (n : ℝ) * s with hlam_def
  have hlam0 : 0 ≤ lam := by rw [hlam_def]; positivity
  have hlamn : lam * (n : ℝ)⁻¹ = s := by rw [hlam_def]; field_simp
  have hmarkov := weighted_upper_tail_le_mgf_div
      (finiteProductSampleWeight p)
      (fun S : Fin n → Z => finitePopulationRisk p ℓ i - finiteEmpiricalRisk ℓ i S)
      (eps := eps) (lam := lam) hlam0 hW_nonneg
  refine hmarkov.trans ?_
  rw [finiteProduct_mgf_empiricalRiskDeviation_eq_pow (ι := ι) (Z := Z) hn p ℓ i lam]
  have hbase :
      (∑ z : Z, p z * Real.exp ((lam * (n:ℝ)⁻¹) * (finitePopulationRisk p ℓ i - ℓ i z)))
        ≤ Real.exp ((Real.exp ((lam * (n:ℝ)⁻¹) * b) - 1 - (lam * (n:ℝ)⁻¹) * b)
            / b ^ 2 * v) :=
    bennett_mgf p (fun z => finitePopulationRisk p ℓ i - ℓ i z)
      hb (by rw [hlamn]; exact hs0) hp.nonneg hp.sum_one hcenter hbound hvar
  have hbase_nonneg :
      0 ≤ ∑ z : Z, p z * Real.exp ((lam * (n:ℝ)⁻¹) * (finitePopulationRisk p ℓ i - ℓ i z)) :=
    Finset.sum_nonneg (fun z _ => mul_nonneg (hp.nonneg z) (Real.exp_pos _).le)
  have hpow := pow_le_pow_left₀ hbase_nonneg hbase n
  rw [← Real.exp_nat_mul] at hpow
  calc (∑ z : Z, p z * Real.exp ((lam * (n:ℝ)⁻¹) * (finitePopulationRisk p ℓ i - ℓ i z))) ^ n
          / Real.exp (lam * eps)
      ≤ Real.exp ((n:ℝ) * ((Real.exp ((lam * (n:ℝ)⁻¹) * b) - 1 - (lam * (n:ℝ)⁻¹) * b)
            / b ^ 2 * v)) / Real.exp (lam * eps) := by gcongr
    _ = Real.exp ((n:ℝ) * ((Real.exp ((lam * (n:ℝ)⁻¹) * b) - 1 - (lam * (n:ℝ)⁻¹) * b)
            / b ^ 2 * v) - lam * eps) := by rw [← Real.exp_sub]
    _ ≤ Real.exp (-(n : ℝ) * eps ^ 2 / (2 * (v + b * eps / 3))) := by
        apply Real.exp_le_exp.mpr
        rw [hlamn]
        have hopt : (Real.exp (s * b) - 1 - s * b) / b ^ 2 * v - s * eps
            ≤ -(eps ^ 2) / (2 * (v + b * eps / 3)) := by
          have hsc := exp_sub_one_sub_le_sq_div (s := s * b) (by positivity) hsb
          have hden : (0:ℝ) < 1 - s * b / 3 := by nlinarith [hsb]
          have hCle : (Real.exp (s * b) - 1 - s * b) / b ^ 2 * v
              ≤ s ^ 2 * v / (2 * (1 - s * b / 3)) := by
            have hstep : (Real.exp (s * b) - 1 - s * b) / b ^ 2
                ≤ (s * b) ^ 2 / (2 * (1 - s * b / 3)) / b ^ 2 := by gcongr
            calc (Real.exp (s * b) - 1 - s * b) / b ^ 2 * v
                ≤ (s * b) ^ 2 / (2 * (1 - s * b / 3)) / b ^ 2 * v :=
                  mul_le_mul_of_nonneg_right hstep hv.le
              _ = s ^ 2 * v / (2 * (1 - s * b / 3)) := by
                  have hbne : b ≠ 0 := ne_of_gt hb
                  have hden_ne : (1:ℝ) - s * b / 3 ≠ 0 := ne_of_gt hden
                  field_simp
          have hkey : (1:ℝ) - s * b / 3 = v / (v + b * eps / 3) := by
            rw [hs]; field_simp; ring
          rw [hkey] at hCle
          have hfinal : s ^ 2 * v / (2 * (v / (v + b * eps / 3))) - s * eps
              = -(eps ^ 2) / (2 * (v + b * eps / 3)) := by
            rw [hs]; field_simp; ring
          linarith [hCle, hfinal]
        rw [hlam_def]
        calc (n:ℝ) * ((Real.exp (s * b) - 1 - s * b) / b ^ 2 * v) - (n:ℝ) * s * eps
            = (n:ℝ) * ((Real.exp (s * b) - 1 - s * b) / b ^ 2 * v - s * eps) := by ring
          _ ≤ (n:ℝ) * (-(eps ^ 2) / (2 * (v + b * eps / 3))) :=
              mul_le_mul_of_nonneg_left hopt hn_pos.le
          _ = -(n : ℝ) * eps ^ 2 / (2 * (v + b * eps / 3)) := by ring

end FormalSLT.Probability.BernsteinMGF
