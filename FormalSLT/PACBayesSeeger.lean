/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayesMcAllester
import FormalSLT.PACBayesFiniteProductMGF
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.IntervalCases

/-!
# Seeger KL-form PAC-Bayes certificate core

This module starts the Seeger KL-form PAC-Bayes track by adding the finite
binary-KL primitive and the deterministic/finite-confidence bridge that the
full Seeger theorem needs.

The theorem proved here is intentionally certificate-shaped.  It composes:

* the existing finite Donsker-Varadhan / change-of-measure core;
* a finite Markov confidence layer for a supplied Seeger prior moment;
* an explicit binary-KL Jensen certificate for posterior-averaged losses.

The q071 addendum in this file closes the finite prior-averaging layer: once
each hypothesis has the scalar Bernoulli-KL moment bound, the prior Seeger
moment certificate follows by finite Fubini and `∑ π = 1`.

The q072 addendum adds the finite scalar Bernoulli moment vocabulary, closes
the finite sample-to-type reduction for `n > 0` and `0 ≤ q ≤ 1`, and proves the
classical type-counting estimate
`Σ_k C(n,k)(k/n)^k(1-k/n)^(n-k) ≤ 2 * sqrt n` for every positive sample size.
The large-`n` branch uses Stirling plus a discrete kernel estimate; the
remaining finite range is discharged by exact normalization.

It does **not** yet discharge the remaining analytic facts that a full textbook
Seeger theorem would need:

* joint convexity/Jensen for binary KL over posterior mixtures.

Those boundaries are reflected in theorem names and hypotheses.  The binary
KL definition below is the standard Bernoulli relative entropy
`p log(p/q) + (1-p) log((1-p)/(1-q))`.  The full Pinsker-for-Bernoulli
quadratic lower bound is left as a named frontier rather than hidden as an
assumption.

Source: Seeger (2002), "PAC-Bayesian generalisation error bounds for Gaussian
process classification", JMLR 3, 233-269; McAllester (1999); Catoni (2007).
-/

namespace FormalSLT.PACBayesSeeger

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF

noncomputable section

variable {ι Ω : Type*}

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Binary KL divergence between Bernoulli parameters, with Lean's real-log junk values. -/
def binKL (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- Real-valued Bernoulli mass on `Bool`: `q` at success and `1 - q` at failure. -/
def bernoulliSuccessMass (q : ℝ) (b : Bool) : ℝ :=
  if b then q else 1 - q

/-- `bernoulliSuccessMass q` is a finite PMF when `q ∈ [0,1]`. -/
theorem bernoulliSuccessMass_isPMF {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsPMF (ι := Bool) (bernoulliSuccessMass q) where
  nonneg b := by
    cases b <;> simp [bernoulliSuccessMass, hq0, sub_nonneg.mpr hq1]
  sum_one := by
    rw [Fintype.sum_bool]
    simp [bernoulliSuccessMass]

/-! ### Scalar Bernoulli KL moment frontier -/

/-- Empirical mean of a Boolean sample, encoded as successes `true = 1`. -/
def bernoulliEmpiricalMean {n : ℕ} (S : Fin n → Bool) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k : Fin n, if S k then 1 else 0

/-- The set of successful coordinates in a Boolean sample. -/
def bernoulliSuccessSet {n : ℕ} (S : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun k => S k

/-- The number of successful coordinates in a Boolean sample. -/
def bernoulliSuccessCount {n : ℕ} (S : Fin n → Bool) : ℕ :=
  (bernoulliSuccessSet S).card

/-- Boolean sample with `true` precisely on a supplied success set. -/
private def boolSampleOfSuccessSet {n : ℕ} (A : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ A then true else false

/--
Samples with exactly `k` successes are equivalent to `k`-element subsets of
the coordinate set.
-/
private def bernoulliSuccessSetSubtypeEquiv {n k : ℕ} :
    {S : Fin n → Bool // bernoulliSuccessCount S = k} ≃
      {A : Finset (Fin n) // A.card = k} where
  toFun S := ⟨bernoulliSuccessSet S.1, S.2⟩
  invFun A := ⟨boolSampleOfSuccessSet A.1, by
    unfold bernoulliSuccessCount bernoulliSuccessSet boolSampleOfSuccessSet
    simp [A.2]
  ⟩
  left_inv S := by
    ext i
    unfold boolSampleOfSuccessSet bernoulliSuccessSet
    by_cases h : S.1 i
    · simp [h]
    · simp [h]
  right_inv A := by
    ext i
    unfold boolSampleOfSuccessSet bernoulliSuccessSet
    simp

/-- The number of Boolean samples with exactly `k` successes is `n.choose k`. -/
theorem bernoulliSuccessCount_fiber_card {n k : ℕ} :
    Fintype.card {S : Fin n → Bool // bernoulliSuccessCount S = k} = n.choose k := by
  calc
    Fintype.card {S : Fin n → Bool // bernoulliSuccessCount S = k} =
        Fintype.card {A : Finset (Fin n) // A.card = k} := by
          exact Fintype.card_congr bernoulliSuccessSetSubtypeEquiv
    _ = n.choose k := by
          simp [Fintype.card_fin]

/-- The success count is at most the sample size. -/
theorem bernoulliSuccessCount_le {n : ℕ} (S : Fin n → Bool) :
    bernoulliSuccessCount S ≤ n := by
  unfold bernoulliSuccessCount bernoulliSuccessSet
  simpa [Fintype.card_fin] using
    Finset.card_le_card (Finset.filter_subset (fun k : Fin n => S k) Finset.univ)

/--
Type grouping for any scalar function of the Bernoulli success count.

This is the finite combinatorial core of the Seeger scalar moment proof:
instead of summing over all `2^n` Boolean samples, one may sum over success
counts, with multiplicity `n.choose k`.
-/
theorem sum_boolSamples_by_bernoulliSuccessCount {n : ℕ} (f : ℕ → ℝ) :
    (∑ S : Fin n → Bool, f (bernoulliSuccessCount S)) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * f k := by
  have hmaps : ∀ S ∈ (Finset.univ : Finset (Fin n → Bool)),
      bernoulliSuccessCount S ∈ Finset.range (n + 1) := by
    intro S _hS
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (bernoulliSuccessCount_le S))
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin n → Bool)))
    (t := Finset.range (n + 1))
    (g := fun S : Fin n → Bool => bernoulliSuccessCount S)
    hmaps
    (f := fun S : Fin n → Bool => f (bernoulliSuccessCount S))
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro k _hk
  have hcard :
      (Finset.univ.filter fun S : Fin n → Bool => bernoulliSuccessCount S = k).card =
        n.choose k := by
    rw [← Fintype.card_subtype
      (fun S : Fin n → Bool => bernoulliSuccessCount S = k)]
    exact bernoulliSuccessCount_fiber_card (n := n) (k := k)
  have hinner :
      (∑ S ∈ (Finset.univ.filter fun S : Fin n → Bool => bernoulliSuccessCount S = k),
          f (bernoulliSuccessCount S)) =
        ((Finset.univ.filter fun S : Fin n → Bool => bernoulliSuccessCount S = k).card : ℝ) *
          f k := by
    rw [Finset.sum_eq_card_nsmul]
    · rw [nsmul_eq_mul]
    · intro S hS
      simp at hS
      simp [hS]
  rw [hinner, hcard]

/-- The Boolean empirical mean is the success count divided by the sample size. -/
theorem bernoulliEmpiricalMean_eq_successCount_div {n : ℕ} (S : Fin n → Bool) :
    bernoulliEmpiricalMean S = (bernoulliSuccessCount S : ℝ) / (n : ℝ) := by
  unfold bernoulliEmpiricalMean bernoulliSuccessCount bernoulliSuccessSet
  rw [div_eq_inv_mul]
  congr 1
  simp [Finset.sum_boole]

/--
The iid Bernoulli product weight of a Boolean sample depends only on its
success count.

This is the finite product algebra needed before the full sample-to-type
reduction: samples with the same `bernoulliSuccessCount` have the same
Bernoulli product mass.
-/
theorem finiteProductSampleWeight_bernoulliSuccessMass_eq
    {n : ℕ} (q : ℝ) (S : Fin n → Bool) :
    finiteProductSampleWeight (n := n) (bernoulliSuccessMass q) S =
      q ^ bernoulliSuccessCount S * (1 - q) ^ (n - bernoulliSuccessCount S) := by
  unfold finiteProductSampleWeight bernoulliSuccessMass bernoulliSuccessCount
    bernoulliSuccessSet
  have hcard_false :
      (Finset.univ.filter (fun k : Fin n => S k = false)).card =
        n - (Finset.univ.filter fun k : Fin n => S k).card := by
    have h :
        (Finset.univ.filter (fun k : Fin n => S k)).card +
          (Finset.univ.filter (fun k : Fin n => S k = false)).card = n := by
      simpa [Fintype.card_fin, Bool.not_eq_true] using
        (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
          (p := fun k : Fin n => S k))
    omega
  have htrueProd :
      (∏ k ∈ (Finset.univ.filter fun k : Fin n => S k),
          (if S k then q else 1 - q)) =
        q ^ (Finset.univ.filter fun k : Fin n => S k).card := by
    exact Finset.prod_eq_pow_card (s := (Finset.univ.filter fun k : Fin n => S k))
      (f := fun k => if S k then q else 1 - q) (b := q)
      (by
        intro k hk
        simp at hk
        simp [hk])
  have hfalseProd :
      (∏ k ∈ (Finset.univ.filter fun k : Fin n => ¬ S k),
          (if S k then q else 1 - q)) =
        (1 - q) ^ (n - (Finset.univ.filter fun k : Fin n => S k).card) := by
    calc
      (∏ k ∈ (Finset.univ.filter fun k : Fin n => ¬ S k),
          (if S k then q else 1 - q)) =
          (1 - q) ^ (Finset.univ.filter fun k : Fin n => ¬ S k).card := by
            exact Finset.prod_eq_pow_card
              (s := (Finset.univ.filter fun k : Fin n => ¬ S k))
              (f := fun k => if S k then q else 1 - q) (b := 1 - q)
              (by
                intro k hk
                simp at hk
                simp [hk])
      _ = (1 - q) ^ (n - (Finset.univ.filter fun k : Fin n => S k).card) := by
            congr 1
            simpa [Bool.not_eq_true] using hcard_false
  calc
    (∏ k : Fin n, (if S k then q else 1 - q)) =
        (∏ k ∈ (Finset.univ.filter fun k : Fin n => S k),
            (if S k then q else 1 - q)) *
          (∏ k ∈ (Finset.univ.filter fun k : Fin n => ¬ S k),
            (if S k then q else 1 - q)) := by
          exact (Finset.prod_filter_mul_prod_filter_not
            (s := (Finset.univ : Finset (Fin n))) (p := fun k : Fin n => S k)
            (f := fun k => if S k then q else 1 - q)).symm
    _ = q ^ (Finset.univ.filter fun k : Fin n => S k).card *
          (1 - q) ^ (n - (Finset.univ.filter fun k : Fin n => S k).card) := by
          rw [htrueProd, hfalseProd]

/--
The scalar Bernoulli-KL moment under the finite iid Bernoulli sample law.

This is the one-hypothesis quantity appearing in Seeger's KL-form proof:
`E exp(n * kl(\hat p || p))`.
-/
def bernoulliKLMoment {n : ℕ} (q : ℝ) : ℝ :=
  ∑ S : Fin n → Bool,
    finiteProductSampleWeight (n := n) (bernoulliSuccessMass q) S *
      Real.exp ((n : ℝ) * binKL (bernoulliEmpiricalMean S) q)

/-- One sample's contribution to the scalar Bernoulli-KL moment. -/
def bernoulliKLMomentSampleTerm {n : ℕ} (q : ℝ) (S : Fin n → Bool) : ℝ :=
  finiteProductSampleWeight (n := n) (bernoulliSuccessMass q) S *
    Real.exp ((n : ℝ) * binKL (bernoulliEmpiricalMean S) q)

/--
The per-type mass
`(k/n)^k * (1-k/n)^(n-k)` appearing after the Bernoulli KL exponential
cancels against the iid Bernoulli product mass.
-/
def bernoulliKLMomentTypeMass (n k : ℕ) : ℝ :=
  ((k : ℝ) / (n : ℝ)) ^ k * (1 - (k : ℝ) / (n : ℝ)) ^ (n - k)

/-- The Bernoulli type mass is nonnegative on valid success counts. -/
theorem bernoulliKLMomentTypeMass_nonneg_of_le {n k : ℕ} (hk : k ≤ n) :
    0 ≤ bernoulliKLMomentTypeMass n k := by
  by_cases hn : n = 0
  · have hk0 : k = 0 := by omega
    simp [bernoulliKLMomentTypeMass, hn, hk0]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hk_nonneg : 0 ≤ (k : ℝ) / (n : ℝ) :=
      div_nonneg (by positivity) hnR.le
    have hk_le_one : (k : ℝ) / (n : ℝ) ≤ 1 := by
      rw [div_le_one hnR]
      exact_mod_cast hk
    have hcomp_nonneg : 0 ≤ 1 - (k : ℝ) / (n : ℝ) :=
      sub_nonneg.mpr hk_le_one
    exact mul_nonneg (pow_nonneg hk_nonneg k)
      (pow_nonneg hcomp_nonneg (n - k))

/--
Interior per-type cancellation for the Bernoulli KL moment.

For `0 < k < n` and `0 < q < 1`, the Bernoulli product mass at any sample with
`k` successes cancels exactly against `exp(n * kl(k/n || q))`, leaving the
maximum-likelihood type mass `(k/n)^k (1-k/n)^(n-k)`.
-/
theorem bernoulliKLMomentTypeMass_cancel_interior
    {n k : ℕ} {q : ℝ} (hn : 0 < n) (hk0 : 0 < k) (hklt : k < n)
    (hq0 : 0 < q) (hq1 : q < 1) :
    q ^ k * (1 - q) ^ (n - k) *
        Real.exp ((n : ℝ) * binKL ((k : ℝ) / (n : ℝ)) q) =
      bernoulliKLMomentTypeMass n k := by
  let p : ℝ := (k : ℝ) / (n : ℝ)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk0
  have hp : 0 < p := by
    unfold p
    exact div_pos hkR hnR
  have hp_lt_one : p < 1 := by
    unfold p
    rw [div_lt_one hnR]
    exact_mod_cast hklt
  have h1mp : 0 < 1 - p := sub_pos.mpr hp_lt_one
  have h1mq : 0 < 1 - q := sub_pos.mpr hq1
  have hpq : 0 < p / q := div_pos hp hq0
  have hcomp : 0 < (1 - p) / (1 - q) := div_pos h1mp h1mq
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hq_ne : q ≠ 0 := ne_of_gt hq0
  have h1mq_ne : 1 - q ≠ 0 := ne_of_gt h1mq
  have hnk : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
    rw [Nat.cast_sub (Nat.le_of_lt hklt)]
  have hexponent :
      (n : ℝ) * binKL p q =
        (k : ℝ) * Real.log (p / q) +
          ((n - k : ℕ) : ℝ) * Real.log ((1 - p) / (1 - q)) := by
    unfold binKL p
    rw [hnk]
    field_simp [hn_ne]
  have hleft1 :
      q ^ k * Real.exp ((k : ℝ) * Real.log (p / q)) = p ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log hpq]
    rw [div_pow]
    field_simp [hq_ne]
  have hleft2 :
      (1 - q) ^ (n - k) *
          Real.exp (((n - k : ℕ) : ℝ) * Real.log ((1 - p) / (1 - q))) =
        (1 - p) ^ (n - k) := by
    rw [Real.exp_nat_mul, Real.exp_log hcomp]
    rw [div_pow]
    field_simp [h1mq_ne]
  unfold bernoulliKLMomentTypeMass
  rw [show ((k : ℝ) / (n : ℝ)) = p by rfl]
  rw [hexponent, Real.exp_add]
  calc
    q ^ k * (1 - q) ^ (n - k) *
        (Real.exp ((k : ℝ) * Real.log (p / q)) *
          Real.exp (((n - k : ℕ) : ℝ) * Real.log ((1 - p) / (1 - q)))) =
        (q ^ k * Real.exp ((k : ℝ) * Real.log (p / q))) *
          ((1 - q) ^ (n - k) *
            Real.exp (((n - k : ℕ) : ℝ) * Real.log ((1 - p) / (1 - q)))) := by
          ring
    _ = p ^ k * (1 - p) ^ (n - k) := by
          rw [hleft1, hleft2]

/--
Sample-level interior cancellation, using the success-count reduction for the
product mass and empirical mean.
-/
theorem bernoulliKLMomentSampleTerm_eq_typeMass_interior
    {n : ℕ} {q : ℝ} (hn : 0 < n) (hq0 : 0 < q) (hq1 : q < 1)
    (S : Fin n → Bool)
    (hk0 : 0 < bernoulliSuccessCount S) (hklt : bernoulliSuccessCount S < n) :
    bernoulliKLMomentSampleTerm (n := n) q S =
      bernoulliKLMomentTypeMass n (bernoulliSuccessCount S) := by
  unfold bernoulliKLMomentSampleTerm
  rw [finiteProductSampleWeight_bernoulliSuccessMass_eq q S]
  rw [bernoulliEmpiricalMean_eq_successCount_div S]
  exact bernoulliKLMomentTypeMass_cancel_interior hn hk0 hklt hq0 hq1

/-- Per-type cancellation at the zero-success endpoint. -/
theorem bernoulliKLMomentTypeMass_cancel_count_zero
    {n : ℕ} {q : ℝ} (hq1 : q < 1) :
    (1 - q) ^ n * Real.exp ((n : ℝ) * binKL 0 q) =
      bernoulliKLMomentTypeMass n 0 := by
  have h1mq : 0 < 1 - q := sub_pos.mpr hq1
  have hcomp : 0 < 1 / (1 - q) := one_div_pos.mpr h1mq
  have h1mq_ne : 1 - q ≠ 0 := ne_of_gt h1mq
  have hbin : binKL 0 q = Real.log (1 / (1 - q)) := by
    unfold binKL
    norm_num
  unfold bernoulliKLMomentTypeMass
  rw [hbin, Real.exp_nat_mul, Real.exp_log hcomp]
  rw [div_pow]
  field_simp [h1mq_ne]
  simp

/-- Sample-level cancellation at the zero-success endpoint. -/
theorem bernoulliKLMomentSampleTerm_eq_typeMass_count_zero
    {n : ℕ} {q : ℝ} (hn : 0 < n) (hq1 : q < 1)
    {S : Fin n → Bool} (hk : bernoulliSuccessCount S = 0) :
    bernoulliKLMomentSampleTerm (n := n) q S = bernoulliKLMomentTypeMass n 0 := by
  unfold bernoulliKLMomentSampleTerm
  rw [finiteProductSampleWeight_bernoulliSuccessMass_eq q S]
  rw [bernoulliEmpiricalMean_eq_successCount_div S]
  rw [hk]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  field_simp [hnR]
  simpa using bernoulliKLMomentTypeMass_cancel_count_zero (n := n) (q := q) hq1

/-- Per-type cancellation at the all-success endpoint. -/
theorem bernoulliKLMomentTypeMass_cancel_count_top
    {n : ℕ} {q : ℝ} (hn : 0 < n) (hq0 : 0 < q) :
    q ^ n * Real.exp ((n : ℝ) * binKL 1 q) =
      bernoulliKLMomentTypeMass n n := by
  have hq_ne : q ≠ 0 := ne_of_gt hq0
  have hcomp : 0 < 1 / q := one_div_pos.mpr hq0
  have hbin : binKL 1 q = Real.log (1 / q) := by
    unfold binKL
    norm_num
  unfold bernoulliKLMomentTypeMass
  rw [hbin, Real.exp_nat_mul, Real.exp_log hcomp]
  rw [div_pow]
  field_simp [hq_ne]
  simp

/-- Sample-level cancellation at the all-success endpoint. -/
theorem bernoulliKLMomentSampleTerm_eq_typeMass_count_top
    {n : ℕ} {q : ℝ} (hn : 0 < n) (hq0 : 0 < q)
    {S : Fin n → Bool} (hk : bernoulliSuccessCount S = n) :
    bernoulliKLMomentSampleTerm (n := n) q S = bernoulliKLMomentTypeMass n n := by
  unfold bernoulliKLMomentSampleTerm
  rw [finiteProductSampleWeight_bernoulliSuccessMass_eq q S]
  rw [bernoulliEmpiricalMean_eq_successCount_div S]
  rw [hk]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  field_simp [hnR]
  simp
  simpa using bernoulliKLMomentTypeMass_cancel_count_top (n := n) (q := q) hn hq0

/--
Every sample contribution equals its per-type mass when `n > 0` and the true
Bernoulli parameter lies in the open unit interval.
-/
theorem bernoulliKLMomentSampleTerm_eq_typeMass_of_q_interior
    {n : ℕ} {q : ℝ} (hn : 0 < n) (hq0 : 0 < q) (hq1 : q < 1)
    (S : Fin n → Bool) :
    bernoulliKLMomentSampleTerm (n := n) q S =
      bernoulliKLMomentTypeMass n (bernoulliSuccessCount S) := by
  by_cases hzero : bernoulliSuccessCount S = 0
  · rw [hzero]
    exact bernoulliKLMomentSampleTerm_eq_typeMass_count_zero
      (n := n) (q := q) hn hq1 hzero
  by_cases htop : bernoulliSuccessCount S = n
  · rw [htop]
    exact bernoulliKLMomentSampleTerm_eq_typeMass_count_top
      (n := n) (q := q) hn hq0 htop
  · have hk0 : 0 < bernoulliSuccessCount S := Nat.pos_of_ne_zero hzero
    have hklt : bernoulliSuccessCount S < n :=
      lt_of_le_of_ne (bernoulliSuccessCount_le S) htop
    exact bernoulliKLMomentSampleTerm_eq_typeMass_interior hn hq0 hq1 S hk0 hklt

/-- Sample-to-type inequality at Bernoulli parameter `q = 0`. -/
theorem bernoulliKLMomentSampleTerm_le_typeMass_q_zero
    {n : ℕ} (hn : 0 < n) (S : Fin n → Bool) :
    bernoulliKLMomentSampleTerm (n := n) 0 S ≤
      bernoulliKLMomentTypeMass n (bernoulliSuccessCount S) := by
  by_cases hzero : bernoulliSuccessCount S = 0
  · rw [hzero]
    exact le_of_eq (bernoulliKLMomentSampleTerm_eq_typeMass_count_zero
      (n := n) (q := 0) hn (by norm_num) hzero)
  · have hkpos : 0 < bernoulliSuccessCount S := Nat.pos_of_ne_zero hzero
    unfold bernoulliKLMomentSampleTerm
    rw [finiteProductSampleWeight_bernoulliSuccessMass_eq 0 S]
    rw [zero_pow (ne_of_gt hkpos)]
    simp
    exact bernoulliKLMomentTypeMass_nonneg_of_le (bernoulliSuccessCount_le S)

/-- Sample-to-type inequality at Bernoulli parameter `q = 1`. -/
theorem bernoulliKLMomentSampleTerm_le_typeMass_q_one
    {n : ℕ} (hn : 0 < n) (S : Fin n → Bool) :
    bernoulliKLMomentSampleTerm (n := n) 1 S ≤
      bernoulliKLMomentTypeMass n (bernoulliSuccessCount S) := by
  by_cases htop : bernoulliSuccessCount S = n
  · rw [htop]
    exact le_of_eq (bernoulliKLMomentSampleTerm_eq_typeMass_count_top
      (n := n) (q := 1) hn (by norm_num) htop)
  · have hklt : bernoulliSuccessCount S < n :=
      lt_of_le_of_ne (bernoulliSuccessCount_le S) htop
    have hsubpos : 0 < n - bernoulliSuccessCount S := Nat.sub_pos_of_lt hklt
    unfold bernoulliKLMomentSampleTerm
    rw [finiteProductSampleWeight_bernoulliSuccessMass_eq 1 S]
    norm_num
    rw [zero_pow (ne_of_gt hsubpos)]
    simp
    exact bernoulliKLMomentTypeMass_nonneg_of_le (bernoulliSuccessCount_le S)

/--
The Bernoulli type-counting term
`C(n,k) (k/n)^k (1-k/n)^(n-k)`.

At the endpoints Lean's real power convention gives `0^0 = 1`, matching the
usual continuous extension of the maximum-likelihood Bernoulli type mass.
-/
def bernoulliKLMomentTypeTerm (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * bernoulliKLMomentTypeMass n k

/-- Sum of the Bernoulli KL moment type-counting terms over `k = 0, ..., n`. -/
def bernoulliKLMomentTypeSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), bernoulliKLMomentTypeTerm n k

/--
The classical scalar type-counting estimate needed to close the full Seeger
prior-moment theorem.

This proposition is intentionally kept as a named scalar certificate shape;
`BernoulliKLMomentTypeCountingBound_of_pos` proves it exactly for `0 < n`.
The zero-sample instance is false for these definitions.
-/
def BernoulliKLMomentTypeCountingBound (n : ℕ) : Prop :=
  bernoulliKLMomentTypeSum n ≤ 2 * Real.sqrt (n : ℝ)

/--
The finite algebraic reduction from the sample-level Bernoulli KL moment to the
type-counting sum.

This is also exposed as a certificate boundary: proving it amounts to grouping
`Fin n → Bool` samples by their number of successes and simplifying
`exp(n * kl(k/n || q))` against the Bernoulli product mass.
-/
def BernoulliKLMomentTypeReduction (n : ℕ) (q : ℝ) : Prop :=
  bernoulliKLMoment (n := n) q ≤ bernoulliKLMomentTypeSum n

/--
Finite grouping reduction for the Bernoulli KL moment, assuming only the
per-sample KL algebra/cancellation step.

The remaining hypothesis says that each sample's weighted exponential KL term
is bounded by the per-type mass for its success count.  The theorem proves the
rest of `BernoulliKLMomentTypeReduction`: summing over samples, grouping by
success count, and using the `n.choose k` fiber cardinality.
-/
theorem bernoulliKLMoment_typeReduction_of_sampleTerm_le_typeMass
    {n : ℕ} {q : ℝ}
    (hterm : ∀ S : Fin n → Bool,
      bernoulliKLMomentSampleTerm (n := n) q S ≤
        bernoulliKLMomentTypeMass n (bernoulliSuccessCount S)) :
    BernoulliKLMomentTypeReduction n q := by
  unfold BernoulliKLMomentTypeReduction bernoulliKLMoment bernoulliKLMomentTypeSum
    bernoulliKLMomentTypeTerm
  calc
    (∑ S : Fin n → Bool,
        finiteProductSampleWeight (n := n) (bernoulliSuccessMass q) S *
          Real.exp ((n : ℝ) * binKL (bernoulliEmpiricalMean S) q))
        ≤ ∑ S : Fin n → Bool, bernoulliKLMomentTypeMass n (bernoulliSuccessCount S) := by
          apply Finset.sum_le_sum
          intro S _hS
          simpa [bernoulliKLMomentSampleTerm] using hterm S
    _ = ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℝ) * bernoulliKLMomentTypeMass n k := by
          exact sum_boolSamples_by_bernoulliSuccessCount
            (n := n) (f := bernoulliKLMomentTypeMass n)

/--
Closed finite sample-to-type reduction for Bernoulli parameters in the open
unit interval.

Together with `BernoulliKLMomentTypeCountingBound_of_pos`, this gives the
closed scalar moment bound below.
-/
theorem bernoulliKLMomentTypeReduction_of_q_interior
    {n : ℕ} {q : ℝ} (hn : 0 < n) (hq0 : 0 < q) (hq1 : q < 1) :
    BernoulliKLMomentTypeReduction n q :=
  bernoulliKLMoment_typeReduction_of_sampleTerm_le_typeMass
    (n := n) (q := q)
    (fun S => le_of_eq
      (bernoulliKLMomentSampleTerm_eq_typeMass_of_q_interior
        (n := n) (q := q) hn hq0 hq1 S))

/--
Closed finite sample-to-type reduction for Bernoulli parameters in the closed
unit interval.

The endpoint cases are inequalities because Lean's `Real.log` is totalized at
zero; impossible samples have zero Bernoulli product mass and are controlled by
nonnegativity of the type mass.
-/
theorem bernoulliKLMomentTypeReduction_of_q_mem_Icc
    {n : ℕ} {q : ℝ} (hn : 0 < n) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    BernoulliKLMomentTypeReduction n q := by
  rcases hq0.eq_or_lt with hqeq | hqpos
  · subst q
    exact bernoulliKLMoment_typeReduction_of_sampleTerm_le_typeMass
      (n := n) (q := 0)
      (fun S => bernoulliKLMomentSampleTerm_le_typeMass_q_zero hn S)
  · rcases lt_or_eq_of_le hq1 with hqlt | hqeq
    · exact bernoulliKLMomentTypeReduction_of_q_interior hn hqpos hqlt
    · subst q
      exact bernoulliKLMoment_typeReduction_of_sampleTerm_le_typeMass
        (n := n) (q := 1)
        (fun S => bernoulliKLMomentSampleTerm_le_typeMass_q_one hn S)

/-! ### Pointwise nonnegativity and unit-bound on the type-mass surface

Unconditional elementary bounds on the type-mass surface.  They supply nonneg
per-type mass, nonneg per-type term, per-type term `≤ 1` (binomial PMF bound),
and the coarse type-counting bound `typeSum n ≤ (n + 1 : ℝ)`. -/

/-- The Bernoulli type mass is nonnegative. -/
theorem bernoulliKLMomentTypeMass_nonneg (n k : ℕ) :
    0 ≤ bernoulliKLMomentTypeMass n k := by
  unfold bernoulliKLMomentTypeMass
  set p := (k : ℝ) / (n : ℝ) with hp_def
  have hp0 : 0 ≤ p := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  by_cases hkn : k ≤ n
  · have hp1 : p ≤ 1 := by
      by_cases hn0 : n = 0
      · subst hn0
        have hk0 : k = 0 := by omega
        simp [hp_def, hk0]
      · rw [hp_def, div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn0)]
        exact_mod_cast hkn
    have h1mp : 0 ≤ 1 - p := sub_nonneg.mpr hp1
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg h1mp _)
  · push Not at hkn
    have h_sub_zero : n - k = 0 := Nat.sub_eq_zero_of_le (le_of_lt hkn)
    rw [h_sub_zero, pow_zero, mul_one]
    exact pow_nonneg hp0 _

/-- The Bernoulli type mass is bounded by `1` whenever `k ≤ n`. -/
theorem bernoulliKLMomentTypeMass_le_one
    {n k : ℕ} (hkle : k ≤ n) :
    bernoulliKLMomentTypeMass n k ≤ 1 := by
  unfold bernoulliKLMomentTypeMass
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hk0 : k = 0 := by omega
    simp [hk0]
  set p := (k : ℝ) / (n : ℝ) with hp_def
  have hp0 : 0 ≤ p := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hp1 : p ≤ 1 := by
    rw [hp_def, div_le_one (by exact_mod_cast hnpos)]
    exact_mod_cast hkle
  have h1mp_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have h1mp_le_one : 1 - p ≤ 1 := by linarith
  have hpk_le_one : p ^ k ≤ 1 := pow_le_one₀ hp0 hp1
  have h1mpk_le_one : (1 - p) ^ (n - k) ≤ 1 :=
    pow_le_one₀ h1mp_nonneg h1mp_le_one
  have hpk_nonneg : 0 ≤ p ^ k := pow_nonneg hp0 _
  calc p ^ k * (1 - p) ^ (n - k)
      ≤ p ^ k * 1 := mul_le_mul_of_nonneg_left h1mpk_le_one hpk_nonneg
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_right hpk_le_one (by norm_num)
    _ = 1 := by ring

/-- The Bernoulli type term is nonnegative. -/
theorem bernoulliKLMomentTypeTerm_nonneg (n k : ℕ) :
    0 ≤ bernoulliKLMomentTypeTerm n k := by
  unfold bernoulliKLMomentTypeTerm
  exact mul_nonneg (Nat.cast_nonneg _) (bernoulliKLMomentTypeMass_nonneg n k)

/--
The Bernoulli type term `C(n,k) (k/n)^k (1-k/n)^(n-k)` is the binomial PMF
value at the maximum-likelihood point and is therefore bounded by `1`.

Routes through the binomial expansion of `1 = (p + (1-p))^n` at `p = k/n`:
identifies the `k`-th summand as `typeTerm n k`, and uses that each summand
of a sum of nonnegative reals is bounded by the sum.
-/
theorem bernoulliKLMomentTypeTerm_le_one
    {n k : ℕ} (hkle : k ≤ n) :
    bernoulliKLMomentTypeTerm n k ≤ 1 := by
  unfold bernoulliKLMomentTypeTerm bernoulliKLMomentTypeMass
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hk0 : k = 0 := by omega
    simp [hk0]
  set p := (k : ℝ) / (n : ℝ) with hp_def
  have hp0 : 0 ≤ p := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hp1 : p ≤ 1 := by
    rw [hp_def, div_le_one (by exact_mod_cast hnpos)]
    exact_mod_cast hkle
  have h1mp : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hterm_nonneg :
      ∀ j ∈ Finset.range (n + 1),
        0 ≤ p ^ j * (1 - p) ^ (n - j) * (n.choose j : ℝ) := by
    intro j _
    refine mul_nonneg (mul_nonneg ?_ ?_) (Nat.cast_nonneg _)
    · exact pow_nonneg hp0 _
    · exact pow_nonneg h1mp _
  have hbinom :
      (p + (1 - p)) ^ n =
        ∑ j ∈ Finset.range (n + 1),
          p ^ j * (1 - p) ^ (n - j) * (n.choose j : ℝ) := by
    rw [add_pow]
  have hsum_one :
      (∑ j ∈ Finset.range (n + 1),
          p ^ j * (1 - p) ^ (n - j) * (n.choose j : ℝ)) = 1 := by
    rw [← hbinom]
    rw [show p + (1 - p) = 1 by ring, one_pow]
  have hkmem : k ∈ Finset.range (n + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hkle)
  have hsingle :=
    Finset.single_le_sum
      (f := fun j => p ^ j * (1 - p) ^ (n - j) * (n.choose j : ℝ))
      hterm_nonneg hkmem
  rw [hsum_one] at hsingle
  rw [show ((n.choose k : ℝ) * (p ^ k * (1 - p) ^ (n - k)) : ℝ) =
        p ^ k * (1 - p) ^ (n - k) * (n.choose k : ℝ) by ring]
  exact hsingle

/-- The Bernoulli type sum is nonnegative. -/
theorem bernoulliKLMomentTypeSum_nonneg (n : ℕ) :
    0 ≤ bernoulliKLMomentTypeSum n := by
  unfold bernoulliKLMomentTypeSum
  exact Finset.sum_nonneg (fun k _ => bernoulliKLMomentTypeTerm_nonneg n k)

/--
Unconditional weaker type-counting bound: `typeSum n ≤ (n + 1 : ℝ)`.

Each of the `n + 1` summands is the binomial PMF value at the
maximum-likelihood point and so is bounded by `1`.  The exact positive bound
below gives the sharp `2 * sqrt n` scalar constant.
-/
theorem bernoulliKLMomentTypeSum_le_succ (n : ℕ) :
    bernoulliKLMomentTypeSum n ≤ (n + 1 : ℝ) := by
  unfold bernoulliKLMomentTypeSum
  calc
    (∑ k ∈ Finset.range (n + 1), bernoulliKLMomentTypeTerm n k)
        ≤ ∑ _k ∈ Finset.range (n + 1), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          exact bernoulliKLMomentTypeTerm_le_one
            (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    _ = (n + 1 : ℝ) := by
          rw [Finset.sum_const, Finset.card_range]
          simp

/-! ### Exact positive type-counting estimate

The large-sample proof combines a one-sided Stirling envelope with a discrete
kernel estimate for `Σ 1 / sqrt(k(n-k))`.  The finitely many small sample sizes
below the resulting threshold are exact normalized real-arithmetic checks. -/

private theorem inv_sqrt_succ_le_sqrt_diff (m : ℕ) :
    (1 : ℝ) / Real.sqrt (m + 1 : ℝ) ≤
      2 * Real.sqrt (m + 1 : ℝ) - 2 * Real.sqrt (m : ℝ) := by
  have hpos : 0 < Real.sqrt (m + 1 : ℝ) := by positivity
  have hsqrt_le : Real.sqrt (m : ℝ) ≤ Real.sqrt (m + 1 : ℝ) := by
    exact Real.sqrt_le_sqrt (by norm_num)
  have hden_pos : 0 < Real.sqrt (m + 1 : ℝ) + Real.sqrt (m : ℝ) := by
    positivity
  calc
    (1 : ℝ) / Real.sqrt (m + 1 : ℝ)
        ≤ 2 / (Real.sqrt (m + 1 : ℝ) + Real.sqrt (m : ℝ)) := by
          rw [div_le_div_iff₀ hpos hden_pos]
          nlinarith
    _ = 2 * Real.sqrt (m + 1 : ℝ) - 2 * Real.sqrt (m : ℝ) := by
          have hsq1 : (Real.sqrt (m + 1 : ℝ)) ^ 2 = (m + 1 : ℝ) := by
            rw [Real.sq_sqrt]; positivity
          have hsq0 : (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) := by
            rw [Real.sq_sqrt]; positivity
          field_simp [hden_pos.ne']
          nlinarith

private theorem sum_range_inv_sqrt_succ_le (m : ℕ) :
    (∑ j ∈ Finset.range m, (1 : ℝ) / Real.sqrt (j + 1 : ℝ)) ≤
      2 * Real.sqrt (m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ j ∈ Finset.range m, (1 : ℝ) / Real.sqrt (j + 1 : ℝ)) +
            (1 : ℝ) / Real.sqrt (m + 1 : ℝ)
            ≤ 2 * Real.sqrt (m : ℝ) + (1 : ℝ) / Real.sqrt (m + 1 : ℝ) := by
              gcongr
        _ ≤ 2 * Real.sqrt (m : ℝ) +
            (2 * Real.sqrt (m + 1 : ℝ) - 2 * Real.sqrt (m : ℝ)) := by
              gcongr
              exact inv_sqrt_succ_le_sqrt_diff m
        _ = 2 * Real.sqrt ((m + 1 : ℕ) : ℝ) := by norm_num

private theorem sqrt_nat_add_le_add_sqrt (a b : ℕ) :
    Real.sqrt ((a + b : ℕ) : ℝ) ≤ Real.sqrt (a : ℝ) + Real.sqrt (b : ℝ) := by
  have hnon : 0 ≤ Real.sqrt (a : ℝ) + Real.sqrt (b : ℝ) := by positivity
  rw [Real.sqrt_le_left hnon]
  have hsq_a : (Real.sqrt (a : ℝ)) ^ 2 = (a : ℝ) := by
    rw [Real.sq_sqrt]; positivity
  have hsq_b : (Real.sqrt (b : ℝ)) ^ 2 = (b : ℝ) := by
    rw [Real.sq_sqrt]; positivity
  rw [show ((a + b : ℕ) : ℝ) = (a : ℝ) + (b : ℝ) by norm_num]
  rw [show (Real.sqrt (a : ℝ) + Real.sqrt (b : ℝ)) ^ 2 =
      (Real.sqrt (a : ℝ)) ^ 2 + (Real.sqrt (b : ℝ)) ^ 2 +
        2 * Real.sqrt (a : ℝ) * Real.sqrt (b : ℝ) by ring]
  rw [hsq_a, hsq_b]
  have hcross : 0 ≤ Real.sqrt (a : ℝ) * Real.sqrt (b : ℝ) := by positivity
  nlinarith

private theorem bernoulliKLMomentKernel_le_split {n k : ℕ}
    (hk0 : 0 < k) (hkn : k < n) :
    (1 : ℝ) / Real.sqrt ((k : ℝ) * (((n - k : ℕ) : ℝ))) ≤
      (1 / Real.sqrt (n : ℝ)) *
        (1 / Real.sqrt (k : ℝ) + 1 / Real.sqrt (((n - k : ℕ) : ℝ))) := by
  have hnkpos : 0 < n - k := Nat.sub_pos_of_lt hkn
  have hnpos : 0 < n := lt_trans hk0 hkn
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk0
  have hnkR : 0 < ((n - k : ℕ) : ℝ) := by exact_mod_cast hnkpos
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hsum : k + (n - k) = n := Nat.add_sub_of_le (Nat.le_of_lt hkn)
  have hsqrt_sum :
      Real.sqrt (n : ℝ) ≤ Real.sqrt (k : ℝ) + Real.sqrt (((n - k : ℕ) : ℝ)) := by
    simpa [hsum] using sqrt_nat_add_le_add_sqrt k (n - k)
  calc
    (1 : ℝ) / Real.sqrt ((k : ℝ) * (((n - k : ℕ) : ℝ)))
        = Real.sqrt (n : ℝ) /
            (Real.sqrt (n : ℝ) * Real.sqrt ((k : ℝ) * (((n - k : ℕ) : ℝ)))) := by
          field_simp [Real.sqrt_ne_zero'.mpr hnR]
    _ ≤ (Real.sqrt (k : ℝ) + Real.sqrt (((n - k : ℕ) : ℝ))) /
            (Real.sqrt (n : ℝ) * Real.sqrt ((k : ℝ) * (((n - k : ℕ) : ℝ)))) := by
          gcongr
    _ = (1 / Real.sqrt (n : ℝ)) *
        (1 / Real.sqrt (k : ℝ) + 1 / Real.sqrt (((n - k : ℕ) : ℝ))) := by
          rw [Real.sqrt_mul hkR.le]
          field_simp [Real.sqrt_ne_zero'.mpr hnR, Real.sqrt_ne_zero'.mpr hkR,
            Real.sqrt_ne_zero'.mpr hnkR]
          ring

private theorem bernoulliKLMomentKernelSum_le_four {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Finset.Ico 1 n,
      (1 : ℝ) / Real.sqrt ((k : ℝ) * (((n - k : ℕ) : ℝ)))) ≤ 4 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    (∑ k ∈ Finset.Ico 1 n,
      (1 : ℝ) / Real.sqrt ((k : ℝ) * (((n - k : ℕ) : ℝ))))
      ≤ ∑ k ∈ Finset.Ico 1 n,
          (1 / Real.sqrt (n : ℝ)) *
            (1 / Real.sqrt (k : ℝ) + 1 / Real.sqrt (((n - k : ℕ) : ℝ))) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
          have hkn : k < n := (Finset.mem_Ico.mp hk).2
          have hk0 : 0 < k := lt_of_lt_of_le (by norm_num) hk1
          exact bernoulliKLMomentKernel_le_split hk0 hkn
    _ = (1 / Real.sqrt (n : ℝ)) *
        ((∑ k ∈ Finset.Ico 1 n, 1 / Real.sqrt (k : ℝ)) +
          (∑ k ∈ Finset.Ico 1 n, 1 / Real.sqrt (((n - k : ℕ) : ℝ)))) := by
          rw [← Finset.mul_sum]
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          ring
    _ ≤ (1 / Real.sqrt (n : ℝ)) * (4 * Real.sqrt (n : ℝ)) := by
          gcongr
          have hfirst :
              (∑ k ∈ Finset.Ico 1 n, 1 / Real.sqrt (k : ℝ)) ≤
                2 * Real.sqrt (n : ℝ) := by
            calc
              (∑ k ∈ Finset.Ico 1 n, 1 / Real.sqrt (k : ℝ))
                = ∑ j ∈ Finset.range (n - 1), 1 / Real.sqrt (((1 + j : ℕ) : ℝ)) := by
                    rw [Finset.sum_Ico_eq_sum_range]
              _ = ∑ j ∈ Finset.range (n - 1), 1 / Real.sqrt (j + 1 : ℝ) := by
                    apply Finset.sum_congr rfl
                    intro j _hj
                    norm_num [add_comm]
              _ ≤ 2 * Real.sqrt ((n - 1 : ℕ) : ℝ) :=
                    sum_range_inv_sqrt_succ_le (n - 1)
              _ ≤ 2 * Real.sqrt (n : ℝ) := by
                    gcongr
                    exact_mod_cast Nat.sub_le n 1
          have hsecond :
              (∑ k ∈ Finset.Ico 1 n, 1 / Real.sqrt (((n - k : ℕ) : ℝ))) ≤
                2 * Real.sqrt (n : ℝ) := by
            rw [Finset.sum_Ico_reflect (f := fun j : ℕ => 1 / Real.sqrt (j : ℝ))
              (k := 1) (m := n) (n := n) (by omega)]
            simpa using hfirst
          linarith
    _ = 4 := by
          field_simp [Real.sqrt_ne_zero'.mpr hnR]

private theorem factorial_le_exp_sqrt_stirling {n : ℕ} (hn : 0 < n) :
    (n.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt (n : ℝ) *
      ((n : ℝ) / Real.exp 1) ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  have hanti := Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  dsimp at hanti
  rw [Stirling.stirlingSeq_one] at hanti
  unfold Stirling.stirlingSeq at hanti
  have hden_pos :
      0 < √(2 * ((m + 1 : ℕ) : ℝ)) *
        (((m + 1 : ℕ) : ℝ) / rexp 1) ^ (m + 1) := by
    positivity
  have h := (div_le_iff₀ hden_pos).mp hanti
  have hsimp :
      (Real.exp 1 / Real.sqrt 2) * Real.sqrt (2 * ((m + 1 : ℕ) : ℝ)) =
        Real.exp 1 * Real.sqrt ((m + 1 : ℕ) : ℝ) := by
    rw [Real.sqrt_mul]
    · field_simp [Real.sqrt_ne_zero'.mpr (show (0 : ℝ) < 2 by norm_num)]
    · norm_num
  calc
    (((m + 1).factorial : ℕ) : ℝ) ≤ (Real.exp 1 / Real.sqrt 2) *
        (Real.sqrt (2 * ((m + 1 : ℕ) : ℝ)) *
          (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1)) := h
    _ = ((Real.exp 1 / Real.sqrt 2) * Real.sqrt (2 * ((m + 1 : ℕ) : ℝ))) *
        (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1) := by ring
    _ = Real.exp 1 * Real.sqrt ((m + 1 : ℕ) : ℝ) *
        (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1) := by rw [hsimp]

private theorem one_sub_nat_div_eq_sub_div {n k : ℕ} (hkn : k ≤ n) (hn : 0 < n) :
    (1 : ℝ) - (k : ℝ) / (n : ℝ) = ((n - k : ℕ) : ℝ) / (n : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [Nat.cast_sub hkn]
  field_simp [hnR]

private theorem bernoulliKLMomentTypeTerm_le_stirling_kernel
    {n k : ℕ} (hk0 : 0 < k) (hkn : k < n) :
    bernoulliKLMomentTypeTerm n k ≤
      (Real.exp 1 / (2 * Real.pi)) * Real.sqrt (n : ℝ) *
        ((1 : ℝ) / Real.sqrt ((k : ℝ) * (((n - k : ℕ) : ℝ)))) := by
  let l : ℕ := n - k
  have hlpos : 0 < l := Nat.sub_pos_of_lt hkn
  have hnpos : 0 < n := lt_trans hk0 hkn
  have hkle : k ≤ n := Nat.le_of_lt hkn
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk0
  have hlR : 0 < (l : ℝ) := by exact_mod_cast hlpos
  have hnfac := factorial_le_exp_sqrt_stirling (n := n) hnpos
  have hkfac := Stirling.le_factorial_stirling k
  have hlfac := Stirling.le_factorial_stirling l
  have hchoose :
      (n.choose k : ℝ) = (n.factorial : ℝ) / ((k.factorial : ℝ) * (l.factorial : ℝ)) := by
    simpa [l] using (Nat.cast_choose ℝ hkle)
  have hkden_pos :
      0 < Real.sqrt (2 * Real.pi * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k := by
    positivity
  have hlden_pos :
      0 < Real.sqrt (2 * Real.pi * (l : ℝ)) * ((l : ℝ) / Real.exp 1) ^ l := by
    positivity
  have hkfac_pos : 0 < (k.factorial : ℝ) := by positivity
  have hlfac_pos : 0 < (l.factorial : ℝ) := by positivity
  have hden_lower :
      (Real.sqrt (2 * Real.pi * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k) *
        (Real.sqrt (2 * Real.pi * (l : ℝ)) * ((l : ℝ) / Real.exp 1) ^ l) ≤
      (k.factorial : ℝ) * (l.factorial : ℝ) := by
    exact mul_le_mul hkfac hlfac hlden_pos.le hkfac_pos.le
  have hden_lower_pos :
      0 < (Real.sqrt (2 * Real.pi * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k) *
        (Real.sqrt (2 * Real.pi * (l : ℝ)) * ((l : ℝ) / Real.exp 1) ^ l) := by
    positivity
  have hchoose_bound :
      (n.choose k : ℝ) ≤
        (Real.exp 1 * Real.sqrt (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n) /
          ((Real.sqrt (2 * Real.pi * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k) *
            (Real.sqrt (2 * Real.pi * (l : ℝ)) * ((l : ℝ) / Real.exp 1) ^ l)) := by
    rw [hchoose]
    calc
      (n.factorial : ℝ) / ((k.factorial : ℝ) * (l.factorial : ℝ))
          ≤ (Real.exp 1 * Real.sqrt (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n) /
              ((k.factorial : ℝ) * (l.factorial : ℝ)) := by
            exact div_le_div_of_nonneg_right hnfac
              (mul_nonneg hkfac_pos.le hlfac_pos.le)
      _ ≤ (Real.exp 1 * Real.sqrt (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n) /
          ((Real.sqrt (2 * Real.pi * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k) *
            (Real.sqrt (2 * Real.pi * (l : ℝ)) * ((l : ℝ) / Real.exp 1) ^ l)) := by
            exact div_le_div_of_nonneg_left (by positivity) hden_lower_pos hden_lower
  unfold bernoulliKLMomentTypeTerm bernoulliKLMomentTypeMass
  rw [one_sub_nat_div_eq_sub_div hkle hnpos]
  have hmain_nonneg :
      0 ≤ ((k : ℝ) / (n : ℝ)) ^ k * (((l : ℕ) : ℝ) / (n : ℝ)) ^ (n - k) := by
    positivity
  calc
    (n.choose k : ℝ) *
        (((k : ℝ) / (n : ℝ)) ^ k * (((l : ℕ) : ℝ) / (n : ℝ)) ^ (n - k))
      ≤ ((Real.exp 1 * Real.sqrt (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n) /
          ((Real.sqrt (2 * Real.pi * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k) *
            (Real.sqrt (2 * Real.pi * (l : ℝ)) * ((l : ℝ) / Real.exp 1) ^ l))) *
          (((k : ℝ) / (n : ℝ)) ^ k * (((l : ℕ) : ℝ) / (n : ℝ)) ^ (n - k)) := by
        exact mul_le_mul_of_nonneg_right hchoose_bound hmain_nonneg
    _ = (Real.exp 1 / (2 * Real.pi)) * Real.sqrt (n : ℝ) *
        ((1 : ℝ) / Real.sqrt ((k : ℝ) * (((n - k : ℕ) : ℝ)))) := by
        have hkln : k + l = n := by
          unfold l
          omega
        have hpow :
            ((n : ℝ) / Real.exp 1) ^ n *
              (((k : ℝ) / (n : ℝ)) ^ k * (((l : ℕ) : ℝ) / (n : ℝ)) ^ l) =
            ((k : ℝ) / Real.exp 1) ^ k * (((l : ℕ) : ℝ) / Real.exp 1) ^ l := by
          rw [← hkln]
          push_cast
          rw [pow_add]
          simp_rw [div_eq_mul_inv, mul_pow]
          have hsum_ne : (↑k + ↑l : ℝ) ≠ 0 := by positivity
          ring_nf
          field_simp [hsum_ne, ne_of_gt hkR, ne_of_gt hlR, (Real.exp_pos 1).ne']
          rw [show (1 / (↑k + ↑l : ℝ)) ^ k * (1 / (↑k + ↑l : ℝ)) ^ l *
                  (↑k + ↑l : ℝ) ^ k * (↑k + ↑l : ℝ) ^ l =
                ((1 / (↑k + ↑l : ℝ)) ^ k * (↑k + ↑l : ℝ) ^ k) *
                  ((1 / (↑k + ↑l : ℝ)) ^ l * (↑k + ↑l : ℝ) ^ l) by ring]
          rw [one_div, inv_pow, inv_mul_cancel₀ (pow_ne_zero k hsum_ne), inv_pow,
            inv_mul_cancel₀ (pow_ne_zero l hsum_ne)]
          ring
        have hsqrtdens :
            Real.sqrt (2 * Real.pi * (k : ℝ)) * Real.sqrt (2 * Real.pi * (l : ℝ)) =
              (2 * Real.pi) * Real.sqrt ((k : ℝ) * (l : ℝ)) := by
          have htwopi_nonneg : 0 ≤ 2 * Real.pi := by positivity
          have htwopi_abs : |2 * Real.pi| = 2 * Real.pi := abs_of_nonneg htwopi_nonneg
          rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi * (k : ℝ))]
          rw [show (2 * Real.pi * (k : ℝ)) * (2 * Real.pi * (l : ℝ)) =
              (2 * Real.pi) ^ 2 * ((k : ℝ) * (l : ℝ)) by ring]
          rw [Real.sqrt_mul (sq_nonneg (2 * Real.pi)), Real.sqrt_sq_eq_abs, htwopi_abs]
        change
          ((Real.exp 1 * Real.sqrt (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n) /
            ((Real.sqrt (2 * Real.pi * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k) *
              (Real.sqrt (2 * Real.pi * (l : ℝ)) * ((l : ℝ) / Real.exp 1) ^ l))) *
              (((k : ℝ) / (n : ℝ)) ^ k * (((l : ℕ) : ℝ) / (n : ℝ)) ^ l) =
            (Real.exp 1 / (2 * Real.pi)) * Real.sqrt (n : ℝ) *
              ((1 : ℝ) / Real.sqrt ((k : ℝ) * (l : ℝ)))
        rw [show Real.exp 1 * Real.sqrt (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n /
              ((Real.sqrt (2 * Real.pi * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k) *
                (Real.sqrt (2 * Real.pi * (l : ℝ)) * ((l : ℝ) / Real.exp 1) ^ l)) *
              (((k : ℝ) / (n : ℝ)) ^ k * (((l : ℕ) : ℝ) / (n : ℝ)) ^ l) =
            Real.exp 1 * Real.sqrt (n : ℝ) *
              ((((n : ℝ) / Real.exp 1) ^ n *
                (((k : ℝ) / (n : ℝ)) ^ k * (((l : ℕ) : ℝ) / (n : ℝ)) ^ l)) /
              ((Real.sqrt (2 * Real.pi * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k) *
                (Real.sqrt (2 * Real.pi * (l : ℝ)) * ((l : ℝ) / Real.exp 1) ^ l))) by ring]
        rw [hpow]
        field_simp [(Real.exp_pos 1).ne', ne_of_gt hkR, ne_of_gt hlR,
          Real.sqrt_ne_zero'.mpr (by positivity : 0 < 2 * Real.pi * (k : ℝ)),
          Real.sqrt_ne_zero'.mpr (by positivity : 0 < 2 * Real.pi * (l : ℝ)),
          Real.sqrt_ne_zero'.mpr (mul_pos hkR hlR), hsqrtdens]
        rw [show Real.sqrt ((k : ℝ) * 2 * Real.pi) =
          Real.sqrt (2 * Real.pi * (k : ℝ)) by ring_nf]
        rw [show Real.sqrt ((l : ℝ) * 2 * Real.pi) =
          Real.sqrt (2 * Real.pi * (l : ℝ)) by ring_nf]
        nlinarith [hsqrtdens]

private theorem bernoulliKLMomentTypeSum_range_decomp {n : ℕ} (hn : 0 < n) :
    Finset.range (n + 1) = insert 0 (insert n (Finset.Ico 1 n)) := by
  ext k
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
  constructor
  · intro hk
    by_cases hk0 : k = 0
    · exact Or.inl hk0
    · right
      by_cases hkn : k = n
      · exact Or.inl hkn
      · right
        omega
  · intro h
    rcases h with rfl | h
    · omega
    rcases h with rfl | h
    · omega
    omega

private theorem bernoulliKLMomentTypeTerm_zero (n : ℕ) :
    bernoulliKLMomentTypeTerm n 0 = 1 := by
  unfold bernoulliKLMomentTypeTerm bernoulliKLMomentTypeMass
  simp

private theorem bernoulliKLMomentTypeTerm_top {n : ℕ} (hn : 0 < n) :
    bernoulliKLMomentTypeTerm n n = 1 := by
  unfold bernoulliKLMomentTypeTerm bernoulliKLMomentTypeMass
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnR]
  simp

private theorem two_mul_exp_one_div_pi_le_seven_four :
    2 * Real.exp 1 / Real.pi ≤ (7 : ℝ) / 4 := by
  rw [div_le_iff₀ Real.pi_pos]
  nlinarith [Real.exp_one_lt_d9.le, Real.pi_gt_d4.le]

private theorem sqrt_ge_eight_of_64_le {n : ℕ} (hn : 64 ≤ n) :
    (8 : ℝ) ≤ Real.sqrt (n : ℝ) := by
  apply Real.le_sqrt_of_sq_le
  norm_num
  exact_mod_cast hn

private theorem bernoulliKLMomentTypeSum_le_two_add_seven_four_sqrt
    {n : ℕ} (hn : 0 < n) :
    bernoulliKLMomentTypeSum n ≤ 2 + ((7 : ℝ) / 4) * Real.sqrt (n : ℝ) := by
  have hcoef_nonneg : 0 ≤ (Real.exp 1 / (2 * Real.pi)) * Real.sqrt (n : ℝ) := by
    positivity
  unfold bernoulliKLMomentTypeSum
  rw [bernoulliKLMomentTypeSum_range_decomp hn]
  rw [Finset.sum_insert]
  · rw [Finset.sum_insert]
    · have hinterior :
          (∑ k ∈ Finset.Ico 1 n, bernoulliKLMomentTypeTerm n k) ≤
            (Real.exp 1 / (2 * Real.pi)) * Real.sqrt (n : ℝ) *
              (∑ k ∈ Finset.Ico 1 n,
                (1 : ℝ) / Real.sqrt ((k : ℝ) * (((n - k : ℕ) : ℝ)))) := by
        calc
          (∑ k ∈ Finset.Ico 1 n, bernoulliKLMomentTypeTerm n k)
              ≤ ∑ k ∈ Finset.Ico 1 n,
                  (Real.exp 1 / (2 * Real.pi)) * Real.sqrt (n : ℝ) *
                    ((1 : ℝ) / Real.sqrt ((k : ℝ) * (((n - k : ℕ) : ℝ)))) := by
                apply Finset.sum_le_sum
                intro k hk
                have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
                have hkn : k < n := (Finset.mem_Ico.mp hk).2
                exact bernoulliKLMomentTypeTerm_le_stirling_kernel
                  (lt_of_lt_of_le (by norm_num) hk1) hkn
          _ = (Real.exp 1 / (2 * Real.pi)) * Real.sqrt (n : ℝ) *
              (∑ k ∈ Finset.Ico 1 n,
                (1 : ℝ) / Real.sqrt ((k : ℝ) * (((n - k : ℕ) : ℝ)))) := by
                rw [Finset.mul_sum]
      have hkernel := bernoulliKLMomentKernelSum_le_four (n := n) hn
      have hkernel_scaled :
          (Real.exp 1 / (2 * Real.pi)) * Real.sqrt (n : ℝ) *
              (∑ k ∈ Finset.Ico 1 n,
                (1 : ℝ) / Real.sqrt ((k : ℝ) * (((n - k : ℕ) : ℝ)))) ≤
            (2 * Real.exp 1 / Real.pi) * Real.sqrt (n : ℝ) := by
        calc
          (Real.exp 1 / (2 * Real.pi)) * Real.sqrt (n : ℝ) *
              (∑ k ∈ Finset.Ico 1 n,
                (1 : ℝ) / Real.sqrt ((k : ℝ) * (((n - k : ℕ) : ℝ))))
              ≤ (Real.exp 1 / (2 * Real.pi)) * Real.sqrt (n : ℝ) * 4 := by
                gcongr
          _ = (2 * Real.exp 1 / Real.pi) * Real.sqrt (n : ℝ) := by
                field_simp [Real.pi_ne_zero]
                ring
      calc
        bernoulliKLMomentTypeTerm n 0 +
            (bernoulliKLMomentTypeTerm n n +
              ∑ k ∈ Finset.Ico 1 n, bernoulliKLMomentTypeTerm n k)
            = 2 + ∑ k ∈ Finset.Ico 1 n, bernoulliKLMomentTypeTerm n k := by
              rw [bernoulliKLMomentTypeTerm_zero, bernoulliKLMomentTypeTerm_top hn]
              ring
        _ ≤ 2 + (2 * Real.exp 1 / Real.pi) * Real.sqrt (n : ℝ) := by
              linarith
        _ ≤ 2 + ((7 : ℝ) / 4) * Real.sqrt (n : ℝ) := by
              have hmul := mul_le_mul_of_nonneg_right
                two_mul_exp_one_div_pi_le_seven_four (Real.sqrt_nonneg (n : ℝ))
              linarith
    · simp only [Finset.mem_Ico, not_and]
      intro _
      omega
  · simp only [Finset.mem_insert, Finset.mem_Ico, not_or]
    constructor
    · exact Ne.symm hn.ne'
    · omega

theorem BernoulliKLMomentTypeCountingBound_of_64_le {n : ℕ} (hn : 64 ≤ n) :
    BernoulliKLMomentTypeCountingBound n := by
  unfold BernoulliKLMomentTypeCountingBound
  have hnpos : 0 < n := by omega
  have hbase := bernoulliKLMomentTypeSum_le_two_add_seven_four_sqrt hnpos
  have hsqrt8 : (8 : ℝ) ≤ Real.sqrt (n : ℝ) := sqrt_ge_eight_of_64_le hn
  calc
    bernoulliKLMomentTypeSum n ≤
        2 + ((7 : ℝ) / 4) * Real.sqrt (n : ℝ) := hbase
    _ ≤ 2 * Real.sqrt (n : ℝ) := by nlinarith

set_option maxHeartbeats 0 in
private theorem BernoulliKLMomentTypeCountingBound_of_pos_lt_64
    {n : ℕ} (hpos : 0 < n) (hlt : n < 64) :
    BernoulliKLMomentTypeCountingBound n := by
  interval_cases n <;>
    unfold BernoulliKLMomentTypeCountingBound bernoulliKLMomentTypeSum
      bernoulliKLMomentTypeTerm bernoulliKLMomentTypeMass <;>
    norm_num [Finset.sum_range_succ, Nat.choose]
  all_goals
    apply le_of_sq_le_sq
    · ring_nf
      rw [Real.sq_sqrt]
      · norm_num
      · norm_num
    · positivity

/--
Exact Bernoulli-KL type-counting estimate for every positive sample size.

The `n = 0` version is false for these definitions: the type sum is `1` while
`2 * sqrt 0 = 0`, so the public theorem carries the necessary positivity
hypothesis explicitly.
-/
theorem BernoulliKLMomentTypeCountingBound_of_pos {n : ℕ} (hn : 0 < n) :
    BernoulliKLMomentTypeCountingBound n := by
  by_cases hlarge : 64 ≤ n
  · exact BernoulliKLMomentTypeCountingBound_of_64_le hlarge
  · exact BernoulliKLMomentTypeCountingBound_of_pos_lt_64 hn (Nat.lt_of_not_ge hlarge)

/--
Closed Bernoulli KL moment bound at the weaker `(n + 1 : ℝ)` constant, valid
for any `0 < q < 1` and any `0 < n`.

This is retained as a simple coarse bound; the exact `2 * sqrt n` scalar
wrappers below use `BernoulliKLMomentTypeCountingBound_of_pos`.
-/
theorem bernoulliKLMoment_le_succ_of_q_interior
    {n : ℕ} {q : ℝ} (hn : 0 < n) (hq0 : 0 < q) (hq1 : q < 1) :
    bernoulliKLMoment (n := n) q ≤ (n + 1 : ℝ) :=
  (bernoulliKLMomentTypeReduction_of_q_interior hn hq0 hq1).trans
    (bernoulliKLMomentTypeSum_le_succ n)

/--
Closed Bernoulli KL moment bound at the weaker `(n + 1 : ℝ)` constant, valid
for every Bernoulli parameter in `[0,1]` and any positive sample size.
-/
theorem bernoulliKLMoment_le_succ_of_q_mem_Icc
    {n : ℕ} {q : ℝ} (hn : 0 < n) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    bernoulliKLMoment (n := n) q ≤ (n + 1 : ℝ) :=
  (bernoulliKLMomentTypeReduction_of_q_mem_Icc hn hq0 hq1).trans
    (bernoulliKLMomentTypeSum_le_succ n)

/--
Reduction from a scalar Bernoulli moment-to-type-sum comparison and the
classical type-counting estimate to Seeger's `2 * sqrt n` scalar moment bound.

This theorem deliberately does not prove the type-counting estimate itself.
It pins the remaining q072 analytic frontier to the explicit hypothesis
`BernoulliKLMomentTypeCountingBound n`, and the finite grouping frontier to
`BernoulliKLMomentTypeReduction n q`.
-/
theorem bernoulliKLMoment_le_two_sqrt_of_typeCountingBound
    {n : ℕ} {q : ℝ}
    (hreduction : BernoulliKLMomentTypeReduction n q)
    (htype : BernoulliKLMomentTypeCountingBound n) :
    bernoulliKLMoment (n := n) q ≤ 2 * Real.sqrt (n : ℝ) :=
  hreduction.trans htype

/--
Scalar Bernoulli KL moment bound for open-interval Bernoulli parameters,
conditional only on the analytic type-counting estimate.

The finite sample-to-type algebra is discharged by
`bernoulliKLMomentTypeReduction_of_q_interior`; the sole remaining supplied
fact is `BernoulliKLMomentTypeCountingBound n`.
-/
theorem bernoulliKLMoment_le_two_sqrt_of_q_interior_and_typeCountingBound
    {n : ℕ} {q : ℝ} (hn : 0 < n) (hq0 : 0 < q) (hq1 : q < 1)
    (htype : BernoulliKLMomentTypeCountingBound n) :
    bernoulliKLMoment (n := n) q ≤ 2 * Real.sqrt (n : ℝ) :=
  bernoulliKLMoment_le_two_sqrt_of_typeCountingBound
    (bernoulliKLMomentTypeReduction_of_q_interior hn hq0 hq1) htype

/--
Scalar Bernoulli KL moment bound for closed-interval Bernoulli parameters,
conditional only on the analytic type-counting estimate.
-/
theorem bernoulliKLMoment_le_two_sqrt_of_q_mem_Icc_and_typeCountingBound
    {n : ℕ} {q : ℝ} (hn : 0 < n) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (htype : BernoulliKLMomentTypeCountingBound n) :
    bernoulliKLMoment (n := n) q ≤ 2 * Real.sqrt (n : ℝ) :=
  bernoulliKLMoment_le_two_sqrt_of_typeCountingBound
    (bernoulliKLMomentTypeReduction_of_q_mem_Icc hn hq0 hq1) htype

/--
Closed scalar Bernoulli KL moment bound for open-interval Bernoulli
parameters.  The exact positive type-counting theorem supplies the formerly
manual scalar certificate.
-/
theorem bernoulliKLMoment_le_two_sqrt_of_q_interior
    {n : ℕ} {q : ℝ} (hn : 0 < n) (hq0 : 0 < q) (hq1 : q < 1) :
    bernoulliKLMoment (n := n) q ≤ 2 * Real.sqrt (n : ℝ) :=
  bernoulliKLMoment_le_two_sqrt_of_q_interior_and_typeCountingBound
    hn hq0 hq1 (BernoulliKLMomentTypeCountingBound_of_pos hn)

/--
Closed scalar Bernoulli KL moment bound for every Bernoulli parameter in
`[0,1]`.  Endpoint cases use the finite sample-to-type inequality, and the
type-counting theorem supplies the exact `2 * sqrt n` scalar constant.
-/
theorem bernoulliKLMoment_le_two_sqrt_of_q_mem_Icc
    {n : ℕ} {q : ℝ} (hn : 0 < n) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    bernoulliKLMoment (n := n) q ≤ 2 * Real.sqrt (n : ℝ) :=
  bernoulliKLMoment_le_two_sqrt_of_q_mem_Icc_and_typeCountingBound
    hn hq0 hq1 (BernoulliKLMomentTypeCountingBound_of_pos hn)

/-- The Seeger prior moment at one finite sample outcome. -/
def priorSeegerKLMoment [Fintype ι] (prior : ι → ℝ) (n : ℕ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ) (ω : Ω) : ℝ :=
  ∑ i, prior i *
    Real.exp ((n : ℝ) * binKL (empiricalRiskFn ω i) (riskFn i))

/-- Expected Seeger prior moment under a finite sample law. -/
def expectedPriorSeegerKLMoment [Fintype Ω] [Fintype ι]
    (ν : Ω → ℝ) (prior : ι → ℝ) (n : ℕ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ) : ℝ :=
  ∑ ω, ν ω * priorSeegerKLMoment prior n riskFn empiricalRiskFn ω

/-- Finite sample mass of outcomes whose Seeger prior moment exceeds a threshold. -/
def priorSeegerKLMomentTailMass [Fintype Ω] [Fintype ι]
    (ν : Ω → ℝ) (prior : ι → ℝ) (n : ℕ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (threshold : ℝ) : ℝ :=
  ∑ ω ∈ (Finset.univ.filter fun ω =>
      threshold ≤ priorSeegerKLMoment prior n riskFn empiricalRiskFn ω), ν ω

/-- The Seeger prior moment is nonnegative under a nonnegative prior. -/
theorem priorSeegerKLMoment_nonneg [Fintype ι]
    {prior : ι → ℝ} (hπ : IsPMF prior) (n : ℕ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ) (ω : Ω) :
    0 ≤ priorSeegerKLMoment prior n riskFn empiricalRiskFn ω := by
  unfold priorSeegerKLMoment
  exact Finset.sum_nonneg
    (fun i _hi => mul_nonneg (hπ.nonneg i) (le_of_lt (Real.exp_pos _)))

private theorem priorSeegerKLMoment_pos [Fintype ι] [Nonempty ι]
    {prior : ι → ℝ} (hπ : IsFullSupportPMF prior) (n : ℕ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ) (ω : Ω) :
    0 < priorSeegerKLMoment prior n riskFn empiricalRiskFn ω := by
  unfold priorSeegerKLMoment
  exact Finset.sum_pos
    (fun i _hi => mul_pos (hπ.pos i) (Real.exp_pos _))
    Finset.univ_nonempty

/-- Finite Markov bound for the Seeger prior moment. -/
theorem priorSeegerKLMoment_tailMass_le_expected_div
    [Fintype Ω] [DecidableEq Ω] [Fintype ι]
    {ν : Ω → ℝ} {prior : ι → ℝ} (hν : IsPMF ν) (hπ : IsPMF prior)
    (n : ℕ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    priorSeegerKLMomentTailMass ν prior n riskFn empiricalRiskFn threshold
      ≤ expectedPriorSeegerKLMoment ν prior n riskFn empiricalRiskFn / threshold := by
  unfold priorSeegerKLMomentTailMass expectedPriorSeegerKLMoment
  calc
    (∑ ω ∈ (Finset.univ.filter fun ω =>
        threshold ≤ priorSeegerKLMoment prior n riskFn empiricalRiskFn ω), ν ω)
        ≤ ∑ ω ∈ (Finset.univ.filter fun ω =>
            threshold ≤ priorSeegerKLMoment prior n riskFn empiricalRiskFn ω),
            (ν ω * priorSeegerKLMoment prior n riskFn empiricalRiskFn ω) / threshold := by
          apply Finset.sum_le_sum
          intro ω hω
          have hTail :
              threshold ≤ priorSeegerKLMoment prior n riskFn empiricalRiskFn ω :=
            (Finset.mem_filter.mp hω).2
          have hScaled :
              ν ω * threshold ≤
                ν ω * priorSeegerKLMoment prior n riskFn empiricalRiskFn ω :=
            mul_le_mul_of_nonneg_left hTail (hν.nonneg ω)
          exact (le_div_iff₀ hthreshold).mpr hScaled
    _ ≤ ∑ ω,
          (ν ω * priorSeegerKLMoment prior n riskFn empiricalRiskFn ω) / threshold := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro ω hω
            exact (Finset.mem_filter.mp hω).1
          · intro ω _hω _hnot
            exact div_nonneg
              (mul_nonneg (hν.nonneg ω)
                (priorSeegerKLMoment_nonneg hπ n riskFn empiricalRiskFn ω))
              (le_of_lt hthreshold)
    _ =
        (∑ ω, ν ω * priorSeegerKLMoment prior n riskFn empiricalRiskFn ω) /
          threshold := by
          rw [Finset.sum_div]

/-- Markov confidence layer for a supplied Seeger prior-moment expectation certificate. -/
theorem priorSeegerKLMoment_tailMass_le_delta_of_expected_bound
    [Fintype Ω] [DecidableEq Ω] [Fintype ι]
    {ν : Ω → ℝ} {prior : ι → ℝ} (hν : IsPMF ν) (hπ : IsPMF prior)
    (n : ℕ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    {momentBound delta : ℝ} (hmomentBound : 0 < momentBound) (hdelta : 0 < delta)
    (hExpected :
      expectedPriorSeegerKLMoment ν prior n riskFn empiricalRiskFn ≤ momentBound) :
    priorSeegerKLMomentTailMass ν prior n riskFn empiricalRiskFn
        (momentBound / delta) ≤ delta := by
  have hthreshold : 0 < momentBound / delta := div_pos hmomentBound hdelta
  have hmarkov :=
    priorSeegerKLMoment_tailMass_le_expected_div
      hν hπ n riskFn empiricalRiskFn hthreshold
  calc
    priorSeegerKLMomentTailMass ν prior n riskFn empiricalRiskFn
        (momentBound / delta)
        ≤ expectedPriorSeegerKLMoment ν prior n riskFn empiricalRiskFn /
            (momentBound / delta) := hmarkov
    _ ≤ momentBound / (momentBound / delta) := by
          exact div_le_div_of_nonneg_right hExpected (le_of_lt hthreshold)
    _ = delta := by
          field_simp [ne_of_gt hmomentBound, ne_of_gt hdelta]

/--
Finite prior averaging for Seeger moments.

If every hypothesis has the same scalar Bernoulli-KL moment budget under the
sample law, then the prior-averaged Seeger moment has that budget.  This is the
q071 closure of the *prior* moment layer; the remaining scalar input is the
binomial/type-counting theorem for one Bernoulli empirical mean.
-/
theorem expectedPriorSeegerKLMoment_le_of_pointwise
    [Fintype Ω] [Fintype ι]
    {ν : Ω → ℝ} {prior : ι → ℝ} (hprior : IsPMF prior)
    (n : ℕ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    {momentBound : ℝ}
    (hpointwise :
      ∀ i : ι,
        (∑ ω : Ω,
          ν ω * Real.exp ((n : ℝ) * binKL (empiricalRiskFn ω i) (riskFn i))) ≤
          momentBound) :
    expectedPriorSeegerKLMoment ν prior n riskFn empiricalRiskFn ≤ momentBound := by
  classical
  unfold expectedPriorSeegerKLMoment priorSeegerKLMoment
  have hswap :
      (∑ ω : Ω,
          ν ω *
            ∑ i : ι,
              prior i *
                Real.exp ((n : ℝ) * binKL (empiricalRiskFn ω i) (riskFn i))) =
        ∑ i : ι,
          prior i *
            ∑ ω : Ω,
              ν ω * Real.exp ((n : ℝ) * binKL (empiricalRiskFn ω i) (riskFn i)) := by
    have h1 :
        (∑ ω : Ω,
            ν ω *
              ∑ i : ι,
                prior i *
                  Real.exp ((n : ℝ) * binKL (empiricalRiskFn ω i) (riskFn i))) =
          ∑ ω : Ω, ∑ i : ι,
            ν ω *
              (prior i *
                Real.exp ((n : ℝ) * binKL (empiricalRiskFn ω i) (riskFn i))) := by
      apply Finset.sum_congr rfl
      intro ω _hω
      rw [Finset.mul_sum]
    have h2 :
        (∑ ω : Ω, ∑ i : ι,
          ν ω *
            (prior i *
              Real.exp ((n : ℝ) * binKL (empiricalRiskFn ω i) (riskFn i)))) =
          ∑ i : ι, ∑ ω : Ω,
            ν ω *
              (prior i *
                Real.exp ((n : ℝ) * binKL (empiricalRiskFn ω i) (riskFn i))) := by
      rw [Finset.sum_comm]
    have h3 :
        (∑ i : ι, ∑ ω : Ω,
            ν ω *
              (prior i *
                Real.exp ((n : ℝ) * binKL (empiricalRiskFn ω i) (riskFn i)))) =
        ∑ i : ι,
          prior i *
            ∑ ω : Ω,
              ν ω * Real.exp ((n : ℝ) * binKL (empiricalRiskFn ω i) (riskFn i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _hω
      ring
    exact h1.trans (h2.trans h3)
  rw [hswap]
  calc
    (∑ i : ι,
        prior i *
          ∑ ω : Ω,
            ν ω * Real.exp ((n : ℝ) * binKL (empiricalRiskFn ω i) (riskFn i)))
        ≤ ∑ i : ι, prior i * momentBound := by
        apply Finset.sum_le_sum
        intro i _hi
        exact mul_le_mul_of_nonneg_left (hpointwise i) (hprior.nonneg i)
    _ = momentBound := by
        rw [← Finset.sum_mul, hprior.sum_one, one_mul]

/--
Prior Seeger moment bound from pointwise Bernoulli-KL moment bounds.

The hypothesis is deliberately pointwise: for each hypothesis, the scalar
Bernoulli-KL moment under the finite sample law is already bounded by
`2 * sqrt n`.  This theorem closes the finite prior aggregation layer.
-/
theorem expectedPriorSeegerKLMoment_bernoulli_le_two_sqrt
    [Fintype Ω] [Fintype ι]
    {ν : Ω → ℝ} {prior : ι → ℝ} (hprior : IsPMF prior)
    (n : ℕ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (hpointwise :
      ∀ i : ι,
        (∑ ω : Ω,
          ν ω * Real.exp ((n : ℝ) * binKL (empiricalRiskFn ω i) (riskFn i))) ≤
          2 * Real.sqrt (n : ℝ)) :
    expectedPriorSeegerKLMoment ν prior n riskFn empiricalRiskFn ≤
      2 * Real.sqrt (n : ℝ) :=
  expectedPriorSeegerKLMoment_le_of_pointwise
    hprior n riskFn empiricalRiskFn hpointwise

/--
Deterministic Seeger KL-form adapter for one finite sample outcome.

The explicit `hbinaryKLJensen` hypothesis is the missing joint-convexity/Jensen
step for binary KL over posterior mixtures.
-/
theorem posteriorBinaryKL_le_of_priorSeegerKLMoment_le
    [Fintype ι] [Nonempty ι]
    {ρ prior : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsFullSupportPMF prior)
    {n : ℕ} (hn : 0 < n)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ) (ω : Ω)
    {threshold : ℝ}
    (hmoment :
      priorSeegerKLMoment prior n riskFn empiricalRiskFn ω ≤ threshold)
    (hbinaryKLJensen :
      binKL (posteriorAverage ρ (empiricalRiskFn ω)) (posteriorAverage ρ riskFn) ≤
        posteriorAverage ρ
          (fun i => binKL (empiricalRiskFn ω i) (riskFn i))) :
    binKL (posteriorAverage ρ (empiricalRiskFn ω)) (posteriorAverage ρ riskFn) ≤
      (klDiv ρ prior + Real.log threshold) / (n : ℝ) := by
  classical
  let pointwiseKL : ι → ℝ := fun i => binKL (empiricalRiskFn ω i) (riskFn i)
  have hmoment_pos : 0 < priorSeegerKLMoment prior n riskFn empiricalRiskFn ω :=
    priorSeegerKLMoment_pos hπ n riskFn empiricalRiskFn ω
  have hdv := donsker_varadhan hρ hπ (fun i : ι => (n : ℝ) * pointwiseKL i)
  have hprior :
      (∑ i : ι, prior i * Real.exp ((n : ℝ) * pointwiseKL i)) =
        priorSeegerKLMoment prior n riskFn empiricalRiskFn ω := by
    unfold priorSeegerKLMoment pointwiseKL
    rfl
  have hscaled :
      (n : ℝ) * posteriorAverage ρ pointwiseKL ≤
        klDiv ρ prior + Real.log threshold := by
    have hlhs :
        (∑ i : ι, ρ i * ((n : ℝ) * pointwiseKL i)) =
          (n : ℝ) * posteriorAverage ρ pointwiseKL := by
      unfold posteriorAverage
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _hi => ?_)
      ring
    rw [hlhs] at hdv
    have hlog :
        Real.log (∑ i : ι, prior i * Real.exp ((n : ℝ) * pointwiseKL i)) ≤
          Real.log threshold := by
      rw [hprior]
      exact Real.log_le_log hmoment_pos hmoment
    linarith
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpointwise :
      posteriorAverage ρ pointwiseKL ≤
        (klDiv ρ prior + Real.log threshold) / (n : ℝ) := by
    rw [le_div_iff₀ hnR]
    simpa [mul_comm] using hscaled
  exact hbinaryKLJensen.trans hpointwise

/--
Finite Seeger KL-form good-event theorem under explicit prior-moment and
binary-KL Jensen certificates.

This is the honest q070 bridge currently available without hiding the hard
Bernoulli-MGF and joint-convexity subgoals.
-/
theorem pacbayes_seeger_klForm_of_priorMoment_and_binaryKLJensen
    [Fintype Ω] [DecidableEq Ω] [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 0 < n)
    (ν : Ω → ℝ) (hν : IsPMF ν)
    (prior : ι → ℝ) (hprior : IsFullSupportPMF prior)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (delta : ℝ) (hdelta : 0 < delta)
    (hExpected :
      expectedPriorSeegerKLMoment ν prior n riskFn empiricalRiskFn ≤
        2 * Real.sqrt (n : ℝ))
    (hbinaryKLJensen :
      ∀ (ω : Ω) (ρ : ι → ℝ), IsPMF ρ →
        binKL (posteriorAverage ρ (empiricalRiskFn ω)) (posteriorAverage ρ riskFn) ≤
          posteriorAverage ρ
            (fun i => binKL (empiricalRiskFn ω i) (riskFn i))) :
    1 - delta ≤
      ∑ ω ∈ (Finset.univ.filter fun ω : Ω =>
        ∀ ρ : ι → ℝ, IsPMF ρ →
          binKL (posteriorAverage ρ (empiricalRiskFn ω))
              (posteriorAverage ρ riskFn) ≤
            (klDiv ρ prior + Real.log ((2 * Real.sqrt (n : ℝ)) / delta)) /
              (n : ℝ)),
        ν ω := by
  classical
  set momentBound : ℝ := 2 * Real.sqrt (n : ℝ) with hmomentBound_def
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmomentBound_pos : 0 < momentBound := by
    rw [hmomentBound_def]
    exact mul_pos two_pos (Real.sqrt_pos.mpr hnR)
  set threshold : ℝ := momentBound / delta with hthreshold_def
  have hthreshold_pos : 0 < threshold := by
    rw [hthreshold_def]
    exact div_pos hmomentBound_pos hdelta
  set badPred : Ω → Prop := fun ω =>
    ∃ ρ : ι → ℝ,
      IsPMF ρ ∧
        binKL (posteriorAverage ρ (empiricalRiskFn ω))
            (posteriorAverage ρ riskFn) >
          (klDiv ρ prior + Real.log threshold) / (n : ℝ)
  set goodPred : Ω → Prop := fun ω =>
    ∀ ρ : ι → ℝ, IsPMF ρ →
      binKL (posteriorAverage ρ (empiricalRiskFn ω))
          (posteriorAverage ρ riskFn) ≤
        (klDiv ρ prior + Real.log threshold) / (n : ℝ)
  have htail :
      (∑ ω ∈ Finset.univ.filter badPred, ν ω) ≤ delta := by
    have hsubset :
        Finset.univ.filter badPred ⊆
          Finset.univ.filter fun ω : Ω =>
            threshold ≤ priorSeegerKLMoment prior n riskFn empiricalRiskFn ω := by
      intro ω hω
      rw [Finset.mem_filter] at hω ⊢
      rcases hω with ⟨hmem, ρ, hρ, hbad⟩
      refine ⟨hmem, ?_⟩
      by_contra hnot
      have hmoment :
          priorSeegerKLMoment prior n riskFn empiricalRiskFn ω ≤ threshold :=
        le_of_not_ge hnot
      have hbound :=
        posteriorBinaryKL_le_of_priorSeegerKLMoment_le
          hρ hprior hn riskFn empiricalRiskFn ω hmoment
          (hbinaryKLJensen ω ρ hρ)
      exact (not_lt.mpr (by simpa [threshold] using hbound)) hbad
    have htail_le :
        (∑ ω ∈ Finset.univ.filter badPred, ν ω) ≤
          priorSeegerKLMomentTailMass ν prior n riskFn empiricalRiskFn threshold := by
      unfold priorSeegerKLMomentTailMass
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun ω _hbig _hnot => hν.nonneg ω)
    have hmarkov :
        priorSeegerKLMomentTailMass ν prior n riskFn empiricalRiskFn threshold ≤ delta := by
      have hExpected' :
          expectedPriorSeegerKLMoment ν prior n riskFn empiricalRiskFn ≤ momentBound := by
        simpa [momentBound, hmomentBound_def] using hExpected
      simpa [threshold, hthreshold_def] using
        priorSeegerKLMoment_tailMass_le_delta_of_expected_bound
          hν hprior.toIsPMF n riskFn empiricalRiskFn hmomentBound_pos hdelta hExpected'
    exact htail_le.trans hmarkov
  have hcompl : ∀ ω, goodPred ω ↔ ¬ badPred ω := by
    intro ω
    refine ⟨?_, ?_⟩
    · rintro hgood ⟨ρ, hρ, hgt⟩
      exact (not_lt.mpr (hgood ρ hρ)) hgt
    · intro hnotbad ρ hρ
      by_contra hgt
      push Not at hgt
      exact hnotbad ⟨ρ, hρ, hgt⟩
  have hdisj :
      Disjoint (Finset.univ.filter badPred) (Finset.univ.filter goodPred) := by
    rw [Finset.disjoint_filter]
    intro ω _hω hbad hgood
    exact ((hcompl ω).mp hgood) hbad
  have hcover :
      (Finset.univ : Finset Ω) =
        Finset.univ.filter badPred ∪ Finset.univ.filter goodPred := by
    ext ω
    refine ⟨fun _ => ?_, fun _ => Finset.mem_univ ω⟩
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases h : badPred ω
    · exact Or.inl ⟨Finset.mem_univ ω, h⟩
    · exact Or.inr ⟨Finset.mem_univ ω, (hcompl ω).mpr h⟩
  have hsum_split :
      (∑ ω : Ω, ν ω) =
        (∑ ω ∈ Finset.univ.filter badPred, ν ω) +
          (∑ ω ∈ Finset.univ.filter goodPred, ν ω) := by
    have hunion :=
      Finset.sum_union (s₁ := Finset.univ.filter badPred)
        (s₂ := Finset.univ.filter goodPred) (f := ν) hdisj
    calc
      (∑ ω : Ω, ν ω) = ∑ ω ∈ (Finset.univ : Finset Ω), ν ω := rfl
      _ = ∑ ω ∈ (Finset.univ.filter badPred ∪ Finset.univ.filter goodPred), ν ω := by
            rw [← hcover]
      _ = (∑ ω ∈ Finset.univ.filter badPred, ν ω) +
            (∑ ω ∈ Finset.univ.filter goodPred, ν ω) := hunion
  have htotal : (∑ ω : Ω, ν ω) = 1 := hν.sum_one
  have hgood :
      1 - delta ≤ ∑ ω ∈ Finset.univ.filter goodPred, ν ω := by
    linarith
  simpa [goodPred, threshold, hthreshold_def, momentBound, hmomentBound_def] using hgood

/--
Finite Seeger KL-form good-event theorem with the prior moment discharged from
pointwise Bernoulli-KL moment bounds.

Compared with `pacbayes_seeger_klForm_of_priorMoment_and_binaryKLJensen`, this
removes the aggregate `expectedPriorSeegerKLMoment` hypothesis.  What remains is
the scalar per-hypothesis Bernoulli-KL moment theorem and the binary-KL Jensen
certificate.
-/
theorem pacbayes_seeger_klForm_of_bernoulliPriorMoment_and_binaryKLJensen
    [Fintype Ω] [DecidableEq Ω] [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 0 < n)
    (ν : Ω → ℝ) (hν : IsPMF ν)
    (prior : ι → ℝ) (hprior : IsFullSupportPMF prior)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (delta : ℝ) (hdelta : 0 < delta)
    (hpointwise :
      ∀ i : ι,
        (∑ ω : Ω,
          ν ω * Real.exp ((n : ℝ) * binKL (empiricalRiskFn ω i) (riskFn i))) ≤
          2 * Real.sqrt (n : ℝ))
    (hbinaryKLJensen :
      ∀ (ω : Ω) (ρ : ι → ℝ), IsPMF ρ →
        binKL (posteriorAverage ρ (empiricalRiskFn ω)) (posteriorAverage ρ riskFn) ≤
          posteriorAverage ρ
            (fun i => binKL (empiricalRiskFn ω i) (riskFn i))) :
    1 - delta ≤
      ∑ ω ∈ (Finset.univ.filter fun ω : Ω =>
        ∀ ρ : ι → ℝ, IsPMF ρ →
          binKL (posteriorAverage ρ (empiricalRiskFn ω))
              (posteriorAverage ρ riskFn) ≤
            (klDiv ρ prior + Real.log ((2 * Real.sqrt (n : ℝ)) / delta)) /
              (n : ℝ)),
        ν ω := by
  exact
    pacbayes_seeger_klForm_of_priorMoment_and_binaryKLJensen
      hn ν hν prior hprior riskFn empiricalRiskFn delta hdelta
      (expectedPriorSeegerKLMoment_bernoulli_le_two_sqrt
        hprior.toIsPMF n riskFn empiricalRiskFn hpointwise)
      hbinaryKLJensen

/-! ### Pinsker for Bernoulli KL

The lower bound `2 (p - q)^2 ≤ binKL p q` for `p ∈ [0,1]`, `q ∈ (0,1)`.  We use the
log-difference rewriting `binKLPinskerG q p` of `binKL p q`, subtract the quadratic to
form `binKLPinskerF q p`, and show this auxiliary function is nonnegative.  Its
derivative `binKLPinskerD q p` vanishes at `p = q` and is monotone in `p` on `(0,1)`
because its own derivative `1/p + 1/(1-p) - 4 = (1 - 2p)^2 / (p (1-p)) ≥ 0`.  Hence
`binKLPinskerF` decreases up to `q` and increases after `q`, with minimum value `0` at
`p = q`.  Continuity of the log-difference form on all of `ℝ` carries the bound to the
closed endpoints `p = 0` and `p = 1`. -/

/-- Log-difference form of `binKL · q`, defined by the same formula at every real `p`. -/
private noncomputable def binKLPinskerG (q p : ℝ) : ℝ :=
  p * Real.log p - p * Real.log q + ((1 - p) * Real.log (1 - p) - (1 - p) * Real.log (1 - q))

/-- The auxiliary gap `binKL p q - 2 (p - q)^2`, in log-difference form. -/
private noncomputable def binKLPinskerF (q p : ℝ) : ℝ := binKLPinskerG q p - 2 * (p - q) ^ 2

/-- The derivative of `binKLPinskerF q` on `(0,1)`. -/
private noncomputable def binKLPinskerD (q p : ℝ) : ℝ :=
  Real.log p - Real.log (1 - p) - Real.log q + Real.log (1 - q) - 4 * (p - q)

private theorem binKLPinskerG_eq_binKL (q p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1) : binKLPinskerG q p = binKL p q := by
  unfold binKLPinskerG binKL
  have hqne : q ≠ 0 := ne_of_gt hq0
  have h1qne : (1 - q) ≠ 0 := by linarith
  rcases eq_or_lt_of_le hp0 with hp0' | hp0'
  · rw [← hp0']; simp
  · rcases eq_or_lt_of_le hp1 with hp1' | hp1'
    · rw [hp1']; simp
    · rw [Real.log_div (ne_of_gt hp0') (ne_of_gt hq0),
          Real.log_div (by linarith) (by linarith)]
      ring

private theorem binKLPinsker_continuous_G (q : ℝ) : Continuous (binKLPinskerG q) := by
  unfold binKLPinskerG
  apply Continuous.add
  apply Continuous.sub
  · exact Real.continuous_mul_log
  · exact continuous_id.mul continuous_const
  apply Continuous.sub
  · exact (continuous_const.sub continuous_id).mul_log
  · exact (continuous_const.sub continuous_id).mul continuous_const

private theorem binKLPinsker_continuous_F (q : ℝ) : Continuous (binKLPinskerF q) := by
  unfold binKLPinskerF
  exact (binKLPinsker_continuous_G q).sub
    (continuous_const.mul ((continuous_id.sub continuous_const).pow 2))

private theorem binKLPinsker_hasDerivAt_G (q p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (binKLPinskerG q)
      (Real.log p - Real.log (1 - p) - Real.log q + Real.log (1 - q)) p := by
  have hpne : p ≠ 0 := ne_of_gt hp0
  have h1mne : (1 - p) ≠ 0 := by linarith
  have d1 : HasDerivAt (fun x : ℝ => x * Real.log x) (Real.log p + 1) p :=
    Real.hasDerivAt_mul_log hpne
  have d2 : HasDerivAt (fun x : ℝ => x * Real.log q) (Real.log q) p := by
    simpa using (hasDerivAt_id p).mul_const (Real.log q)
  have du : HasDerivAt (fun x : ℝ => (1 : ℝ) - x) (-1) p := by
    simpa using (hasDerivAt_id p).const_sub 1
  have d3 : HasDerivAt (fun x : ℝ => (1 - x) * Real.log (1 - x))
      (-(Real.log (1 - p) + 1)) p := by
    have := (Real.hasDerivAt_mul_log h1mne).comp p du
    have hfun :
        (fun x : ℝ => x * Real.log x) ∘ (fun x : ℝ => 1 - x) =
          fun x : ℝ => (1 - x) * Real.log (1 - x) := by
      rfl
    rw [hfun] at this
    simpa using this
  have d4 : HasDerivAt (fun x : ℝ => (1 - x) * Real.log (1 - q))
      (-(Real.log (1 - q))) p := by
    have := du.mul_const (Real.log (1 - q))
    simpa using this
  have := ((d1.sub d2).add (d3.sub d4))
  have hfun :
      ((fun x : ℝ => x * Real.log x) - (fun x : ℝ => x * Real.log q)) +
          ((fun x : ℝ => (1 - x) * Real.log (1 - x)) -
            (fun x : ℝ => (1 - x) * Real.log (1 - q))) =
        binKLPinskerG q := by
    funext x
    rfl
  have hcoeff :
      Real.log p + 1 - Real.log q +
          (-(Real.log (1 - p) + 1) - -Real.log (1 - q)) =
        Real.log p - Real.log (1 - p) - Real.log q + Real.log (1 - q) := by
    ring
  rw [hfun, hcoeff] at this
  exact this

private theorem binKLPinsker_hasDerivAt_F (q p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (binKLPinskerF q) (binKLPinskerD q p) p := by
  have hg := binKLPinsker_hasDerivAt_G q p hp0 hp1
  have hsq : HasDerivAt (fun x : ℝ => 2 * (x - q) ^ 2) (4 * (p - q)) p := by
    have h : HasDerivAt (fun x : ℝ => (x - q) ^ 2) (2 * (p - q) ^ 1 * 1) p := by
      have := (hasDerivAt_id p).sub_const q
      have hpow := this.pow 2
      have hfun : (fun x : ℝ => id x - q) ^ 2 = fun x : ℝ => (x - q) ^ 2 := by
        rfl
      rw [hfun] at hpow
      simpa using hpow
    have := h.const_mul (2 : ℝ)
    have hcoeff : 2 * (2 * (p - q) ^ 1 * 1) = 4 * (p - q) := by ring
    rw [hcoeff] at this
    exact this
  have hd := hg.sub hsq
  have heq : binKLPinskerD q p =
      (Real.log p - Real.log (1 - p) - Real.log q + Real.log (1 - q)) - 4 * (p - q) := by
    unfold binKLPinskerD; ring
  rw [heq]
  have hfun :
      binKLPinskerG q - (fun x : ℝ => 2 * (x - q) ^ 2) = binKLPinskerF q := by
    funext x
    rfl
  rw [hfun] at hd
  exact hd

private theorem binKLPinsker_hasDerivAt_D (q p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (binKLPinskerD q) (p⁻¹ + (1 - p)⁻¹ - 4) p := by
  have hpne : p ≠ 0 := ne_of_gt hp0
  have h1mne : (1 - p) ≠ 0 := by linarith
  have d1 : HasDerivAt (fun x : ℝ => Real.log x) p⁻¹ p := Real.hasDerivAt_log hpne
  have du : HasDerivAt (fun x : ℝ => (1 : ℝ) - x) (-1) p := by
    simpa using (hasDerivAt_id p).const_sub 1
  have d2 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-(1 - p)⁻¹) p := by
    have := (Real.hasDerivAt_log h1mne).comp p du
    have hfun : Real.log ∘ (fun x : ℝ => 1 - x) = fun x : ℝ => Real.log (1 - x) := by
      rfl
    rw [hfun] at this
    simpa [div_eq_mul_inv] using this
  have d3 : HasDerivAt (fun _ : ℝ => Real.log q) (0 : ℝ) p := hasDerivAt_const p _
  have d4 : HasDerivAt (fun _ : ℝ => Real.log (1 - q)) (0 : ℝ) p := hasDerivAt_const p _
  have d5 : HasDerivAt (fun x : ℝ => 4 * (x - q)) (4 : ℝ) p := by
    have := ((hasDerivAt_id p).sub_const q).const_mul (4 : ℝ)
    simpa using this
  have := (((d1.sub d2).sub d3).add d4).sub d5
  have hfun :
      ((((fun x : ℝ => Real.log x) - (fun x : ℝ => Real.log (1 - x))) -
          (fun _ : ℝ => Real.log q)) + (fun _ : ℝ => Real.log (1 - q))) -
        (fun x : ℝ => 4 * (x - q)) = binKLPinskerD q := by
    funext x
    rfl
  have hcoeff : p⁻¹ - -(1 - p)⁻¹ - 0 + 0 - 4 = p⁻¹ + (1 - p)⁻¹ - 4 := by
    ring
  rw [hfun, hcoeff] at this
  exact this

private theorem binKLPinsker_derivD_nonneg (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    0 ≤ p⁻¹ + (1 - p)⁻¹ - 4 := by
  have h1mp : (0 : ℝ) < 1 - p := by linarith
  have hprod : 0 < p * (1 - p) := mul_pos hp0 h1mp
  have key : p⁻¹ + (1 - p)⁻¹ - 4 = (1 - 2 * p) ^ 2 / (p * (1 - p)) := by
    field_simp; ring
  rw [key]; positivity

private theorem binKLPinskerD_self (q : ℝ) : binKLPinskerD q q = 0 := by
  unfold binKLPinskerD; ring

private theorem binKLPinskerF_self (q : ℝ) : binKLPinskerF q q = 0 := by
  unfold binKLPinskerF binKLPinskerG; ring

private theorem binKLPinsker_continuousOn_D (q : ℝ) :
    ContinuousOn (binKLPinskerD q) (Set.Ioo 0 1) := by
  intro p hp
  exact (binKLPinsker_hasDerivAt_D q p hp.1 hp.2).continuousAt.continuousWithinAt

private theorem binKLPinsker_differentiableOn_D (q : ℝ) :
    DifferentiableOn ℝ (binKLPinskerD q) (Set.Ioo 0 1) := by
  intro p hp
  exact (binKLPinsker_hasDerivAt_D q p hp.1 hp.2).differentiableAt.differentiableWithinAt

private theorem binKLPinsker_monotoneOn_D (q : ℝ) :
    MonotoneOn (binKLPinskerD q) (Set.Ioo 0 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 1) (binKLPinsker_continuousOn_D q)
  · rw [interior_Ioo]; exact binKLPinsker_differentiableOn_D q
  · intro p hp
    rw [interior_Ioo] at hp
    rw [(binKLPinsker_hasDerivAt_D q p hp.1 hp.2).deriv]
    exact binKLPinsker_derivD_nonneg p hp.1 hp.2

private theorem binKLPinskerD_nonneg_of_ge (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hqp : q ≤ p) : 0 ≤ binKLPinskerD q p := by
  have := binKLPinsker_monotoneOn_D q ⟨hq0, hq1⟩ hp hqp
  rwa [binKLPinskerD_self q] at this

private theorem binKLPinskerD_nonpos_of_le (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hpq : p ≤ q) : binKLPinskerD q p ≤ 0 := by
  have := binKLPinsker_monotoneOn_D q hp ⟨hq0, hq1⟩ hpq
  rwa [binKLPinskerD_self q] at this

private theorem binKLPinskerF_nonneg (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ binKLPinskerF q p := by
  have hcont : ContinuousOn (binKLPinskerF q) (Set.Icc 0 1) :=
    (binKLPinsker_continuous_F q).continuousOn
  rcases le_total q p with hqp | hpq
  · have hsub : Set.Icc q p ⊆ Set.Icc 0 1 := by
      intro x hx; exact ⟨le_of_lt (lt_of_lt_of_le hq0 hx.1), le_trans hx.2 hp1⟩
    have hint : Set.Ioo q p ⊆ Set.Ioo 0 1 := by
      intro x hx; exact ⟨lt_of_lt_of_le hq0 (le_of_lt hx.1), lt_of_lt_of_le hx.2 hp1⟩
    have hmono : MonotoneOn (binKLPinskerF q) (Set.Icc q p) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc q p) (hcont.mono hsub)
      · rw [interior_Icc]
        intro x hx
        have hxioo : x ∈ Set.Ioo (0 : ℝ) 1 := hint hx
        exact (binKLPinsker_hasDerivAt_F q x hxioo.1
          hxioo.2).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hxioo : x ∈ Set.Ioo (0 : ℝ) 1 := hint hx
        rw [(binKLPinsker_hasDerivAt_F q x hxioo.1 hxioo.2).deriv]
        exact binKLPinskerD_nonneg_of_ge q hq0 hq1 x hxioo (le_of_lt hx.1)
    have := hmono (Set.left_mem_Icc.mpr hqp) (Set.right_mem_Icc.mpr hqp) hqp
    rwa [binKLPinskerF_self q] at this
  · have hsub : Set.Icc p q ⊆ Set.Icc 0 1 := by
      intro x hx; exact ⟨le_trans hp0 hx.1, le_of_lt (lt_of_le_of_lt hx.2 hq1)⟩
    have hint : Set.Ioo p q ⊆ Set.Ioo 0 1 := by
      intro x hx; exact ⟨lt_of_le_of_lt hp0 hx.1, lt_of_lt_of_le hx.2 (le_of_lt hq1)⟩
    have hanti : AntitoneOn (binKLPinskerF q) (Set.Icc p q) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc p q) (hcont.mono hsub)
      · rw [interior_Icc]
        intro x hx
        have hxioo : x ∈ Set.Ioo (0 : ℝ) 1 := hint hx
        exact (binKLPinsker_hasDerivAt_F q x hxioo.1
          hxioo.2).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hxioo : x ∈ Set.Ioo (0 : ℝ) 1 := hint hx
        rw [(binKLPinsker_hasDerivAt_F q x hxioo.1 hxioo.2).deriv]
        exact binKLPinskerD_nonpos_of_le q hq0 hq1 x hxioo (le_of_lt hx.2)
    have := hanti (Set.left_mem_Icc.mpr hpq) (Set.right_mem_Icc.mpr hpq) hpq
    rwa [binKLPinskerF_self q] at this

/--
Pinsker's inequality for the Bernoulli relative entropy: for `p ∈ [0,1]` and
`q ∈ (0,1)`, the binary KL divergence dominates `2 (p - q)^2`.  Proved by the
tangent-line/second-derivative argument on `Real.log`, with the open-interval bound
carried to the endpoints by continuity of the log-difference form.
-/
theorem binKL_pinsker (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤ binKL p q := by
  have h := binKLPinskerF_nonneg q hq0 hq1 p hp0 hp1
  rw [show binKLPinskerF q p
        = binKLPinskerG q p - 2 * (p - q) ^ 2 from rfl,
      binKLPinskerG_eq_binKL q p hp0 hp1 hq0 hq1] at h
  linarith

/--
Pinsker converts the KL-form certificate into the usual square-root-style
posterior gap, provided the Bernoulli Pinsker inequality is supplied for the
posterior empirical/population pair.
-/
theorem pacbayes_seeger_klForm_implies_mcallester_sqrt_of_pinsker
    {empiricalRisk populationRisk complexity : ℝ}
    (hpinsker :
      2 * (populationRisk - empiricalRisk) ^ 2 ≤
        binKL empiricalRisk populationRisk)
    (hkl : binKL empiricalRisk populationRisk ≤ complexity) :
    populationRisk - empiricalRisk ≤ Real.sqrt (complexity / 2) := by
  have hsq : (populationRisk - empiricalRisk) ^ 2 ≤ complexity / 2 := by
    have htwo : 0 < (2 : ℝ) := by norm_num
    nlinarith
  exact Real.le_sqrt_of_sq_le hsq

/--
Unconditional square-root-style posterior gap: once the Bernoulli population risk
lies in `(0,1)` and the empirical risk in `[0,1]`, the KL-form bound
`binKL empiricalRisk populationRisk ≤ complexity` yields the McAllester square-root
gap.  The Pinsker hypothesis of
`pacbayes_seeger_klForm_implies_mcallester_sqrt_of_pinsker` is discharged here by
`binKL_pinsker`.
-/
theorem pacbayes_seeger_klForm_implies_mcallester_sqrt
    {empiricalRisk populationRisk complexity : ℝ}
    (hemp0 : 0 ≤ empiricalRisk) (hemp1 : empiricalRisk ≤ 1)
    (hpop0 : 0 < populationRisk) (hpop1 : populationRisk < 1)
    (hkl : binKL empiricalRisk populationRisk ≤ complexity) :
    populationRisk - empiricalRisk ≤ Real.sqrt (complexity / 2) := by
  have hpinsker :
      2 * (populationRisk - empiricalRisk) ^ 2 ≤ binKL empiricalRisk populationRisk := by
    have h := binKL_pinsker empiricalRisk populationRisk hemp0 hemp1 hpop0 hpop1
    have hsqeq : (empiricalRisk - populationRisk) ^ 2 = (populationRisk - empiricalRisk) ^ 2 := by
      ring
    rwa [hsqeq] at h
  exact pacbayes_seeger_klForm_implies_mcallester_sqrt_of_pinsker hpinsker hkl

end

end FormalSLT.PACBayesSeeger
