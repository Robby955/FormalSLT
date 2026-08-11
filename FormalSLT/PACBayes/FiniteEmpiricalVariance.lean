/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayesFiniteProductMGF
import FormalSLT.Statistics.ClassicalEstimation

/-!
# Finite empirical-variance foundations for PAC-Bayes

This module isolates the deterministic variance objects used by finite
PAC-Bayes empirical-Bernstein arguments:

* the population variance of a hypothesis loss under a finite PMF;
* the Bessel-corrected empirical variance of the observed losses;
* the exact ordered off-diagonal pairwise representation of that empirical
  variance; and
* elementary `[0, 1]` bounds; and
* unbiasedness under the explicit finite iid product sample law.

The ordered representation is the finite `U`-statistic form

`(2 n (n - 1))⁻¹ ∑ᵢ ∑_{j ≠ i} (xᵢ - xⱼ)²`.

Equivalently, it is `(n (n - 1))⁻¹` times the sum over unordered pairs.  This
module does not prove an exponential-moment inequality, a confidence event, or
a PAC-Bayes empirical-Bernstein theorem. The object is per hypothesis; it is
not the variance of a posterior-averaged loss. Substantive sample-variance
results assume `n ≥ 2`.

The normalization follows Tolstikhin and Seldin (2013),
"PAC-Bayes-Empirical-Bernstein Inequality," equation (5). The ordered-pair
identity is the equivalent second-order `U`-statistic representation used in
the empirical-Bernstein literature; see also Maurer and Pontil (2009),
"Empirical Bernstein Bounds and Sample Variance Penalization."
-/

namespace FormalSLT.PACBayes.FiniteEmpiricalVariance

open Finset BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.Statistics
open FormalSLT.Statistics.ClassicalEstimation

noncomputable section

variable {ι Z : Type*}

/-- Population variance of the loss of hypothesis `i` under a finite PMF. -/
def finitePopulationVariance [Fintype Z]
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (i : ι) : ℝ :=
  ∑ z : Z, p z * (ℓ i z - finitePopulationRisk p ℓ i) ^ (2 : Nat)

/--
Bessel-corrected empirical variance of the losses observed in `S`.

The denominator is `n - 1`; substantive theorems below assume `2 ≤ n`.
-/
def finiteEmpiricalVariance {n : ℕ}
    (ℓ : ι → Z → ℝ) (i : ι) (S : Fin n → Z) : ℝ :=
  sampleVarianceBessel (fun k => ℓ i (S k))

/-- Sum of squared differences over ordered, distinct sample-index pairs. -/
def orderedOffDiagonalSquaredDifference {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ k : Fin n, ∑ j ∈ (Finset.univ : Finset (Fin n)).erase k,
    (x k - x j) ^ (2 : Nat)

/-- Ordered-pair realization of the empirical-variance `U`-statistic. -/
def finitePairwiseEmpiricalVariance {n : ℕ}
    (ℓ : ι → Z → ℝ) (i : ι) (S : Fin n → Z) : ℝ :=
  orderedOffDiagonalSquaredDifference (fun k => ℓ i (S k)) /
    (2 * (n : ℝ) * ((n : ℝ) - 1))

/-- Population variance is nonnegative under a finite PMF. -/
theorem finitePopulationVariance_nonneg [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p) (ℓ : ι → Z → ℝ) (i : ι) :
    0 ≤ finitePopulationVariance p ℓ i := by
  unfold finitePopulationVariance
  exact Finset.sum_nonneg
    (fun z _ => mul_nonneg (hp.nonneg z) (sq_nonneg _))

/-- Population variance is the second moment minus the squared population risk. -/
theorem finitePopulationVariance_eq_secondMoment_sub_riskSq [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p) (ℓ : ι → Z → ℝ) (i : ι) :
    finitePopulationVariance p ℓ i =
      (∑ z : Z, p z * (ℓ i z) ^ (2 : Nat)) -
        (finitePopulationRisk p ℓ i) ^ (2 : Nat) := by
  let R := finitePopulationRisk p ℓ i
  have hR : (∑ z : Z, p z * ℓ i z) = R := by
    rfl
  have hconst : (∑ z : Z, p z * R ^ (2 : Nat)) = R ^ (2 : Nat) := by
    rw [← Finset.sum_mul, hp.sum_one, one_mul]
  have hlinear :
      (∑ z : Z, p z * (2 * ℓ i z * R)) = 2 * R * R := by
    calc
      (∑ z : Z, p z * (2 * ℓ i z * R)) =
          2 * R * ∑ z : Z, p z * ℓ i z := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun z _ => ?_)
            ring
      _ = 2 * R * R := by rw [hR]
  unfold finitePopulationVariance
  change
    (∑ z : Z, p z * (ℓ i z - R) ^ (2 : Nat)) =
      (∑ z : Z, p z * (ℓ i z) ^ (2 : Nat)) - R ^ (2 : Nat)
  calc
    (∑ z : Z, p z * (ℓ i z - R) ^ (2 : Nat)) =
        ∑ z : Z,
          (p z * (ℓ i z) ^ (2 : Nat) -
            p z * (2 * ℓ i z * R) + p z * R ^ (2 : Nat)) := by
          refine Finset.sum_congr rfl (fun z _ => ?_)
          ring
    _ = (∑ z : Z, p z * (ℓ i z) ^ (2 : Nat)) -
          (∑ z : Z, p z * (2 * ℓ i z * R)) +
          (∑ z : Z, p z * R ^ (2 : Nat)) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (∑ z : Z, p z * (ℓ i z) ^ (2 : Nat)) - 2 * R * R + R ^ (2 : Nat) := by
          rw [hlinear, hconst]
    _ = (∑ z : Z, p z * (ℓ i z) ^ (2 : Nat)) - R ^ (2 : Nat) := by
          ring

/-- A finite `[0,1]`-valued loss has population risk in `[0,1]`. -/
theorem finitePopulationRisk_mem_Icc_of_bounded [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p) (ℓ : ι → Z → ℝ) (i : ι)
    (hℓ : ∀ z : Z, ℓ i z ∈ Set.Icc (0 : ℝ) 1) :
    finitePopulationRisk p ℓ i ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · unfold finitePopulationRisk
    exact Finset.sum_nonneg
      (fun z _ => mul_nonneg (hp.nonneg z) (hℓ z).1)
  · unfold finitePopulationRisk
    calc
      (∑ z : Z, p z * ℓ i z) ≤ ∑ z : Z, p z * 1 := by
        exact Finset.sum_le_sum
          (fun z _ => mul_le_mul_of_nonneg_left (hℓ z).2 (hp.nonneg z))
      _ = 1 := by simp [hp.sum_one]

/-- The population variance of a finite `[0,1]`-valued loss is at most `1/4`. -/
theorem finitePopulationVariance_le_quarter [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p) (ℓ : ι → Z → ℝ) (i : ι)
    (hℓ : ∀ z : Z, ℓ i z ∈ Set.Icc (0 : ℝ) 1) :
    finitePopulationVariance p ℓ i ≤ (1 : ℝ) / 4 := by
  let R := finitePopulationRisk p ℓ i
  have hR := finitePopulationRisk_mem_Icc_of_bounded p hp ℓ i hℓ
  have hsecond :
      (∑ z : Z, p z * (ℓ i z) ^ (2 : Nat)) ≤ R := by
    change (∑ z : Z, p z * (ℓ i z) ^ (2 : Nat)) ≤
      ∑ z : Z, p z * ℓ i z
    exact Finset.sum_le_sum (fun z _ => by
      apply mul_le_mul_of_nonneg_left _ (hp.nonneg z)
      nlinarith [(mul_nonneg (hℓ z).1 (sub_nonneg.mpr (hℓ z).2))])
  rw [finitePopulationVariance_eq_secondMoment_sub_riskSq p hp ℓ i]
  calc
    (∑ z : Z, p z * (ℓ i z) ^ (2 : Nat)) - R ^ (2 : Nat)
        ≤ R - R ^ (2 : Nat) := sub_le_sub_right hsecond _
    _ ≤ (1 : ℝ) / 4 := by nlinarith [sq_nonneg (R - (1 : ℝ) / 2)]

/-- Bessel-corrected empirical variance is nonnegative for `n ≥ 2`. -/
theorem finiteEmpiricalVariance_nonneg {n : ℕ} (hn : 2 ≤ n)
    (ℓ : ι → Z → ℝ) (i : ι) (S : Fin n → Z) :
    0 ≤ finiteEmpiricalVariance ℓ i S := by
  exact sampleVarianceBessel_nonneg hn (fun k => ℓ i (S k))

/--
The ordered off-diagonal squared-difference sum is twice `n` times the centered
sum of squares.
-/
theorem orderedOffDiagonalSquaredDifference_eq_two_mul_card_mul_centeredSum
    {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    orderedOffDiagonalSquaredDifference x =
      2 * (n : ℝ) * ∑ k : Fin n, (x k - sampleMean x) ^ (2 : Nat) := by
  let d : Fin n → ℝ := fun k => x k - sampleMean x
  have hcenter : (∑ k : Fin n, d k) = 0 := by
    dsimp [d]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← sampleMean_mul_card hn x]
    ring
  have herase :
      orderedOffDiagonalSquaredDifference x =
        ∑ k : Fin n, ∑ j : Fin n, (x k - x j) ^ (2 : Nat) := by
    unfold orderedOffDiagonalSquaredDifference
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hsplit := Finset.add_sum_erase
      (Finset.univ : Finset (Fin n))
      (fun j => (x k - x j) ^ (2 : Nat)) (Finset.mem_univ k)
    rw [← hsplit]
    simp
  have hinner (k : Fin n) :
      (∑ j : Fin n, (d k - d j) ^ (2 : Nat)) =
        (n : ℝ) * (d k) ^ (2 : Nat) -
          (2 * d k) * (∑ j : Fin n, d j) +
          ∑ j : Fin n, (d j) ^ (2 : Nat) := by
    calc
      (∑ j : Fin n, (d k - d j) ^ (2 : Nat)) =
          ∑ j : Fin n,
            ((d k) ^ (2 : Nat) - (2 * d k) * d j + (d j) ^ (2 : Nat)) := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            ring
      _ = (∑ _j : Fin n, (d k) ^ (2 : Nat)) -
            (∑ j : Fin n, (2 * d k) * d j) +
            ∑ j : Fin n, (d j) ^ (2 : Nat) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (n : ℝ) * (d k) ^ (2 : Nat) -
            (2 * d k) * (∑ j : Fin n, d j) +
            ∑ j : Fin n, (d j) ^ (2 : Nat) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul, ← Finset.mul_sum]
  rw [herase]
  calc
    (∑ k : Fin n, ∑ j : Fin n, (x k - x j) ^ (2 : Nat)) =
        ∑ k : Fin n, ∑ j : Fin n, (d k - d j) ^ (2 : Nat) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          refine Finset.sum_congr rfl (fun j _ => ?_)
          dsimp [d]
          ring
    _ = ∑ k : Fin n,
          ((n : ℝ) * (d k) ^ (2 : Nat) +
            ∑ j : Fin n, (d j) ^ (2 : Nat)) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [hinner, hcenter]
          ring
    _ = 2 * (n : ℝ) * ∑ k : Fin n, (d k) ^ (2 : Nat) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
    _ = 2 * (n : ℝ) * ∑ k : Fin n, (x k - sampleMean x) ^ (2 : Nat) := by
          rfl

/--
Exact source-facing pairwise identity for the finite empirical variance.

The ordered sum counts each unordered pair twice, which accounts for the
factor `2` in the denominator.
-/
theorem finiteEmpiricalVariance_eq_pairwise {n : ℕ} (hn : 2 ≤ n)
    (ℓ : ι → Z → ℝ) (i : ι) (S : Fin n → Z) :
    finiteEmpiricalVariance ℓ i S = finitePairwiseEmpiricalVariance ℓ i S := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hpredR : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
    linarith
  unfold finiteEmpiricalVariance finitePairwiseEmpiricalVariance
  rw [orderedOffDiagonalSquaredDifference_eq_two_mul_card_mul_centeredSum hnpos]
  unfold sampleVarianceBessel
  field_simp [hnR, hpredR]

/-- Ordered pairwise numerator bound for a sample taking values in `[0,1]`. -/
theorem orderedOffDiagonalSquaredDifference_le {n : ℕ} (hn : 2 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ k, x k ∈ Set.Icc (0 : ℝ) 1) :
    orderedOffDiagonalSquaredDifference x ≤ (n : ℝ) * ((n : ℝ) - 1) := by
  have hone : 1 ≤ n := le_trans (by norm_num) hn
  have hcard (k : Fin n) :
      (∑ _j ∈ (Finset.univ : Finset (Fin n)).erase k, (1 : ℝ)) =
        (n : ℝ) - 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    simp [Finset.card_erase_of_mem (Finset.mem_univ k), Fintype.card_fin,
      Nat.cast_sub hone]
  unfold orderedOffDiagonalSquaredDifference
  calc
    (∑ k : Fin n, ∑ j ∈ (Finset.univ : Finset (Fin n)).erase k,
        (x k - x j) ^ (2 : Nat)) ≤
        ∑ k : Fin n, ∑ _j ∈ (Finset.univ : Finset (Fin n)).erase k, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          refine Finset.sum_le_sum (fun j _ => ?_)
          have hlow : -(1 : ℝ) ≤ x k - x j := by
            simpa only [zero_sub] using sub_le_sub (hx k).1 (hx j).2
          have hupp : x k - x j ≤ (1 : ℝ) := by
            simpa only [sub_zero] using sub_le_sub (hx k).2 (hx j).1
          have hsquare : (x k - x j) ^ (2 : Nat) ≤ (1 : ℝ) ^ (2 : Nat) :=
            sq_le_sq' hlow hupp
          norm_num at hsquare ⊢
          exact hsquare
    _ = ∑ _k : Fin n, ((n : ℝ) - 1) := by
          refine Finset.sum_congr rfl (fun k _ => hcard k)
    _ = (n : ℝ) * ((n : ℝ) - 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/--
For `[0,1]` losses, empirical variance is at most `n / (n - 1)` times empirical
risk. This is the deterministic comparison used in Tolstikhin--Seldin after
their equation (7).
-/
theorem finiteEmpiricalVariance_le_card_div_pred_mul_empiricalRisk
    {n : ℕ} (hn : 2 ≤ n)
    (ℓ : ι → Z → ℝ) (i : ι) (S : Fin n → Z)
    (hℓ : ∀ k : Fin n, ℓ i (S k) ∈ Set.Icc (0 : ℝ) 1) :
    finiteEmpiricalVariance ℓ i S ≤
      (n : ℝ) / ((n : ℝ) - 1) * finiteEmpiricalRisk ℓ i S := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hpredRpos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
    linarith
  let x : Fin n → ℝ := fun k => ℓ i (S k)
  have hnumerator :
      (∑ k : Fin n, (x k - 0) ^ (2 : Nat)) -
          (n : ℝ) * (sampleMean x - 0) ^ (2 : Nat) ≤
        ∑ k : Fin n, x k := by
    calc
      (∑ k : Fin n, (x k - 0) ^ (2 : Nat)) -
            (n : ℝ) * (sampleMean x - 0) ^ (2 : Nat) ≤
          ∑ k : Fin n, (x k - 0) ^ (2 : Nat) := by
            exact sub_le_self _
              (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _))
      _ ≤ ∑ k : Fin n, x k := by
            exact Finset.sum_le_sum (fun k _ => by
              dsimp [x]
              nlinarith [mul_nonneg (hℓ k).1
                (sub_nonneg.mpr (hℓ k).2)])
  change sampleVarianceBessel x ≤
    (n : ℝ) / ((n : ℝ) - 1) *
      ((n : ℝ)⁻¹ * ∑ k : Fin n, x k)
  rw [sampleVarianceBessel_eq_centered_secondMoment_sub_meanSq hnpos x 0]
  calc
    ((∑ k : Fin n, (x k - 0) ^ (2 : Nat)) -
          (n : ℝ) * (sampleMean x - 0) ^ (2 : Nat)) /
        ((n : ℝ) - 1) ≤
      (∑ k : Fin n, x k) / ((n : ℝ) - 1) := by
        exact div_le_div_of_nonneg_right hnumerator hpredRpos.le
    _ = (n : ℝ) / ((n : ℝ) - 1) *
        ((n : ℝ)⁻¹ * ∑ k : Fin n, x k) := by
          field_simp [hnR, hpredRpos.ne']

/-- A Bessel-corrected empirical variance of `[0,1]` observations is at most `1/2`. -/
theorem finiteEmpiricalVariance_le_half {n : ℕ} (hn : 2 ≤ n)
    (ℓ : ι → Z → ℝ) (i : ι) (S : Fin n → Z)
    (hℓ : ∀ k : Fin n, ℓ i (S k) ∈ Set.Icc (0 : ℝ) 1) :
    finiteEmpiricalVariance ℓ i S ≤ (1 : ℝ) / 2 := by
  have hnRpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hpredRpos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
    linarith
  have hnum := orderedOffDiagonalSquaredDifference_le hn
    (fun k => ℓ i (S k)) hℓ
  rw [finiteEmpiricalVariance_eq_pairwise hn]
  unfold finitePairwiseEmpiricalVariance
  calc
    orderedOffDiagonalSquaredDifference (fun k => ℓ i (S k)) /
          (2 * (n : ℝ) * ((n : ℝ) - 1)) ≤
        ((n : ℝ) * ((n : ℝ) - 1)) /
          (2 * (n : ℝ) * ((n : ℝ) - 1)) := by
            exact div_le_div_of_nonneg_right hnum
              (mul_nonneg (mul_nonneg (by norm_num) hnRpos.le) hpredRpos.le)
    _ = (1 : ℝ) / 2 := by
          field_simp [hnRpos.ne', hpredRpos.ne']

/-! ### Finite iid expectation identities -/

private lemma finiteProductSampleWeight_sum_eq_one {n : ℕ} [Fintype Z]
    {p : Z → ℝ} (hp : IsPMF p) :
    ∑ S : Fin n → Z, finiteProductSampleWeight p S = 1 := by
  unfold finiteProductSampleWeight
  calc
    (∑ S : Fin n → Z, ∏ k : Fin n, p (S k)) =
        ∏ _k : Fin n, ∑ z : Z, p z := by
          exact (Fintype.prod_sum (f := fun _k : Fin n => p)).symm
    _ = 1 := by simp [hp.sum_one]

private lemma finiteProductSampleWeight_update_mul {n : ℕ} [Fintype Z]
    (p : Z → ℝ) (S : Fin n → Z) (k : Fin n) (z : Z) :
    finiteProductSampleWeight p (Function.update S k z) * p (S k) =
      finiteProductSampleWeight p S * p z := by
  classical
  unfold finiteProductSampleWeight
  have h_update :
      (∏ j : Fin n, p ((Function.update S k z) j)) =
        p z * ∏ j ∈ ({k}ᶜ : Finset (Fin n)), p (S j) := by
    rw [Fintype.prod_eq_mul_prod_compl k]
    rw [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hne : j ≠ k := by simpa using hj
    rw [Function.update_of_ne hne]
  have h_original :
      (∏ j : Fin n, p (S j)) =
        p (S k) * ∏ j ∈ ({k}ᶜ : Finset (Fin n)), p (S j) := by
    rw [Fintype.prod_eq_mul_prod_compl k]
  rw [h_update, h_original]
  ring

private def finiteCoordinateSwapEquiv {n : ℕ} (k : Fin n) :
    ((Fin n → Z) × Z) ≃ ((Fin n → Z) × Z) where
  toFun P := (Function.update P.1 k P.2, P.1 k)
  invFun P := (Function.update P.1 k P.2, P.1 k)
  left_inv := by
    intro P
    rcases P with ⟨S, z⟩
    apply Prod.ext
    · funext j
      by_cases hj : j = k
      · subst j
        simp [Function.update_self]
      · simp [Function.update_of_ne hj]
    · simp [Function.update_self]
  right_inv := by
    intro P
    rcases P with ⟨S, z⟩
    apply Prod.ext
    · funext j
      by_cases hj : j = k
      · subst j
        simp [Function.update_self]
      · simp [Function.update_of_ne hj]
    · simp [Function.update_self]

private theorem finiteProductSampleWeight_coordinateSwapIdentity
    {n : ℕ} [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p) (k : Fin n)
    (G : (Fin n → Z) → Z → ℝ) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          ∑ z : Z, p z * G (Function.update S k z) z) =
      ∑ S : Fin n → Z,
        finiteProductSampleWeight p S * G S (S k) := by
  classical
  calc
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          ∑ z : Z, p z * G (Function.update S k z) z) =
      ∑ S : Fin n → Z, ∑ z : Z,
        finiteProductSampleWeight p S *
          (p z * G (Function.update S k z) z) := by
            apply Finset.sum_congr rfl
            intro S _hS
            rw [Finset.mul_sum]
    _ = ∑ P : (Fin n → Z) × Z,
        finiteProductSampleWeight p P.1 *
          (p P.2 * G (Function.update P.1 k P.2) P.2) := by
            exact (Fintype.sum_prod_type'
              (fun S : Fin n → Z => fun z : Z =>
                finiteProductSampleWeight p S *
                  (p z * G (Function.update S k z) z))).symm
    _ = ∑ P : (Fin n → Z) × Z,
        finiteProductSampleWeight p (Function.update P.1 k P.2) *
          (p (P.1 k) * G P.1 (P.1 k)) := by
            refine Fintype.sum_equiv
              (finiteCoordinateSwapEquiv (Z := Z) k) _ _ ?_
            intro P
            rcases P with ⟨S, z⟩
            simp [finiteCoordinateSwapEquiv, Function.update_self]
    _ = ∑ P : (Fin n → Z) × Z,
        finiteProductSampleWeight p P.1 * p P.2 * G P.1 (P.1 k) := by
            apply Finset.sum_congr rfl
            intro P _hP
            rw [← mul_assoc, finiteProductSampleWeight_update_mul]
    _ = ∑ S : Fin n → Z, ∑ z : Z,
        finiteProductSampleWeight p S * p z * G S (S k) := by
            exact Fintype.sum_prod_type'
              (fun S : Fin n → Z => fun z : Z =>
                finiteProductSampleWeight p S * p z * G S (S k))
    _ = ∑ S : Fin n → Z,
        finiteProductSampleWeight p S * G S (S k) := by
            apply Finset.sum_congr rfl
            intro S _hS
            calc
              (∑ z : Z,
                  finiteProductSampleWeight p S * p z * G S (S k)) =
                (finiteProductSampleWeight p S * G S (S k)) *
                  ∑ z : Z, p z := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro z _hz
                    ring
              _ = finiteProductSampleWeight p S * G S (S k) := by
                    rw [hp.sum_one, mul_one]

/-- Two distinct coordinates of a finite iid product sample have the expected
product marginal. -/
theorem finiteProductSampleWeight_pairExpectation
    {n : ℕ} [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p)
    (k j : Fin n) (hkj : k ≠ j) (g : Z → Z → ℝ) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S * g (S k) (S j)) =
      ∑ z : Z, ∑ w : Z, p z * p w * g z w := by
  classical
  have hk := finiteProductSampleWeight_coordinateSwapIdentity
    (Z := Z) p hp k (fun S z => g z (S j))
  have hj := finiteProductSampleWeight_coordinateSwapIdentity
    (Z := Z) p hp j (fun _S w => ∑ z : Z, p z * g z w)
  have hfirst :
      (∑ S : Fin n → Z,
          finiteProductSampleWeight p S * g (S k) (S j)) =
        ∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            ∑ z : Z, p z * g z (S j) := by
    rw [← hk]
    apply Finset.sum_congr rfl
    intro S _hS
    congr 1
    apply Finset.sum_congr rfl
    intro z _hz
    rw [Function.update_of_ne hkj.symm]
  have hsecond :
      (∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            ∑ z : Z, p z * g z (S j)) =
        ∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            ∑ w : Z, p w * ∑ z : Z, p z * g z w := by
    rw [← hj]
  rw [hfirst, hsecond]
  calc
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          ∑ w : Z, p w * ∑ z : Z, p z * g z w) =
      (∑ S : Fin n → Z, finiteProductSampleWeight p S) *
        (∑ w : Z, p w * ∑ z : Z, p z * g z w) := by
          rw [Finset.sum_mul]
    _ = ∑ w : Z, p w * ∑ z : Z, p z * g z w := by
          rw [finiteProductSampleWeight_sum_eq_one hp, one_mul]
    _ = ∑ z : Z, ∑ w : Z, p z * p w * g z w := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro z _hz
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _hw
          ring

/-- The expected independent-pair squared-difference kernel is the population
variance. -/
theorem finitePairVarianceKernelExpectation_eq_populationVariance
    [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p) (ℓ : ι → Z → ℝ) (i : ι) :
    (∑ z : Z, ∑ w : Z,
        p z * p w * ((ℓ i z - ℓ i w) ^ (2 : Nat) / 2)) =
      finitePopulationVariance p ℓ i := by
  let R := finitePopulationRisk p ℓ i
  let M2 := ∑ z : Z, p z * (ℓ i z) ^ (2 : Nat)
  have hR : (∑ z : Z, p z * ℓ i z) = R := rfl
  have hM2 : (∑ z : Z, p z * (ℓ i z) ^ (2 : Nat)) = M2 := rfl
  have hinner (z : Z) :
      (∑ w : Z,
          p z * p w * ((ℓ i z - ℓ i w) ^ (2 : Nat) / 2)) =
        p z / 2 * ((ℓ i z) ^ (2 : Nat) - 2 * ℓ i z * R + M2) := by
    calc
      (∑ w : Z,
          p z * p w * ((ℓ i z - ℓ i w) ^ (2 : Nat) / 2)) =
        p z / 2 *
          ∑ w : Z, p w *
            ((ℓ i z) ^ (2 : Nat) - 2 * ℓ i z * ℓ i w +
              (ℓ i w) ^ (2 : Nat)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _hw
          ring
      _ = p z / 2 *
          ((ℓ i z) ^ (2 : Nat) * (∑ w : Z, p w) -
            2 * ℓ i z * (∑ w : Z, p w * ℓ i w) +
            ∑ w : Z, p w * (ℓ i w) ^ (2 : Nat)) := by
          congr 1
          rw [Finset.mul_sum, Finset.mul_sum]
          rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro w _hw
          ring
      _ = p z / 2 *
          ((ℓ i z) ^ (2 : Nat) - 2 * ℓ i z * R + M2) := by
          rw [hp.sum_one, hR, hM2]
          ring
  rw [finitePopulationVariance_eq_secondMoment_sub_riskSq p hp ℓ i]
  change (∑ z : Z, ∑ w : Z,
      p z * p w * ((ℓ i z - ℓ i w) ^ (2 : Nat) / 2)) = M2 - R ^ 2
  simp_rw [hinner]
  calc
    (∑ z : Z, p z / 2 *
        ((ℓ i z) ^ (2 : Nat) - 2 * ℓ i z * R + M2)) =
      (1 / 2 : ℝ) * (∑ z : Z, p z * (ℓ i z) ^ (2 : Nat)) -
        R * (∑ z : Z, p z * ℓ i z) +
        (M2 / 2) * (∑ z : Z, p z) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro z _hz
        ring
    _ = M2 - R ^ 2 := by
      rw [hM2, hR, hp.sum_one]
      ring

/-- For two distinct sample coordinates, the expected squared loss difference
is twice the population variance. -/
theorem finiteProductSampleWeight_pairSquaredDifferenceExpectation_eq
    {n : ℕ} [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p) (ℓ : ι → Z → ℝ) (i : ι)
    (k j : Fin n) (hkj : k ≠ j) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          (ℓ i (S k) - ℓ i (S j)) ^ (2 : Nat)) =
      2 * finitePopulationVariance p ℓ i := by
  calc
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          (ℓ i (S k) - ℓ i (S j)) ^ (2 : Nat)) =
      ∑ z : Z, ∑ w : Z,
        p z * p w * (ℓ i z - ℓ i w) ^ (2 : Nat) := by
          exact finiteProductSampleWeight_pairExpectation p hp k j hkj
            (fun z w => (ℓ i z - ℓ i w) ^ (2 : Nat))
    _ = 2 * finitePopulationVariance p ℓ i := by
      have hkernel :=
        finitePairVarianceKernelExpectation_eq_populationVariance p hp ℓ i
      calc
        (∑ z : Z, ∑ w : Z,
            p z * p w * (ℓ i z - ℓ i w) ^ (2 : Nat)) =
          2 * (∑ z : Z, ∑ w : Z,
            p z * p w * ((ℓ i z - ℓ i w) ^ (2 : Nat) / 2)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro z _hz
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro w _hw
              ring
        _ = 2 * finitePopulationVariance p ℓ i := by rw [hkernel]

/-- The Bessel-corrected empirical loss variance is unbiased under the finite
iid product sample law. -/
theorem finiteEmpiricalVariance_unbiased_finiteProduct
    {n : ℕ} [Fintype Z]
    (hn : 2 ≤ n) (p : Z → ℝ) (hp : IsPMF p)
    (ℓ : ι → Z → ℝ) (i : ι) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S * finiteEmpiricalVariance ℓ i S) =
      finitePopulationVariance p ℓ i := by
  classical
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hpredR : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
    linarith
  have hone : 1 ≤ n := le_trans (by norm_num) hn
  simp_rw [finiteEmpiricalVariance_eq_pairwise hn]
  unfold finitePairwiseEmpiricalVariance orderedOffDiagonalSquaredDifference
  calc
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          ((∑ k : Fin n,
              ∑ j ∈ (Finset.univ : Finset (Fin n)).erase k,
                (ℓ i (S k) - ℓ i (S j)) ^ (2 : Nat)) /
            (2 * (n : ℝ) * ((n : ℝ) - 1)))) =
      (∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            (∑ k : Fin n,
              ∑ j ∈ (Finset.univ : Finset (Fin n)).erase k,
                (ℓ i (S k) - ℓ i (S j)) ^ (2 : Nat))) /
        (2 * (n : ℝ) * ((n : ℝ) - 1)) := by
          calc
            (∑ S : Fin n → Z,
                finiteProductSampleWeight p S *
                  ((∑ k : Fin n,
                      ∑ j ∈ (Finset.univ : Finset (Fin n)).erase k,
                        (ℓ i (S k) - ℓ i (S j)) ^ (2 : Nat)) /
                    (2 * (n : ℝ) * ((n : ℝ) - 1)))) =
              ∑ S : Fin n → Z,
                (finiteProductSampleWeight p S *
                  (∑ k : Fin n,
                    ∑ j ∈ (Finset.univ : Finset (Fin n)).erase k,
                      (ℓ i (S k) - ℓ i (S j)) ^ (2 : Nat))) /
                    (2 * (n : ℝ) * ((n : ℝ) - 1)) := by
                      apply Finset.sum_congr rfl
                      intro S _hS
                      ring
            _ = (∑ S : Fin n → Z,
                finiteProductSampleWeight p S *
                  (∑ k : Fin n,
                    ∑ j ∈ (Finset.univ : Finset (Fin n)).erase k,
                      (ℓ i (S k) - ℓ i (S j)) ^ (2 : Nat))) /
                    (2 * (n : ℝ) * ((n : ℝ) - 1)) := by
                      rw [Finset.sum_div]
    _ = (∑ k : Fin n,
          ∑ j ∈ (Finset.univ : Finset (Fin n)).erase k,
            ∑ S : Fin n → Z,
              finiteProductSampleWeight p S *
                (ℓ i (S k) - ℓ i (S j)) ^ (2 : Nat)) /
        (2 * (n : ℝ) * ((n : ℝ) - 1)) := by
          congr 1
          calc
            (∑ S : Fin n → Z,
                finiteProductSampleWeight p S *
                  (∑ k : Fin n,
                    ∑ j ∈ (Finset.univ : Finset (Fin n)).erase k,
                      (ℓ i (S k) - ℓ i (S j)) ^ (2 : Nat))) =
              ∑ S : Fin n → Z, ∑ k : Fin n,
                ∑ j ∈ (Finset.univ : Finset (Fin n)).erase k,
                  finiteProductSampleWeight p S *
                    (ℓ i (S k) - ℓ i (S j)) ^ (2 : Nat) := by
                      apply Finset.sum_congr rfl
                      intro S _hS
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro k _hk
                      rw [Finset.mul_sum]
            _ = ∑ k : Fin n,
                ∑ j ∈ (Finset.univ : Finset (Fin n)).erase k,
                  ∑ S : Fin n → Z,
                    finiteProductSampleWeight p S *
                      (ℓ i (S k) - ℓ i (S j)) ^ (2 : Nat) := by
                        rw [Finset.sum_comm]
                        apply Finset.sum_congr rfl
                        intro k _hk
                        rw [Finset.sum_comm]
    _ = (∑ k : Fin n,
          ∑ _j ∈ (Finset.univ : Finset (Fin n)).erase k,
            2 * finitePopulationVariance p ℓ i) /
        (2 * (n : ℝ) * ((n : ℝ) - 1)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro k _hk
          apply Finset.sum_congr rfl
          intro j hj
          have hjk : j ≠ k := by
            intro h
            subst j
            simp at hj
          exact finiteProductSampleWeight_pairSquaredDifferenceExpectation_eq
            p hp ℓ i k j hjk.symm
    _ = finitePopulationVariance p ℓ i := by
          simp [Finset.card_erase_of_mem (Finset.mem_univ _),
            Fintype.card_fin, Nat.cast_sub hone]
          field_simp [hnR, hpredR]

end

end FormalSLT.PACBayes.FiniteEmpiricalVariance
