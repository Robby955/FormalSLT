/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayesKL
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite product MGF bridge for PAC-Bayes

This module is a finite, scalar-valued exponential-moment layer for the
PAC-Bayes path. It does not prove McAllester or Catoni yet. It proves the
finite iid product-measure algebra those bounds need:

* finite empirical risk and finite population risk;
* exact factorization of the empirical-risk-deviation MGF under finite iid
  product sample weights;
* a prior-averaged MGF bound from per-hypothesis one-coordinate MGF bounds.

The scope is finite throughout: finite data domain, finite hypothesis class,
finite samples, real-valued losses, and finite sums.
-/

namespace FormalSLT.PACBayesFiniteProductMGF

open Finset Real BigOperators
open FormalSLT.PACBayesKL

noncomputable section

variable {ι Z : Type*}

/-! ### Finite risks and iid sample weights -/

/-- Finite population risk under a finite data mass function. -/
def finitePopulationRisk [Fintype Z]
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (i : ι) : ℝ :=
  ∑ z : Z, p z * ℓ i z

/-- Finite empirical risk on a sample `S : Fin n → Z`. -/
def finiteEmpiricalRisk {n : ℕ}
    (ℓ : ι → Z → ℝ) (i : ι) (S : Fin n → Z) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k : Fin n, ℓ i (S k)

/-- Finite iid product sample weight induced by a finite data mass function. -/
def finiteProductSampleWeight {n : ℕ} [Fintype Z]
    (p : Z → ℝ) (S : Fin n → Z) : ℝ :=
  ∏ k : Fin n, p (S k)

/-! ### One-hypothesis product MGF factorization -/

private lemma exp_empiricalRiskDeviation_eq_prod {n : ℕ} [Fintype Z]
    (hn : 0 < n) (p : Z → ℝ) (ℓ : ι → Z → ℝ) (i : ι) (lam : ℝ)
    (S : Fin n → Z) :
    Real.exp (lam * (finitePopulationRisk p ℓ i - finiteEmpiricalRisk ℓ i S)) =
      ∏ k : Fin n,
        Real.exp ((lam * (n : ℝ)⁻¹) * (finitePopulationRisk p ℓ i - ℓ i (S k))) := by
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [← Real.exp_sum]
  congr 1
  unfold finiteEmpiricalRisk
  calc
    lam * (finitePopulationRisk p ℓ i - (n : ℝ)⁻¹ * ∑ k : Fin n, ℓ i (S k))
        =
      (lam * (n : ℝ)⁻¹) *
        ((n : ℝ) * finitePopulationRisk p ℓ i - ∑ k : Fin n, ℓ i (S k)) := by
        field_simp [hn_ne]
    _ =
      (lam * (n : ℝ)⁻¹) *
        ((∑ k : Fin n, finitePopulationRisk p ℓ i) - ∑ k : Fin n, ℓ i (S k)) := by
        simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
    _ =
      (lam * (n : ℝ)⁻¹) *
        (∑ k : Fin n, (finitePopulationRisk p ℓ i - ℓ i (S k))) := by
        rw [Finset.sum_sub_distrib]
    _ =
      ∑ k : Fin n,
        (lam * (n : ℝ)⁻¹) * (finitePopulationRisk p ℓ i - ℓ i (S k)) := by
        rw [Finset.mul_sum]

/--
Exact finite iid product factorization for the empirical-risk-deviation MGF.

For a fixed hypothesis `i`, the finite sample expectation of
`exp(lam * (R_i - Rhat_i(S)))` under product weights factors as the `n`th power
of the one-coordinate exponential moment. This is the finite algebraic bridge
needed before adding bounded-loss Hoeffding, Markov, and PAC-Bayes confidence
steps.
-/
theorem finiteProduct_mgf_empiricalRiskDeviation_eq_pow
    {n : ℕ} [Fintype Z] (hn : 0 < n)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (i : ι) (lam : ℝ) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp (lam * (finitePopulationRisk p ℓ i - finiteEmpiricalRisk ℓ i S))) =
      (∑ z : Z,
        p z * Real.exp ((lam * (n : ℝ)⁻¹) * (finitePopulationRisk p ℓ i - ℓ i z))) ^ n := by
  classical
  have hcombine : ∀ S : Fin n → Z,
      finiteProductSampleWeight p S *
          Real.exp (lam * (finitePopulationRisk p ℓ i - finiteEmpiricalRisk ℓ i S)) =
        ∏ k : Fin n,
          p (S k) *
            Real.exp ((lam * (n : ℝ)⁻¹) * (finitePopulationRisk p ℓ i - ℓ i (S k))) := by
    intro S
    unfold finiteProductSampleWeight
    rw [exp_empiricalRiskDeviation_eq_prod hn p ℓ i lam S]
    rw [← Finset.prod_mul_distrib]
  simp_rw [hcombine]
  rw [← Fintype.prod_sum
    (f := fun _k : Fin n => fun z : Z =>
      p z * Real.exp ((lam * (n : ℝ)⁻¹) * (finitePopulationRisk p ℓ i - ℓ i z)))]
  simp [Finset.prod_const, Fintype.card_fin]

/-! ### MGF upper bounds from one-coordinate assumptions -/

/-- The one-coordinate MGF that appears in the finite product factorization. -/
def oneCoordinateDeviationMGF [Fintype Z]
    {n : ℕ} (p : Z → ℝ) (ℓ : ι → Z → ℝ) (i : ι) (lam : ℝ) : ℝ :=
  ∑ z : Z,
    p z * Real.exp ((lam * (n : ℝ)⁻¹) * (finitePopulationRisk p ℓ i - ℓ i z))

/--
Finite product MGF bound from a one-coordinate MGF bound.

If each one-coordinate deviation MGF for hypothesis `i` is bounded by
`exp(λ² * variance / (2n²))`, then the full sample-average deviation MGF is
bounded by `exp(λ² * variance / (2n))`.
-/
theorem finiteProduct_mgf_empiricalRiskDeviation_le_of_single
    {n : ℕ} [Fintype Z] (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (ℓ : ι → Z → ℝ) (i : ι) (lam variance : ℝ)
    (hsingle :
      oneCoordinateDeviationMGF (n := n) p ℓ i lam ≤
        Real.exp (lam ^ 2 * variance / (2 * (n : ℝ) ^ 2))) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp (lam * (finitePopulationRisk p ℓ i - finiteEmpiricalRisk ℓ i S))) ≤
      Real.exp (lam ^ 2 * variance / (2 * (n : ℝ))) := by
  classical
  have h_eq :=
    finiteProduct_mgf_empiricalRiskDeviation_eq_pow
      (ι := ι) (Z := Z) hn p ℓ i lam
  rw [h_eq]
  have hsingle_nonneg : 0 ≤ oneCoordinateDeviationMGF (n := n) p ℓ i lam := by
    unfold oneCoordinateDeviationMGF
    exact Finset.sum_nonneg
      (fun z _hz => mul_nonneg (hp.nonneg z) (le_of_lt (Real.exp_pos _)))
  have h_pow :
      (oneCoordinateDeviationMGF (n := n) p ℓ i lam) ^ n ≤
        (Real.exp (lam ^ 2 * variance / (2 * (n : ℝ) ^ 2))) ^ n :=
    pow_le_pow_left₀ hsingle_nonneg hsingle n
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have h_exp_pow :
      (Real.exp (lam ^ 2 * variance / (2 * (n : ℝ) ^ 2))) ^ n =
        Real.exp (lam ^ 2 * variance / (2 * (n : ℝ))) := by
    rw [← Real.exp_nat_mul]
    field_simp [hn_ne]
  exact h_pow.trans_eq h_exp_pow

/--
Finite product MGF bound from an arbitrary one-coordinate exponential budget.

This is the same product-factorization step as
`finiteProduct_mgf_empiricalRiskDeviation_le_of_single`, but keeps the
one-coordinate budget explicit. It is useful for Bernstein/sub-Gamma bounds,
whose denominator depends on the one-coordinate scale.
-/
theorem finiteProduct_mgf_empiricalRiskDeviation_le_exp_of_single
    {n : ℕ} [Fintype Z] (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (ℓ : ι → Z → ℝ) (i : ι) (lam singleBudget : ℝ)
    (hsingle :
      oneCoordinateDeviationMGF (n := n) p ℓ i lam ≤
        Real.exp singleBudget) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp (lam * (finitePopulationRisk p ℓ i - finiteEmpiricalRisk ℓ i S))) ≤
      Real.exp ((n : ℝ) * singleBudget) := by
  classical
  have h_eq :=
    finiteProduct_mgf_empiricalRiskDeviation_eq_pow
      (ι := ι) (Z := Z) hn p ℓ i lam
  rw [h_eq]
  have hsingle_nonneg : 0 ≤ oneCoordinateDeviationMGF (n := n) p ℓ i lam := by
    unfold oneCoordinateDeviationMGF
    exact Finset.sum_nonneg
      (fun z _hz => mul_nonneg (hp.nonneg z) (le_of_lt (Real.exp_pos _)))
  have h_pow :
      (oneCoordinateDeviationMGF (n := n) p ℓ i lam) ^ n ≤
        (Real.exp singleBudget) ^ n :=
    pow_le_pow_left₀ hsingle_nonneg hsingle n
  have h_exp_pow :
      (Real.exp singleBudget) ^ n = Real.exp ((n : ℝ) * singleBudget) := by
    rw [← Real.exp_nat_mul]
  exact h_pow.trans_eq h_exp_pow

/--
Prior-averaged finite product MGF bound.

This is the PAC-Bayes-facing form: averaging the exponential deviation over a
finite prior `π` and then over finite iid samples is bounded by the same
single-hypothesis exponential budget, assuming the one-coordinate MGF bound
holds for every hypothesis.
-/
theorem finitePriorAveraged_mgf_empiricalRiskDeviation_le
    {n : ℕ} [Fintype Z] [Fintype ι] (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (π : ι → ℝ) (hπ : IsPMF π)
    (ℓ : ι → Z → ℝ) (lam variance : ℝ)
    (hsingle :
      ∀ i : ι,
        oneCoordinateDeviationMGF (n := n) p ℓ i lam ≤
          Real.exp (lam ^ 2 * variance / (2 * (n : ℝ) ^ 2))) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          ∑ i : ι,
            π i *
              Real.exp (lam * (finitePopulationRisk p ℓ i - finiteEmpiricalRisk ℓ i S))) ≤
      Real.exp (lam ^ 2 * variance / (2 * (n : ℝ))) := by
  classical
  have hswap :
      (∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            ∑ i : ι,
              π i *
                Real.exp (lam * (finitePopulationRisk p ℓ i - finiteEmpiricalRisk ℓ i S))) =
        ∑ i : ι,
          π i *
            ∑ S : Fin n → Z,
              finiteProductSampleWeight p S *
                Real.exp (lam * (finitePopulationRisk p ℓ i - finiteEmpiricalRisk ℓ i S)) := by
    calc
      (∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            ∑ i : ι,
              π i *
                Real.exp (lam * (finitePopulationRisk p ℓ i - finiteEmpiricalRisk ℓ i S)))
          =
        ∑ S : Fin n → Z, ∑ i : ι,
          finiteProductSampleWeight p S *
            (π i *
              Real.exp (lam * (finitePopulationRisk p ℓ i - finiteEmpiricalRisk ℓ i S))) := by
            apply Finset.sum_congr rfl
            intro S _hS
            rw [Finset.mul_sum]
      _ =
        ∑ i : ι, ∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            (π i *
              Real.exp (lam * (finitePopulationRisk p ℓ i - finiteEmpiricalRisk ℓ i S))) := by
            rw [Finset.sum_comm]
      _ =
        ∑ i : ι,
          π i *
            ∑ S : Fin n → Z,
              finiteProductSampleWeight p S *
                Real.exp (lam * (finitePopulationRisk p ℓ i - finiteEmpiricalRisk ℓ i S)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro S _hS
            ring
  rw [hswap]
  calc
    (∑ i : ι,
        π i *
          ∑ S : Fin n → Z,
            finiteProductSampleWeight p S *
              Real.exp (lam * (finitePopulationRisk p ℓ i - finiteEmpiricalRisk ℓ i S)))
        ≤
      ∑ i : ι, π i * Real.exp (lam ^ 2 * variance / (2 * (n : ℝ))) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact mul_le_mul_of_nonneg_left
          (finiteProduct_mgf_empiricalRiskDeviation_le_of_single
            (ι := ι) (Z := Z) hn p hp ℓ i lam variance (hsingle i))
          (hπ.nonneg i)
    _ = Real.exp (lam ^ 2 * variance / (2 * (n : ℝ))) := by
        rw [← Finset.sum_mul]
        rw [hπ.sum_one, one_mul]

end

end FormalSLT.PACBayesFiniteProductMGF
