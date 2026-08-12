/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteEmpiricalVarianceMatching
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Finite empirical-variance exponential moments

This module proves a finite, source-normalized lower-tail MGF inequality for the
Bessel-corrected empirical variance of a bounded loss. The proof uses a sharp
single-pair chord bound, exact factorization over disjoint random-matching
blocks, and finite Jensen over all coordinate permutations.

For every sample size `n ≥ 2`, the final theorem matches the coefficient in
Tolstikhin and Seldin (2013), equation (9):

`E exp(eta * n * (V - Vhat)) ≤ exp(eta^2 * n^2 * V / (2 * (n - 1)))`.

The intermediate matching theorem is sharper when `n` is even. These are
fixed-hypothesis finite-product moment bounds; no PAC-Bayes change of measure or
posterior-uniform confidence statement is claimed here.
-/

namespace FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF

open Finset BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVarianceMatching
open FormalSLT.Statistics.ClassicalEstimation

noncomputable section

variable {ι Z : Type*}

/-- For `[0,1]`-valued losses, the pair-variance kernel lies in `[0,1/2]`. -/
lemma pairVarianceKernel_mem_Icc
    (ℓ : ι → Z → ℝ) (i : ι)
    (hℓ : ∀ z : Z, ℓ i z ∈ Set.Icc (0 : ℝ) 1)
    (z w : Z) :
    pairVarianceKernel ℓ i z w ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ) := by
  unfold pairVarianceKernel
  constructor
  · positivity
  · have hlo : -(1 : ℝ) ≤ ℓ i z - ℓ i w := by
      simpa only [zero_sub] using sub_le_sub (hℓ z).1 (hℓ w).2
    have hhi : ℓ i z - ℓ i w ≤ (1 : ℝ) := by
      simpa only [sub_zero] using sub_le_sub (hℓ z).2 (hℓ w).1
    have hsquare : (ℓ i z - ℓ i w) ^ (2 : Nat) ≤ (1 : ℝ) := by
      nlinarith
    nlinarith

private lemma exp_neg_mul_le_half_chord {t y : ℝ}
    (hy : y ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ)) :
    Real.exp (-t * y) ≤
      (1 - 2 * y) + (2 * y) * Real.exp (-t / 2) := by
  calc
    Real.exp (-t * y) =
        Real.exp ((1 - 2 * y) * 0 + (2 * y) * (-t / 2)) := by ring_nf
    _ ≤ (1 - 2 * y) * Real.exp 0 +
        (2 * y) * Real.exp (-t / 2) :=
      convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _)
        (by linarith [hy.2]) (by linarith [hy.1]) (by ring)
    _ = (1 - 2 * y) + (2 * y) * Real.exp (-t / 2) := by simp

private lemma two_exp_neg_half_add_le_sq_div_four {t : ℝ} (ht : 0 ≤ t) :
    2 * Real.exp (-t / 2) + t - 2 ≤ t ^ (2 : Nat) / 4 := by
  have h := FormalSLT.Probability.BernsteinMGF.exp_le_one_add_add_sq_of_nonpos
    (show -t / 2 ≤ 0 by linarith)
  nlinarith [sq_nonneg t]

/-- Sharp single-pair lower-tail MGF.  The kernel range is `[0,1/2]`, which
improves the quadratic coefficient from `1/2` to `1/4`. -/
theorem pairVarianceKernel_lowerTailMGF
    [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p)
    (ℓ : ι → Z → ℝ) (i : ι)
    (hℓ : ∀ z : Z, ℓ i z ∈ Set.Icc (0 : ℝ) 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ z : Z, ∑ w : Z,
        p z * p w *
          Real.exp
            (t *
              (finitePopulationVariance p ℓ i - pairVarianceKernel ℓ i z w))) ≤
      Real.exp (t ^ (2 : Nat) * finitePopulationVariance p ℓ i / 4) := by
  let V := finitePopulationVariance p ℓ i
  have hVnonneg : 0 ≤ V := finitePopulationVariance_nonneg p hp ℓ i
  have hkernel :
      (∑ z : Z, ∑ w : Z, p z * p w * pairVarianceKernel ℓ i z w) = V := by
    exact finitePairVarianceKernelExpectation_eq_populationVariance p hp ℓ i
  have hweight : (∑ z : Z, ∑ w : Z, p z * p w) = 1 := by
    calc
      (∑ z : Z, ∑ w : Z, p z * p w) =
          ∑ z : Z, p z * (∑ w : Z, p w) := by
            apply Finset.sum_congr rfl
            intro z _
            rw [Finset.mul_sum]
      _ = 1 := by simp [hp.sum_one]
  have hchord :
      (∑ z : Z, ∑ w : Z,
          p z * p w * Real.exp (-t * pairVarianceKernel ℓ i z w)) ≤
        1 - 2 * V + 2 * V * Real.exp (-t / 2) := by
    calc
      (∑ z : Z, ∑ w : Z,
          p z * p w * Real.exp (-t * pairVarianceKernel ℓ i z w)) ≤
          ∑ z : Z, ∑ w : Z,
            p z * p w *
              ((1 - 2 * pairVarianceKernel ℓ i z w) +
                (2 * pairVarianceKernel ℓ i z w) * Real.exp (-t / 2)) := by
            exact Finset.sum_le_sum (fun z _ =>
              Finset.sum_le_sum (fun w _ =>
                mul_le_mul_of_nonneg_left
                  (exp_neg_mul_le_half_chord
                    (pairVarianceKernel_mem_Icc ℓ i hℓ z w))
                  (mul_nonneg (hp.nonneg z) (hp.nonneg w))))
      _ = 1 - 2 * V + 2 * V * Real.exp (-t / 2) := by
        calc
          (∑ z : Z, ∑ w : Z,
              p z * p w *
                ((1 - 2 * pairVarianceKernel ℓ i z w) +
                  (2 * pairVarianceKernel ℓ i z w) * Real.exp (-t / 2))) =
              (∑ z : Z, ∑ w : Z, p z * p w) -
                (∑ z : Z, ∑ w : Z,
                  p z * p w * pairVarianceKernel ℓ i z w) * 2 +
                (∑ z : Z, ∑ w : Z,
                  p z * p w * pairVarianceKernel ℓ i z w) *
                    (2 * Real.exp (-t / 2)) := by
                    rw [Finset.sum_mul, Finset.sum_mul]
                    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
                    apply Finset.sum_congr rfl
                    intro z _
                    rw [Finset.sum_mul, Finset.sum_mul]
                    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
                    apply Finset.sum_congr rfl
                    intro w _
                    ring
          _ = 1 - 2 * V + 2 * V * Real.exp (-t / 2) := by
            rw [hweight, hkernel]
            ring
  have hlinear_exp :
      1 - 2 * V + 2 * V * Real.exp (-t / 2) ≤
        Real.exp (2 * V * (Real.exp (-t / 2) - 1)) := by
    have h := Real.add_one_le_exp (2 * V * (Real.exp (-t / 2) - 1))
    convert h using 1
    ring
  have hpsi := two_exp_neg_half_add_le_sq_div_four ht
  calc
    (∑ z : Z, ∑ w : Z,
        p z * p w *
          Real.exp (t * (finitePopulationVariance p ℓ i -
            pairVarianceKernel ℓ i z w))) =
        Real.exp (t * V) *
          (∑ z : Z, ∑ w : Z,
            p z * p w * Real.exp (-t * pairVarianceKernel ℓ i z w)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro z _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro w _
              have hexp :
                  Real.exp (t * (finitePopulationVariance p ℓ i -
                    pairVarianceKernel ℓ i z w)) =
                    Real.exp (t * V) *
                      Real.exp (-t * pairVarianceKernel ℓ i z w) := by
                rw [← Real.exp_add]
                dsimp [V]
                congr 1
                ring
              rw [hexp]
              ring
    _ ≤ Real.exp (t * V) *
        (1 - 2 * V + 2 * V * Real.exp (-t / 2)) :=
      mul_le_mul_of_nonneg_left hchord (Real.exp_pos _).le
    _ ≤ Real.exp (t * V) *
        Real.exp (2 * V * (Real.exp (-t / 2) - 1)) :=
      mul_le_mul_of_nonneg_left hlinear_exp (Real.exp_pos _).le
    _ = Real.exp (V * (2 * Real.exp (-t / 2) + t - 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (V * (t ^ (2 : Nat) / 4)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hpsi hVnonneg
    _ = Real.exp (t ^ (2 : Nat) * V / 4) := by
      congr 1
      ring

/-- Sharp lower-tail MGF for the mean of `m` independent pair kernels. -/
theorem finitePairBlocks_lowerTailMGF
    [Fintype Z] [DecidableEq Z]
    {m : ℕ} (hm : 0 < m)
    (p : Z → ℝ) (hp : IsPMF p)
    (ℓ : ι → Z → ℝ) (i : ι)
    (hℓ : ∀ z : Z, ℓ i z ∈ Set.Icc (0 : ℝ) 1)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    (∑ S : Fin m → (Fin 2 → Z),
        ∏ r : Fin m,
          finiteProductSampleWeight p (S r) *
            Real.exp
              ((lam / (m : ℝ)) *
                (finitePopulationVariance p ℓ i -
                  pairVarianceKernel ℓ i (S r 0) (S r 1)))) ≤
      Real.exp
        (lam ^ (2 : Nat) * finitePopulationVariance p ℓ i /
          (4 * (m : ℝ))) := by
  let t : ℝ := lam / (m : ℝ)
  let V : ℝ := finitePopulationVariance p ℓ i
  have hmRpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmR : (m : ℝ) ≠ 0 := ne_of_gt hmRpos
  have ht : 0 ≤ t := div_nonneg hlam hmRpos.le
  rw [finitePairBlock_factorization p hp
    (fun _r z w => Real.exp (t * (V - pairVarianceKernel ℓ i z w)))]
  calc
    (∏ _r : Fin m, ∑ z : Z, ∑ w : Z,
        p z * p w * Real.exp (t * (V - pairVarianceKernel ℓ i z w))) ≤
      ∏ _r : Fin m,
        Real.exp (t ^ (2 : Nat) * V / 4) := by
          apply Finset.prod_le_prod
          · intro r _hr
            exact Finset.sum_nonneg (fun z _hz =>
              Finset.sum_nonneg (fun w _hw =>
                mul_nonneg (mul_nonneg (hp.nonneg z) (hp.nonneg w))
                  (Real.exp_pos _).le))
          · intro r _hr
            exact pairVarianceKernel_lowerTailMGF
              p hp ℓ i hℓ ht
    _ = Real.exp
        (lam ^ (2 : Nat) * finitePopulationVariance p ℓ i /
          (4 * (m : ℝ))) := by
      rw [← Real.exp_sum]
      congr 1
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      dsimp only [t, V]
      field_simp [hmR]

/-- Natural centered-MGF form of the independent-pair result. -/
theorem finitePairBlockMean_lowerTailMGF
    [Fintype Z] [DecidableEq Z]
    {m : ℕ} (hm : 0 < m)
    (p : Z → ℝ) (hp : IsPMF p)
    (ℓ : ι → Z → ℝ) (i : ι)
    (hℓ : ∀ z : Z, ℓ i z ∈ Set.Icc (0 : ℝ) 1)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    (∑ S : Fin m → (Fin 2 → Z),
        finitePairBlockSampleWeight p S *
          Real.exp
            (lam *
              (finitePopulationVariance p ℓ i -
                finitePairBlockMean ℓ i S))) ≤
      Real.exp
        (lam ^ (2 : Nat) * finitePopulationVariance p ℓ i /
          (4 * (m : ℝ))) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpoint (S : Fin m → (Fin 2 → Z)) :
      finitePairBlockSampleWeight p S *
          Real.exp
            (lam *
              (finitePopulationVariance p ℓ i -
                finitePairBlockMean ℓ i S)) =
        ∏ r : Fin m,
          finiteProductSampleWeight p (S r) *
            Real.exp
              ((lam / (m : ℝ)) *
                (finitePopulationVariance p ℓ i -
                  pairVarianceKernel ℓ i (S r 0) (S r 1))) := by
    have hexponent :
        (∑ r : Fin m,
            (lam / (m : ℝ)) *
              (finitePopulationVariance p ℓ i -
                pairVarianceKernel ℓ i (S r 0) (S r 1))) =
          lam *
            (finitePopulationVariance p ℓ i -
              finitePairBlockMean ℓ i S) := by
      unfold finitePairBlockMean
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hmR]
    unfold finitePairBlockSampleWeight
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, hexponent]
  calc
    (∑ S : Fin m → (Fin 2 → Z),
        finitePairBlockSampleWeight p S *
          Real.exp
            (lam *
              (finitePopulationVariance p ℓ i -
                finitePairBlockMean ℓ i S))) =
      ∑ S : Fin m → (Fin 2 → Z),
        ∏ r : Fin m,
          finiteProductSampleWeight p (S r) *
            Real.exp
              ((lam / (m : ℝ)) *
                (finitePopulationVariance p ℓ i -
                  pairVarianceKernel ℓ i (S r 0) (S r 1))) := by
        apply Finset.sum_congr rfl
        intro S _hS
        exact hpoint S
    _ ≤ Real.exp
        (lam ^ (2 : Nat) * finitePopulationVariance p ℓ i /
          (4 * (m : ℝ))) :=
      finitePairBlocks_lowerTailMGF hm p hp ℓ i hℓ hlam

/-- Unused iid coordinates integrate out exactly.  This is the odd-sample
bridge: instantiate `r = 1`. -/
theorem finitePairBlockMean_withRemainder_lowerTailMGF
    [Fintype Z] [DecidableEq Z]
    {m r : ℕ} (hm : 0 < m)
    (p : Z → ℝ) (hp : IsPMF p)
    (ℓ : ι → Z → ℝ) (i : ι)
    (hℓ : ∀ z : Z, ℓ i z ∈ Set.Icc (0 : ℝ) 1)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    (∑ S : Fin m → (Fin 2 → Z), ∑ U : Fin r → Z,
        finitePairBlockSampleWeight p S *
          finiteProductSampleWeight p U *
          Real.exp
            (lam *
              (finitePopulationVariance p ℓ i -
                finitePairBlockMean ℓ i S))) ≤
      Real.exp
        (lam ^ (2 : Nat) * finitePopulationVariance p ℓ i /
          (4 * (m : ℝ))) := by
  have hrest :
      (∑ U : Fin r → Z, finiteProductSampleWeight p U) = 1 := by
    unfold finiteProductSampleWeight
    calc
      (∑ U : Fin r → Z, ∏ k : Fin r, p (U k)) =
          ∏ _k : Fin r, ∑ z : Z, p z := by
            exact (Fintype.prod_sum (f := fun _k : Fin r => p)).symm
      _ = 1 := by simp [hp.sum_one]
  calc
    (∑ S : Fin m → (Fin 2 → Z), ∑ U : Fin r → Z,
        finitePairBlockSampleWeight p S *
          finiteProductSampleWeight p U *
          Real.exp
            (lam *
              (finitePopulationVariance p ℓ i -
                finitePairBlockMean ℓ i S))) =
      ∑ S : Fin m → (Fin 2 → Z),
        (finitePairBlockSampleWeight p S *
          Real.exp
            (lam *
              (finitePopulationVariance p ℓ i -
                finitePairBlockMean ℓ i S))) *
          (∑ U : Fin r → Z, finiteProductSampleWeight p U) := by
            apply Finset.sum_congr rfl
            intro S _hS
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro U _hU
            ring
    _ = ∑ S : Fin m → (Fin 2 → Z),
        finitePairBlockSampleWeight p S *
          Real.exp
            (lam *
              (finitePopulationVariance p ℓ i -
                finitePairBlockMean ℓ i S)) := by
      rw [hrest]
      simp
    _ ≤ Real.exp
        (lam ^ (2 : Nat) * finitePopulationVariance p ℓ i /
          (4 * (m : ℝ))) :=
      finitePairBlockMean_lowerTailMGF hm p hp ℓ i hℓ hlam

/-- The sharp pair-block MGF transported back to an ordinary `Fin`-indexed
iid sample, allowing `r` unused coordinates. -/
theorem finiteCanonicalPairMean_lowerTailMGF
    [Fintype Z] [DecidableEq Z]
    {m r : ℕ} (hm : 0 < m)
    (p : Z → ℝ) (hp : IsPMF p)
    (ℓ : ι → Z → ℝ) (i : ι)
    (hℓ : ∀ z : Z, ℓ i z ∈ Set.Icc (0 : ℝ) 1)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    (∑ T : Fin (m * 2 + r) → Z,
        finiteProductSampleWeight p T *
          Real.exp
            (lam *
              (finitePopulationVariance p ℓ i -
                finiteCanonicalPairMean ℓ i T))) ≤
      Real.exp
        (lam ^ (2 : Nat) * finitePopulationVariance p ℓ i /
          (4 * (m : ℝ))) := by
  let e := finSamplePairRemainderEquiv m r Z
  have hreindex :
      (∑ T : Fin (m * 2 + r) → Z,
          finiteProductSampleWeight p T *
            Real.exp
              (lam *
                (finitePopulationVariance p ℓ i -
                  finiteCanonicalPairMean ℓ i T))) =
        ∑ SU : (Fin m → Fin 2 → Z) × (Fin r → Z),
          finitePairBlockSampleWeight p SU.1 *
            finiteProductSampleWeight p SU.2 *
            Real.exp
              (lam *
                (finitePopulationVariance p ℓ i -
                  finitePairBlockMean ℓ i SU.1)) := by
    apply Fintype.sum_equiv e
    intro T
    rw [finiteProductSampleWeight_eq_pairRemainder]
    rfl
  rw [hreindex, Fintype.sum_prod_type]
  exact finitePairBlockMean_withRemainder_lowerTailMGF
    hm p hp ℓ i hℓ hlam

/-- Finite Jensen bounds the exponential centered at the sample variance by
the uniform average over permuted canonical matchings. -/
theorem exp_population_sub_sampleVariance_le_permAverage
    {m r : ℕ} (hm : 0 < m)
    (ℓ : ι → Z → ℝ) (i : ι) (T : Fin (m * 2 + r) → Z)
    (V lam : ℝ) :
    Real.exp
        (lam * (V - sampleVarianceBessel (fun k => ℓ i (T k)))) ≤
      (∑ σ : Equiv.Perm (Fin (m * 2 + r)),
          Real.exp
            (lam *
              (V - finiteCanonicalPairMean ℓ i (fun k => T (σ k))))) /
        (Fintype.card (Equiv.Perm (Fin (m * 2 + r))) : ℝ) := by
  let P : ℝ := Fintype.card (Equiv.Perm (Fin (m * 2 + r)))
  let H : Equiv.Perm (Fin (m * 2 + r)) → ℝ := fun σ =>
    finiteCanonicalPairMean ℓ i (fun k => T (σ k))
  have hPnat : 0 < Fintype.card (Equiv.Perm (Fin (m * 2 + r))) :=
    Fintype.card_pos_iff.mpr ⟨Equiv.refl _⟩
  have hP : P ≠ 0 := by
    dsimp only [P]
    exact_mod_cast hPnat.ne'
  have havg :
      (∑ σ : Equiv.Perm (Fin (m * 2 + r)), H σ) / P =
        sampleVarianceBessel (fun k => ℓ i (T k)) := by
    exact average_perm_finiteCanonicalPairMean_eq_sampleVarianceBessel hm ℓ i T
  have hsumw :
      (∑ _σ : Equiv.Perm (Fin (m * 2 + r)), P⁻¹) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    dsimp only [P]
    exact mul_inv_cancel₀ (by exact_mod_cast hPnat.ne')
  have hjensen :
      Real.exp
          (∑ σ ∈ (Finset.univ :
              Finset (Equiv.Perm (Fin (m * 2 + r)))),
            P⁻¹ • (lam * (V - H σ))) ≤
        ∑ σ ∈ (Finset.univ :
            Finset (Equiv.Perm (Fin (m * 2 + r)))),
          P⁻¹ • Real.exp (lam * (V - H σ)) :=
    convexOn_exp.map_sum_le
      (t := (Finset.univ : Finset (Equiv.Perm (Fin (m * 2 + r)))))
      (w := fun _σ => P⁻¹)
      (p := fun σ => lam * (V - H σ))
      (fun _σ _hσ => inv_nonneg.mpr (by
        dsimp only [P]
        exact_mod_cast hPnat.le))
      (by simpa using hsumw)
      (fun _σ _hσ => Set.mem_univ _)
  have hcenter :
      (∑ σ ∈ (Finset.univ :
          Finset (Equiv.Perm (Fin (m * 2 + r)))),
        P⁻¹ • (lam * (V - H σ))) =
      lam * (V - sampleVarianceBessel (fun k => ℓ i (T k))) := by
    simp only [smul_eq_mul]
    calc
      (∑ σ : Equiv.Perm (Fin (m * 2 + r)),
          P⁻¹ * (lam * (V - H σ))) =
        P⁻¹ * lam *
          (P * V - ∑ σ : Equiv.Perm (Fin (m * 2 + r)), H σ) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum,
              Finset.sum_sub_distrib, Finset.sum_const,
              Finset.card_univ, nsmul_eq_mul]
            dsimp only [P]
            ring
      _ = lam *
          (V - (∑ σ : Equiv.Perm (Fin (m * 2 + r)), H σ) / P) := by
            field_simp [hP]
      _ = lam * (V - sampleVarianceBessel (fun k => ℓ i (T k))) := by
        rw [havg]
  rw [hcenter] at hjensen
  calc
    Real.exp
        (lam * (V - sampleVarianceBessel (fun k => ℓ i (T k)))) ≤
      ∑ σ : Equiv.Perm (Fin (m * 2 + r)),
        P⁻¹ • Real.exp (lam * (V - H σ)) := hjensen
    _ = (∑ σ : Equiv.Perm (Fin (m * 2 + r)),
          Real.exp (lam * (V - H σ))) / P := by
      simp only [smul_eq_mul, div_eq_mul_inv]
      rw [← Finset.mul_sum]
      ring

/-- Every permuted canonical matching has the same product-law MGF bound as
the canonical matching. -/
theorem permutedCanonicalPairMean_lowerTailMGF
    [Fintype Z] [DecidableEq Z]
    {m r : ℕ} (hm : 0 < m)
    (p : Z → ℝ) (hp : IsPMF p)
    (ℓ : ι → Z → ℝ) (i : ι)
    (hℓ : ∀ z : Z, ℓ i z ∈ Set.Icc (0 : ℝ) 1)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (σ : Equiv.Perm (Fin (m * 2 + r))) :
    (∑ T : Fin (m * 2 + r) → Z,
        finiteProductSampleWeight p T *
          Real.exp
            (lam *
              (finitePopulationVariance p ℓ i -
                finiteCanonicalPairMean ℓ i
                  (samplePrecompPerm σ Z T)))) ≤
      Real.exp
        (lam ^ (2 : Nat) * finitePopulationVariance p ℓ i /
          (4 * (m : ℝ))) := by
  let e := samplePrecompPerm σ Z
  have hreindex :
      (∑ T : Fin (m * 2 + r) → Z,
          finiteProductSampleWeight p T *
            Real.exp
              (lam *
                (finitePopulationVariance p ℓ i -
                  finiteCanonicalPairMean ℓ i (e T)))) =
        ∑ U : Fin (m * 2 + r) → Z,
          finiteProductSampleWeight p U *
            Real.exp
              (lam *
                (finitePopulationVariance p ℓ i -
                  finiteCanonicalPairMean ℓ i U)) := by
    apply Fintype.sum_equiv e
    intro T
    rw [finiteProductSampleWeight_precompPerm]
  rw [hreindex]
  exact finiteCanonicalPairMean_lowerTailMGF
    hm p hp ℓ i hℓ hlam

/-- Full sample-variance lower-tail MGF obtained by random matching and
finite Jensen. -/
theorem finiteEmpiricalVariance_lowerTailMGF_randomMatching
    [Fintype Z] [DecidableEq Z]
    {m r : ℕ} (hm : 0 < m)
    (p : Z → ℝ) (hp : IsPMF p)
    (ℓ : ι → Z → ℝ) (i : ι)
    (hℓ : ∀ z : Z, ℓ i z ∈ Set.Icc (0 : ℝ) 1)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    (∑ T : Fin (m * 2 + r) → Z,
        finiteProductSampleWeight p T *
          Real.exp
            (lam *
              (finitePopulationVariance p ℓ i -
                finiteEmpiricalVariance ℓ i T))) ≤
      Real.exp
        (lam ^ (2 : Nat) * finitePopulationVariance p ℓ i /
          (4 * (m : ℝ))) := by
  let P : ℝ := Fintype.card (Equiv.Perm (Fin (m * 2 + r)))
  let V : ℝ := finitePopulationVariance p ℓ i
  let F : (Fin (m * 2 + r) → Z) →
      Equiv.Perm (Fin (m * 2 + r)) → ℝ := fun T σ =>
    Real.exp
      (lam * (V - finiteCanonicalPairMean ℓ i (samplePrecompPerm σ Z T)))
  have hPnat : 0 < Fintype.card (Equiv.Perm (Fin (m * 2 + r))) :=
    Fintype.card_pos_iff.mpr ⟨Equiv.refl _⟩
  have hPRpos : 0 < P := by
    dsimp only [P]
    exact_mod_cast hPnat
  have hweight (T : Fin (m * 2 + r) → Z) :
      0 ≤ finiteProductSampleWeight p T := by
    unfold finiteProductSampleWeight
    exact Finset.prod_nonneg (fun k _hk => hp.nonneg (T k))
  have hpoint (T : Fin (m * 2 + r) → Z) :
      Real.exp
          (lam *
            (V - finiteEmpiricalVariance ℓ i T)) ≤
        (∑ σ : Equiv.Perm (Fin (m * 2 + r)), F T σ) / P := by
    unfold finiteEmpiricalVariance
    exact exp_population_sub_sampleVariance_le_permAverage
      hm ℓ i T V lam
  have hfirst :
      (∑ T : Fin (m * 2 + r) → Z,
          finiteProductSampleWeight p T *
            Real.exp
              (lam * (V - finiteEmpiricalVariance ℓ i T))) ≤
        ∑ T : Fin (m * 2 + r) → Z,
          finiteProductSampleWeight p T *
            ((∑ σ : Equiv.Perm (Fin (m * 2 + r)), F T σ) / P) := by
    exact Finset.sum_le_sum (fun T _hT =>
      mul_le_mul_of_nonneg_left (hpoint T) (hweight T))
  have hexchange :
      (∑ T : Fin (m * 2 + r) → Z,
          finiteProductSampleWeight p T *
            ((∑ σ : Equiv.Perm (Fin (m * 2 + r)), F T σ) / P)) =
        (∑ σ : Equiv.Perm (Fin (m * 2 + r)),
          ∑ T : Fin (m * 2 + r) → Z,
            finiteProductSampleWeight p T * F T σ) / P := by
    calc
      (∑ T : Fin (m * 2 + r) → Z,
          finiteProductSampleWeight p T *
            ((∑ σ : Equiv.Perm (Fin (m * 2 + r)), F T σ) / P)) =
        ∑ T : Fin (m * 2 + r) → Z,
          (∑ σ : Equiv.Perm (Fin (m * 2 + r)),
            finiteProductSampleWeight p T * F T σ) / P := by
              apply Finset.sum_congr rfl
              intro T _hT
              rw [← Finset.mul_sum]
              ring
      _ = (∑ T : Fin (m * 2 + r) → Z,
          ∑ σ : Equiv.Perm (Fin (m * 2 + r)),
            finiteProductSampleWeight p T * F T σ) / P := by
              exact (Finset.sum_div
                (Finset.univ : Finset (Fin (m * 2 + r) → Z))
                (fun T => ∑ σ : Equiv.Perm (Fin (m * 2 + r)),
                  finiteProductSampleWeight p T * F T σ) P).symm
      _ = (∑ σ : Equiv.Perm (Fin (m * 2 + r)),
          ∑ T : Fin (m * 2 + r) → Z,
            finiteProductSampleWeight p T * F T σ) / P := by
              rw [Finset.sum_comm]
  have hinner (σ : Equiv.Perm (Fin (m * 2 + r))) :
      (∑ T : Fin (m * 2 + r) → Z,
          finiteProductSampleWeight p T * F T σ) ≤
        Real.exp (lam ^ (2 : Nat) * V / (4 * (m : ℝ))) := by
    exact permutedCanonicalPairMean_lowerTailMGF
      hm p hp ℓ i hℓ hlam σ
  calc
    (∑ T : Fin (m * 2 + r) → Z,
        finiteProductSampleWeight p T *
          Real.exp
            (lam *
              (finitePopulationVariance p ℓ i -
                finiteEmpiricalVariance ℓ i T))) ≤
      ∑ T : Fin (m * 2 + r) → Z,
        finiteProductSampleWeight p T *
          ((∑ σ : Equiv.Perm (Fin (m * 2 + r)), F T σ) / P) := hfirst
    _ = (∑ σ : Equiv.Perm (Fin (m * 2 + r)),
          ∑ T : Fin (m * 2 + r) → Z,
            finiteProductSampleWeight p T * F T σ) / P := hexchange
    _ ≤ (∑ _σ : Equiv.Perm (Fin (m * 2 + r)),
          Real.exp (lam ^ (2 : Nat) * V / (4 * (m : ℝ)))) / P := by
            exact div_le_div_of_nonneg_right
              (Finset.sum_le_sum (fun σ _hσ => hinner σ)) hPRpos.le
    _ = Real.exp
        (lam ^ (2 : Nat) * finitePopulationVariance p ℓ i /
          (4 * (m : ℝ))) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp only [P, V]
      field_simp [ne_of_gt hPRpos]

/-- `n`-scaled form.  With `m = floor(n/2)` this is the
Tolstikhin--Seldin coefficient `n²/(4m)`. -/
theorem finiteEmpiricalVariance_lowerTailMGF_randomMatching_scaled
    [Fintype Z] [DecidableEq Z]
    {m r : ℕ} (hm : 0 < m)
    (p : Z → ℝ) (hp : IsPMF p)
    (ℓ : ι → Z → ℝ) (i : ι)
    (hℓ : ∀ z : Z, ℓ i z ∈ Set.Icc (0 : ℝ) 1)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    (∑ T : Fin (m * 2 + r) → Z,
        finiteProductSampleWeight p T *
          Real.exp
            (lam * (m * 2 + r : ℕ) *
              (finitePopulationVariance p ℓ i -
                finiteEmpiricalVariance ℓ i T))) ≤
      Real.exp
        (lam ^ (2 : Nat) * (m * 2 + r : ℕ) ^ (2 : Nat) *
          finitePopulationVariance p ℓ i / (4 * (m : ℝ))) := by
  have h := finiteEmpiricalVariance_lowerTailMGF_randomMatching
    (r := r) hm p hp ℓ i hℓ
    (lam := lam * (m * 2 + r : ℕ))
    (mul_nonneg hlam (Nat.cast_nonneg _))
  convert h using 1
  ring_nf

/-- Source-normalized finite version of Tolstikhin--Seldin (2013), Eq. (9).
The Bessel empirical variance is averaged under the explicit finite iid
product law. -/
theorem finiteEmpiricalVariance_lowerTailMGF_tolstikhinSeldin
    [Fintype Z] [DecidableEq Z]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : ι → Z → ℝ) (i : ι)
    (hell : ∀ z : Z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {eta : ℝ} (heta : 0 ≤ eta) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp
            (eta * (n : ℝ) *
              (finitePopulationVariance p ell i -
                finiteEmpiricalVariance ell i S))) ≤
      Real.exp
        (eta ^ (2 : Nat) * (n : ℝ) ^ (2 : Nat) *
          finitePopulationVariance p ell i /
            (2 * ((n : ℝ) - 1))) := by
  obtain ⟨m, heven | hodd⟩ := Nat.even_or_odd' n
  · have hnm : n = m * 2 := by omega
    clear heven
    subst n
    have hm : 0 < m := by omega
    have hmatch :=
      finiteEmpiricalVariance_lowerTailMGF_randomMatching_scaled
        (m := m) (r := 0) hm p hp ell i hell heta
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hdenSource : (0 : ℝ) < 2 * (((m * 2 : ℕ) : ℝ) - 1) := by
      have : (1 : ℝ) < ((m * 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < m * 2)
      positivity
    have hV : 0 ≤ finitePopulationVariance p ell i :=
      finitePopulationVariance_nonneg p hp ell i
    have hexp :
        eta ^ (2 : Nat) * (((m * 2 : ℕ) : ℝ) ^ (2 : Nat)) *
              finitePopulationVariance p ell i / (4 * (m : ℝ)) ≤
          eta ^ (2 : Nat) * (((m * 2 : ℕ) : ℝ) ^ (2 : Nat)) *
              finitePopulationVariance p ell i /
                (2 * ((((m * 2 : ℕ) : ℝ)) - 1)) := by
      have hnum : 0 ≤
          eta ^ (2 : Nat) * (((m * 2 : ℕ) : ℝ) ^ (2 : Nat)) *
            finitePopulationVariance p ell i := by positivity
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (m : ℝ)) hdenSource]
      have hden :
          2 * ((((m * 2 : ℕ) : ℝ)) - 1) ≤ 4 * (m : ℝ) := by
        push_cast
        linarith
      exact mul_le_mul_of_nonneg_left hden hnum
    refine hmatch.trans ?_
    apply Real.exp_le_exp.mpr
    simpa only [Nat.add_zero] using hexp
  · have hnm : n = m * 2 + 1 := by omega
    clear hodd
    subst n
    have hm : 0 < m := by omega
    have hmatch :=
      finiteEmpiricalVariance_lowerTailMGF_randomMatching_scaled
        (m := m) (r := 1) hm p hp ell i hell heta
    calc
      _ ≤ Real.exp
          (eta ^ (2 : Nat) * ((m * 2 + 1 : ℕ) : ℝ) ^ (2 : Nat) *
            finitePopulationVariance p ell i / (4 * (m : ℝ))) := hmatch
      _ = _ := by
        congr 1
        have hden :
            2 * (((m * 2 + 1 : ℕ) : ℝ) - 1) = 4 * (m : ℝ) := by
          push_cast
          ring
        rw [hden]

/-- Normalized form of the source-facing empirical-variance MGF.

The deterministic variance penalty is moved inside the exponential, so the
finite-product expectation is at most one. This is the form consumed by the
finite PAC-Bayes change-of-measure layer.
-/
theorem finiteEmpiricalVariance_normalizedLowerTailMGF_le_one
    [Fintype Z] [DecidableEq Z]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : ι → Z → ℝ) (i : ι)
    (hell : ∀ z : Z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {eta : ℝ} (heta : 0 ≤ eta) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp
            (eta * (n : ℝ) *
                (finitePopulationVariance p ell i -
                  finiteEmpiricalVariance ell i S) -
              eta ^ (2 : Nat) * (n : ℝ) ^ (2 : Nat) *
                finitePopulationVariance p ell i /
                  (2 * ((n : ℝ) - 1)))) ≤ 1 := by
  let penalty : ℝ :=
    eta ^ (2 : Nat) * (n : ℝ) ^ (2 : Nat) *
      finitePopulationVariance p ell i / (2 * ((n : ℝ) - 1))
  have hmgf :=
    finiteEmpiricalVariance_lowerTailMGF_tolstikhinSeldin
      hn p hp ell i hell heta
  have hfactor :
      (∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            Real.exp
              (eta * (n : ℝ) *
                  (finitePopulationVariance p ell i -
                    finiteEmpiricalVariance ell i S) - penalty)) =
        Real.exp (-penalty) *
          (∑ S : Fin n → Z,
            finiteProductSampleWeight p S *
              Real.exp
                (eta * (n : ℝ) *
                  (finitePopulationVariance p ell i -
                    finiteEmpiricalVariance ell i S))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [Real.exp_sub, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  change
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp
            (eta * (n : ℝ) *
                (finitePopulationVariance p ell i -
                  finiteEmpiricalVariance ell i S) - penalty)) ≤ 1
  rw [hfactor]
  calc
    Real.exp (-penalty) *
          (∑ S : Fin n → Z,
            finiteProductSampleWeight p S *
              Real.exp
                (eta * (n : ℝ) *
                  (finitePopulationVariance p ell i -
                    finiteEmpiricalVariance ell i S)))
        ≤ Real.exp (-penalty) * Real.exp penalty :=
          mul_le_mul_of_nonneg_left hmgf (le_of_lt (Real.exp_pos _))
    _ = 1 := by rw [← Real.exp_add]; simp

end

end FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF
