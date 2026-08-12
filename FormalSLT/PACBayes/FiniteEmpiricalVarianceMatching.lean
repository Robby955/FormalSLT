/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteEmpiricalVariance
import Mathlib.Data.Fintype.Perm

/-!
# Finite random matchings for empirical variance

This module contains the deterministic and finite-product identities behind the
random-matching proof of the sample-variance MGF. Averaging any nonempty catalog
of distinct coordinate pairs over all sample permutations recovers the
Bessel-corrected sample variance. It also supplies an explicit equivalence
between an ordinary finite sample and independent two-coordinate blocks plus
unused remainder coordinates.

No concentration inequality is proved here. The exponential-moment argument is
in `FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF`.
-/

namespace FormalSLT.PACBayes.FiniteEmpiricalVarianceMatching

open Finset BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.Statistics.ClassicalEstimation

noncomputable section

variable {ι Z β : Type*}

/-- Half the squared difference between two losses. Its expectation under two
independent observations is the population variance. -/
def pairVarianceKernel (ℓ : ι → Z → ℝ) (i : ι) (z w : Z) : ℝ :=
  (ℓ i z - ℓ i w) ^ (2 : Nat) / 2

private lemma exists_perm_map_pair {α : Type*} [DecidableEq α]
    {a b u v : α} (hab : a ≠ b) (huv : u ≠ v) :
    ∃ τ : Equiv.Perm α, τ a = u ∧ τ b = v := by
  let τ₁ : Equiv.Perm α := Equiv.swap a u
  let b₁ : α := τ₁ b
  have hτ₁a : τ₁ a = u := by simp [τ₁]
  have hb₁u : b₁ ≠ u := by
    intro h
    apply hab
    apply τ₁.injective
    exact hτ₁a.trans h.symm
  let τ₂ : Equiv.Perm α := Equiv.swap b₁ v
  let τ : Equiv.Perm α := τ₂ * τ₁
  refine ⟨τ, ?_, ?_⟩
  · simp only [τ, Equiv.Perm.mul_apply, hτ₁a]
    exact Equiv.swap_apply_of_ne_of_ne hb₁u.symm huv
  · simp only [τ, Equiv.Perm.mul_apply]
    change τ₂ b₁ = v
    simp [τ₂]

private lemma permPairSum_eq {α : Type*} [Fintype α] [DecidableEq α]
    (g : α → α → ℝ) {a b u v : α} (hab : a ≠ b) (huv : u ≠ v) :
    (∑ σ : Equiv.Perm α, g (σ a) (σ b)) =
      ∑ σ : Equiv.Perm α, g (σ u) (σ v) := by
  obtain ⟨τ, hτa, hτb⟩ := exists_perm_map_pair hab huv
  have hreindex :
      (∑ σ : Equiv.Perm α, g ((σ * τ) a) ((σ * τ) b)) =
        ∑ σ : Equiv.Perm α, g (σ a) (σ b) := by
    apply Fintype.sum_equiv (Equiv.mulRight τ)
    intro σ
    rfl
  calc
    (∑ σ : Equiv.Perm α, g (σ a) (σ b)) =
      ∑ σ : Equiv.Perm α, g ((σ * τ) a) ((σ * τ) b) := hreindex.symm
    _ = ∑ σ : Equiv.Perm α, g (σ u) (σ v) := by
      apply Finset.sum_congr rfl
      intro σ _hσ
      simp [Equiv.Perm.mul_apply, hτa, hτb]

private lemma permDoubleSum_eq {α : Type*} [Fintype α] [DecidableEq α]
    (g : α → α → ℝ) (σ : Equiv.Perm α) :
    (∑ u : α, ∑ v : α, g (σ u) (σ v)) =
      ∑ u : α, ∑ v : α, g u v := by
  calc
    (∑ u : α, ∑ v : α, g (σ u) (σ v)) =
        ∑ u : α, ∑ v : α, g u (σ v) := by
      apply Fintype.sum_equiv σ
      intro u
      rfl
    _ = ∑ u : α, ∑ v : α, g u v := by
      apply Finset.sum_congr rfl
      intro u _hu
      apply Fintype.sum_equiv σ
      intro v
      rfl

private lemma doubleSum_eq_offDiagonal {α : Type*} [Fintype α] [DecidableEq α]
    (g : α → α → ℝ) (hdiag : ∀ u, g u u = 0) :
    (∑ u : α, ∑ v : α, g u v) =
      ∑ u : α, ∑ v ∈ (Finset.univ : Finset α).erase u, g u v := by
  apply Finset.sum_congr rfl
  intro u _hu
  have hsplit := Finset.add_sum_erase
    (Finset.univ : Finset α) (fun v => g u v) (Finset.mem_univ u)
  rw [← hsplit, hdiag, zero_add]

private lemma doubleOffDiagonalConst {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 1 ≤ Fintype.card α) (c : ℝ) :
    (∑ _u : α, ∑ _v ∈ (Finset.univ : Finset α).erase _u, c) =
      (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) * c := by
  simp only [Finset.sum_const, Finset.card_erase_of_mem, Finset.mem_univ,
    Finset.card_univ, nsmul_eq_mul]
  rw [Nat.cast_sub hα]
  ring

private lemma tripleSum_rotate {α β γ M : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [AddCommMonoid M] (f : α → β → γ → M) :
    (∑ a : α, ∑ b : β, ∑ c : γ, f a b c) =
      ∑ c : γ, ∑ a : α, ∑ b : β, f a b c := by
  calc
    (∑ a : α, ∑ b : β, ∑ c : γ, f a b c) =
        ∑ a : α, ∑ c : γ, ∑ b : β, f a b c := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.sum_comm]
    _ = ∑ c : γ, ∑ a : α, ∑ b : β, f a b c := by
      rw [Finset.sum_comm]

private theorem permPairSum_mul_orderedPairCount
    {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 2 ≤ Fintype.card α) (g : α → α → ℝ)
    (hdiag : ∀ u, g u u = 0) (a b : α) (hab : a ≠ b) :
    ((∑ σ : Equiv.Perm α, g (σ a) (σ b)) *
        ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1))) =
      (Fintype.card (Equiv.Perm α) : ℝ) *
        (∑ u : α, ∑ v : α, g u v) := by
  let A : ℝ := ∑ σ : Equiv.Perm α, g (σ a) (σ b)
  let T : ℝ := ∑ u : α, ∑ v : α,
    ∑ σ : Equiv.Perm α, g (σ u) (σ v)
  have hcardone : 1 ≤ Fintype.card α := le_trans (by norm_num) hα
  have hleft :
      T = (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) * A := by
    dsimp only [T]
    rw [doubleSum_eq_offDiagonal
      (fun u v => ∑ σ : Equiv.Perm α, g (σ u) (σ v))]
    · calc
        (∑ u : α,
            ∑ v ∈ (Finset.univ : Finset α).erase u,
              ∑ σ : Equiv.Perm α, g (σ u) (σ v)) =
            ∑ u : α,
              ∑ v ∈ (Finset.univ : Finset α).erase u, A := by
          apply Finset.sum_congr rfl
          intro u _hu
          apply Finset.sum_congr rfl
          intro v hv
          have hvu : v ≠ u := by simpa using hv
          have huv : u ≠ v := fun h => hvu h.symm
          exact permPairSum_eq g huv hab
        _ = (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) * A :=
          doubleOffDiagonalConst hcardone A
    · intro u
      simp [hdiag]
  have hright :
      T = (Fintype.card (Equiv.Perm α) : ℝ) *
          (∑ u : α, ∑ v : α, g u v) := by
    dsimp only [T]
    calc
      (∑ u : α, ∑ v : α,
          ∑ σ : Equiv.Perm α, g (σ u) (σ v)) =
          ∑ σ : Equiv.Perm α, ∑ u : α, ∑ v : α,
            g (σ u) (σ v) :=
        tripleSum_rotate (α := α) (β := α) (γ := Equiv.Perm α)
          (fun u v σ => g (σ u) (σ v))
      _ = ∑ _σ : Equiv.Perm α, ∑ u : α, ∑ v : α, g u v := by
        apply Finset.sum_congr rfl
        intro σ _hσ
        exact permDoubleSum_eq g σ
      _ = (Fintype.card (Equiv.Perm α) : ℝ) *
          (∑ u : α, ∑ v : α, g u v) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  dsimp only [A] at hleft
  rw [← hright, hleft]
  ring

/-- A uniformly permuted fixed distinct pair has the same average as a
uniformly selected ordered distinct pair. -/
theorem average_perm_pair_eq_average_all_pairs
    {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 2 ≤ Fintype.card α) (g : α → α → ℝ)
    (hdiag : ∀ u, g u u = 0) (a b : α) (hab : a ≠ b) :
    (∑ σ : Equiv.Perm α, g (σ a) (σ b)) /
        (Fintype.card (Equiv.Perm α) : ℝ) =
      (∑ u : α, ∑ v : α, g u v) /
        ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1)) := by
  have hpermpos : 0 < Fintype.card (Equiv.Perm α) :=
    Fintype.card_pos_iff.mpr ⟨Equiv.refl α⟩
  have hpermR : (Fintype.card (Equiv.Perm α) : ℝ) ≠ 0 := by
    exact_mod_cast hpermpos.ne'
  have hαR : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hα).ne'
  have hαm1R : (Fintype.card α : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hα
    linarith
  apply (div_eq_div_iff hpermR (mul_ne_zero hαR hαm1R)).2
  have hmain := permPairSum_mul_orderedPairCount hα g hdiag a b hab
  nlinarith

private lemma fullPairKernel_eq_half_orderedOffDiagonal
    {n : ℕ} (x : Fin n → ℝ) :
    (∑ u : Fin n, ∑ v : Fin n, (x u - x v) ^ (2 : Nat) / 2) =
      orderedOffDiagonalSquaredDifference x / 2 := by
  rw [doubleSum_eq_offDiagonal
    (fun u v => (x u - x v) ^ (2 : Nat) / 2)]
  · unfold orderedOffDiagonalSquaredDifference
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u _hu
    rw [Finset.sum_div]
  · intro u
    simp

/-- The permutation average of one fixed squared-difference pair is the
Bessel-corrected sample variance. -/
theorem average_perm_pairSquaredDifference_eq_sampleVarianceBessel
    {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (a b : Fin n) (hab : a ≠ b) :
    (∑ σ : Equiv.Perm (Fin n),
        (x (σ a) - x (σ b)) ^ (2 : Nat) / 2) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) =
      sampleVarianceBessel x := by
  have hcard : 2 ≤ Fintype.card (Fin n) := by simpa using hn
  rw [average_perm_pair_eq_average_all_pairs (α := Fin n) hcard
    (fun u v => (x u - x v) ^ (2 : Nat) / 2) (by intro u; simp) a b hab]
  rw [fullPairKernel_eq_half_orderedOffDiagonal,
    orderedOffDiagonalSquaredDifference_eq_two_mul_card_mul_centeredSum
      (lt_of_lt_of_le (by norm_num) hn)]
  unfold sampleVarianceBessel
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hn).ne'
  have hpredR : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  simp only [Fintype.card_fin]
  field_simp [hnR, hpredR]

/-- Averaging any fixed catalog of disjoint or overlapping distinct index pairs
over all coordinate permutations recovers the Bessel sample variance.  The
matching application takes the catalog to be a partition into adjacent pairs. -/
theorem average_perm_pairCatalog_eq_sampleVarianceBessel
    {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) (x : Fin n → ℝ)
    (left right : Fin m → Fin n) (hne : ∀ r, left r ≠ right r) :
    (∑ σ : Equiv.Perm (Fin n),
        (∑ r : Fin m,
          (x (σ (left r)) - x (σ (right r))) ^ (2 : Nat) / 2) /
          (m : ℝ)) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) =
      sampleVarianceBessel x := by
  let P : ℝ := Fintype.card (Equiv.Perm (Fin n))
  let V : ℝ := sampleVarianceBessel x
  have hpermpos : 0 < Fintype.card (Equiv.Perm (Fin n)) :=
    Fintype.card_pos_iff.mpr ⟨Equiv.refl (Fin n)⟩
  have hpermR : P ≠ 0 := by
    dsimp only [P]
    exact_mod_cast hpermpos.ne'
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpair (r : Fin m) :
      (∑ σ : Equiv.Perm (Fin n),
          (x (σ (left r)) - x (σ (right r))) ^ (2 : Nat) / 2) =
        P * V := by
    have h := average_perm_pairSquaredDifference_eq_sampleVarianceBessel
      hn x (left r) (right r) (hne r)
    dsimp only [P, V]
    apply (div_eq_iff (by exact_mod_cast hpermpos.ne')).mp at h
    nlinarith
  dsimp only [P, V] at hpermR ⊢
  calc
    (∑ σ : Equiv.Perm (Fin n),
        (∑ r : Fin m,
          (x (σ (left r)) - x (σ (right r))) ^ (2 : Nat) / 2) /
          (m : ℝ)) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) =
      ((∑ σ : Equiv.Perm (Fin n), ∑ r : Fin m,
          (x (σ (left r)) - x (σ (right r))) ^ (2 : Nat) / 2) /
          (m : ℝ)) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
          apply congrArg
            (fun y : ℝ => y / (Fintype.card (Equiv.Perm (Fin n)) : ℝ))
          exact (Finset.sum_div (Finset.univ : Finset (Equiv.Perm (Fin n)))
            (fun σ => ∑ r : Fin m,
              (x (σ (left r)) - x (σ (right r))) ^ (2 : Nat) / 2)
            (m : ℝ)).symm
    _ = ((∑ r : Fin m, ∑ σ : Equiv.Perm (Fin n),
          (x (σ (left r)) - x (σ (right r))) ^ (2 : Nat) / 2) /
          (m : ℝ)) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
          rw [Finset.sum_comm]
    _ = ((∑ _r : Fin m,
          (Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
            sampleVarianceBessel x) /
          (m : ℝ)) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
          congr 2
          apply Finset.sum_congr rfl
          intro r _hr
          exact hpair r
    _ = sampleVarianceBessel x := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hmR, hpermR]

/-- Exact product-law factorization for a finite catalog of independent
two-coordinate blocks. -/
theorem finitePairBlock_factorization
    [Fintype Z] [DecidableEq Z] [Fintype β] [DecidableEq β]
    (p : Z → ℝ) (hp : IsPMF p) (q : β → Z → Z → ℝ) :
    (∑ S : β → (Fin 2 → Z),
        ∏ r : β,
          finiteProductSampleWeight p (S r) * q r (S r 0) (S r 1)) =
      ∏ r : β, ∑ z : Z, ∑ w : Z, p z * p w * q r z w := by
  have hlocal (r : β) :
      (∑ T : Fin 2 → Z,
          finiteProductSampleWeight p T * q r (T 0) (T 1)) =
        ∑ z : Z, ∑ w : Z, p z * p w * q r z w := by
    exact finiteProductSampleWeight_pairExpectation p hp 0 1 (by decide) (q r)
  calc
    (∑ S : β → (Fin 2 → Z),
        ∏ r : β,
          finiteProductSampleWeight p (S r) * q r (S r 0) (S r 1)) =
      ∏ r : β, ∑ T : Fin 2 → Z,
        finiteProductSampleWeight p T * q r (T 0) (T 1) := by
          exact (Fintype.prod_sum
            (fun r (T : Fin 2 → Z) =>
              finiteProductSampleWeight p T * q r (T 0) (T 1))).symm
    _ = ∏ r : β, ∑ z : Z, ∑ w : Z, p z * p w * q r z w := by
      apply Finset.prod_congr rfl
      intro r _hr
      exact hlocal r

/-- Product weight of a sample represented as independent two-coordinate
blocks. -/
def finitePairBlockSampleWeight
    [Fintype Z] {m : ℕ} (p : Z → ℝ) (S : Fin m → (Fin 2 → Z)) : ℝ :=
  ∏ r : Fin m, finiteProductSampleWeight p (S r)

/-- Mean pair-variance kernel over a nonempty block catalog. -/
def finitePairBlockMean
    {m : ℕ} (ℓ : ι → Z → ℝ) (i : ι)
    (S : Fin m → (Fin 2 → Z)) : ℝ :=
  (∑ r : Fin m, pairVarianceKernel ℓ i (S r 0) (S r 1)) / (m : ℝ)

/-- Coordinates of `m` two-element blocks followed by `r` remainder
coordinates are equivalent to `Fin (2m + r)`. -/
def pairRemainderCoordEquiv (m r : ℕ) :
    ((Fin m × Fin 2) ⊕ Fin r) ≃ Fin (m * 2 + r) :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin r))).trans finSumFinEquiv

/-- Reindex a `Fin (2m + r)` sample as pair blocks and remainder coordinates. -/
def finSamplePairRemainderEquiv (m r : ℕ) (Z : Type*) :
    (Fin (m * 2 + r) → Z) ≃
      (Fin m → Fin 2 → Z) × (Fin r → Z) :=
  (Equiv.piCongrLeft (fun _ : Fin (m * 2 + r) => Z)
      (pairRemainderCoordEquiv m r)).symm |>.trans
    ((Equiv.sumPiEquivProdPi
      (fun _ : (Fin m × Fin 2) ⊕ Fin r => Z)).trans
        (Equiv.prodCongr (Equiv.curry (Fin m) (Fin 2) Z)
          (Equiv.refl (Fin r → Z))))

@[simp] lemma finSamplePairRemainderEquiv_apply_left
    {m r : ℕ} {Z : Type*} (T : Fin (m * 2 + r) → Z)
    (a : Fin m) (b : Fin 2) :
    (finSamplePairRemainderEquiv m r Z T).1 a b =
      T (pairRemainderCoordEquiv m r (Sum.inl (a, b))) := by
  rfl

@[simp] lemma finSamplePairRemainderEquiv_apply_right
    {m r : ℕ} {Z : Type*} (T : Fin (m * 2 + r) → Z)
    (c : Fin r) :
    (finSamplePairRemainderEquiv m r Z T).2 c =
      T (pairRemainderCoordEquiv m r (Sum.inr c)) := by
  rfl

/-- The ordinary product-sample weight factors over pair blocks and remainder
coordinates under `finSamplePairRemainderEquiv`. -/
lemma finiteProductSampleWeight_eq_pairRemainder
    [Fintype Z] {m r : ℕ} (p : Z → ℝ)
    (T : Fin (m * 2 + r) → Z) :
    finiteProductSampleWeight p T =
      finitePairBlockSampleWeight p
          (finSamplePairRemainderEquiv m r Z T).1 *
        finiteProductSampleWeight p
          (finSamplePairRemainderEquiv m r Z T).2 := by
  unfold finiteProductSampleWeight finitePairBlockSampleWeight
  let e := pairRemainderCoordEquiv m r
  calc
    (∏ k : Fin (m * 2 + r), p (T k)) =
        ∏ q : (Fin m × Fin 2) ⊕ Fin r, p (T (e q)) := by
          exact (Fintype.prod_equiv e
            (fun q => p (T (e q))) (fun k => p (T k)) (fun q => rfl)).symm
    _ = (∏ q : Fin m × Fin 2, p (T (e (Sum.inl q)))) *
          ∏ c : Fin r, p (T (e (Sum.inr c))) := by
            exact Fintype.prod_sum_type
              (fun q : (Fin m × Fin 2) ⊕ Fin r => p (T (e q)))
    _ = (∏ a : Fin m, ∏ b : Fin 2,
          p ((finSamplePairRemainderEquiv m r Z T).1 a b)) *
        ∏ c : Fin r,
          p ((finSamplePairRemainderEquiv m r Z T).2 c) := by
      rw [Fintype.prod_prod_type]
      rfl

/-- Pair-kernel mean for the canonical block decomposition of a finite sample. -/
def finiteCanonicalPairMean
    {m r : ℕ} (ℓ : ι → Z → ℝ) (i : ι)
    (T : Fin (m * 2 + r) → Z) : ℝ :=
  finitePairBlockMean ℓ i (finSamplePairRemainderEquiv m r Z T).1

variable {ι Z : Type*}

/-- Left coordinate of canonical pair `a`. -/
def canonicalPairLeft (m r : ℕ) (a : Fin m) : Fin (m * 2 + r) :=
  pairRemainderCoordEquiv m r (Sum.inl (a, 0))

/-- Right coordinate of canonical pair `a`. -/
def canonicalPairRight (m r : ℕ) (a : Fin m) : Fin (m * 2 + r) :=
  pairRemainderCoordEquiv m r (Sum.inl (a, 1))

/-- The two coordinates in every canonical pair are distinct. -/
lemma canonicalPairLeft_ne_right {m r : ℕ} (a : Fin m) :
    canonicalPairLeft m r a ≠ canonicalPairRight m r a := by
  intro h
  have h' := (pairRemainderCoordEquiv m r).injective h
  simp at h'

/-- Averaging the canonical pair mean over all coordinate permutations gives
the Bessel-corrected sample variance. -/
theorem average_perm_finiteCanonicalPairMean_eq_sampleVarianceBessel
    {m r : ℕ} (hm : 0 < m)
    (ℓ : ι → Z → ℝ) (i : ι) (T : Fin (m * 2 + r) → Z) :
    (∑ σ : Equiv.Perm (Fin (m * 2 + r)),
        finiteCanonicalPairMean ℓ i (fun k => T (σ k))) /
        (Fintype.card (Equiv.Perm (Fin (m * 2 + r))) : ℝ) =
      sampleVarianceBessel (fun k => ℓ i (T k)) := by
  have hn : 2 ≤ m * 2 + r := by omega
  have hcatalog := average_perm_pairCatalog_eq_sampleVarianceBessel
    hn hm (fun k => ℓ i (T k))
    (canonicalPairLeft m r) (canonicalPairRight m r)
    (canonicalPairLeft_ne_right (r := r))
  simpa [finiteCanonicalPairMean, finitePairBlockMean,
    pairVarianceKernel, canonicalPairLeft, canonicalPairRight] using hcatalog

/-- Precompose a finite sample with a coordinate permutation. -/
def samplePrecompPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) (Z : Type*) :
    (Fin n → Z) ≃ (Fin n → Z) where
  toFun T := fun k => T (σ k)
  invFun T := fun k => T (σ.symm k)
  left_inv T := by
    funext k
    simp
  right_inv T := by
    funext k
    simp

/-- Product-sample weights are invariant under coordinate permutations. -/
lemma finiteProductSampleWeight_precompPerm
    [Fintype Z] {n : ℕ} (p : Z → ℝ) (T : Fin n → Z)
    (σ : Equiv.Perm (Fin n)) :
    finiteProductSampleWeight p (samplePrecompPerm σ Z T) =
      finiteProductSampleWeight p T := by
  unfold finiteProductSampleWeight samplePrecompPerm
  exact Fintype.prod_equiv σ
    (fun k => p (T (σ k))) (fun k => p (T k)) (fun _k => rfl)

end

end FormalSLT.PACBayes.FiniteEmpiricalVarianceMatching
