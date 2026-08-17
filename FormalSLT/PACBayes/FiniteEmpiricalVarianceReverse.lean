/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteEmpiricalVariance
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.MeasurableSpace.Invariants
import Mathlib.Probability.Process.Filtration

/-!
# Reverse-time identities for finite empirical variance

This module starts the finite-horizon reverse-martingale construction behind
time-uniform empirical-variance bounds.  Its deterministic core is the exact
leave-one-out identity for Bessel-corrected sample variance: the variance of
`n + 1` observations is the average of the Bessel variances obtained by
deleting one observation.

It also constructs the decreasing exchangeable sigma algebras on one common
horizon product space and proves the load-bearing one-step conditional-
expectation identity under a finite iid law.  It does **not** yet prove an
all-times reverse martingale, a reverse maximal inequality, an exponential
process, or a time-uniform PAC-Bayes theorem.
-/

namespace FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse

open Finset BigOperators
open FormalSLT.Statistics
open FormalSLT.Statistics.ClassicalEstimation
open FormalSLT.PACBayes.FiniteEmpiricalVariance

noncomputable section

/-- Delete coordinate `r` from a tuple of length `n + 1`. -/
def eraseCoordinate {n : ℕ} {Z : Type*} (r : Fin (n + 1))
    (x : Fin (n + 1) → Z) : Fin n → Z :=
  fun k ↦ x (r.succAbove k)

/-- Summing a diagonal-zero kernel over all leave-one-out tuples counts every
ordered off-diagonal pair exactly `n - 1` times. -/
theorem sum_eraseCoordinate_double_of_diag_zero {n : ℕ}
    (f : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hdiag : ∀ i, f i i = 0) :
    (∑ r : Fin (n + 1), ∑ a : Fin n, ∑ b : Fin n,
        f (r.succAbove a) (r.succAbove b)) =
      ((n : ℝ) - 1) * ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), f i j := by
  let T : ℝ := ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), f i j
  have hpoint (r : Fin (n + 1)) :
      (∑ a : Fin n, ∑ b : Fin n, f (r.succAbove a) (r.succAbove b)) =
        T - (∑ j : Fin (n + 1), f r j) -
          (∑ i : Fin (n + 1), f i r) + f r r := by
    have hinner (i : Fin (n + 1)) :
        (∑ b : Fin n, f i (r.succAbove b)) =
          (∑ j : Fin (n + 1), f i j) - f i r := by
      have h := Fin.sum_univ_succAbove (fun j : Fin (n + 1) ↦ f i j) r
      linarith
    calc
      (∑ a : Fin n, ∑ b : Fin n, f (r.succAbove a) (r.succAbove b)) =
          ∑ a : Fin n,
            ((∑ j : Fin (n + 1), f (r.succAbove a) j) -
              f (r.succAbove a) r) := by
            refine Finset.sum_congr rfl (fun a _ ↦ hinner (r.succAbove a))
      _ = (∑ a : Fin n, ∑ j : Fin (n + 1), f (r.succAbove a) j) -
            ∑ a : Fin n, f (r.succAbove a) r := by
            rw [Finset.sum_sub_distrib]
      _ = (T - ∑ j : Fin (n + 1), f r j) -
            ((∑ i : Fin (n + 1), f i r) - f r r) := by
            have hrow := Fin.sum_univ_succAbove
              (fun i : Fin (n + 1) ↦ ∑ j : Fin (n + 1), f i j) r
            have hcol := Fin.sum_univ_succAbove
              (fun i : Fin (n + 1) ↦ f i r) r
            dsimp [T] at hrow ⊢
            linarith
      _ = T - (∑ j : Fin (n + 1), f r j) -
            (∑ i : Fin (n + 1), f i r) + f r r := by ring
  calc
    (∑ r : Fin (n + 1), ∑ a : Fin n, ∑ b : Fin n,
        f (r.succAbove a) (r.succAbove b)) =
        ∑ r : Fin (n + 1),
          (T - (∑ j : Fin (n + 1), f r j) -
            (∑ i : Fin (n + 1), f i r) + f r r) := by
          refine Finset.sum_congr rfl (fun r _ ↦ hpoint r)
    _ = ((n + 1 : ℕ) : ℝ) * T - T - T := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_sub_distrib]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          have htranspose :
              (∑ y : Fin (n + 1), ∑ x : Fin (n + 1), f x y) = T := by
            dsimp [T]
            rw [Finset.sum_comm]
          have hrows :
              (∑ x : Fin (n + 1), ∑ j : Fin (n + 1), f x j) = T := rfl
          simp_rw [hdiag]
          simp only [Finset.sum_const_zero]
          rw [hrows, htranspose]
          ring
    _ = ((n : ℝ) - 1) * T := by
          norm_num [Nat.cast_add]
          ring
    _ = ((n : ℝ) - 1) *
          ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), f i j := by rfl

/-- The ordered squared-difference numerator over all leave-one-out tuples. -/
theorem sum_orderedOffDiagonalSquaredDifference_eraseCoordinate {n : ℕ}
    (x : Fin (n + 1) → ℝ) :
    (∑ r : Fin (n + 1),
        orderedOffDiagonalSquaredDifference (eraseCoordinate r x)) =
      ((n : ℝ) - 1) * orderedOffDiagonalSquaredDifference x := by
  have hfull (m : ℕ) (y : Fin m → ℝ) :
      orderedOffDiagonalSquaredDifference y =
        ∑ i : Fin m, ∑ j : Fin m, (y i - y j) ^ (2 : Nat) := by
    unfold orderedOffDiagonalSquaredDifference
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    have hsplit := Finset.add_sum_erase
      (Finset.univ : Finset (Fin m))
      (fun j ↦ (y i - y j) ^ (2 : Nat)) (Finset.mem_univ i)
    rw [← hsplit]
    simp
  simp_rw [hfull]
  exact sum_eraseCoordinate_double_of_diag_zero
    (fun i j ↦ (x i - x j) ^ (2 : Nat)) (fun i ↦ by simp)

/-- Bessel variance as the normalized ordered squared-difference sum. -/
theorem sampleVarianceBessel_eq_orderedOffDiagonalSquaredDifference {n : ℕ}
    (hn : 2 ≤ n) (x : Fin n → ℝ) :
    sampleVarianceBessel x =
      orderedOffDiagonalSquaredDifference x /
        (2 * (n : ℝ) * ((n : ℝ) - 1)) := by
  have h := finiteEmpiricalVariance_eq_pairwise (Z := ℝ) (hn := hn)
    (fun _ : Unit ↦ id) () x
  simpa [finiteEmpiricalVariance, finitePairwiseEmpiricalVariance] using h

/-- Bessel variance is invariant under a permutation of sample indices. -/
theorem sampleVarianceBessel_comp_perm {n : ℕ} (x : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) :
    sampleVarianceBessel (x ∘ σ) = sampleVarianceBessel x := by
  have hmean : sampleMean (x ∘ σ) = sampleMean x := by
    unfold sampleMean
    simp only [Function.comp_apply]
    rw [Equiv.sum_comp σ x]
  unfold sampleVarianceBessel
  rw [hmean]
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp σ (fun i ↦ (x i - sampleMean x) ^ (2 : Nat))]

/-- **Leave-one-out Bessel identity.**  For `n ≥ 2`, the Bessel-corrected
variance of `n + 1` observations is the average of the `n + 1` Bessel
variances obtained by deleting one observation. -/
theorem sampleVarianceBessel_eq_average_eraseCoordinate {n : ℕ} (hn : 2 ≤ n)
    (x : Fin (n + 1) → ℝ) :
    sampleVarianceBessel x =
      (∑ r : Fin (n + 1), sampleVarianceBessel (eraseCoordinate r x)) /
        (n + 1 : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hnpred : (0 : ℝ) < (n : ℝ) - 1 := by
    have h : (1 : ℝ) < n := by
      exact_mod_cast (show 1 < n from lt_of_lt_of_le (by norm_num) hn)
    linarith
  have hnsucc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [sampleVarianceBessel_eq_orderedOffDiagonalSquaredDifference
    (n := n + 1) (by omega)]
  simp_rw [sampleVarianceBessel_eq_orderedOffDiagonalSquaredDifference hn]
  rw [← Finset.sum_div,
    sum_orderedOffDiagonalSquaredDifference_eraseCoordinate]
  norm_num [Nat.cast_add]
  field_simp

/-! ### The exchangeable reverse filtration -/

open MeasureTheory

section ExchangeableFiltration

variable {Z : Type*} [MeasurableSpace Z]

/-- Reindex a finite sample by a permutation of its coordinates.  The
orientation is chosen so that coordinate `k` of the result is coordinate
`σ k` of the input. -/
def samplePermutation {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (Fin N → Z) ≃ᵐ (Fin N → Z) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin N ↦ Z) σ.symm

@[simp]
theorem samplePermutation_apply {N : ℕ} (σ : Equiv.Perm (Fin N))
    (x : Fin N → Z) (k : Fin N) :
    samplePermutation σ x k = x (σ k) := by
  simp [samplePermutation, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft, Equiv.piCongrLeft']

/-- Coordinate permutations preserve a finite iid product measure. -/
theorem measurePreserving_samplePermutation {N : ℕ} (mu : Measure Z)
    [SigmaFinite mu] (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (samplePermutation σ)
      (Measure.pi (fun _ : Fin N ↦ mu))
      (Measure.pi (fun _ : Fin N ↦ mu)) := by
  simpa [samplePermutation] using
    (measurePreserving_piCongrLeft
      (μ := fun _ : Fin N ↦ mu)
      (α := fun _ : Fin N ↦ Z) σ.symm)

/-- Permutations supported on the first `t` coordinates of a horizon-`N`
sample.  When `t > N`, this is simply the full permutation group. -/
def prefixPermutationSubgroup (N t : ℕ) : Subgroup (Equiv.Perm (Fin N)) where
  carrier := {σ | ∀ k : Fin N, t ≤ k.1 → σ k = k}
  one_mem' := by simp
  mul_mem' := by
    intro σ τ hσ hτ k hk
    simp [hσ k hk, hτ k hk]
  inv_mem' := by
    intro σ hσ k hk
    apply σ.injective
    simp [hσ k hk]

/-- The sigma algebra of measurable events invariant under every permutation
of the first `t` coordinates.  It keeps the suffix ordered and forgets the
order of the prefix. -/
@[implicit_reducible]
def prefixExchangeableSpace (N t : ℕ) : MeasurableSpace (Fin N → Z) :=
  ⨅ σ : prefixPermutationSubgroup N t,
    MeasurableSpace.invariants (samplePermutation (σ : Equiv.Perm (Fin N)))

theorem measurableSet_prefixExchangeableSpace_iff {N t : ℕ}
    {s : Set (Fin N → Z)} :
    MeasurableSet[prefixExchangeableSpace (Z := Z) N t] s ↔
      MeasurableSet s ∧
        ∀ σ : prefixPermutationSubgroup N t,
          samplePermutation (σ : Equiv.Perm (Fin N)) ⁻¹' s = s := by
  rw [prefixExchangeableSpace, MeasurableSpace.measurableSet_iInf]
  constructor
  · intro h
    exact ⟨(MeasurableSpace.measurableSet_invariants.mp (h 1)).1,
      fun σ ↦ (MeasurableSpace.measurableSet_invariants.mp (h σ)).2⟩
  · rintro ⟨hs, hinv⟩ σ
    exact MeasurableSpace.measurableSet_invariants.mpr ⟨hs, hinv σ⟩

/-- More coordinates are symmetrized as time increases, so the exchangeable
sigma algebras decrease in the ordinary natural-number order. -/
theorem prefixExchangeableSpace_antitone (N : ℕ) :
    Antitone (prefixExchangeableSpace (Z := Z) N) := by
  intro t u htu s hs
  rw [measurableSet_prefixExchangeableSpace_iff] at hs ⊢
  refine ⟨hs.1, fun σ ↦ ?_⟩
  let τ : prefixPermutationSubgroup N u :=
    ⟨(σ : Equiv.Perm (Fin N)), fun k huk ↦ σ.property k (htu.trans huk)⟩
  exact hs.2 τ

theorem prefixExchangeableSpace_le (N t : ℕ) :
    prefixExchangeableSpace (Z := Z) N t ≤
      (inferInstance : MeasurableSpace (Fin N → Z)) := by
  intro s hs
  exact (measurableSet_prefixExchangeableSpace_iff.mp hs).1

/-- The explicit reverse filtration generated by unordered prefixes and
ordered suffixes.  `OrderDual ℕ` turns the decreasing family into a standard
mathlib filtration. -/
def exchangeableReverseFiltration (N : ℕ) :
    Filtration (OrderDual ℕ) (inferInstance : MeasurableSpace (Fin N → Z)) where
  seq t := prefixExchangeableSpace (Z := Z) N t.ofDual
  mono' := by
    intro t u htu
    exact prefixExchangeableSpace_antitone (Z := Z) N htu
  le' t := prefixExchangeableSpace_le (Z := Z) N t.ofDual

/-- The first `t` coordinates of a horizon-`N` sample. -/
def samplePrefix {N t : ℕ} (ht : t ≤ N) (x : Fin N → Z) : Fin t → Z :=
  fun k ↦ x (Fin.castLE ht k)

/-- Identify `Fin t` with the prefix subtype inside `Fin N`. -/
def finPrefixEquiv {N t : ℕ} (ht : t ≤ N) :
    Fin t ≃ {k : Fin N // k.1 < t} where
  toFun k := ⟨Fin.castLE ht k, k.2⟩
  invFun k := ⟨k.1.1, k.2⟩
  left_inv k := rfl
  right_inv k := by cases k; rfl

/-- A permutation fixing the suffix preserves membership in the prefix. -/
theorem prefixPermutation_lt_iff {N t : ℕ} (σ : Equiv.Perm (Fin N))
    (hσ : ∀ k : Fin N, t ≤ k.1 → σ k = k) (k : Fin N) :
    (σ k).1 < t ↔ k.1 < t := by
  constructor
  · intro hσk
    by_contra hk
    have hfix := hσ k (Nat.le_of_not_gt hk)
    rw [hfix] at hσk
    exact (Nat.not_lt_of_ge (Nat.le_of_not_gt hk)) hσk
  · intro hk
    by_contra hσk
    have hfix := hσ (σ k) (Nat.le_of_not_gt hσk)
    have heq : σ k = k := by
      apply σ.injective
      simpa using hfix
    rw [heq] at hσk
    exact hσk hk

/-- Restrict a suffix-fixing horizon permutation to the prefix it permutes. -/
def restrictPrefixPermutation {N t : ℕ} (ht : t ≤ N)
    (σ : Equiv.Perm (Fin N))
    (hσ : ∀ k : Fin N, t ≤ k.1 → σ k = k) : Equiv.Perm (Fin t) :=
  let e := finPrefixEquiv ht
  e |>.trans (σ.subtypePerm (prefixPermutation_lt_iff σ hσ)) |>.trans e.symm

theorem castLE_restrictPrefixPermutation {N t : ℕ} (ht : t ≤ N)
    (σ : Equiv.Perm (Fin N))
    (hσ : ∀ k : Fin N, t ≤ k.1 → σ k = k) (k : Fin t) :
    Fin.castLE ht (restrictPrefixPermutation ht σ hσ k) =
      σ (Fin.castLE ht k) := by
  simp [restrictPrefixPermutation, finPrefixEquiv, Equiv.Perm.subtypePerm_apply]

/-- Bessel variance of the losses in the first `t` coordinates. -/
def prefixBesselVariance {N t : ℕ} (ht : t ≤ N) (ell : Z → ℝ)
    (x : Fin N → Z) : ℝ :=
  sampleVarianceBessel (fun k ↦ ell (samplePrefix ht x k))

/-- A prefix statistic is unchanged by any horizon permutation supported on
that prefix. -/
theorem prefixBesselVariance_samplePermutation {N t : ℕ} (ht : t ≤ N)
    (ell : Z → ℝ) (x : Fin N → Z) (σ : Equiv.Perm (Fin N))
    (hσ : ∀ k : Fin N, t ≤ k.1 → σ k = k) :
    prefixBesselVariance ht ell (samplePermutation σ x) =
      prefixBesselVariance ht ell x := by
  let τ := restrictPrefixPermutation ht σ hσ
  let y : Fin t → ℝ := fun k ↦ ell (samplePrefix ht x k)
  have hperm := sampleVarianceBessel_comp_perm y τ
  unfold prefixBesselVariance
  change sampleVarianceBessel _ = sampleVarianceBessel y
  rw [← hperm]
  congr 1
  funext k
  simp only [Function.comp_apply, samplePrefix,
    samplePermutation_apply, y, τ]
  rw [castLE_restrictPrefixPermutation]

/-- The prefix Bessel statistic is measurable for the exchangeable reverse
sigma algebra at the same time. -/
theorem measurable_prefixBesselVariance [Fintype Z] [MeasurableSingletonClass Z]
    {N t : ℕ} (ht : t ≤ N) (ell : Z → ℝ) :
    Measurable[prefixExchangeableSpace (Z := Z) N t]
      (prefixBesselVariance ht ell) := by
  intro s hs
  rw [measurableSet_prefixExchangeableSpace_iff]
  refine ⟨(measurable_of_finite (prefixBesselVariance ht ell)) hs, fun σ ↦ ?_⟩
  ext x
  simp only [Set.mem_preimage]
  rw [prefixBesselVariance_samplePermutation ht ell x
    (σ : Equiv.Perm (Fin N)) σ.property]

/-- Move the standard final coordinate of `Fin (n + 1)` to `r`, while the
remaining coordinates enumerate the order-preserving deletion of `r`. -/
def deletionPermutation {n : ℕ} (r : Fin (n + 1)) :
    Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' (Fin.last n)).trans (finSuccEquiv' r).symm

@[simp]
theorem deletionPermutation_castSucc {n : ℕ} (r : Fin (n + 1)) (k : Fin n) :
    deletionPermutation r k.castSucc = r.succAbove k := by
  simp [deletionPermutation, finSuccEquiv'_last_apply_castSucc]

@[simp]
theorem deletionPermutation_last {n : ℕ} (r : Fin (n + 1)) :
    deletionPermutation r (Fin.last n) = r := by
  simp [deletionPermutation]

/-- Extend the deletion permutation of the first `n + 1` coordinates to a
horizon-`N` permutation that fixes the suffix. -/
def horizonDeletionPermutation {N n : ℕ} (h : n + 1 ≤ N)
    (r : Fin (n + 1)) : Equiv.Perm (Fin N) :=
  (deletionPermutation r).viaFintypeEmbedding (Fin.castLEEmb h)

@[simp]
theorem horizonDeletionPermutation_castLE {N n : ℕ} (h : n + 1 ≤ N)
    (r : Fin (n + 1)) (k : Fin (n + 1)) :
    horizonDeletionPermutation h r (Fin.castLE h k) =
      Fin.castLE h (deletionPermutation r k) := by
  exact Equiv.Perm.viaFintypeEmbedding_apply_image
    (deletionPermutation r) (Fin.castLEEmb h) k

theorem horizonDeletionPermutation_fix_suffix {N n : ℕ} (h : n + 1 ≤ N)
    (r : Fin (n + 1)) (k : Fin N) (hk : n + 1 ≤ k.1) :
    horizonDeletionPermutation h r k = k := by
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  rintro ⟨j, hj⟩
  have hval := congrArg Fin.val hj
  simp only [Fin.coe_castLEEmb, Fin.val_castLE] at hval
  omega

/-- The horizon deletion permutation is an element of the prefix permutation
group at time `n + 1`. -/
def horizonDeletionPrefixPermutation {N n : ℕ} (h : n + 1 ≤ N)
    (r : Fin (n + 1)) : prefixPermutationSubgroup N (n + 1) :=
  ⟨horizonDeletionPermutation h r,
    fun k hk ↦ horizonDeletionPermutation_fix_suffix h r k hk⟩

/-- Applying a horizon deletion permutation and then taking the first `n`
coordinates is exactly order-preserving deletion from the first `n + 1`. -/
theorem samplePrefix_samplePermutation_horizonDeletion {N n : ℕ}
    (h : n + 1 ≤ N) (r : Fin (n + 1)) (x : Fin N → Z) :
    samplePrefix ((Nat.le_succ n).trans h)
        (samplePermutation (horizonDeletionPermutation h r) x) =
      eraseCoordinate r (samplePrefix h x) := by
  funext k
  unfold samplePrefix eraseCoordinate
  rw [samplePermutation_apply]
  change x (horizonDeletionPermutation h r (Fin.castLE h k.castSucc)) =
    x (Fin.castLE h (r.succAbove k))
  rw [horizonDeletionPermutation_castLE, deletionPermutation_castSucc]

/-- Leave-one-out Bessel identity inside a common horizon sample space. -/
theorem prefixBesselVariance_eq_average_horizonDeletion {N n : ℕ}
    (hn : 2 ≤ n) (h : n + 1 ≤ N) (ell : Z → ℝ) (x : Fin N → Z) :
    prefixBesselVariance h ell x =
      (∑ r : Fin (n + 1),
          prefixBesselVariance ((Nat.le_succ n).trans h) ell
            (samplePermutation (horizonDeletionPermutation h r) x)) /
        (n + 1 : ℝ) := by
  have hbessel := sampleVarianceBessel_eq_average_eraseCoordinate hn
    (fun k ↦ ell (samplePrefix h x k))
  unfold prefixBesselVariance
  rw [hbessel]
  congr 1
  refine Finset.sum_congr rfl (fun r _ ↦ ?_)
  rw [samplePrefix_samplePermutation_horizonDeletion h r x]
  rfl

/-- Set integrals are invariant under a coordinate permutation when the set
itself is invariant. -/
theorem setIntegral_comp_samplePermutation_eq {N : ℕ} (mu : Measure Z)
    [SigmaFinite mu] (sigma : Equiv.Perm (Fin N)) (f : (Fin N → Z) → ℝ)
    {s : Set (Fin N → Z)} (hs : MeasurableSet s)
    (hinv : samplePermutation sigma ⁻¹' s = s) :
    ∫ x in s, f (samplePermutation sigma x)
        ∂(Measure.pi (fun _ : Fin N ↦ mu)) =
      ∫ x in s, f x ∂(Measure.pi (fun _ : Fin N ↦ mu)) := by
  let muN : Measure (Fin N → Z) := Measure.pi (fun _ : Fin N ↦ mu)
  rw [← integral_indicator hs, ← integral_indicator hs]
  have hfun :
      s.indicator (fun x ↦ f (samplePermutation sigma x)) =
        (s.indicator f) ∘ samplePermutation sigma := by
    funext x
    have hx : samplePermutation sigma x ∈ s ↔ x ∈ s := by
      change x ∈ samplePermutation sigma ⁻¹' s ↔ x ∈ s
      rw [hinv]
    by_cases hxs : x ∈ s
    · have hperm : samplePermutation sigma x ∈ s := hx.mpr hxs
      simp [Set.indicator_of_mem hxs, Set.indicator_of_mem hperm,
        Function.comp_apply]
    · have hperm : samplePermutation sigma x ∉ s := fun h ↦ hxs (hx.mp h)
      simp [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hperm,
        Function.comp_apply]
  rw [hfun]
  exact (measurePreserving_samplePermutation mu sigma).integral_comp'
    (s.indicator f)

/-- The leave-one-out identity upgrades to the defining set-integral identity
for one reverse conditional-expectation step under the finite iid law. -/
theorem setIntegral_prefixBesselVariance_succ_eq [Fintype Z]
    [MeasurableSingletonClass Z] (mu : Measure Z) [IsProbabilityMeasure mu]
    {N n : ℕ} (hn : 2 ≤ n) (h : n + 1 ≤ N) (ell : Z → ℝ)
    {s : Set (Fin N → Z)}
    (hs : MeasurableSet[prefixExchangeableSpace (Z := Z) N (n + 1)] s) :
    ∫ x in s, prefixBesselVariance h ell x
        ∂(Measure.pi (fun _ : Fin N ↦ mu)) =
      ∫ x in s, prefixBesselVariance ((Nat.le_succ n).trans h) ell x
        ∂(Measure.pi (fun _ : Fin N ↦ mu)) := by
  let muN : Measure (Fin N → Z) := Measure.pi (fun _ : Fin N ↦ mu)
  have hs' : MeasurableSet s :=
    (measurableSet_prefixExchangeableSpace_iff.mp hs).1
  have hinv (r : Fin (n + 1)) :
      samplePermutation (horizonDeletionPermutation h r) ⁻¹' s = s := by
    exact (measurableSet_prefixExchangeableSpace_iff.mp hs).2
      (horizonDeletionPrefixPermutation h r)
  have hint (r : Fin (n + 1)) :
      Integrable
        (fun x : Fin N → Z ↦
          prefixBesselVariance ((Nat.le_succ n).trans h) ell
            (samplePermutation (horizonDeletionPermutation h r) x))
        (muN.restrict s) :=
    Integrable.of_finite
  calc
    ∫ x in s, prefixBesselVariance h ell x ∂muN =
        ∫ x in s,
          ((∑ r : Fin (n + 1),
              prefixBesselVariance ((Nat.le_succ n).trans h) ell
                (samplePermutation (horizonDeletionPermutation h r) x)) /
            (n + 1 : ℝ)) ∂muN := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (prefixBesselVariance_eq_average_horizonDeletion hn h ell)
    _ = (∑ r : Fin (n + 1),
          ∫ x in s,
            prefixBesselVariance ((Nat.le_succ n).trans h) ell
              (samplePermutation (horizonDeletionPermutation h r) x) ∂muN) /
          (n + 1 : ℝ) := by
            rw [integral_div]
            rw [integral_finsetSum Finset.univ (fun r _ ↦ hint r)]
    _ = (∑ _r : Fin (n + 1),
          ∫ x in s,
            prefixBesselVariance ((Nat.le_succ n).trans h) ell x ∂muN) /
          (n + 1 : ℝ) := by
            apply congrArg (fun z : ℝ ↦ z / (n + 1 : ℝ))
            refine Finset.sum_congr rfl (fun r _ ↦ ?_)
            exact setIntegral_comp_samplePermutation_eq mu
              (horizonDeletionPermutation h r)
              (prefixBesselVariance ((Nat.le_succ n).trans h) ell) hs' (hinv r)
    _ = ∫ x in s,
          prefixBesselVariance ((Nat.le_succ n).trans h) ell x ∂muN := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            have hne : (n + 1 : ℝ) ≠ 0 := by positivity
            norm_num [Nat.cast_add]
            exact mul_div_cancel_left₀ _ hne

/-- **Load-bearing reverse conditional-expectation step.**  Under a finite iid
product law, the Bessel variance of the first `n + 1` observations is the
conditional expectation of the Bessel variance of the first `n` observations
given the sigma algebra that forgets the order of the first `n + 1` values.

This one-step reverse identity is derived from leave-one-out algebra and
coordinate exchangeability; it is not a caller-supplied martingale
assumption. -/
theorem prefixBesselVariance_ae_eq_condExp [Fintype Z]
    [MeasurableSingletonClass Z] (mu : Measure Z) [IsProbabilityMeasure mu]
    {N n : ℕ} (hn : 2 ≤ n) (h : n + 1 ≤ N) (ell : Z → ℝ) :
    prefixBesselVariance h ell =ᵐ[Measure.pi (fun _ : Fin N ↦ mu)]
      condExp (prefixExchangeableSpace (Z := Z) N (n + 1))
        (Measure.pi (fun _ : Fin N ↦ mu))
        (prefixBesselVariance ((Nat.le_succ n).trans h) ell) := by
  let muN : Measure (Fin N → Z) := Measure.pi (fun _ : Fin N ↦ mu)
  haveI : IsProbabilityMeasure muN := by
    dsimp [muN]
    infer_instance
  have hsource : Integrable
      (prefixBesselVariance ((Nat.le_succ n).trans h) ell) muN :=
    Integrable.of_finite
  have hcandidate : Integrable (prefixBesselVariance h ell) muN :=
    Integrable.of_finite
  have hm := prefixExchangeableSpace_le (Z := Z) N (n + 1)
  change prefixBesselVariance h ell =ᵐ[muN]
    condExp (prefixExchangeableSpace (Z := Z) N (n + 1)) muN
      (prefixBesselVariance ((Nat.le_succ n).trans h) ell)
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hsource
    (fun _s _hs _hfinite ↦ hcandidate.integrableOn)
    (fun s hs _hfinite ↦ ?_)
    (measurable_prefixBesselVariance h ell).aestronglyMeasurable
  exact setIntegral_prefixBesselVariance_succ_eq mu hn h ell hs

end ExchangeableFiltration

end

end FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse
