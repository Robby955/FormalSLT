import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite-sample Rademacher machinery

Sign-vector machinery for the finite-sample Rademacher symmetrization story.
This module deliberately avoids the product-measure abstraction
(`Measure.pi`, `MeasureTheory.Integral.Pi`). Instead, the "Rademacher
expectation" is realized as a finite uniform average over the discrete
function space `Fin n → Bool`, with `2^n` elements.

What this module provides (all closed, no `sorry`, no `admit`):

* `signOfBool : Bool → ℝ` with `false ↦ -1`, `true ↦ +1`, plus basic
  identities (`signOfBool_neg`, `signOfBool_sq`, `abs_signOfBool`).
* `flipAt i : (Fin n → Bool) → (Fin n → Bool)` and its `Equiv.Perm`
  packaging `flipAtEquiv i`. The map flips the `i`-th coordinate and
  fixes all others; involutive, hence a permutation of sign vectors.
* `negateAll : (Fin n → Bool) → (Fin n → Bool)` and its `Equiv.Perm`
  packaging `negateAllEquiv`. Negates every coordinate; also involutive.
* `sum_signOfBool_eq_zero` — for any fixed coordinate `i`, the sum of
  `signOfBool (σ i)` over all sign vectors is zero. This is the discrete
  analogue of "the Rademacher mean is zero" without invoking any
  measure-theoretic abstraction.
* `empiricalRademacherComplexity` — the standard definition for a finite
  hypothesis class indexed by `[Fintype ι] [Nonempty ι]`, sample size
  `n`, loss `ℓ`, and sample `z : Fin n → Z`. Realized as the finite
  average over `(Fin n → Bool)` of the sup over `ι` of the σ-weighted
  empirical mean.
* `card_signVectors` — `|Fin n → Bool| = 2^n`.

Out of scope for this module:

- Symmetrization theorem (`E_S sup_h (R - R̂_S) ≤ 2 E_S R̂Rad_S`). The
  next layer.
- Scaling / monotonicity / contraction lemmas for empirical Rademacher
  complexity. Add as needed when the symmetrization theorem is built.
- Connection to the existing `FormalSLT.Rademacher`
  measure-theoretic scaffolding (`Measure ℝ`-valued
  `rademacherMeasure`). The two are duplicates by design: one finite
  combinatorial, one measure-theoretic. They will eventually be linked
  by an explicit pushforward identity, but not in this PR.
-/

namespace FormalSLT.Rademacher.FiniteSample

open Finset
open scoped BigOperators

/-! ### Sign of a Boolean -/

/-- Rademacher sign of a Boolean: `false ↦ -1`, `true ↦ +1`. -/
def signOfBool : Bool → ℝ
  | false => -1
  | true  => 1

@[simp] lemma signOfBool_false : signOfBool false = -1 := rfl
@[simp] lemma signOfBool_true  : signOfBool true  = 1  := rfl

lemma signOfBool_neg (b : Bool) : signOfBool (!b) = -signOfBool b := by
  cases b <;> simp [signOfBool]

lemma signOfBool_sq (b : Bool) : signOfBool b * signOfBool b = 1 := by
  cases b <;> simp [signOfBool]

lemma abs_signOfBool (b : Bool) : |signOfBool b| = 1 := by
  cases b <;> simp [signOfBool]

/-! ### Coordinate flip on sign vectors -/

variable {n : ℕ}

/-- Flip the `i`-th coordinate of a sign vector; fix all others. -/
def flipAt (i : Fin n) (σ : Fin n → Bool) : Fin n → Bool :=
  fun k => if k = i then !σ k else σ k

@[simp] lemma flipAt_same (i : Fin n) (σ : Fin n → Bool) :
    flipAt i σ i = !σ i := by
  simp [flipAt]

lemma flipAt_other (i : Fin n) (σ : Fin n → Bool) {k : Fin n} (hk : k ≠ i) :
    flipAt i σ k = σ k := by
  simp [flipAt, hk]

lemma flipAt_involutive (i : Fin n) :
    Function.Involutive (flipAt i : (Fin n → Bool) → (Fin n → Bool)) := by
  intro σ
  funext k
  by_cases hk : k = i
  · subst hk; simp [flipAt]
  · simp [flipAt, hk]

/-- `flipAt i` packaged as an `Equiv.Perm` on sign vectors. -/
def flipAtEquiv (i : Fin n) : Equiv.Perm (Fin n → Bool) :=
  Function.Involutive.toPerm (flipAt i) (flipAt_involutive i)

@[simp] lemma flipAtEquiv_apply (i : Fin n) (σ : Fin n → Bool) :
    flipAtEquiv i σ = flipAt i σ := rfl

/-! ### Negate-all (full sign flip) -/

/-- Negate every coordinate of a sign vector. -/
def negateAll (σ : Fin n → Bool) : Fin n → Bool := fun k => !σ k

@[simp] lemma negateAll_apply (σ : Fin n → Bool) (k : Fin n) :
    negateAll σ k = !σ k := rfl

lemma negateAll_involutive :
    Function.Involutive (negateAll : (Fin n → Bool) → (Fin n → Bool)) := by
  intro σ
  funext k
  simp [negateAll]

/-- `negateAll` packaged as an `Equiv.Perm` on sign vectors. -/
def negateAllEquiv : Equiv.Perm (Fin n → Bool) :=
  Function.Involutive.toPerm negateAll negateAll_involutive

@[simp] lemma negateAllEquiv_apply (σ : Fin n → Bool) :
    negateAllEquiv σ = negateAll σ := rfl

/-! ### Cardinality and sign-symmetry -/

/-- Cardinality of the sign-vector type: `|Fin n → Bool| = 2^n`. -/
lemma card_signVectors :
    Fintype.card (Fin n → Bool) = 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- Sum of `signOfBool (σ i)` over all sign vectors is zero, for any fixed
coordinate `i`. The pairing `σ ↔ flipAt i σ` swaps the contribution at
coordinate `i` and leaves all others fixed; the swapped sum equals the
negation of the original. -/
lemma sum_signOfBool_eq_zero (i : Fin n) :
    ∑ σ : Fin n → Bool, signOfBool (σ i) = 0 := by
  set f : (Fin n → Bool) → ℝ := fun σ => signOfBool (σ i) with hf_def
  -- Reindex by the involution flipAt i.
  have h_reindex : ∑ σ, f (flipAtEquiv i σ) = ∑ σ, f σ :=
    Equiv.sum_comp (flipAtEquiv i) f
  -- Compute f ∘ flipAtEquiv i = -f pointwise.
  have h_neg : ∀ σ, f (flipAtEquiv i σ) = -f σ := by
    intro σ
    simp only [hf_def, flipAtEquiv_apply, flipAt_same, signOfBool_neg]
  -- Substitute the pointwise identity into the reindex equation.
  have h_sum_neg :
      ∑ σ : Fin n → Bool, f (flipAtEquiv i σ) =
        ∑ σ : Fin n → Bool, -f σ :=
    Finset.sum_congr rfl (fun σ _ => h_neg σ)
  -- Combine: ∑ f σ = -∑ f σ, hence ∑ f σ = 0.
  have h_eq : ∑ σ : Fin n → Bool, f σ = -∑ σ : Fin n → Bool, f σ := by
    have := h_reindex.symm.trans h_sum_neg
    rw [Finset.sum_neg_distrib] at this
    exact this
  linarith [h_eq]

/-! ### Empirical Rademacher complexity -/

variable {ι Z : Type*} [Fintype ι] [Nonempty ι]

/-- Empirical Rademacher complexity of a finite hypothesis class on a
sample of size `n`. The discrete uniform average over all sign vectors
`σ : Fin n → Bool` of the sup over `ι` of `(1/n) ∑_k σ_k · ℓ_i(z_k)`.

For `n = 0` the inner sum is empty and the (1/n) factor evaluates to
`0`, so the value is `0`; this is consistent with the convention used in
the empirical-process literature. -/
noncomputable def empiricalRademacherComplexity
    (ℓ : ι → Z → ℝ) (z : Fin n → Z) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ *
    ∑ σ : Fin n → Bool,
      (Finset.univ : Finset ι).sup' Finset.univ_nonempty
        (fun i => (n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k))

/-- The leading averaging factor `(2^n)⁻¹` is strictly positive in `ℝ`. -/
lemma two_pow_inv_pos : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by
  apply inv_pos.mpr
  exact pow_pos (by norm_num : (0 : ℝ) < 2) n

end FormalSLT.Rademacher.FiniteSample
