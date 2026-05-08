import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import FormalSLT.Rademacher.FiniteSample

/-!
# Finite-sample symmetrization scaffolding

Builds on `FormalSLT.Rademacher.FiniteSample`. Provides
the combinatorial identities that power the symmetrization step in the
finite-sample Rademacher analysis, expressed entirely as finite uniform
averages over `Fin n → Bool` (no product measure, no `Measure ℝ`).

What this module provides (all closed, no `sorry`, no `admit`):

* `sum_signOfBool_smul_eq_zero` — for any real-valued `f : Fin n → ℝ`
  and any fixed coordinate `i`, `∑_σ signOfBool (σ i) * f i = 0`. The
  scalar generalization of `sum_signOfBool_eq_zero`.
* `sum_negateAll_eq_self` — for any real-valued `F : (Fin n → Bool) → ℝ`,
  `∑_σ F (negateAll σ) = ∑_σ F σ`. The full sign-flip is a bijection on
  the sign-vector cube, so reindexing leaves the sum invariant.
* `signOfBool_negateAll` — pointwise: `signOfBool (negateAll σ k) =
  -signOfBool (σ k)`.
* `finsetSup_sub_le_sup_add_sup_neg` — the triangle / decoupling
  inequality for `Finset.sup'` over a real-valued family of differences:
  `sup_i (a i - b i) ≤ sup_i (a i) + sup_i (-(b i))`.
* `finiteSampleSymmetrizationDecoupling` — the discrete-sample
  decoupling identity used in symmetrization:
  for any two samples `z, z' : Fin n → Z`, any loss family `ℓ : ι → Z → ℝ`,
  the σ-average of the sup of σ-weighted *differences* is bounded by the
  sum of two σ-averaged sup-of-σ-weighted single-sample terms.

Out of scope:

- Connection to a sampling probability measure on `Z` or to expectations
  over an iid product. That step makes this combinatorial bound a
  generalization-error symmetrization theorem; it is not part of this PR.
- The `(1/n)` averaging factor and tail-bound forms. Stated here without
  the `(1/n)` so that the algebraic structure is readable; rescale at use
  site.
- The contraction (Talagrand) and concentration steps that follow
  symmetrization in the standard Rademacher chain.
- Connection to `FormalSLT.Rademacher.oneSampleFiniteClassSymmetrization`,
  which uses a `Measure ℝ`-valued Rademacher distribution and integrals.
  The two are duplicates by design; an explicit pushforward identity
  linking them will land in a later PR.
-/

namespace FormalSLT.Rademacher.FiniteSampleSymmetrization

open Finset
open scoped BigOperators
open FormalSLT.Rademacher.FiniteSample

variable {n : ℕ}

/-! ### Scalar generalizations of the mean-zero identity -/

/-- For any real-valued `f`, the sum of `signOfBool (σ i) * f` over all
sign vectors is zero. Scalar generalization of `sum_signOfBool_eq_zero`. -/
lemma sum_signOfBool_smul_eq_zero (i : Fin n) (c : ℝ) :
    ∑ σ : Fin n → Bool, signOfBool (σ i) * c = 0 := by
  have h1 : ∀ σ : Fin n → Bool, signOfBool (σ i) * c = c * signOfBool (σ i) :=
    fun _ => mul_comm _ _
  simp_rw [h1]
  rw [← Finset.mul_sum, sum_signOfBool_eq_zero, mul_zero]

/-- Pointwise: `negateAll` flips the sign of `signOfBool` at every
coordinate. Direct corollary of `signOfBool_neg` and the definition of
`negateAll`. -/
@[simp] lemma signOfBool_negateAll (σ : Fin n → Bool) (k : Fin n) :
    signOfBool (negateAll σ k) = -signOfBool (σ k) := by
  simp [negateAll, signOfBool_neg]

/-! ### Reindexing under the negate-all involution -/

/-- For any real-valued `F : (Fin n → Bool) → ℝ`, summing `F` over all
sign vectors is invariant under the `negateAll` involution. -/
lemma sum_negateAll_eq_self (F : (Fin n → Bool) → ℝ) :
    ∑ σ : Fin n → Bool, F (negateAll σ) = ∑ σ : Fin n → Bool, F σ := by
  have h : ∑ σ : Fin n → Bool, F (negateAllEquiv σ) = ∑ σ : Fin n → Bool, F σ :=
    Equiv.sum_comp negateAllEquiv F
  simpa [negateAllEquiv_apply] using h

/-! ### Decoupling triangle inequality on `Finset.sup'` -/

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Triangle / decoupling bound for `Finset.sup'` of a real-valued
difference family: `sup_i (a i - b i) ≤ sup_i (a i) + sup_i (-(b i))`.

Proof: `a i - b i = a i + (-(b i)) ≤ sup a + sup (-b)` for every `i`,
so the sup over `i` is bounded by the same value. -/
lemma finsetSup_sub_le_sup_add_sup_neg (a b : ι → ℝ) :
    (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun i => a i - b i) ≤
      (Finset.univ : Finset ι).sup' Finset.univ_nonempty a +
      (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun i => -(b i)) := by
  apply Finset.sup'_le
  intro i _
  have ha : a i ≤
      (Finset.univ : Finset ι).sup' Finset.univ_nonempty a :=
    Finset.le_sup' a (Finset.mem_univ i)
  have hb : -(b i) ≤
      (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun j => -(b j)) :=
    Finset.le_sup' (f := fun j => -(b j)) (Finset.mem_univ i)
  have hsub : a i - b i = a i + -(b i) := sub_eq_add_neg _ _
  linarith

/-! ### Discrete-sample symmetrization decoupling -/

variable {Z : Type*}

/-- The σ-weighted empirical sum (no `1/n` rescaling): for a sign vector
`σ`, sample `z`, and loss `ℓ`, the inner product `∑_k signOfBool (σ k) · ℓ i (z k)`. -/
noncomputable def signedEmpiricalSum
    (ℓ : ι → Z → ℝ) (z : Fin n → Z) (σ : Fin n → Bool) (i : ι) : ℝ :=
  ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k)

set_option linter.unusedSectionVars false in
/-- Negating the sign vector negates the σ-weighted empirical sum:
`signedEmpiricalSum ℓ z (negateAll σ) i = -signedEmpiricalSum ℓ z σ i`. -/
lemma signedEmpiricalSum_negateAll
    (ℓ : ι → Z → ℝ) (z : Fin n → Z) (σ : Fin n → Bool) (i : ι) :
    signedEmpiricalSum ℓ z (negateAll σ) i = -signedEmpiricalSum ℓ z σ i := by
  simp only [signedEmpiricalSum, signOfBool_negateAll, neg_mul]
  rw [Finset.sum_neg_distrib]

/-- The σ-average of the sup over `ι` of the σ-weighted *single-sample*
sum is invariant under negating the sign vector applied to the loss
inside the sup. Concretely, for any sample `z` and loss `ℓ`:

`∑_σ sup_i (signedEmpiricalSum ℓ z σ i)
   = ∑_σ sup_i (-(signedEmpiricalSum ℓ z σ i))`.

Reindex `σ ↦ negateAll σ` and use the negation identity. -/
lemma sum_sup_signed_neg_eq_sum_sup_signed
    (ℓ : ι → Z → ℝ) (z : Fin n → Z) :
    ∑ σ : Fin n → Bool,
        (Finset.univ : Finset ι).sup' Finset.univ_nonempty
          (fun i => -(signedEmpiricalSum ℓ z σ i)) =
      ∑ σ : Fin n → Bool,
        (Finset.univ : Finset ι).sup' Finset.univ_nonempty
          (fun i => signedEmpiricalSum ℓ z σ i) := by
  -- Pointwise: sup_i (-signed σ i) = sup_i (signed (negateAll σ) i),
  -- because the inner functions agree pointwise via `signedEmpiricalSum_negateAll`.
  have h_pt : ∀ σ : Fin n → Bool,
      (Finset.univ : Finset ι).sup' Finset.univ_nonempty
        (fun i => -(signedEmpiricalSum ℓ z σ i)) =
      (Finset.univ : Finset ι).sup' Finset.univ_nonempty
        (fun i => signedEmpiricalSum ℓ z (negateAll σ) i) := by
    intro σ
    have h_funext : (fun i : ι => -(signedEmpiricalSum ℓ z σ i)) =
                    (fun i : ι => signedEmpiricalSum ℓ z (negateAll σ) i) := by
      funext i
      exact (signedEmpiricalSum_negateAll ℓ z σ i).symm
    rw [h_funext]
  -- Sum the pointwise equality, then reindex via the `negateAll` involution.
  rw [Finset.sum_congr rfl (fun σ _ => h_pt σ)]
  exact sum_negateAll_eq_self
    (fun τ => (Finset.univ : Finset ι).sup' Finset.univ_nonempty
      (fun i => signedEmpiricalSum ℓ z τ i))

/-- **Finite-sample symmetrization decoupling.** For any two samples
`z, z' : Fin n → Z` and any finite nonempty hypothesis class `ι`, the
σ-average of the sup of σ-weighted *differences* is bounded by the sum
of two σ-averaged sup-of-σ-weighted single-sample terms.

This is the purely combinatorial, no-measure step that the standard
"factor of 2" in the Rademacher symmetrization theorem comes from: the
right-hand side is twice the empirical Rademacher sum of `ℓ` against `z`
once we fold in `sum_sup_signed_neg_eq_sum_sup_signed` to identify the
two samples. Stated without the `1/n` rescaling so the algebraic
structure is visible. -/
theorem finiteSampleSymmetrizationDecoupling
    (ℓ : ι → Z → ℝ) (z z' : Fin n → Z) :
    ∑ σ : Fin n → Bool,
        (Finset.univ : Finset ι).sup' Finset.univ_nonempty
          (fun i => signedEmpiricalSum ℓ z σ i -
                    signedEmpiricalSum ℓ z' σ i) ≤
      ∑ σ : Fin n → Bool,
        (Finset.univ : Finset ι).sup' Finset.univ_nonempty
          (fun i => signedEmpiricalSum ℓ z σ i) +
      ∑ σ : Fin n → Bool,
        (Finset.univ : Finset ι).sup' Finset.univ_nonempty
          (fun i => -(signedEmpiricalSum ℓ z' σ i)) := by
  have h_pt : ∀ σ : Fin n → Bool,
      (Finset.univ : Finset ι).sup' Finset.univ_nonempty
          (fun i => signedEmpiricalSum ℓ z σ i -
                    signedEmpiricalSum ℓ z' σ i) ≤
        (Finset.univ : Finset ι).sup' Finset.univ_nonempty
            (fun i => signedEmpiricalSum ℓ z σ i) +
          (Finset.univ : Finset ι).sup' Finset.univ_nonempty
            (fun i => -(signedEmpiricalSum ℓ z' σ i)) := by
    intro σ
    exact finsetSup_sub_le_sup_add_sup_neg
      (fun i => signedEmpiricalSum ℓ z σ i)
      (fun i => signedEmpiricalSum ℓ z' σ i)
  -- Sum the pointwise bound and split the right-hand side.
  have h_sum :
      ∑ σ : Fin n → Bool,
          (Finset.univ : Finset ι).sup' Finset.univ_nonempty
            (fun i => signedEmpiricalSum ℓ z σ i -
                      signedEmpiricalSum ℓ z' σ i) ≤
        ∑ σ : Fin n → Bool,
          ((Finset.univ : Finset ι).sup' Finset.univ_nonempty
              (fun i => signedEmpiricalSum ℓ z σ i) +
            (Finset.univ : Finset ι).sup' Finset.univ_nonempty
              (fun i => -(signedEmpiricalSum ℓ z' σ i))) :=
    Finset.sum_le_sum (fun σ _ => h_pt σ)
  -- Split sum-of-add into add-of-sums.
  have h_split :
      ∑ σ : Fin n → Bool,
          ((Finset.univ : Finset ι).sup' Finset.univ_nonempty
              (fun i => signedEmpiricalSum ℓ z σ i) +
            (Finset.univ : Finset ι).sup' Finset.univ_nonempty
              (fun i => -(signedEmpiricalSum ℓ z' σ i))) =
        (∑ σ : Fin n → Bool,
            (Finset.univ : Finset ι).sup' Finset.univ_nonempty
              (fun i => signedEmpiricalSum ℓ z σ i)) +
          (∑ σ : Fin n → Bool,
            (Finset.univ : Finset ι).sup' Finset.univ_nonempty
              (fun i => -(signedEmpiricalSum ℓ z' σ i))) :=
    Finset.sum_add_distrib
  linarith

/-- **Finite-sample symmetrization "factor of 2" identity.** The σ-sum of
the sup-of-σ-weighted differences is bounded by *twice* the σ-sum of
the sup-of-σ-weighted single-sample term on `z` *plus* the σ-sum of
sup-of-σ-weighted single-sample term on `z'`. Combine the previous
decoupling with `sum_sup_signed_neg_eq_sum_sup_signed` to fold the
negative-z' term into a positive-z' term:

`∑_σ sup (σ ⋅ ℓ(z) - σ ⋅ ℓ(z'))
   ≤ ∑_σ sup (σ ⋅ ℓ(z)) + ∑_σ sup (σ ⋅ ℓ(z'))`. -/
theorem finiteSampleSymmetrizationFactorTwo
    (ℓ : ι → Z → ℝ) (z z' : Fin n → Z) :
    ∑ σ : Fin n → Bool,
        (Finset.univ : Finset ι).sup' Finset.univ_nonempty
          (fun i => signedEmpiricalSum ℓ z σ i -
                    signedEmpiricalSum ℓ z' σ i) ≤
      ∑ σ : Fin n → Bool,
        (Finset.univ : Finset ι).sup' Finset.univ_nonempty
          (fun i => signedEmpiricalSum ℓ z σ i) +
      ∑ σ : Fin n → Bool,
        (Finset.univ : Finset ι).sup' Finset.univ_nonempty
          (fun i => signedEmpiricalSum ℓ z' σ i) := by
  have h_decouple := finiteSampleSymmetrizationDecoupling ℓ z z'
  have h_neg_eq := sum_sup_signed_neg_eq_sum_sup_signed (n := n) (ι := ι) ℓ z'
  linarith

end FormalSLT.Rademacher.FiniteSampleSymmetrization
