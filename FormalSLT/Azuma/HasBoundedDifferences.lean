import FormalSLT.Azuma.BoundedDifferences

/-!
# `HasBoundedDifferences`: abstract predicate for bounded coordinate sensitivity

Stage B sub-PR 2b of `docs/plans/mcdiarmid-rademacher-plan.md`.

This module packages the bounded-coordinate-sensitivity property of a
real-valued function on `Fin n → Z` as a stand-alone Prop predicate.
It is the **abstract input** that the eventual McDiarmid concentration
bridge (PR B3) will consume; the concrete predicate witness for
`genGap` is supplied here so that downstream PRs need not re-thread
the loss-class hypotheses.

Contents (all closed; no `sorry`, no `admit`, no custom `axiom`):

* `HasBoundedDifferences f c`: the predicate
  `∀ S k z', |f S - f (Function.update S k z')| ≤ c k`. The bound is
  per-coordinate (a `Fin n → ℝ` family of widths `c k`), matching the
  shape mathlib's Azuma-Hoeffding / McDiarmid consumers expect.
* `HasBoundedDifferences.symm`: the absolute value is symmetric in
  `S` and the updated point. A trivial corollary, but exposing it
  gives downstream proofs a directional rewrite.
* `HasBoundedDifferences.mono`: if `f` has bounded differences with
  width `c` and `c i ≤ c' i` pointwise, then `f` has bounded
  differences with width `c'`. Useful when the McDiarmid consumer
  prefers a uniform width `max c i`.
* `HasBoundedDifferences.neg`: negating a statistic preserves the same
  bounded-differences widths.
* `HasBoundedDifferences.const_width`: specialization to a constant
  width `c : ℝ` — i.e. all coordinates have the same Lipschitz
  constant.
* `genGap_hasBoundedDifferences`: the `genGap` functional from
  `BoundedDifferences.lean` satisfies `HasBoundedDifferences` with
  `c k = 2 B / n` whenever the loss class is uniformly bounded by
  `B`. This is the McDiarmid analytic input expressed as the abstract
  predicate; the concrete witness is `abs_genGap_update_le_of_bdd`.

Deliberately **not** in scope here (deferred to PR B2c):

* Prefix/tail integral representation of the exposure martingale,
  `M_k S =ᵐ ∫ tail, f (prefix S k, tail) dμ_tail`.
* Conditional Hoeffding lemma, lifting unconditional Hoeffding to
  produce `HasCondSubgaussianMGF` from bounded-coord sensitivity.
* `Filtration ℕ` adapter so mathlib's `Filtration ℕ`-indexed
  Azuma-Hoeffding can consume our `Fin (n+1)`-indexed
  `coordinateFiltration`.
* `StandardBorelSpace Z` typeclass restriction (mathlib's
  `condExpKernel` Martingale section opens with that hypothesis).

Constraints respected:

* No `sorry`, no `admit`, no custom `axiom`. All lemmas close.
* No concentration claim, no high-probability claim, no McDiarmid
  claim. The strongest statement here is a Prop-valued repackaging of
  Stage A's `abs_genGap_update_le_of_bdd`.
* No manifest entry. No `/lean` dashboard update.
-/

namespace FormalSLT.Azuma.BoundedDifferences

open FormalSLT.GhostSample

variable {Z : Type*}

/-- `HasBoundedDifferences f c` says that `f : (Fin n → Z) → ℝ` changes
by at most `c k` when its `k`-th coordinate is replaced by an arbitrary
new value. This is the per-coordinate bounded-differences property in
the form that mathlib's Azuma-Hoeffding / McDiarmid consumers expect. -/
def HasBoundedDifferences {n : ℕ} (f : (Fin n → Z) → ℝ) (c : Fin n → ℝ) : Prop :=
  ∀ S : Fin n → Z, ∀ k : Fin n, ∀ z' : Z,
    |f S - f (Function.update S k z')| ≤ c k

namespace HasBoundedDifferences

variable {n : ℕ} {f : (Fin n → Z) → ℝ} {c c' : Fin n → ℝ}

/-- The absolute value in `HasBoundedDifferences` is symmetric in the
two sample points. Useful for directional rewrites on the consumer
side. -/
lemma symm (h : HasBoundedDifferences f c) (S : Fin n → Z) (k : Fin n) (z' : Z) :
    |f (Function.update S k z') - f S| ≤ c k := by
  rw [abs_sub_comm]
  exact h S k z'

/-- Monotonicity in the width family: if `c i ≤ c' i` for every
coordinate, the bounded-differences property carries over. -/
lemma mono (h : HasBoundedDifferences f c) (hcc' : ∀ k, c k ≤ c' k) :
    HasBoundedDifferences f c' :=
  fun S k z' => (h S k z').trans (hcc' k)

/-- Negating the statistic preserves the same coordinate sensitivity. -/
lemma neg (h : HasBoundedDifferences f c) :
    HasBoundedDifferences (fun S => -f S) c := by
  intro S k z'
  simpa only [Pi.neg_apply, neg_sub_neg] using h.symm S k z'

/-- A constant-width version: if `f` has bounded differences with
per-coordinate widths `c` and every `c k ≤ C`, then `f` has bounded
differences with the constant width `fun _ => C`. -/
lemma const_width (h : HasBoundedDifferences f c) {C : ℝ} (hC : ∀ k, c k ≤ C) :
    HasBoundedDifferences f (fun _ => C) :=
  h.mono hC

/-- Two-sample form: if `S` and `S'` agree on every coordinate except
`k`, then `|f S - f S'| ≤ c k`. This is the "agree-off-coordinate"
form of bounded differences used by Boucheron-Lugosi-Massart's textbook
statement of McDiarmid's inequality. -/
lemma sub_le_of_agree_off (h : HasBoundedDifferences f c)
    {S S' : Fin n → Z} {k : Fin n}
    (hagree : ∀ i, i ≠ k → S i = S' i) :
    |f S - f S'| ≤ c k := by
  -- `S'` equals `Function.update S k (S' k)` since they agree off `k`.
  have hS' : S' = Function.update S k (S' k) := by
    funext i
    by_cases hi : i = k
    · subst hi; rw [Function.update_self]
    · rw [Function.update_of_ne hi]
      exact (hagree i hi).symm
  rw [hS']
  exact h S k (S' k)

end HasBoundedDifferences

/-! ### `genGap` as a bounded-differences functional

Stage A's `abs_genGap_update_le_of_bdd` packages the
bounded-coordinate-sensitivity of the generalization-gap functional
`genGap` over a finite, nonempty, uniformly-bounded loss class. We
re-state it here as a `HasBoundedDifferences` witness so that
downstream PRs (the McDiarmid bridge in PR B3) can consume the
abstract predicate without re-threading the loss-class hypotheses. -/

lemma genGap_hasBoundedDifferences
    {ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace Z]
    (μ : MeasureTheory.Measure Z) (ℓ : ι → Z → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n) :
    HasBoundedDifferences (fun S : Fin n → Z => genGap μ ℓ S)
      (fun _ : Fin n => 2 * B / n) :=
  fun S k z' => abs_genGap_update_le_of_bdd μ ℓ hB hℓ_bdd hn S k z'

end FormalSLT.Azuma.BoundedDifferences
