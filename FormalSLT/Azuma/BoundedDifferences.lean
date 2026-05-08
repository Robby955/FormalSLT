import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import FormalSLT.Risk
import FormalSLT.GhostSample

/-!
# Bounded-coordinate sensitivity of the generalization gap (Stage A of
McDiarmid → high-probability Rademacher uniform deviation)

This module proves that the generalization-gap functional `genGap` over a
finite, nonempty hypothesis class with uniformly bounded loss is
Lipschitz in each coordinate of the sample, with Lipschitz constant
`2 B / n`. This is the *bounded-differences* analytic input to
McDiarmid's inequality.

What this module provides (all closed; no `sorry`, no `admit`, no
custom `axiom`):

* `abs_sup'_sub_sup'_le_sup'_abs_sub` — pure order/algebra fact: the
  `Finset.sup'` is Lipschitz in the underlying function.
* `empiricalRisk_update_sub` — exact identity for the change in
  `Risk.empiricalRisk` under a single-coordinate update.
* `abs_empiricalRisk_update_le_of_bdd` — bounded-loss corollary of the
  previous identity: `|R̂_{update S k z'}(ℓ_i) - R̂_S(ℓ_i)| ≤ 2 B / n`.
* `abs_genGap_update_le_of_bdd` — bounded-coordinate sensitivity of
  the generalization gap: `|genGap μ ℓ S - genGap μ ℓ (update S k z')| ≤
  2 B / n`. The McDiarmid analytic input.

What this module does **not** provide:

* No measure-theoretic argument (Stage A is purely algebraic).
* No martingale, sub-Gaussian, or concentration inequality. McDiarmid's
  inequality itself, the Azuma-Hoeffding bridge, and the
  high-probability Rademacher tail are deferred to Stages B and C of
  `docs/plans/mcdiarmid-rademacher-plan.md`.
* No manifest entry. The Lean evidence dashboard is unchanged by this
  module; nothing here is publicly advertised as verified beyond what
  the docstring asserts. Manifest exposure is gated on Stage D of the
  plan, which closes the high-probability theorem itself.
-/

namespace FormalSLT.Azuma.BoundedDifferences

open scoped BigOperators

variable {ι Z : Type*}

/-! ### Sup' Lipschitz inequality

This is a pure order/lattice fact in `ℝ`. It is needed because `genGap`
is a `Finset.sup'` of pointwise differences, and the bounded-differences
property must propagate through the sup. -/

lemma abs_sup'_sub_sup'_le_sup'_abs_sub
    {α : Type*} (s : Finset α) (hs : s.Nonempty) (f g : α → ℝ) :
    |s.sup' hs f - s.sup' hs g| ≤ s.sup' hs (fun i => |f i - g i|) := by
  -- Forward direction: sup' f ≤ sup' g + sup' |f - g|.
  have h_fg : s.sup' hs f ≤ s.sup' hs g + s.sup' hs (fun i => |f i - g i|) := by
    refine Finset.sup'_le hs _ (fun i hi => ?_)
    have h_diff_le_abs : f i - g i ≤ |f i - g i| := le_abs_self _
    have h_g_le : g i ≤ s.sup' hs g := Finset.le_sup' g hi
    have h_abs_le : |f i - g i| ≤ s.sup' hs (fun j => |f j - g j|) :=
      Finset.le_sup' (fun j => |f j - g j|) hi
    linarith
  -- Reverse direction: sup' g ≤ sup' f + sup' |f - g|.
  have h_gf : s.sup' hs g ≤ s.sup' hs f + s.sup' hs (fun i => |f i - g i|) := by
    refine Finset.sup'_le hs _ (fun i hi => ?_)
    have h_diff_le_abs : g i - f i ≤ |g i - f i| := le_abs_self _
    have h_swap : |g i - f i| = |f i - g i| := abs_sub_comm _ _
    have h_f_le : f i ≤ s.sup' hs f := Finset.le_sup' f hi
    have h_abs_le : |f i - g i| ≤ s.sup' hs (fun j => |f j - g j|) :=
      Finset.le_sup' (fun j => |f j - g j|) hi
    linarith [h_diff_le_abs, h_swap, h_f_le, h_abs_le]
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-! ### Bounded-coordinate sensitivity of `empiricalRisk`

Single-coordinate update `S ↦ Function.update S k z'` changes the
empirical risk of hypothesis `i` by exactly `(ℓ i z' - ℓ i (S k)) / n`.
Pure arithmetic on `Finset.sum`. -/

lemma empiricalRisk_update_sub
    {n : ℕ} (S : Fin n → Z) (k : Fin n) (z' : Z) (ℓ : ι → Z → ℝ) (i : ι) :
    Risk.empiricalRisk (Function.update S k z') ℓ i - Risk.empiricalRisk S ℓ i
      = (n : ℝ)⁻¹ * (ℓ i z' - ℓ i (S k)) := by
  unfold Risk.empiricalRisk
  rw [← mul_sub]
  congr 1
  -- Goal: ∑ j, ℓ i (update S k z' j) - ∑ j, ℓ i (S j) = ℓ i z' - ℓ i (S k)
  -- Split each sum at the index `k` using `Finset.add_sum_erase`.
  have h1 :
      ℓ i (Function.update S k z' k)
        + ∑ j ∈ (Finset.univ : Finset (Fin n)).erase k,
            ℓ i (Function.update S k z' j)
        = ∑ j, ℓ i (Function.update S k z' j) :=
    Finset.add_sum_erase (Finset.univ : Finset (Fin n))
      (fun j => ℓ i (Function.update S k z' j)) (Finset.mem_univ k)
  have h2 :
      ℓ i (S k)
        + ∑ j ∈ (Finset.univ : Finset (Fin n)).erase k, ℓ i (S j)
        = ∑ j, ℓ i (S j) :=
    Finset.add_sum_erase (Finset.univ : Finset (Fin n))
      (fun j => ℓ i (S j)) (Finset.mem_univ k)
  rw [← h1, ← h2, Function.update_self]
  -- The two `erase`-sums are equal: at each `j ≠ k`, the update is a no-op.
  have h_sum_eq :
      ∑ j ∈ (Finset.univ : Finset (Fin n)).erase k, ℓ i (Function.update S k z' j)
        = ∑ j ∈ (Finset.univ : Finset (Fin n)).erase k, ℓ i (S j) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [h_sum_eq]
  ring

/-- Bounded-loss corollary: a single-coordinate update changes the
empirical risk by at most `2 B / n`. -/
lemma abs_empiricalRisk_update_le_of_bdd
    {n : ℕ} (hn : 0 < n) (S : Fin n → Z) (k : Fin n) (z' : Z)
    (ℓ : ι → Z → ℝ) (i : ι) {B : ℝ}
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B) :
    |Risk.empiricalRisk (Function.update S k z') ℓ i
        - Risk.empiricalRisk S ℓ i| ≤ 2 * B / n := by
  rw [empiricalRisk_update_sub S k z' ℓ i]
  rw [abs_mul]
  have h_n_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_n_inv_nonneg : (0 : ℝ) ≤ (n : ℝ)⁻¹ := le_of_lt (inv_pos.mpr h_n_pos)
  have h_abs_inv : |((n : ℝ)⁻¹)| = (n : ℝ)⁻¹ := abs_of_nonneg h_n_inv_nonneg
  rw [h_abs_inv]
  have h_diff_bound : |ℓ i z' - ℓ i (S k)| ≤ 2 * B := by
    calc |ℓ i z' - ℓ i (S k)|
        ≤ |ℓ i z'| + |ℓ i (S k)| := abs_sub _ _
      _ ≤ B + B := add_le_add (hℓ_bdd i z') (hℓ_bdd i (S k))
      _ = 2 * B := by ring
  have h_target : (n : ℝ)⁻¹ * |ℓ i z' - ℓ i (S k)| ≤ (n : ℝ)⁻¹ * (2 * B) :=
    mul_le_mul_of_nonneg_left h_diff_bound h_n_inv_nonneg
  calc (n : ℝ)⁻¹ * |ℓ i z' - ℓ i (S k)|
      ≤ (n : ℝ)⁻¹ * (2 * B) := h_target
    _ = 2 * B / n := by
        field_simp

/-! ### Bounded-coordinate sensitivity of `genGap`

The McDiarmid analytic input. Combines the sup' Lipschitz lemma with
the bounded-loss empiricalRisk bound. -/

open FormalSLT.GhostSample
  (genGap)

set_option linter.unusedVariables false in
/-- Bounded-coordinate sensitivity of the generalization-gap functional.
Changing one coordinate of the sample `S` changes `genGap` by at most
`2 B / n`. This is the analytic input to McDiarmid's inequality.

Stage A. Pure algebra; no measure theory beyond what `Risk.risk` already
requires for its definition.

The hypothesis `hB : 0 ≤ B` is kept in the public signature for spec
clarity (the bound `2 * B / n` is only meaningful for non-negative `B`);
the proof itself derives non-negativity from `hℓ_bdd`, so the explicit
hypothesis is not needed in the body. -/
lemma abs_genGap_update_le_of_bdd
    [Fintype ι] [Nonempty ι] [MeasurableSpace Z]
    (μ : MeasureTheory.Measure Z) (ℓ : ι → Z → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n) (S : Fin n → Z) (k : Fin n) (z' : Z) :
    |genGap μ ℓ S - genGap μ ℓ (Function.update S k z')| ≤ 2 * B / n := by
  -- Step 1: rewrite genGap as a Finset.sup'.
  unfold genGap
  -- Step 2: apply the sup' Lipschitz lemma.
  refine (abs_sup'_sub_sup'_le_sup'_abs_sub
    (Finset.univ : Finset ι) Finset.univ_nonempty
    (fun i => Risk.risk μ ℓ i - Risk.empiricalRisk S ℓ i)
    (fun i => Risk.risk μ ℓ i - Risk.empiricalRisk (Function.update S k z') ℓ i)).trans ?_
  -- Step 3: each pointwise difference is bounded by 2B/n.
  refine Finset.sup'_le _ _ (fun i _ => ?_)
  -- The pointwise difference simplifies to
  -- |R̂_{update}(i) - R̂_S(i)|, which is bounded by 2B/n.
  have h_simp :
      |(Risk.risk μ ℓ i - Risk.empiricalRisk S ℓ i)
        - (Risk.risk μ ℓ i - Risk.empiricalRisk (Function.update S k z') ℓ i)|
      = |Risk.empiricalRisk (Function.update S k z') ℓ i
          - Risk.empiricalRisk S ℓ i| := by
    congr 1
    ring
  rw [h_simp]
  exact abs_empiricalRisk_update_le_of_bdd hn S k z' ℓ i hℓ_bdd

end FormalSLT.Azuma.BoundedDifferences
