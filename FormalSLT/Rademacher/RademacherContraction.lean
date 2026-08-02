import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import FormalSLT.Rademacher.FiniteSample

/-!
# Finite-sample scalar Rademacher contraction

Finite, scalar-valued contraction lemmas for the combinatorial empirical
Rademacher complexity in `FormalSLT.Rademacher.FiniteSample`.

The results here are deliberately finite-sample and finite-class: the sample
is indexed by `Fin n`, the hypothesis class by a finite nonempty type `ι`, and
the functions are real-valued. They are not a formalization of the full
Talagrand contraction theorem for arbitrary processes.

**Comparison Lemma.** For any `u, a, b : ι → ℝ` with `ι` finite nonempty,
if `|a i - a j| ≤ |b i - b j|` for all `i, j`, then:

  `sup'(u + a) + sup'(u - a) ≤ sup'(u + b) + sup'(u - b)`
-/

namespace FormalSLT.Rademacher.RademacherContraction

open Finset
open scoped BigOperators
open FormalSLT.Rademacher.FiniteSample

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **Comparison lemma.** If `a` is a contraction of `b` in the pairwise
distance sense (`|a i - a j| ≤ |b i - b j|` for all `i, j`), then
`sup'(u + a) + sup'(u - a) ≤ sup'(u + b) + sup'(u - b)`.

The proof extracts maximizers `i*` of `u + a` and `j*` of `u - a`, uses
`a i* - a j* ≤ |a i* - a j*| ≤ |b i* - b j*|`, then case-splits on the
sign of `b i* - b j*` to bound by `sup'(u + b) + sup'(u - b)`. -/
theorem comparison_lemma (u a b : ι → ℝ)
    (h_contract : ∀ i j : ι, |a i - a j| ≤ |b i - b j|) :
    Finset.univ.sup' Finset.univ_nonempty (fun i => u i + a i) +
      Finset.univ.sup' Finset.univ_nonempty (fun i => u i - a i)
    ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => u i + b i) +
      Finset.univ.sup' Finset.univ_nonempty (fun i => u i - b i) := by
  -- Extract maximizers.
  obtain ⟨i_star, _, hi_star⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => u i + a i)
  obtain ⟨j_star, _, hj_star⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => u i - a i)
  -- LHS = (u i* + a i*) + (u j* - a j*).
  have h_lhs : Finset.univ.sup' Finset.univ_nonempty (fun i => u i + a i) +
      Finset.univ.sup' Finset.univ_nonempty (fun i => u i - a i)
    = (u i_star + a i_star) + (u j_star - a j_star) := by
    rw [hi_star, hj_star]
  rw [h_lhs]
  -- Bound: a i* - a j* ≤ |a i* - a j*| ≤ |b i* - b j*|
  have h_abs_bound : a i_star - a j_star ≤ |b i_star - b j_star| :=
    (le_abs_self _).trans (h_contract i_star j_star)
  -- RHS bounds from sup' membership.
  have h_ub1 : u i_star + b i_star ≤
      Finset.univ.sup' Finset.univ_nonempty (fun i => u i + b i) :=
    Finset.le_sup' (fun i => u i + b i) (Finset.mem_univ i_star)
  have h_ub2 : u j_star - b j_star ≤
      Finset.univ.sup' Finset.univ_nonempty (fun i => u i - b i) :=
    Finset.le_sup' (fun i => u i - b i) (Finset.mem_univ j_star)
  have h_ub3 : u i_star - b i_star ≤
      Finset.univ.sup' Finset.univ_nonempty (fun i => u i - b i) :=
    Finset.le_sup' (fun i => u i - b i) (Finset.mem_univ i_star)
  have h_ub4 : u j_star + b j_star ≤
      Finset.univ.sup' Finset.univ_nonempty (fun i => u i + b i) :=
    Finset.le_sup' (fun i => u i + b i) (Finset.mem_univ j_star)
  -- Case split on sign of b i* - b j*.
  by_cases h_case : b j_star ≤ b i_star
  · -- Case 1: b i* ≥ b j*. Then |b i* - b j*| = b i* - b j*.
    have h_abs_eq : |b i_star - b j_star| = b i_star - b j_star :=
      abs_of_nonneg (sub_nonneg.mpr h_case)
    linarith
  · -- Case 2: b i* < b j*. Then |b i* - b j*| = b j* - b i*.
    have h_lt : b i_star < b j_star := not_le.mp h_case
    have h_abs_eq : |b i_star - b j_star| = b j_star - b i_star := by
      rw [abs_of_neg (sub_neg.mpr h_lt)]; ring
    linarith

/-- Scaled version: if `|a i - a j| ≤ |b i - b j|`, then for `c ≥ 0`:
`sup'(u + c*a) + sup'(u - c*a) ≤ sup'(u + c*b) + sup'(u - c*b)`. -/
theorem comparison_lemma_scaled (u a b : ι → ℝ) {c : ℝ} (_hc : 0 ≤ c)
    (h_contract : ∀ i j : ι, |a i - a j| ≤ |b i - b j|) :
    Finset.univ.sup' Finset.univ_nonempty (fun i => u i + c * a i) +
      Finset.univ.sup' Finset.univ_nonempty (fun i => u i - c * a i)
    ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => u i + c * b i) +
      Finset.univ.sup' Finset.univ_nonempty (fun i => u i - c * b i) := by
  apply comparison_lemma u (fun i => c * a i) (fun i => c * b i)
  intro i j
  show |c * a i - c * a j| ≤ |c * b i - c * b j|
  rw [show c * a i - c * a j = c * (a i - a j) by ring,
      show c * b i - c * b j = c * (b i - b j) by ring,
      abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (h_contract i j) (abs_nonneg c)

/-! ## One-step contraction

For a single coordinate `j`, we show that replacing `f_i(z_j)` with
`φ(f_i(z_j))` (same φ for all hypotheses) does not increase the
sign-averaged sup, using the flipAt pairing and the comparison lemma.

The key identity: for each σ with σ j = true, the pair (σ, flipAt j σ)
gives signOfBool(σ j) = 1 and signOfBool(flipAt j σ j) = -1, while
all other coordinates agree. So the paired sup is exactly in the form
needed by the comparison lemma.
-/

variable {n : ℕ} {Z : Type*}

/-- For any `g : (Fin n → Bool) → ℝ` and involution `e` on sign vectors,
the sum is preserved: `∑ σ, g (e σ) = ∑ σ, g σ`. -/
lemma sum_equiv_perm (g : (Fin n → Bool) → ℝ) (e : Equiv.Perm (Fin n → Bool)) :
    ∑ σ : Fin n → Bool, g (e σ) = ∑ σ : Fin n → Bool, g σ :=
  Equiv.sum_comp e g

/-- **One-step contraction inequality.** For a fixed coordinate `j` and
a 1-Lipschitz function `φ` (same φ for all hypotheses):

  `∑_σ sup'_i(Σ_k σ_k · g^j_i(z_k)) ≤ ∑_σ sup'_i(Σ_k σ_k · f_i(z_k))`

where `g^j` agrees with `f` except at coordinate `j`, where it uses `φ(f_i(z_j))`.

The proof pairs sign vectors via `flipAt j`: for each pair (σ, flipAt j σ),
the comparison lemma gives the pointwise inequality on paired sups, and
summing over all pairs gives the inequality on the full sign-vector sum. -/
theorem one_step_contraction {φ : ℝ → ℝ}
    (hφ_lip : ∀ s t : ℝ, |φ s - φ t| ≤ |s - t|)
    (f : ι → Z → ℝ) (z : Fin n → Z) (j : Fin n) :
    ∑ σ : Fin n → Bool,
        Finset.univ.sup' Finset.univ_nonempty
          (fun i => ∑ k : Fin n, signOfBool (σ k) *
            if k = j then φ (f i (z k)) else f i (z k))
    ≤ ∑ σ : Fin n → Bool,
        Finset.univ.sup' Finset.univ_nonempty
          (fun i => ∑ k : Fin n, signOfBool (σ k) * f i (z k)) := by
  -- Normalize: when k = j, z k = z j, so φ(f i (z k)) = φ(f i (z j)).
  have h_if_norm : ∀ (i : ι) (k : Fin n),
      (if k = j then φ (f i (z k)) else f i (z k)) =
      (if k = j then φ (f i (z j)) else f i (z k)) := by
    intro i k; by_cases h : k = j <;> simp [h]
  simp_rw [h_if_norm]
  -- Now the LHS uses φ(f i (z j)) uniformly.
  set F_φ : (Fin n → Bool) → ℝ := fun σ =>
    Finset.univ.sup' Finset.univ_nonempty
      (fun i => ∑ k : Fin n, signOfBool (σ k) *
        if k = j then φ (f i (z j)) else f i (z k))
  set F : (Fin n → Bool) → ℝ := fun σ =>
    Finset.univ.sup' Finset.univ_nonempty
      (fun i => ∑ k : Fin n, signOfBool (σ k) * f i (z k))

  -- Key: ∑_σ F_φ(flipAt j σ) = ∑_σ F_φ(σ) by Equiv.sum_comp.
  have h_flip_φ : ∑ σ, F_φ (flipAt j σ) = ∑ σ, F_φ σ :=
    sum_equiv_perm F_φ (flipAtEquiv j)
  have h_flip : ∑ σ, F (flipAt j σ) = ∑ σ, F σ :=
    sum_equiv_perm F (flipAtEquiv j)

  -- Therefore: 2 * ∑_σ F_φ(σ) = ∑_σ [F_φ(σ) + F_φ(flipAt j σ)].
  have h_double_φ : 2 * ∑ σ, F_φ σ = ∑ σ, (F_φ σ + F_φ (flipAt j σ)) := by
    rw [Finset.sum_add_distrib, h_flip_φ]; ring
  have h_double : 2 * ∑ σ, F σ = ∑ σ, (F σ + F (flipAt j σ)) := by
    rw [Finset.sum_add_distrib, h_flip]; ring

  -- It suffices to show: ∑_σ [F_φ(σ) + F_φ(flipAt j σ)] ≤ ∑_σ [F(σ) + F(flipAt j σ)].
  suffices h_paired : ∑ σ, (F_φ σ + F_φ (flipAt j σ)) ≤
      ∑ σ, (F σ + F (flipAt j σ)) by linarith

  -- This follows from pointwise: ∀ σ, F_φ(σ) + F_φ(flipAt j σ) ≤ F(σ) + F(flipAt j σ).
  apply Finset.sum_le_sum
  intro σ _

  -- Now prove the pointwise inequality using the comparison lemma.
  -- For each σ, define u_i = ∑_{k≠j} signOfBool(σ k) * f_i(z_k).
  -- F_φ(σ) = sup'_i(u_i + signOfBool(σ j) * φ(f_i(z_j)))
  -- F_φ(flipAt j σ) = sup'_i(u_i + signOfBool(flipAt j σ j) * φ(f_i(z_j)))
  -- = sup'_i(u_i - signOfBool(σ j) * φ(f_i(z_j)))  [since flipAt negates at j]

  -- So F_φ(σ) + F_φ(flipAt j σ) = sup'(u + s*φ(f·(z_j))) + sup'(u - s*φ(f·(z_j)))
  -- where s = signOfBool(σ j) ∈ {±1}.
  -- Similarly F(σ) + F(flipAt j σ) = sup'(u + s*f·(z_j)) + sup'(u - s*f·(z_j)).
  -- comparison_lemma with a_i = s*φ(f_i(z_j)), b_i = s*f_i(z_j):
  -- |s*φ(x_i) - s*φ(x_l)| = |φ(x_i) - φ(x_l)| ≤ |x_i - x_l| = |s*x_i - s*x_l| ✓

  -- Split ∑_k into (rest over k ≠ j) + (j-th term).
  -- add_sum_erase puts the j-th term at the front; we swap with add_comm.
  have h_split_ite : ∀ (g_at_j : ι → ℝ) (τ : Fin n → Bool),
      (fun i => ∑ k : Fin n, signOfBool (τ k) *
        if k = j then g_at_j i else f i (z k))
      = fun i => (∑ k ∈ Finset.univ.filter (· ≠ j),
          signOfBool (τ k) * f i (z k)) + signOfBool (τ j) * g_at_j i := by
    intro g_at_j τ; funext i
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j), add_comm]
    congr 1
    · apply Finset.sum_congr
      · ext k; simp [Finset.mem_erase, ne_comm]
      · intro k hk; rw [Finset.mem_filter] at hk; simp [hk.2]
    · simp

  have h_split_orig : ∀ (τ : Fin n → Bool),
      (fun i => ∑ k : Fin n, signOfBool (τ k) * f i (z k))
      = fun i => (∑ k ∈ Finset.univ.filter (· ≠ j),
          signOfBool (τ k) * f i (z k)) + signOfBool (τ j) * f i (z j) := by
    intro τ; funext i
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j), add_comm]
    congr 1
    · apply Finset.sum_congr
      · ext k; simp [Finset.mem_erase, ne_comm]
      · intros; rfl

  -- flipAt j σ agrees with σ on k ≠ j.
  have h_flip_other : ∀ k : Fin n, k ≠ j → flipAt j σ k = σ k :=
    fun k hk => flipAt_other j σ hk

  -- The "other coordinates" sum is the same for σ and flipAt j σ.
  have h_u_eq : ∀ i : ι,
      ∑ k ∈ Finset.univ.filter (· ≠ j), signOfBool (flipAt j σ k) * f i (z k)
    = ∑ k ∈ Finset.univ.filter (· ≠ j), signOfBool (σ k) * f i (z k) := by
    intro i
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [h_flip_other k hk.2]

  -- signOfBool(flipAt j σ j) = -signOfBool(σ j).
  have h_flip_sign : signOfBool (flipAt j σ j) = -signOfBool (σ j) := by
    simp [flipAt, signOfBool_neg]

  -- Now rewrite F_φ σ and F_φ (flipAt j σ).
  set u : ι → ℝ := fun i => ∑ k ∈ Finset.univ.filter (· ≠ j),
      signOfBool (σ k) * f i (z k) with hu_def

  -- F_φ σ = sup'(u + signOfBool(σ j) * φ(f·(z_j)))
  have hFφ_σ : F_φ σ = Finset.univ.sup' Finset.univ_nonempty
      (fun i => u i + signOfBool (σ j) * φ (f i (z j))) := by
    dsimp [F_φ]; congr 1
    rw [h_split_ite (fun i => φ (f i (z j))) σ]

  -- F_φ (flipAt j σ) = sup'(u - signOfBool(σ j) * φ(f·(z_j)))
  have hFφ_flip : F_φ (flipAt j σ) = Finset.univ.sup' Finset.univ_nonempty
      (fun i => u i - signOfBool (σ j) * φ (f i (z j))) := by
    dsimp [F_φ]
    congr 1
    rw [h_split_ite (fun i => φ (f i (z j))) (flipAt j σ)]
    ext i
    rw [h_u_eq i, h_flip_sign]; ring

  -- F σ = sup'(u + signOfBool(σ j) * f·(z_j))
  have hF_σ : F σ = Finset.univ.sup' Finset.univ_nonempty
      (fun i => u i + signOfBool (σ j) * f i (z j)) := by
    dsimp [F]
    congr 1; rw [h_split_orig σ]

  -- F (flipAt j σ) = sup'(u - signOfBool(σ j) * f·(z_j))
  have hF_flip : F (flipAt j σ) = Finset.univ.sup' Finset.univ_nonempty
      (fun i => u i - signOfBool (σ j) * f i (z j)) := by
    dsimp [F]
    congr 1
    rw [h_split_orig (flipAt j σ)]
    ext i
    rw [h_u_eq i, h_flip_sign]; ring

  rw [hFφ_σ, hFφ_flip, hF_σ, hF_flip]

  -- Now apply comparison_lemma with
  -- a_i = signOfBool(σ j) * φ(f_i(z_j))
  -- b_i = signOfBool(σ j) * f_i(z_j)
  -- |a_i - a_l| = |s| * |φ(f_i(z_j)) - φ(f_l(z_j))| ≤ |s| * |f_i(z_j) - f_l(z_j)| = |b_i - b_l|
  apply comparison_lemma u
    (fun i => signOfBool (σ j) * φ (f i (z j)))
    (fun i => signOfBool (σ j) * f i (z j))
  intro i l
  rw [show signOfBool (σ j) * φ (f i (z j)) - signOfBool (σ j) * φ (f l (z j))
      = signOfBool (σ j) * (φ (f i (z j)) - φ (f l (z j))) by ring,
      show signOfBool (σ j) * f i (z j) - signOfBool (σ j) * f l (z j)
      = signOfBool (σ j) * (f i (z j) - f l (z j)) by ring,
      abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hφ_lip _ _) (abs_nonneg _)

/-! ## Full contraction via iteration

Iterate the one-step contraction over all `n` coordinates to get the
finite-class scalar inequality:

  `∑_σ sup'(∑_k σ_k * φ(g i k)) ≤ ∑_σ sup'(∑_k σ_k * g i k)`

for any 1-Lipschitz φ. Then rescale to the positive-`L` Lipschitz version and
wrap the result as an `empiricalRademacherComplexity` theorem.
-/

/-- Partially apply `φ` to the initial `m` coordinates: coordinates `k` with
`k.val < m` get `φ (g i k)`, the rest stay as `g i k`. -/
private def partialApply (φ : ℝ → ℝ) (g : ι → Fin n → ℝ) (m : ℕ) : ι → Fin n → ℝ :=
  fun i k => if k.val < m then φ (g i k) else g i k

omit [Fintype ι] [Nonempty ι] in
private lemma partialApply_zero (φ : ℝ → ℝ) (g : ι → Fin n → ℝ) :
    partialApply φ g 0 = g := by
  ext i k; simp [partialApply]

omit [Fintype ι] [Nonempty ι] in
private lemma partialApply_full (φ : ℝ → ℝ) (g : ι → Fin n → ℝ) (i : ι) (k : Fin n) :
    partialApply φ g n i k = φ (g i k) := by
  simp [partialApply, k.isLt]

omit [Fintype ι] [Nonempty ι] in
/-- The key step decomposition: `partialApply (m+1)` differs from `partialApply m`
at the single coordinate `⟨m, hm⟩`, where it replaces `g i ⟨m, hm⟩` with
`φ(g i ⟨m, hm⟩)`. -/
private lemma partialApply_step (φ : ℝ → ℝ) (g : ι → Fin n → ℝ) (m : ℕ) (hm : m < n)
    (i : ι) (k : Fin n) :
    partialApply φ g (m + 1) i k =
      if k = ⟨m, hm⟩ then φ (partialApply φ g m i k) else partialApply φ g m i k := by
  simp only [partialApply]
  by_cases hk : k = ⟨m, hm⟩
  · subst hk; simp
  · have hk_val : k.val ≠ m := fun h => hk (Fin.ext h)
    simp only [hk, ↓reduceIte]
    by_cases hlt : k.val < m
    · simp [Nat.lt_succ_of_lt hlt, hlt]
    · have : ¬ (k.val < m + 1) := by omega
      simp [this, hlt]

/-- Induction: for all `m ≤ n`, the sum with `partialApply m` is at most
the sum with the original function `g`. -/
private theorem contraction_induction {φ : ℝ → ℝ}
    (hφ_lip : ∀ s t : ℝ, |φ s - φ t| ≤ |s - t|)
    (g : ι → Fin n → ℝ) (m : ℕ) (hm : m ≤ n) :
    ∑ σ : Fin n → Bool,
        Finset.univ.sup' Finset.univ_nonempty
          (fun i => ∑ k : Fin n, signOfBool (σ k) * partialApply φ g m i k)
    ≤ ∑ σ : Fin n → Bool,
        Finset.univ.sup' Finset.univ_nonempty
          (fun i => ∑ k : Fin n, signOfBool (σ k) * g i k) := by
  induction m with
  | zero => rw [partialApply_zero]
  | succ m ih =>
    have hm_lt : m < n := Nat.lt_of_succ_le hm
    -- Rewrite: partialApply (m+1) = one-step modification of partialApply m
    simp_rw [partialApply_step φ g m hm_lt]
    -- Apply one_step_contraction to partialApply m at coordinate ⟨m, hm_lt⟩
    have h_one := one_step_contraction hφ_lip (partialApply φ g m) id ⟨m, hm_lt⟩
    simp only [id_eq] at h_one
    exact le_trans h_one (ih (Nat.le_of_succ_le hm))

/-- **Finite-sample scalar contraction, 1-Lipschitz form.** For a finite
sample `Fin n`, finite hypothesis class `ι`, and scalar 1-Lipschitz `φ`:

  `∑_σ sup'(∑_k σ_k * φ(g i k)) ≤ ∑_σ sup'(∑_k σ_k * g i k)` -/
theorem contraction_1lip {φ : ℝ → ℝ}
    (hφ_lip : ∀ s t : ℝ, |φ s - φ t| ≤ |s - t|)
    (g : ι → Fin n → ℝ) :
    ∑ σ : Fin n → Bool,
        Finset.univ.sup' Finset.univ_nonempty
          (fun i => ∑ k : Fin n, signOfBool (σ k) * φ (g i k))
    ≤ ∑ σ : Fin n → Bool,
        Finset.univ.sup' Finset.univ_nonempty
          (fun i => ∑ k : Fin n, signOfBool (σ k) * g i k) := by
  have h := contraction_induction hφ_lip g n le_rfl
  simp_rw [partialApply_full] at h
  exact h

omit [Fintype ι] [Nonempty ι] in
/-- Nonnegative scaling commutes with `sup'` over a finite nonempty set. -/
private lemma sup'_nonneg_mul {s : Finset ι} (hs : s.Nonempty) {c : ℝ} (hc : 0 ≤ c)
    (f : ι → ℝ) :
    s.sup' hs (fun i => c * f i) = c * s.sup' hs f := by
  apply le_antisymm
  · apply Finset.sup'_le hs
    intro i hi
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' f hi) hc
  · obtain ⟨i_star, hi_mem, hi_eq⟩ := Finset.exists_mem_eq_sup' hs f
    rw [hi_eq]
    exact Finset.le_sup' (fun i => c * f i) hi_mem

/-- **Finite-sample scalar contraction, positive-`L` form.** For a finite
sample `Fin n`, finite hypothesis class `ι`, scalar real-valued functions, and
`φ` satisfying `|φ s - φ t| ≤ L * |s - t|` with `0 < L`:

  `∑_σ sup'_i(∑_k σ_k * φ(g i k))
    ≤ L * ∑_σ sup'_i(∑_k σ_k * g i k)`.

This is the finite combinatorial contraction bound used by the empirical
Rademacher wrapper below; it is not the full general Talagrand contraction
principle. -/
theorem finiteSampleScalarContraction_lipschitz {φ : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L)
    (hφ_lip : ∀ s t : ℝ, |φ s - φ t| ≤ L * |s - t|)
    (g : ι → Fin n → ℝ) :
    ∑ σ : Fin n → Bool,
        Finset.univ.sup' Finset.univ_nonempty
          (fun i => ∑ k : Fin n, signOfBool (σ k) * φ (g i k))
    ≤ L * ∑ σ : Fin n → Bool,
        Finset.univ.sup' Finset.univ_nonempty
          (fun i => ∑ k : Fin n, signOfBool (σ k) * g i k) := by
  let ψ : ℝ → ℝ := fun x => φ (L⁻¹ * x)
  have hψ_lip : ∀ s t : ℝ, |ψ s - ψ t| ≤ |s - t| := by
    intro s t
    have h := hφ_lip (L⁻¹ * s) (L⁻¹ * t)
    have h_scale :
        L * |L⁻¹ * s - L⁻¹ * t| = |s - t| := by
      rw [show L⁻¹ * s - L⁻¹ * t = L⁻¹ * (s - t) by ring, abs_mul]
      rw [abs_of_nonneg (inv_nonneg.mpr hL.le)]
      rw [← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
    exact h.trans_eq h_scale
  have hψ_apply : ∀ x : ℝ, ψ (L * x) = φ x := by
    intro x
    dsimp [ψ]
    rw [← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul]
  have h_base := contraction_1lip hψ_lip (fun i k => L * g i k)
  simp_rw [hψ_apply] at h_base
  calc
    ∑ σ : Fin n → Bool,
        Finset.univ.sup' Finset.univ_nonempty
          (fun i => ∑ k : Fin n, signOfBool (σ k) * φ (g i k))
        ≤ ∑ σ : Fin n → Bool,
            Finset.univ.sup' Finset.univ_nonempty
              (fun i => ∑ k : Fin n, signOfBool (σ k) * (L * g i k)) := h_base
    _ = L * ∑ σ : Fin n → Bool,
        Finset.univ.sup' Finset.univ_nonempty
          (fun i => ∑ k : Fin n, signOfBool (σ k) * g i k) := by
        have h_factor : ∀ (σ : Fin n → Bool) (i : ι),
            (∑ k : Fin n, signOfBool (σ k) * (L * g i k)) =
              L * ∑ k : Fin n, signOfBool (σ k) * g i k := by
          intro σ i
          calc
            (∑ k : Fin n, signOfBool (σ k) * (L * g i k))
                = ∑ k : Fin n, L * (signOfBool (σ k) * g i k) := by
                  apply Finset.sum_congr rfl
                  intro k _
                  ring
            _ = L * ∑ k : Fin n, signOfBool (σ k) * g i k := by
                  rw [← Finset.mul_sum]
        simp_rw [h_factor]
        simp_rw [sup'_nonneg_mul Finset.univ_nonempty hL.le]
        rw [← Finset.mul_sum]

/-! ## Empirical Rademacher complexity wrapper -/

/-- **Finite-sample empirical Rademacher contraction.** For a finite sample,
finite hypothesis class, scalar real-valued loss class, and 1-Lipschitz `φ`:

  `R̂_S(φ ∘ ℓ) ≤ R̂_S(ℓ)`

The key step is factoring `n⁻¹` out of `sup'` (valid since `n⁻¹ ≥ 0`),
applying `contraction_1lip` at the raw sum level, then reassembling.

Claim-facing wrapper for theorempath.com evidence entry `claim:rademacher-complexity::one-lipschitz-empirical-rademacher-contraction`.
-/
theorem contraction_empirical {φ : ℝ → ℝ}
    (hφ_lip : ∀ s t : ℝ, |φ s - φ t| ≤ |s - t|)
    (ℓ : ι → Z → ℝ) (z : Fin n → Z) :
    empiricalRademacherComplexity (fun i x => φ (ℓ i x)) z ≤
    empiricalRademacherComplexity ℓ z := by
  unfold empiricalRademacherComplexity
  -- Factor n⁻¹ out of both sup's
  simp_rw [sup'_nonneg_mul Finset.univ_nonempty (inv_nonneg.mpr (Nat.cast_nonneg' n))]
  -- Factor n⁻¹ out of both sums over σ
  simp_rw [← Finset.mul_sum]
  -- Strip the two nonneg prefactors
  apply mul_le_mul_of_nonneg_left _ (le_of_lt two_pow_inv_pos)
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg' n))
  exact contraction_1lip hφ_lip (fun i k => ℓ i (z k))

/-- **Finite-sample empirical Rademacher contraction, positive-`L` form.**
For a finite sample, finite hypothesis class, scalar real-valued loss class,
and `φ` satisfying `|φ s - φ t| ≤ L * |s - t|` with `0 < L`:

  `R̂_S(φ ∘ ℓ) ≤ L * R̂_S(ℓ)`.

This is a finite-class wrapper around `finiteSampleScalarContraction_lipschitz`,
not a statement about infinite classes or general stochastic processes.

Claim-facing wrapper for theorempath.com evidence entry `claim:rademacher-complexity::finite-sample-contraction`.
-/
theorem empiricalRademacherComplexity_contraction_lipschitz {φ : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L)
    (hφ_lip : ∀ s t : ℝ, |φ s - φ t| ≤ L * |s - t|)
    (ℓ : ι → Z → ℝ) (z : Fin n → Z) :
    empiricalRademacherComplexity (fun i x => φ (ℓ i x)) z ≤
    L * empiricalRademacherComplexity ℓ z := by
  unfold empiricalRademacherComplexity
  simp_rw [sup'_nonneg_mul Finset.univ_nonempty (inv_nonneg.mpr (Nat.cast_nonneg' n))]
  simp_rw [← Finset.mul_sum]
  calc
    ((2 : ℝ) ^ n)⁻¹ *
        ((n : ℝ)⁻¹ *
          ∑ σ : Fin n → Bool,
            Finset.univ.sup' Finset.univ_nonempty
              (fun i => ∑ k : Fin n, signOfBool (σ k) * φ (ℓ i (z k))))
        ≤ ((2 : ℝ) ^ n)⁻¹ *
            ((n : ℝ)⁻¹ *
              (L * ∑ σ : Fin n → Bool,
                Finset.univ.sup' Finset.univ_nonempty
                  (fun i => ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k)))) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt two_pow_inv_pos)
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg' n))
          exact finiteSampleScalarContraction_lipschitz hL hφ_lip (fun i k => ℓ i (z k))
    _ = L * (((2 : ℝ) ^ n)⁻¹ *
        ((n : ℝ)⁻¹ *
          ∑ σ : Fin n → Bool,
            Finset.univ.sup' Finset.univ_nonempty
              (fun i => ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k)))) := by
          ring

end FormalSLT.Rademacher.RademacherContraction
