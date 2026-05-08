import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import FormalSLT.Rademacher.FiniteSample
import FormalSLT.Rademacher.Massart

/-!
# Covering number bound for Rademacher complexity

The ε-net peeling bound: if `N` is an ε-cover of a hypothesis class `F`
(for each `f ∈ F` there exists `g ∈ N` with pointwise loss difference
at most `ε` on the sample), then:

  `R̂_S(F) ≤ ε + R̂_S(N)`

Corollary with Massart on the finite net:

  `R̂_S(F) ≤ ε + B · √(2 · log|N| / n)`

This is the first step toward the Dudley integral bound.

No `sorry`, no `admit`, no custom `axiom`.
-/

namespace FormalSLT.Covering.Rademacher

open Finset
open scoped BigOperators
open FormalSLT.Rademacher.FiniteSample

variable {n : ℕ}

/-! ## Helper lemmas -/

/-- A Rademacher sign times a value is bounded by the absolute value:
`signOfBool(b) · a ≤ |a|`. -/
lemma signOfBool_mul_le_abs (b : Bool) (a : ℝ) :
    signOfBool b * a ≤ |a| :=
  le_trans (le_abs_self _)
    (by rw [abs_mul, abs_signOfBool, one_mul])

/-! ## Main theorem: ε-net peeling -/

/-- **Rademacher covering bound** (ε-net peeling): if for every hypothesis
`i : ι` there is a "nearest net point" `π i : κ` with pointwise loss
difference at most `ε` on the sample, then the Rademacher complexity of
the full class is bounded by `ε` plus the Rademacher complexity of the
net class.

The proof decomposes each σ-weighted sum into a residual (bounded by ε
via `|σ_k| = 1`) and a net term (bounded by `sup` over `κ`). -/
theorem rademacher_covering_bound
    {ι κ Z : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (ℓ : ι → Z → ℝ) (g : κ → Z → ℝ) (z : Fin n → Z)
    (π : ι → κ) (ε : ℝ) (_hε : 0 ≤ ε)
    (hn : 0 < (n : ℝ))
    (hcover : ∀ i : ι, ∀ k : Fin n, |ℓ i (z k) - g (π i) (z k)| ≤ ε) :
    empiricalRademacherComplexity ℓ z ≤ ε + empiricalRademacherComplexity g z := by
  unfold empiricalRademacherComplexity
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos two_pos n
  have h2n_inv_nn : (0 : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹ := inv_nonneg.mpr h2n_pos.le
  have hn_inv_nn : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hn.le
  -- Step 1: For each σ, bound sup over ι by ε + sup over κ
  suffices h_per_sigma : ∀ σ : Fin n → Bool,
      univ.sup' univ_nonempty
        (fun i => (n : ℝ)⁻¹ * ∑ k, signOfBool (σ k) * ℓ i (z k)) ≤
      ε + univ.sup' univ_nonempty
        (fun j => (n : ℝ)⁻¹ * ∑ k, signOfBool (σ k) * g j (z k)) by
    -- Step 2: Sum over σ and multiply by (2^n)⁻¹
    calc ((2 : ℝ) ^ n)⁻¹ *
          ∑ σ : Fin n → Bool, univ.sup' univ_nonempty
            (fun i => (n : ℝ)⁻¹ * ∑ k, signOfBool (σ k) * ℓ i (z k))
        ≤ ((2 : ℝ) ^ n)⁻¹ *
          ∑ σ : Fin n → Bool,
            (ε + univ.sup' univ_nonempty
              (fun j => (n : ℝ)⁻¹ * ∑ k, signOfBool (σ k) * g j (z k))) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun σ _ => h_per_sigma σ) h2n_inv_nn
      _ = ε + ((2 : ℝ) ^ n)⁻¹ *
            ∑ σ : Fin n → Bool, univ.sup' univ_nonempty
              (fun j => (n : ℝ)⁻¹ * ∑ k, signOfBool (σ k) * g j (z k)) := by
          rw [Finset.sum_add_distrib, mul_add]
          congr 1
          rw [Finset.sum_const, card_univ,
              show Fintype.card (Fin n → Bool) = 2 ^ n from card_signVectors,
              nsmul_eq_mul, show ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n from by simp,
              ← mul_assoc, inv_mul_cancel₀ h2n_pos.ne', one_mul]
  -- Prove the per-σ bound
  intro σ
  apply Finset.sup'_le
  intro i _
  -- Decompose: σ·ℓ = σ·(ℓ - g∘π) + σ·g∘π
  have h_eq : (n : ℝ)⁻¹ * ∑ k, signOfBool (σ k) * ℓ i (z k) =
      (n : ℝ)⁻¹ * ∑ k, signOfBool (σ k) * (ℓ i (z k) - g (π i) (z k)) +
      (n : ℝ)⁻¹ * ∑ k, signOfBool (σ k) * g (π i) (z k) := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1; apply Finset.sum_congr rfl; intro k _; ring
  -- Bound the residual: n⁻¹ · ∑ σ·(ℓ - g) ≤ ε
  have h_residual : (n : ℝ)⁻¹ *
      ∑ k : Fin n, signOfBool (σ k) * (ℓ i (z k) - g (π i) (z k)) ≤ ε := by
    have h1 : ∑ k : Fin n, signOfBool (σ k) * (ℓ i (z k) - g (π i) (z k)) ≤
        (n : ℝ) * ε :=
      calc ∑ k : Fin n, signOfBool (σ k) * (ℓ i (z k) - g (π i) (z k))
          ≤ ∑ k : Fin n, |ℓ i (z k) - g (π i) (z k)| :=
            Finset.sum_le_sum fun k _ => signOfBool_mul_le_abs _ _
        _ ≤ ∑ _k : Fin n, ε :=
            Finset.sum_le_sum fun k _ => hcover i k
        _ = (n : ℝ) * ε := by
            rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc (n : ℝ)⁻¹ * ∑ k, signOfBool (σ k) * (ℓ i (z k) - g (π i) (z k))
        ≤ (n : ℝ)⁻¹ * ((n : ℝ) * ε) := mul_le_mul_of_nonneg_left h1 hn_inv_nn
      _ = ε := by rw [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
  rw [h_eq]
  calc (n : ℝ)⁻¹ * ∑ k, signOfBool (σ k) * (ℓ i (z k) - g (π i) (z k)) +
        (n : ℝ)⁻¹ * ∑ k, signOfBool (σ k) * g (π i) (z k)
      ≤ ε + (n : ℝ)⁻¹ * ∑ k, signOfBool (σ k) * g (π i) (z k) := by
        linarith
    _ ≤ ε + univ.sup' univ_nonempty
          (fun j => (n : ℝ)⁻¹ * ∑ k, signOfBool (σ k) * g j (z k)) := by
        have := Finset.le_sup'
          (fun j => (n : ℝ)⁻¹ * ∑ k, signOfBool (σ k) * g j (z k))
          (mem_univ (π i))
        linarith

/-! ## Corollary: Massart on the net -/

/-- **Rademacher covering + Massart**: combining the ε-net peeling with
Massart's finite-class bound on the net gives
`R̂_S(F) ≤ ε + B · √(2 · log|N| / n)`. -/
theorem rademacher_covering_massart
    {ι κ Z : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (ℓ : ι → Z → ℝ) (g : κ → Z → ℝ) (z : Fin n → Z)
    (π : ι → κ) (ε B : ℝ) (hε : 0 ≤ ε) (hB : 0 < B)
    (hn : 0 < n) (hCard : 1 < Fintype.card κ)
    (hcover : ∀ i : ι, ∀ k : Fin n, |ℓ i (z k) - g (π i) (z k)| ≤ ε)
    (hBound : ∀ j : κ, ∀ k : Fin n, |g j (z k)| ≤ B) :
    empiricalRademacherComplexity ℓ z ≤
    ε + B * Real.sqrt (2 * Real.log (Fintype.card κ : ℝ) / (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  calc empiricalRademacherComplexity ℓ z
      ≤ ε + empiricalRademacherComplexity g z :=
        rademacher_covering_bound ℓ g z π ε hε hn_pos hcover
    _ ≤ ε + B * Real.sqrt (2 * Real.log (Fintype.card κ : ℝ) / (n : ℝ)) := by
        have := FormalSLT.Rademacher.Massart.massart_finite_class hB hBound hn hCard
        linarith

end FormalSLT.Covering.Rademacher
