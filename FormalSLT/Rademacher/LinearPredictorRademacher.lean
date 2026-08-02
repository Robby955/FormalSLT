import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import FormalSLT.Rademacher.FiniteSample

/-!
# Linear predictor Rademacher bound

For a finite class of scalar linear predictors on `EuclideanSpace ℝ (Fin d)`,
indexed by weights `w₁, ..., wₘ` with `‖wᵢ‖ ≤ R`, and evaluated on a finite
sample `z₁, ..., zₙ`:

  `R̂_S ≤ (R / n) · √(∑ₖ ‖zₖ‖²)`

Corollary: if `‖zₖ‖ ≤ B` for all k, then `R̂_S ≤ R · B / √n`.

The public theorem names below are the finite-dimensional Euclidean API.  The
Cauchy-Schwarz proof is factored through private inner-product-space helpers to
avoid repeating algebra while keeping the exported statement scoped to the
finite-dimensional case.

The proof uses:
1. Sign product orthogonality: `(2ⁿ)⁻¹ · ∑_σ σₖ · σⱼ = δₖⱼ`
2. Sign-averaged squared norm: `∑_σ ‖∑ₖ σₖ • zₖ‖² = 2ⁿ · ∑ₖ ‖zₖ‖²`
3. Cauchy-Schwarz: `sup'_i ⟪wᵢ, v⟫ ≤ R · ‖v‖`
4. Discrete Cauchy-Schwarz for Jensen/RMS bound
-/

namespace FormalSLT.Rademacher.LinearPredictorRademacher

open Finset
open scoped BigOperators
open FormalSLT.Rademacher.FiniteSample

variable {n : ℕ}

/-! ## Sign product orthogonality -/

/-- Product of signs at the same coordinate squares to 1. -/
lemma signProduct_same (σ : Fin n → Bool) (k : Fin n) :
    signOfBool (σ k) * signOfBool (σ k) = 1 :=
  signOfBool_sq (σ k)

/-- Sum of sign products over all sign vectors: when k = j, the sum is 2^n
(each term is 1); when k ≠ j, the sum is 0 (cancellation via flipAt). -/
lemma sum_signProduct (k j : Fin n) :
    ∑ σ : Fin n → Bool, signOfBool (σ k) * signOfBool (σ j) =
    if k = j then (2 : ℝ) ^ n else 0 := by
  by_cases hkj : k = j
  · subst hkj
    simp [signOfBool_sq]
  · have h_cancel : ∀ σ : Fin n → Bool,
        signOfBool (σ k) * signOfBool (σ j) +
        signOfBool (flipAt k σ k) * signOfBool (flipAt k σ j) = 0 := by
      intro σ
      rw [flipAt_same, signOfBool_neg, flipAt_other k σ (Ne.symm hkj)]
      ring
    have h_sum_flip : ∑ σ : Fin n → Bool,
          signOfBool (flipAt k σ k) * signOfBool (flipAt k σ j) =
        ∑ σ : Fin n → Bool, signOfBool (σ k) * signOfBool (σ j) :=
      Equiv.sum_comp (flipAtEquiv k)
        (fun (σ : Fin n → Bool) => signOfBool (σ k) * signOfBool (σ j))
    have h_pair_zero : ∑ σ : Fin n → Bool,
        (signOfBool (σ k) * signOfBool (σ j) +
         signOfBool (flipAt k σ k) * signOfBool (flipAt k σ j)) = 0 :=
      Finset.sum_eq_zero (fun σ _ => h_cancel σ)
    rw [Finset.sum_add_distrib, h_sum_flip] at h_pair_zero
    simp [hkj]
    linarith

/-- Normalized sign product orthogonality:
`(2^n)⁻¹ · ∑_σ signOfBool(σ k) · signOfBool(σ j) = δ_{kj}`. -/
lemma avg_signProduct (k j : Fin n) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, signOfBool (σ k) * signOfBool (σ j) =
    if k = j then 1 else 0 := by
  rw [sum_signProduct]
  split
  · exact inv_mul_cancel₀ (pow_ne_zero n (two_ne_zero' ℝ))
  · simp

/-! ## Sign-averaged squared norm -/

/-- The sign-averaged squared norm identity: summing ‖∑_k σ_k • z_k‖² over
all sign vectors σ gives 2^n · ∑_k ‖z_k‖². The key step is the bilinear
expansion of the norm² into a double sum, followed by sign orthogonality. -/
lemma sum_sign_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : Fin n → E) :
    ∑ σ : Fin n → Bool, ‖∑ k : Fin n, signOfBool (σ k) • z k‖ ^ 2 =
    (2 : ℝ) ^ n * ∑ k : Fin n, ‖z k‖ ^ 2 := by
  -- Step 1: ‖v‖² = ⟪v, v⟫_ℝ
  simp_rw [← real_inner_self_eq_norm_sq]
  -- Step 2: Bilinear expansion of ⟪∑ σ•z, ∑ σ•z⟫
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, inner_smul_right]
  -- Now: ∑ σ, ∑ k, ∑ j, signOfBool(σ k) * (signOfBool(σ j) * ⟪z k, z j⟫)
  -- Step 3: Reassociate: a * (b * c) → (a * b) * c
  simp_rw [← mul_assoc]
  -- Step 4: Exchange summation order: ∑_σ ∑_k → ∑_k ∑_σ
  rw [Finset.sum_comm]
  -- Step 5: Inside each k, exchange σ and j
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  -- Step 6: Factor ⟪z k, z j⟫ out of σ-sum
  simp_rw [← Finset.sum_mul]
  -- Step 7: Apply sign orthogonality
  simp_rw [sum_signProduct]
  -- Step 8: Simplify if-then-else sum
  simp_rw [ite_mul, zero_mul]
  simp only [sum_ite_eq, mem_univ, ite_true]
  -- Step 9: Convert back to norm²
  simp_rw [real_inner_self_eq_norm_sq, Finset.mul_sum]

/-! ## Cauchy-Schwarz sup bound -/

/-- For predictors with `‖w_i‖ ≤ R`, the sup of inner products is bounded:
`sup'_i ⟪w_i, v⟫ ≤ R · ‖v‖`. -/
lemma sup_inner_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → E) (R : ℝ) (_hR : 0 ≤ R) (hw : ∀ i, ‖w i‖ ≤ R) (v : E) :
    Finset.univ.sup' Finset.univ_nonempty
      (fun i => @inner ℝ E _ (w i) v) ≤ R * ‖v‖ := by
  apply Finset.sup'_le
  intro i _
  calc @inner ℝ E _ (w i) v
      ≤ |@inner ℝ E _ (w i) v| := le_abs_self _
    _ = ‖@inner ℝ E _ (w i) v‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖w i‖ * ‖v‖ := norm_inner_le_norm (𝕜 := ℝ) (w i) v
    _ ≤ R * ‖v‖ := by apply mul_le_mul_of_nonneg_right (hw i) (norm_nonneg v)

/-! ## Sign-averaged norm bound (Jensen/RMS via Cauchy-Schwarz for sums) -/

/-- The sign-averaged norm is bounded by √(∑ ‖z_k‖²). This combines the
discrete Cauchy-Schwarz inequality (Jensen for RMS) with the sign-averaged
squared norm identity. -/
lemma sign_avg_norm_le_sqrt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : Fin n → E) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
      ‖∑ k : Fin n, signOfBool (σ k) • z k‖ ≤
    Real.sqrt (∑ k : Fin n, ‖z k‖ ^ 2) := by
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow]
  -- Cauchy-Schwarz for finite sums: (∑ f)² ≤ card * ∑ f²
  have h_cs := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin n → Bool)))
    (f := fun (σ : Fin n → Bool) => ‖∑ k : Fin n, signOfBool (σ k) • z k‖)
  -- #univ = Fintype.card (Fin n → Bool) = 2^n
  rw [card_univ, show Fintype.card (Fin n → Bool) = 2 ^ n from by
    simp [Fintype.card_bool, Fintype.card_fin]] at h_cs
  push_cast at h_cs
  -- h_cs : (∑ σ, ‖v_σ‖)² ≤ ↑(2^n) * ∑ σ, ‖v_σ‖²
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num : (0 : ℝ) < 2) n
  calc ((2 : ℝ) ^ n)⁻¹ ^ 2 *
        (∑ σ : Fin n → Bool, ‖∑ k, signOfBool (σ k) • z k‖) ^ 2
      ≤ ((2 : ℝ) ^ n)⁻¹ ^ 2 *
        (↑(2 ^ n) * ∑ σ : Fin n → Bool, ‖∑ k, signOfBool (σ k) • z k‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h_cs (sq_nonneg _)
    _ = ((2 : ℝ) ^ n)⁻¹ *
        ∑ σ : Fin n → Bool, ‖∑ k, signOfBool (σ k) • z k‖ ^ 2 := by
        rw [sq ((2 : ℝ) ^ n)⁻¹, mul_assoc,
            ← mul_assoc ((2 : ℝ) ^ n)⁻¹ ((↑(2 ^ n) : ℝ)),
            show (↑(2 ^ n) : ℝ) = (2 : ℝ) ^ n from by simp,
            inv_mul_cancel₀ h2n_pos.ne', one_mul]
    _ = ∑ k : Fin n, ‖z k‖ ^ 2 := by
        rw [sum_sign_norm_sq z, ← mul_assoc,
            inv_mul_cancel₀ h2n_pos.ne', one_mul]

/-! ## Helper: factor nonneg constant from sup' -/

private lemma sup'_nonneg_mul {ι' : Type*} {s : Finset ι'} (hs : s.Nonempty)
    {c : ℝ} (hc : 0 ≤ c) (f : ι' → ℝ) :
    s.sup' hs (fun i => c * f i) = c * s.sup' hs f := by
  apply le_antisymm
  · apply Finset.sup'_le hs
    intro i hi
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' f hi) hc
  · obtain ⟨i_star, hi_mem, hi_eq⟩ := Finset.exists_mem_eq_sup' hs f
    rw [hi_eq]
    exact Finset.le_sup' (fun i => c * f i) hi_mem

/-! ## Internal inner-product-space bound -/

/-- Internal Cauchy-Schwarz bound used by the finite-dimensional public API. -/
private theorem linearPredictor_rademacher_innerProduct
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → E) (z : Fin n → E) (R : ℝ) (hR : 0 ≤ R)
    (hw : ∀ i, ‖w i‖ ≤ R)
    (hn : 0 < (n : ℝ)) :
    empiricalRademacherComplexity (fun i (x : E) => @inner ℝ E _ (w i) x) z ≤
    R * (n : ℝ)⁻¹ * Real.sqrt (∑ k : Fin n, ‖z k‖ ^ 2) := by
  unfold empiricalRademacherComplexity
  -- Step 1: Factor n⁻¹ out of sup'
  simp_rw [sup'_nonneg_mul univ_nonempty (inv_nonneg.mpr (le_of_lt hn))]
  -- Goal: (2^n)⁻¹ * ∑ σ, n⁻¹ * sup'_i (∑_k σ_k * ⟪w_i, z_k⟫) ≤ ...
  -- Step 2: Rewrite ∑_k σ_k * ⟪w_i, z_k⟫ = ⟪w_i, ∑_k σ_k • z_k⟫
  simp_rw [show ∀ (i : ι) (σ : Fin n → Bool),
    ∑ k : Fin n, signOfBool (σ k) * @inner ℝ E _ (w i) (z k) =
    @inner ℝ E _ (w i) (∑ k : Fin n, signOfBool (σ k) • z k)
    from fun i σ => by simp_rw [← inner_smul_right, ← inner_sum]]
  -- Goal: (2^n)⁻¹ * ∑ σ, n⁻¹ * sup'_i ⟪w_i, ∑_k σ_k • z_k⟫ ≤ ...
  -- Step 3: Bound sup'_i ⟪w_i, v⟫ ≤ R * ‖v‖
  have h2n_inv_nonneg : (0 : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
  have hn_inv_nonneg : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hn)
  calc ((2 : ℝ) ^ n)⁻¹ *
      ∑ σ : Fin n → Bool, (n : ℝ)⁻¹ *
        univ.sup' univ_nonempty (fun i =>
          @inner ℝ E _ (w i) (∑ k, signOfBool (σ k) • z k))
    ≤ ((2 : ℝ) ^ n)⁻¹ *
      ∑ σ : Fin n → Bool, (n : ℝ)⁻¹ *
        (R * ‖∑ k : Fin n, signOfBool (σ k) • z k‖) := by
        apply mul_le_mul_of_nonneg_left _ h2n_inv_nonneg
        apply Finset.sum_le_sum
        intro σ _
        apply mul_le_mul_of_nonneg_left _ hn_inv_nonneg
        exact sup_inner_le w R hR hw _
    _ = R * (n : ℝ)⁻¹ *
        (((2 : ℝ) ^ n)⁻¹ *
          ∑ σ : Fin n → Bool, ‖∑ k, signOfBool (σ k) • z k‖) := by
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        ring_nf
    _ ≤ R * (n : ℝ)⁻¹ *
        Real.sqrt (∑ k : Fin n, ‖z k‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left (sign_avg_norm_le_sqrt z)
        apply mul_nonneg hR hn_inv_nonneg

/-! ## Internal bounded-input corollary -/

/-- Internal bounded-input corollary used by the finite-dimensional public API. -/
private theorem linearPredictor_rademacher_uniform_innerProduct
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → E) (z : Fin n → E)
    (R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hw : ∀ i, ‖w i‖ ≤ R) (hz : ∀ k, ‖z k‖ ≤ B)
    (hn : 0 < (n : ℝ)) :
    empiricalRademacherComplexity (fun i (x : E) => @inner ℝ E _ (w i) x) z ≤
    R * B / Real.sqrt (n : ℝ) := by
  calc empiricalRademacherComplexity (fun i (x : E) => @inner ℝ E _ (w i) x) z
      ≤ R * (n : ℝ)⁻¹ * Real.sqrt (∑ k : Fin n, ‖z k‖ ^ 2) :=
        linearPredictor_rademacher_innerProduct w z R hR hw hn
    _ ≤ R * (n : ℝ)⁻¹ * Real.sqrt (∑ _k : Fin n, B ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hR (inv_nonneg.mpr (le_of_lt hn)))
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro k _
        apply sq_le_sq'
        · linarith [norm_nonneg (z k)]
        · exact hz k
    _ = R * B / Real.sqrt (n : ℝ) := by
        simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Real.sqrt_mul (Nat.cast_nonneg' n), Real.sqrt_sq hB]
        have hn_ne : (↑n : ℝ) ≠ 0 := hn.ne'
        have h_sqrt_ne : Real.sqrt ↑n ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
        field_simp
        rw [Real.sq_sqrt (le_of_lt hn)]

/-! ## Finite-dimensional Euclidean specialization -/

/-- Finite-sample, finite-hypothesis-class Rademacher bound for scalar
linear predictors on `EuclideanSpace ℝ (Fin d)`. This is the finite-dimensional
Euclidean API for the proved inner-product-space lemma above:
`Rad_S({x ↦ ⟪w_i, x⟫ : ‖w_i‖ ≤ R}) ≤ R * n⁻¹ * sqrt(∑_k ‖z_k‖²)`.
Claim-facing wrapper for theorempath.com evidence entry `claim:rademacher-complexity::linear-predictor-rademacher-bound`.
-/
theorem linearPredictor_rademacher
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → EuclideanSpace ℝ (Fin d)) (z : Fin n → EuclideanSpace ℝ (Fin d))
    (R : ℝ) (hR : 0 ≤ R)
    (hw : ∀ i, ‖w i‖ ≤ R)
    (hn : 0 < (n : ℝ)) :
    empiricalRademacherComplexity
      (fun i (x : EuclideanSpace ℝ (Fin d)) =>
        @inner ℝ (EuclideanSpace ℝ (Fin d)) _ (w i) x) z ≤
    R * (n : ℝ)⁻¹ * Real.sqrt (∑ k : Fin n, ‖z k‖ ^ 2) :=
  linearPredictor_rademacher_innerProduct w z R hR hw hn

/-- Bounded-input corollary for the finite-dimensional Euclidean API: if each
sample vector in `EuclideanSpace ℝ (Fin d)` satisfies `‖z_k‖ ≤ B`, then the
finite-sample, finite-class Rademacher complexity of the scalar linear class is
at most `R * B / sqrt n`.
-/
theorem linearPredictor_rademacher_uniform
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → EuclideanSpace ℝ (Fin d)) (z : Fin n → EuclideanSpace ℝ (Fin d))
    (R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hw : ∀ i, ‖w i‖ ≤ R) (hz : ∀ k, ‖z k‖ ≤ B)
    (hn : 0 < (n : ℝ)) :
    empiricalRademacherComplexity
      (fun i (x : EuclideanSpace ℝ (Fin d)) =>
        @inner ℝ (EuclideanSpace ℝ (Fin d)) _ (w i) x) z ≤
    R * B / Real.sqrt (n : ℝ) :=
  linearPredictor_rademacher_uniform_innerProduct w z R B hR hB hw hz hn

/-- Compatibility alias for the finite-dimensional Euclidean linear-predictor
Rademacher bound. -/
theorem linearPredictor_rademacher_finiteDim
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → EuclideanSpace ℝ (Fin d)) (z : Fin n → EuclideanSpace ℝ (Fin d))
    (R : ℝ) (hR : 0 ≤ R)
    (hw : ∀ i, ‖w i‖ ≤ R)
    (hn : 0 < (n : ℝ)) :
    empiricalRademacherComplexity
      (fun i (x : EuclideanSpace ℝ (Fin d)) =>
        @inner ℝ (EuclideanSpace ℝ (Fin d)) _ (w i) x) z ≤
    R * (n : ℝ)⁻¹ * Real.sqrt (∑ k : Fin n, ‖z k‖ ^ 2) :=
  linearPredictor_rademacher w z R hR hw hn

/-- Compatibility alias for the finite-dimensional bounded-input corollary. -/
theorem linearPredictor_rademacher_uniform_finiteDim
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → EuclideanSpace ℝ (Fin d)) (z : Fin n → EuclideanSpace ℝ (Fin d))
    (R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hw : ∀ i, ‖w i‖ ≤ R) (hz : ∀ k, ‖z k‖ ≤ B)
    (hn : 0 < (n : ℝ)) :
    empiricalRademacherComplexity
      (fun i (x : EuclideanSpace ℝ (Fin d)) =>
        @inner ℝ (EuclideanSpace ℝ (Fin d)) _ (w i) x) z ≤
    R * B / Real.sqrt (n : ℝ) :=
  linearPredictor_rademacher_uniform w z R B hR hB hw hz hn

end FormalSLT.Rademacher.LinearPredictorRademacher
