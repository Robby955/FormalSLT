import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import FormalSLT.Rademacher.FiniteSample

/-!
# Massart's finite-class lemma for empirical Rademacher complexity

Proves the deterministic upper bound on empirical Rademacher complexity
for a finite hypothesis class with bounded loss:

  `empiricalRademacherComplexity ℓ z ≤ B * Real.sqrt (2 * Real.log ↑|ι| / ↑n)`

The proof uses the standard exponential method (Chernoff bound for
expectations):

1. `sup_i x_i ≤ (1/t) · log(∑_i exp(t · x_i))` for any `t > 0`.
2. Average over sign vectors: the uniform-sign MGF of each signed
   empirical mean decomposes as a product over coordinates.
3. The single-coordinate Rademacher MGF satisfies
   `(exp(t·a) + exp(-t·a))/2 ≤ exp(t²·a²/2)` (Hoeffding's cosh lemma).
4. Combine and optimize `t = sqrt(2n · log|H|) / B`.

All lemmas are closed (no `sorry`, no `admit`).

Out of scope:
- Two-sided or absolute-value variants
- Sharp constants (the constant 2 inside the sqrt is not tight for all
  class sizes; sharper forms use `2 log(2|H|)` or refined entropy bounds)
- Connection to VC dimension or covering numbers
- Population (expected over S~μ^n) version of Massart (this is the
  sample-conditional / empirical form)
-/

open scoped BigOperators
open Finset

namespace FormalSLT.Rademacher.Massart

noncomputable section

open FormalSLT.Rademacher.FiniteSample

variable {n : ℕ} {ι Z : Type*} [Fintype ι] [Nonempty ι]

/-! ## Helper: Rademacher cosh bound

For any `a : ℝ` and `t : ℝ`, the average of `exp(t·signOfBool(b)·a)`
over the two Boolean values satisfies:
  `(exp(t·a) + exp(-t·a)) / 2 ≤ exp(t²·a²/2)`.

This is the discrete (one-coordinate) Hoeffding/cosh lemma for sign
variables.
-/

/-- The Hoeffding cosh inequality: for all `t a : ℝ`,
`(Real.exp (t * a) + Real.exp (-(t * a))) / 2 ≤ Real.exp (t ^ 2 * a ^ 2 / 2)`.

Equivalent to `cosh(ta) ≤ exp(t²a²/2)`. This is the core sub-Gaussian
bound for a symmetric ±a random variable. -/
lemma cosh_le_exp_sq_half (t a : ℝ) :
    (Real.exp (t * a) + Real.exp (-(t * a))) / 2
      ≤ Real.exp (t ^ 2 * a ^ 2 / 2) := by
  have h := Real.cosh_le_exp_half_sq (t * a)
  rw [Real.cosh_eq] at h
  have hrw : (t * a) ^ 2 / 2 = t ^ 2 * a ^ 2 / 2 := by ring
  rw [hrw] at h
  exact h

/-- Average of `exp(t · signOfBool(b) · a)` over `b : Bool` equals
`(exp(t·a) + exp(-t·a))/2`. -/
lemma avg_exp_sign (t a : ℝ) :
    (∑ b : Bool, Real.exp (t * signOfBool b * a)) / 2
      = (Real.exp (t * a) + Real.exp (-(t * a))) / 2 := by
  simp only [Fintype.sum_bool, signOfBool_true, signOfBool_false]
  ring_nf

/-! ## Helper: product MGF bound over coordinates

For a fixed hypothesis `i` and parameter `t > 0`, the average over all
sign vectors of `exp(t · (1/n) ∑_k σ_k · ℓ_i(z_k))` is bounded by
`exp(t² · B² / (2·n))` when `|ℓ_i(z_k)| ≤ B` for all `k`.
-/

omit [Fintype ι] [Nonempty ι] in
/-- The sign-vector average of `exp(t · signedEmpiricalMean_i)` factors
as a product over coordinates and is bounded by `exp(t² · B² / (2·n))`. -/
lemma sign_avg_exp_le {ℓ : ι → Z → ℝ} {z : Fin n → Z} {B : ℝ}
    (hBound : ∀ i : ι, ∀ k : Fin n, |ℓ i (z k)| ≤ B)
    (hn : 0 < n) (i : ι) (t : ℝ) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
        Real.exp (t * ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k)))
      ≤ Real.exp (t ^ 2 * B ^ 2 / (2 * n)) := by
  -- Step 1: rewrite the exponent so exp of sum becomes product of exps.
  have h_exp_sum : ∀ σ : Fin n → Bool,
      Real.exp (t * ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k)))
        = ∏ k : Fin n, Real.exp (t * (n : ℝ)⁻¹ * signOfBool (σ k) * ℓ i (z k)) := by
    intro σ
    have hrw : t * ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k))
          = ∑ k : Fin n, t * (n : ℝ)⁻¹ * signOfBool (σ k) * ℓ i (z k) := by
      have h1 : t * ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k))
            = (t * (n : ℝ)⁻¹) * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k) := by ring
      rw [h1, Finset.mul_sum Finset.univ _ (t * (n : ℝ)⁻¹)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [hrw, Real.exp_sum]
  -- Step 2: use h_exp_sum to rewrite the LHS.
  simp_rw [h_exp_sum]
  -- Now LHS is: (2^n)⁻¹ * ∑_σ ∏_k exp(t/n * signOfBool(σ k) * ℓ i (z k))
  -- Step 3: factor the sum over sign vectors as a product over coordinates.
  -- Use Fintype.prod_sum: ∏_k ∑_b f k b = ∑_{σ : ∀ k, Bool} ∏_k f k (σ k)
  rw [show ∑ σ : Fin n → Bool, ∏ k : Fin n,
        Real.exp (t * (n : ℝ)⁻¹ * signOfBool (σ k) * ℓ i (z k))
      = ∏ k : Fin n, ∑ b : Bool,
        Real.exp (t * (n : ℝ)⁻¹ * signOfBool b * ℓ i (z k)) from by
    rw [← Fintype.prod_sum (fun k (b : Bool) =>
        Real.exp (t * (n : ℝ)⁻¹ * signOfBool b * ℓ i (z k)))]]
  -- Step 4: bound each coordinate factor by the cosh lemma.
  -- Each ∑_{b:Bool} exp(t/n * signOfBool(b) * a_k) = 2 · cosh(t*a_k/n) ≤ 2 · exp(t²a_k²/(2n²))
  have h_coord_bound : ∀ k : Fin n,
      ∑ b : Bool, Real.exp (t * (n : ℝ)⁻¹ * signOfBool b * ℓ i (z k))
        ≤ 2 * Real.exp (t ^ 2 * (n : ℝ)⁻¹ ^ 2 * ℓ i (z k) ^ 2 / 2) := by
    intro k
    have hcosh := cosh_le_exp_sq_half (t * (n : ℝ)⁻¹) (ℓ i (z k))
    have hsum : ∑ b : Bool, Real.exp (t * (n : ℝ)⁻¹ * signOfBool b * ℓ i (z k))
        = Real.exp (t * (n : ℝ)⁻¹ * ℓ i (z k))
          + Real.exp (-(t * (n : ℝ)⁻¹ * ℓ i (z k))) := by
      simp only [Fintype.sum_bool, signOfBool_true, signOfBool_false]
      ring_nf
    rw [hsum]
    have hrw2 : (t * (↑n)⁻¹) ^ 2 * ℓ i (z k) ^ 2 / 2 = t ^ 2 * (↑n)⁻¹ ^ 2 * ℓ i (z k) ^ 2 / 2 := by
      ring
    linarith [hcosh, hrw2 ▸ hcosh]
  -- Step 5: bound the product using coordinate bounds.
  -- ∏_k (∑_b exp(...)) ≤ ∏_k (2 * exp(t²/(2n²) * ℓ_i(z_k)²))
  have h_prod_bound :
      ∏ k : Fin n, ∑ b : Bool, Real.exp (t * (n : ℝ)⁻¹ * signOfBool b * ℓ i (z k))
        ≤ ∏ k : Fin n, (2 * Real.exp (t ^ 2 * (n : ℝ)⁻¹ ^ 2 * ℓ i (z k) ^ 2 / 2)) :=
    Finset.prod_le_prod
      (fun k _ => Finset.sum_nonneg (fun b _ => le_of_lt (Real.exp_pos _)))
      (fun k _ => h_coord_bound k)
  -- Step 6: simplify (2^n)⁻¹ * ∏_k (2 * exp(c_k)).
  -- ∏_k (2 * exp(c_k)) = 2^n * ∏_k exp(c_k)
  have h_factor_two :
      ∏ k : Fin n, (2 * Real.exp (t ^ 2 * (n : ℝ)⁻¹ ^ 2 * ℓ i (z k) ^ 2 / 2))
        = (2 : ℝ) ^ n * ∏ k : Fin n, Real.exp (t ^ 2 * (n : ℝ)⁻¹ ^ 2 * ℓ i (z k) ^ 2 / 2) := by
    rw [Finset.prod_mul_distrib]
    simp [Finset.prod_const]
  -- Step 7: (2^n)⁻¹ * (2^n * X) = X
  have h_cancel : ((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n *
      ∏ k : Fin n, Real.exp (t ^ 2 * (n : ℝ)⁻¹ ^ 2 * ℓ i (z k) ^ 2 / 2))
    = ∏ k : Fin n, Real.exp (t ^ 2 * (n : ℝ)⁻¹ ^ 2 * ℓ i (z k) ^ 2 / 2) := by
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)), one_mul]
  -- Step 8: ∏_k exp(c_k) = exp(∑_k c_k)
  have h_prod_exp :
      ∏ k : Fin n, Real.exp (t ^ 2 * (n : ℝ)⁻¹ ^ 2 * ℓ i (z k) ^ 2 / 2)
        = Real.exp (∑ k : Fin n, t ^ 2 * (n : ℝ)⁻¹ ^ 2 * ℓ i (z k) ^ 2 / 2) :=
    (Real.exp_sum Finset.univ _).symm
  -- Step 9: bound ∑_k ℓ_i(z_k)² ≤ n * B²
  have h_sum_sq_bound :
      ∑ k : Fin n, t ^ 2 * (n : ℝ)⁻¹ ^ 2 * ℓ i (z k) ^ 2 / 2
        ≤ t ^ 2 * B ^ 2 / (2 * n) := by
    have h_nnR : (0 : ℝ) ≤ t ^ 2 * (n : ℝ)⁻¹ ^ 2 / 2 := by positivity
    calc ∑ k : Fin n, t ^ 2 * (n : ℝ)⁻¹ ^ 2 * ℓ i (z k) ^ 2 / 2
        = t ^ 2 * (n : ℝ)⁻¹ ^ 2 / 2 * ∑ k : Fin n, ℓ i (z k) ^ 2 := by
          rw [Finset.mul_sum Finset.univ (fun k => ℓ i (z k) ^ 2) (t ^ 2 * (n : ℝ)⁻¹ ^ 2 / 2)]
          refine Finset.sum_congr rfl (fun k _ => ?_); ring
      _ ≤ t ^ 2 * (n : ℝ)⁻¹ ^ 2 / 2 * (↑n * B ^ 2) := by
          gcongr
          calc ∑ k : Fin n, ℓ i (z k) ^ 2
              ≤ ∑ _k : Fin n, B ^ 2 :=
                Finset.sum_le_sum (fun k _ => by
                  have hab := hBound i k
                  have h1 := (abs_le.mp hab).1
                  have h2 := (abs_le.mp hab).2
                  exact sq_le_sq' (by linarith) h2)
            _ = ↑n * B ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
      _ = t ^ 2 * B ^ 2 / (2 * n) := by
          field_simp
  -- Assemble: LHS ≤ (2^n)⁻¹ * ∏_k (...) ≤ ... ≤ exp(t²B²/(2n))
  calc ((2 : ℝ) ^ n)⁻¹ * ∏ k : Fin n, ∑ b : Bool,
        Real.exp (t * (n : ℝ)⁻¹ * signOfBool b * ℓ i (z k))
      ≤ ((2 : ℝ) ^ n)⁻¹ * ∏ k : Fin n,
          (2 * Real.exp (t ^ 2 * (n : ℝ)⁻¹ ^ 2 * ℓ i (z k) ^ 2 / 2)) := by
        gcongr
    _ = ((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n *
          ∏ k : Fin n, Real.exp (t ^ 2 * (n : ℝ)⁻¹ ^ 2 * ℓ i (z k) ^ 2 / 2)) := by
        rw [h_factor_two]
    _ = ∏ k : Fin n, Real.exp (t ^ 2 * (n : ℝ)⁻¹ ^ 2 * ℓ i (z k) ^ 2 / 2) := h_cancel
    _ = Real.exp (∑ k : Fin n, t ^ 2 * (n : ℝ)⁻¹ ^ 2 * ℓ i (z k) ^ 2 / 2) := h_prod_exp
    _ ≤ Real.exp (t ^ 2 * B ^ 2 / (2 * n)) := Real.exp_le_exp.mpr h_sum_sq_bound

/-! ## Helper: log-sum-exp bound for finite supremum

For any `t > 0` and any finite family of reals `x : ι → ℝ`,
`Finset.univ.sup' H x ≤ (1/t) · Real.log (∑ i, Real.exp (t * x i))`.
-/

/-- The sup of a finite nonempty family of reals is bounded above by the
log-sum-exp with parameter `t > 0`:
`sup_i x_i ≤ (1/t) · log(∑_i exp(t · x_i))`. -/
lemma sup_le_log_sum_exp (x : ι → ℝ) {t : ℝ} (ht : 0 < t) :
    (Finset.univ : Finset ι).sup' Finset.univ_nonempty x
      ≤ t⁻¹ * Real.log (∑ i : ι, Real.exp (t * x i)) := by
  -- It suffices to show that for every i, x i ≤ RHS.
  refine Finset.sup'_le _ _ (fun i _ => ?_)
  -- For any i: exp(t * x i) ≤ ∑_j exp(t * x j)
  have h_le_sum : Real.exp (t * x i) ≤ ∑ j : ι, Real.exp (t * x j) :=
    Finset.single_le_sum (f := fun j => Real.exp (t * x j))
      (fun j _ => le_of_lt (Real.exp_pos _)) (Finset.mem_univ i)
  -- The sum of exponentials is positive
  have h_sum_pos : (0 : ℝ) < ∑ j : ι, Real.exp (t * x j) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) ⟨i, Finset.mem_univ i⟩
  -- Take log: t * x i ≤ log(∑_j exp(t * x j))
  have h_log : t * x i ≤ Real.log (∑ j : ι, Real.exp (t * x j)) := by
    calc t * x i = Real.log (Real.exp (t * x i)) := (Real.log_exp _).symm
      _ ≤ Real.log (∑ j : ι, Real.exp (t * x j)) :=
          Real.log_le_log (Real.exp_pos _) h_le_sum
  -- Divide by t > 0
  rwa [le_inv_mul_iff₀ ht]

/-! ## Helper: Jensen + averaging

Combining the sup bound with the sign average.
-/

/-- The empirical Rademacher complexity is bounded by the log-sum-exp of
the sign-vector MGFs:
`empiricalRademacherComplexity ℓ z ≤ t⁻¹ · log(∑_i E_σ[exp(t · f_i(σ))])`.
-/
lemma rademacher_le_log_sum_mgf {ℓ : ι → Z → ℝ} {z : Fin n → Z}
    {t : ℝ} (ht : 0 < t) :
    empiricalRademacherComplexity ℓ z
      ≤ t⁻¹ * Real.log (∑ i : ι,
          ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
            Real.exp (t * ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k)))) := by
  -- Unfold empiricalRademacherComplexity
  unfold empiricalRademacherComplexity
  -- For each σ, apply sup_le_log_sum_exp:
  -- sup_i f_i(σ) ≤ t⁻¹ * log(∑_i exp(t * f_i(σ)))
  have h_pointwise : ∀ σ : Fin n → Bool,
      (Finset.univ : Finset ι).sup' Finset.univ_nonempty
        (fun i => (n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k))
      ≤ t⁻¹ * Real.log (∑ i : ι,
          Real.exp (t * ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k)))) :=
    fun σ => sup_le_log_sum_exp _ ht
  -- Average both sides over sign vectors (multiply by (2^n)⁻¹ and sum)
  have h_avg : ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
      (Finset.univ : Finset ι).sup' Finset.univ_nonempty
        (fun i => (n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k))
    ≤ ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
        t⁻¹ * Real.log (∑ i : ι,
          Real.exp (t * ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k)))) := by
    gcongr with σ
    exact h_pointwise σ
  -- Factor out t⁻¹ from the RHS of h_avg.
  have h_rhs_factor :
      ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
        t⁻¹ * Real.log (∑ i : ι,
          Real.exp (t * ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k))))
      = t⁻¹ * (((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
          Real.log (∑ i : ι,
            Real.exp (t * ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k))))) := by
    rw [← Finset.mul_sum]
    ring
  -- Set Y(σ) = ∑_i exp(t * f_i(σ)).
  set Y : (Fin n → Bool) → ℝ :=
    fun σ => ∑ i : ι, Real.exp (t * ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k)))
  -- Y(σ) > 0 for all σ.
  have hY_pos : ∀ σ, 0 < Y σ :=
    fun σ => Finset.sum_pos (fun i _ => Real.exp_pos _) ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  -- Jensen for concave log: E[log Y] ≤ log(E[Y]) where weights are uniform.
  -- Using ConcaveOn.le_map_sum with w_σ = (2^n)⁻¹, p_σ = Y(σ).
  have h_two_pow_pos : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have h_inv_nn : (0 : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹ := le_of_lt (inv_pos.mpr h_two_pow_pos)
  have h_weights_sum : ∑ _σ : Fin n → Bool, ((2 : ℝ) ^ n)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, card_signVectors]
    simp [nsmul_eq_mul]
  have h_jensen' :
      ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, Real.log (Y σ)
        ≤ Real.log (((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, Y σ) := by
    -- Convert to smul form and apply ConcaveOn.le_map_sum.
    have lhs_rw : ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, Real.log (Y σ)
        = ∑ σ : Fin n → Bool, ((2 : ℝ) ^ n)⁻¹ * Real.log (Y σ) := by
      rw [Finset.mul_sum]
    have rhs_rw : ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, Y σ
        = ∑ σ : Fin n → Bool, ((2 : ℝ) ^ n)⁻¹ * Y σ := by
      rw [Finset.mul_sum]
    rw [lhs_rw, rhs_rw]
    -- Now in the form: ∑ w • f(p) ≤ f(∑ w • p) with smul = mul for ℝ.
    have := ConcaveOn.le_map_sum (f := Real.log) (s := Set.Ioi 0)
      (t := Finset.univ) (w := fun _ => ((2 : ℝ) ^ n)⁻¹) (p := Y)
      strictConcaveOn_log_Ioi.concaveOn
      (fun σ _ => h_inv_nn)
      h_weights_sum
      (fun σ _ => Set.mem_Ioi.mpr (hY_pos σ))
    simp only [smul_eq_mul] at this
    exact this
  -- Swap the inner sum: (2^n)⁻¹ * ∑_σ Y(σ) = (2^n)⁻¹ * ∑_σ ∑_i exp(...)
  --   = ∑_i (2^n)⁻¹ * ∑_σ exp(...)
  have h_swap : ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, Y σ
      = ∑ i : ι, ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
          Real.exp (t * ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k))) := by
    dsimp [Y]
    rw [← Finset.mul_sum, Finset.sum_comm]
  -- Assemble the full proof via explicit steps.
  have step1 : ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
      (Finset.univ : Finset ι).sup' Finset.univ_nonempty
        (fun i => (n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k))
    ≤ t⁻¹ * (((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, Real.log (Y σ)) := by
    rw [← h_rhs_factor]; exact h_avg
  have step2 : t⁻¹ * (((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, Real.log (Y σ))
    ≤ t⁻¹ * Real.log (((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, Y σ) :=
    mul_le_mul_of_nonneg_left h_jensen' (le_of_lt (inv_pos.mpr ht))
  have step3 : t⁻¹ * Real.log (((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, Y σ)
    = t⁻¹ * Real.log (∑ i : ι, ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
          Real.exp (t * ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k)))) := by
    exact congrArg (fun x => t⁻¹ * Real.log x) h_swap
  exact step1.trans (step2.trans_eq step3)

/-! ## Main theorem: Massart's finite-class lemma -/

/-- **Massart's finite-class lemma.**

For a finite nonempty hypothesis class `ι` and sample `z : Fin n → Z`
with loss functions `ℓ : ι → Z → ℝ` uniformly bounded by `B` (i.e.,
`|ℓ i (z k)| ≤ B` for all `i`, `k`), the empirical Rademacher complexity
satisfies:

  `empiricalRademacherComplexity ℓ z ≤ B * Real.sqrt (2 * Real.log ↑(Fintype.card ι) / ↑n)`

Requires `1 < Fintype.card ι` (at least two hypotheses) and `0 < n`
(nonempty sample). The bound is trivially true for a singleton class
(where the complexity is 0) but the log form requires `log|H| > 0`.
-/
theorem massart_finite_class {ℓ : ι → Z → ℝ} {z : Fin n → Z} {B : ℝ}
    (hB : 0 < B)
    (hBound : ∀ i : ι, ∀ k : Fin n, |ℓ i (z k)| ≤ B)
    (hn : 0 < n)
    (hCard : 1 < Fintype.card ι) :
    empiricalRademacherComplexity ℓ z
      ≤ B * Real.sqrt (2 * Real.log (Fintype.card ι : ℝ) / (n : ℝ)) := by
  -- Choose the optimal t = √(2n · log|H|) / B.
  set logH := Real.log (Fintype.card ι : ℝ) with hlogH_def
  have hlogH_pos : 0 < logH := by
    rw [hlogH_def]
    exact Real.log_pos (by exact_mod_cast hCard)
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  set t₀ := Real.sqrt (2 * (n : ℝ) * logH) / B with ht₀_def
  have ht₀_pos : 0 < t₀ := by
    rw [ht₀_def]
    exact div_pos (Real.sqrt_pos.mpr (by positivity)) hB
  -- Apply rademacher_le_log_sum_mgf with t = t₀.
  have h1 := rademacher_le_log_sum_mgf (ι := ι) (Z := Z) ht₀_pos (ℓ := ℓ) (z := z)
  -- Bound each sign-average MGF.
  have h_mgf_bound : ∀ i : ι,
      ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
        Real.exp (t₀ * ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k)))
      ≤ Real.exp (t₀ ^ 2 * B ^ 2 / (2 * n)) :=
    fun i => sign_avg_exp_le hBound hn i t₀
  -- The sum of MGFs ≤ |H| * exp(t₀²B²/(2n)).
  have h_sum_bound :
      ∑ i : ι, ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
        Real.exp (t₀ * ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k)))
      ≤ (Fintype.card ι : ℝ) * Real.exp (t₀ ^ 2 * B ^ 2 / (2 * n)) := by
    calc ∑ i : ι, ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
          Real.exp (t₀ * ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k)))
        ≤ ∑ _i : ι, Real.exp (t₀ ^ 2 * B ^ 2 / (2 * n)) :=
          Finset.sum_le_sum (fun i _ => h_mgf_bound i)
      _ = (Fintype.card ι : ℝ) * Real.exp (t₀ ^ 2 * B ^ 2 / (2 * n)) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Compute t₀² * B² / (2n) and log|H| / t₀.
  have ht₀_sq : t₀ ^ 2 = 2 * (n : ℝ) * logH / B ^ 2 := by
    rw [ht₀_def, div_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * ↑n * logH)]
  have h_exp_arg : t₀ ^ 2 * B ^ 2 / (2 * n) = logH := by
    rw [ht₀_sq]; field_simp
  -- So the sum ≤ |H| * exp(logH) = |H|².
  -- And log of that: log(|H| * exp(logH)) = log|H| + logH = 2*log|H|.
  have h_log_bound :
      Real.log ((Fintype.card ι : ℝ) * Real.exp (t₀ ^ 2 * B ^ 2 / (2 * n)))
        = 2 * logH := by
    rw [h_exp_arg, Real.log_mul (by positivity : (Fintype.card ι : ℝ) ≠ 0)
        (ne_of_gt (Real.exp_pos _)), Real.exp_log (by positivity : (0 : ℝ) < Fintype.card ι)]
    ring
  -- Compute t₀⁻¹ = B / √(2n·log|H|).
  have ht₀_inv : t₀⁻¹ = B / Real.sqrt (2 * (n : ℝ) * logH) := by
    rw [ht₀_def, inv_div]
  -- So t₀⁻¹ * log(...) ≤ t₀⁻¹ * 2 * logH = B * 2*logH / √(2n*logH)
  --   = B * 2*logH / √(2n*logH) = B * √(2*logH/n).
  -- Actually: t₀⁻¹ * 2*logH = (B/√(2n*logH)) * 2*logH = 2B*logH/√(2n*logH)
  -- = B * √(4*logH²/(2n*logH)) = B * √(2*logH/n). ✓
  have h_final_rhs : t₀⁻¹ * (2 * logH) = B * Real.sqrt (2 * logH / (n : ℝ)) := by
    rw [ht₀_inv]
    have h2nL_pos : (0 : ℝ) < 2 * ↑n * logH := by positivity
    -- B / √(2nL) * (2L) = B * (2L / √(2nL)) = B * √(4L²/(2nL)) = B * √(2L/n)
    rw [show B / Real.sqrt (2 * ↑n * logH) * (2 * logH)
          = B * (2 * logH / Real.sqrt (2 * ↑n * logH)) from by ring]
    congr 1
    -- Need: 2L / √(2nL) = √(2L/n)
    -- We prove by showing both sides are nonneg and have the same square.
    have hlhs_nn : (0 : ℝ) ≤ 2 * logH / Real.sqrt (2 * ↑n * logH) := by positivity
    have hrhs_nn : (0 : ℝ) ≤ Real.sqrt (2 * logH / ↑n) := Real.sqrt_nonneg _
    rw [← Real.sqrt_sq hlhs_nn]
    congr 1
    rw [div_pow, Real.sq_sqrt (le_of_lt h2nL_pos)]
    field_simp
  -- Combine: rademacher ≤ t₀⁻¹ * log(sum) ≤ t₀⁻¹ * log(|H|*exp(logH)) = t₀⁻¹ * 2*logH = B*√(2logH/n)
  calc empiricalRademacherComplexity ℓ z
      ≤ t₀⁻¹ * Real.log (∑ i : ι, ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
          Real.exp (t₀ * ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k)))) := h1
    _ ≤ t₀⁻¹ * Real.log ((Fintype.card ι : ℝ) * Real.exp (t₀ ^ 2 * B ^ 2 / (2 * n))) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (inv_pos.mpr ht₀_pos))
        apply Real.log_le_log
        · exact Finset.sum_pos (fun i _ => by positivity)
            ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
        · exact h_sum_bound
    _ = t₀⁻¹ * (2 * logH) := by rw [h_log_bound]
    _ = B * Real.sqrt (2 * logH / (n : ℝ)) := h_final_rhs

end

end FormalSLT.Rademacher.Massart
