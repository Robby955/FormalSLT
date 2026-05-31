/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import FormalSLT.Concentration.SubGamma.BennettBound
import FormalSLT.Concentration.SubGamma.BoundedExpIntegrable

/-!
# Conditional sub-gamma MGF extractor

This file proves the conditional sub-gamma MGF extractor lemma. A bounded,
conditionally centered random variable `X`
with conditional second moment at most `σ²` has a conditional MGF bounded
by the sub-gamma exponential

    exp(σ² λ² / (2 (1 − b λ / 3))).

This is the conditional analogue of the usual bounded-increment
sub-gamma MGF estimate. It derives the conditional MGF bound from
boundedness, conditional centering, and a conditional second-moment proxy.

The proof combines:

- `FormalSLT.Concentration.SubGamma.bennett_taylor_bound`, the pointwise
  sub-gamma Taylor inequality
  `exp(λ x) ≤ 1 + λ x + (λ² x²) / (2 (1 − b λ / 3))`
  for `|x| ≤ b` and `b λ < 3`;
- conditional-expectation monotonicity and linearity;
- conditional centering and the conditional second-moment bound;
- the elementary final step `1 + u ≤ exp u`.
-/

open MeasureTheory ProbabilityTheory

namespace FormalSLT.Concentration.SubGamma

/--
**Conditional sub-gamma MGF extractor.**

For a bounded random variable `X` with `|X| ≤ b` a.s., conditional mean
`μ[X | m] = 0`, and conditional second moment `μ[X² | m] ≤ σ²`, the
conditional MGF satisfies a sub-gamma bound on the regime `b · λ < 3`.

This derives the bound from the bounded and conditional-variance
hypotheses alone, with no MGF assumption.
-/
theorem condSubGammaMGF_of_bounded_centered_condVariance
    {Ω : Type*} [m₀ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω}
    {X : Ω → ℝ}
    {b σ2 : ℝ}
    (hb_pos : 0 < b)
    (_hσ_nonneg : 0 ≤ σ2)
    (hX_meas : Measurable[m₀] X)
    (hX_int : Integrable X μ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b)
    (hcenter : μ[X | m] =ᵐ[μ] 0)
    (hvar : μ[fun ω => X ω ^ 2 | m] ≤ᵐ[μ] fun _ => σ2) :
    ∀ lam, 0 ≤ lam → b * lam < 3 →
      μ[fun ω => Real.exp (lam * X ω) | m]
        ≤ᵐ[μ]
      fun _ => Real.exp (σ2 * lam ^ 2 / (2 * (1 - b * lam / 3))) := by
  intro lam hlam hblam
  -- The sub-gamma denominator constant; positive on the regime `b · lam < 3`.
  set K : ℝ := 2 * (1 - b * lam / 3) with hK_def
  have hK_pos : 0 < K := by
    have h1 : 0 < 1 - b * lam / 3 := by linarith
    have : 0 < 2 * (1 - b * lam / 3) := by positivity
    exact this
  -- Default-case branch: when `m ≰ m₀`, every conditional expectation is `0`
  -- by `condExp_of_not_le`, so the LHS is `0 ≤ exp(...)` trivially.
  by_cases hm : m ≤ m₀
  swap
  · rw [condExp_of_not_le hm]
    refine ae_of_all _ (fun ω => ?_)
    exact (Real.exp_pos _).le
  -- ─── main branch: m ≤ m₀ ────────────────────────────────────────────────
  -- Step 1: pointwise sub-gamma Taylor bound from `bennett_taylor_bound`,
  -- applied on the a.s. set `|X(ω)| ≤ b`.
  have h_pw :
      (fun ω => Real.exp (lam * X ω))
        ≤ᵐ[μ]
      (fun ω => 1 + lam * X ω + lam ^ 2 * X ω ^ 2 / K) := by
    filter_upwards [hbound] with ω hω
    have hxlo : -b ≤ X ω := (abs_le.mp hω).1
    have hxhi : X ω ≤ b := (abs_le.mp hω).2
    have h := bennett_taylor_bound (x := X ω) (b := b) (lam := lam)
      hb_pos hlam hblam hxlo hxhi
    -- `h` uses the literal `2 * (1 - b * lam / 3)`; `K` is the same.
    simpa [hK_def] using h
  -- Step 2: integrabilities for `condExp_mono`.
  have h_explamX_int : Integrable (fun ω => Real.exp (lam * X ω)) μ :=
    integrable_exp_mul_of_bounded hX_meas hbound
  -- X² integrable: dominated by the constant `b²` on the a.s. set `|X| ≤ b`.
  have hXsq_int : Integrable (fun ω => X ω ^ 2) μ := by
    refine MeasureTheory.Integrable.mono' (g := fun _ => b ^ 2)
      (integrable_const _) (hX_meas.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, ← sq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (abs_nonneg _) hω 2
  -- RHS integrability: sum of constant, scalar·X, scalar·X².
  have hRHS_int :
      Integrable (fun ω => 1 + lam * X ω + lam ^ 2 * X ω ^ 2 / K) μ := by
    have h1 : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const _
    have h2 : Integrable (fun ω => lam * X ω) μ := hX_int.const_mul lam
    have h3 : Integrable (fun ω => lam ^ 2 * X ω ^ 2 / K) μ := by
      have := (hXsq_int.const_mul (lam ^ 2)).div_const K
      simpa [mul_div_assoc] using this
    exact (h1.add h2).add h3
  -- Step 3: condExp_mono lifts the pointwise bound to conditional expectations.
  have h_mono :
      μ[fun ω => Real.exp (lam * X ω) | m]
        ≤ᵐ[μ]
      μ[fun ω => 1 + lam * X ω + lam ^ 2 * X ω ^ 2 / K | m] :=
    condExp_mono h_explamX_int hRHS_int h_pw
  -- ─── Step 4: linearize the RHS conditional expectation ────────────────
  -- Rewrite the integrand into the `Pi.add` form `1 + (λX + (λ²/K)X²)` so
  -- `condExp_add` unifies cleanly. The `Pi.add` of two functions is
  -- definitionally the pointwise-sum lambda, so `rfl` closes the equality.
  have hrewrite :
      (fun ω => 1 + lam * X ω + lam ^ 2 * X ω ^ 2 / K) =
      ((fun _ : Ω => (1 : ℝ)) + fun ω => lam * X ω + lam ^ 2 / K * X ω ^ 2) := by
    funext ω
    show 1 + lam * X ω + lam ^ 2 * X ω ^ 2 / K
       = (1 : ℝ) + (lam * X ω + lam ^ 2 / K * X ω ^ 2)
    ring
  have h_const_int : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const _
  have h_lin_int : Integrable (fun ω => lam * X ω) μ := hX_int.const_mul lam
  have h_quad_int : Integrable (fun ω => lam ^ 2 / K * X ω ^ 2) μ :=
    hXsq_int.const_mul _
  have h_lin_plus_quad_int :
      Integrable (fun ω => lam * X ω + lam ^ 2 / K * X ω ^ 2) μ :=
    h_lin_int.add h_quad_int
  -- μ[(fun _ => 1) + (fun ω => λX + (λ²/K)X²) | m]
  --   =ᵐ μ[(fun _ => 1) | m] + μ[(fun ω => λX + (λ²/K)X²) | m]
  have h_step1 :=
    condExp_add (μ := μ) h_const_int h_lin_plus_quad_int m
  -- μ[(fun ω => λX) + (fun ω => (λ²/K)X²) | m]
  --   =ᵐ μ[(fun ω => λX) | m] + μ[(fun ω => (λ²/K)X²) | m]
  have h_step2 := condExp_add (μ := μ) h_lin_int h_quad_int m
  -- μ[(fun _ => 1) | m] = (fun _ => 1)
  have h_const : μ[(fun _ : Ω => (1 : ℝ)) | m] = fun _ => 1 := condExp_const hm 1
  -- μ[λ • X | m] =ᵐ λ • μ[X | m]
  have h_smul_lin := condExp_smul (𝕜 := ℝ) (μ := μ) (m := m) lam X
  -- μ[(λ²/K) • X² | m] =ᵐ (λ²/K) • μ[X² | m]
  have h_smul_quad :=
    condExp_smul (𝕜 := ℝ) (μ := μ) (m := m) (lam ^ 2 / K) (fun ω => X ω ^ 2)
  -- The two `condExp_smul` instances apply with `λ • X = fun ω => lam * X ω`
  -- (definitional via `Pi.smul_apply` + `smul_eq_mul`). Translate
  -- `h_step2` and `h_smul_*` into the `μ[fun ω => …]` lambda form via
  -- `Pi.add` / `Pi.smul` rewrites so they unify with the lambda-form `condExp`s
  -- in the assembled goal.
  have h_lin_eq : μ[fun ω => lam * X ω | m] =ᵐ[μ] fun ω => lam * (μ[X | m]) ω := by
    have := h_smul_lin
    -- `lam • X = fun ω => lam * X ω` by `Pi.smul_apply` + `smul_eq_mul`.
    simpa [Pi.smul_apply, smul_eq_mul] using this
  have h_quad_eq :
      μ[fun ω => lam ^ 2 / K * X ω ^ 2 | m]
        =ᵐ[μ] fun ω => lam ^ 2 / K * (μ[fun ω => X ω ^ 2 | m]) ω := by
    have := h_smul_quad
    simpa [Pi.smul_apply, smul_eq_mul] using this
  -- Translate `h_step1` / `h_step2` from `Pi.add` form to `μ[fun ω => …]` form.
  -- `(f + g) ω = f ω + g ω` is `Pi.add_apply`; for `condExp` the integrand is
  -- the function itself, and `(fun _ => 1) + g` is definitionally
  -- `fun ω => 1 + g ω`, so a `simp` / `change` on the integrand closes.
  have h_sum_eq :
      μ[fun ω => 1 + lam * X ω + lam ^ 2 * X ω ^ 2 / K | m]
        =ᵐ[μ]
      μ[(fun _ : Ω => (1 : ℝ)) | m] + μ[fun ω => lam * X ω + lam ^ 2 / K * X ω ^ 2 | m] := by
    rw [hrewrite]; exact h_step1
  have h_sum_eq2 :
      μ[fun ω => lam * X ω + lam ^ 2 / K * X ω ^ 2 | m]
        =ᵐ[μ]
      μ[fun ω => lam * X ω | m] + μ[fun ω => lam ^ 2 / K * X ω ^ 2 | m] := h_step2
  -- Assemble: μ[1 + λX + (λ²/K)X² | m]
  --   =ᵐ 1 + λ·μ[X|m] + (λ²/K)·μ[X²|m]
  have h_lin :
      μ[fun ω => 1 + lam * X ω + lam ^ 2 * X ω ^ 2 / K | m]
        =ᵐ[μ]
      fun ω => 1 + lam * (μ[X | m]) ω + lam ^ 2 / K * (μ[fun ω => X ω ^ 2 | m]) ω := by
    filter_upwards [h_sum_eq, h_sum_eq2, h_lin_eq, h_quad_eq]
      with ω hs1 hs2 hle hqe
    -- hs1 : μ[1+λX+(λ²/K)X² | m] ω = (μ[1|m] + μ[λX+(λ²/K)X²|m]) ω
    -- hs2 : μ[λX+(λ²/K)X²|m] ω = (μ[λX|m] + μ[(λ²/K)X²|m]) ω
    -- hle : μ[λX|m] ω = λ·μ[X|m] ω
    -- hqe : μ[(λ²/K)X²|m] ω = (λ²/K)·μ[X²|m] ω
    -- h_const : μ[1|m] = fun _ => 1
    simp only [Pi.add_apply] at hs1 hs2
    rw [hs1, hs2, h_const, hle, hqe]
    show (1 : ℝ) + (lam * (μ[X | m]) ω + lam ^ 2 / K * (μ[fun ω => X ω ^ 2 | m]) ω)
       = 1 + lam * (μ[X | m]) ω + lam ^ 2 / K * (μ[fun ω => X ω ^ 2 | m]) ω
    ring
  -- ─── Step 5: substitute `hcenter` and `hvar` ──────────────────────────
  -- After linearization, the RHS becomes `1 + λ·0 + (λ²/K)·μ[X²|m]`, and
  -- `μ[X²|m] ≤ σ²` a.s. gives `1 + (λ²/K) σ² = 1 + σ² λ² / K`.
  have hlamK_nonneg : 0 ≤ lam ^ 2 / K :=
    div_nonneg (sq_nonneg _) hK_pos.le
  have h_bound :
      μ[fun ω => 1 + lam * X ω + lam ^ 2 * X ω ^ 2 / K | m]
        ≤ᵐ[μ]
      fun _ => 1 + σ2 * lam ^ 2 / K := by
    filter_upwards [h_lin, hcenter, hvar] with ω h_lin' h_ctr' h_var'
    -- h_lin': μ[1+λX+(λ²/K)X²|m] ω = 1 + λ * μ[X|m] ω + (λ²/K) * μ[X²|m] ω
    -- h_ctr': μ[X|m] ω = 0  (Pi.zero_apply gives `(0 : Ω → ℝ) ω = 0`)
    -- h_var': μ[X²|m] ω ≤ σ²
    rw [h_lin']
    have h_ctr'' : (μ[X | m]) ω = 0 := by simpa using h_ctr'
    rw [h_ctr'', mul_zero, add_zero]
    -- Goal: 1 + (λ²/K) * μ[X²|m] ω ≤ 1 + σ² * λ² / K
    have h_quad_le : lam ^ 2 / K * (μ[fun ω => X ω ^ 2 | m]) ω ≤ lam ^ 2 / K * σ2 :=
      mul_le_mul_of_nonneg_left h_var' hlamK_nonneg
    have : (1 : ℝ) + lam ^ 2 / K * σ2 = 1 + σ2 * lam ^ 2 / K := by ring
    linarith
  -- ─── Step 6: combine with `h_mono` and apply `1 + u ≤ exp u` ───────────
  -- Final: μ[exp(λX) | m] ≤ᵐ 1 + σ²λ²/K ≤ exp(σ²λ²/K).
  refine (h_mono.trans h_bound).trans ?_
  refine ae_of_all _ (fun ω => ?_)
  -- Goal: 1 + σ² * λ² / K ≤ Real.exp (σ² * λ² / (2 * (1 - b * lam / 3)))
  -- K = 2 * (1 - b * lam / 3), so σ² * λ² / K = σ² * λ² / (2 * (1 - b*lam/3)).
  show (1 : ℝ) + σ2 * lam ^ 2 / K ≤ Real.exp (σ2 * lam ^ 2 / (2 * (1 - b * lam / 3)))
  rw [show (2 : ℝ) * (1 - b * lam / 3) = K from rfl]
  have := Real.add_one_le_exp (σ2 * lam ^ 2 / K)
  linarith

end FormalSLT.Concentration.SubGamma
