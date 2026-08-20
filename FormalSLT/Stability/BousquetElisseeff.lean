/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AlgorithmicStability
import FormalSLT.Azuma.SharpMcDiarmid
import FormalSLT.Concentration.SharpMcDiarmid
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# T4: McDiarmid-style i.i.d. concentration and stability bounds

Sources:
* McDiarmid (1989), "On the method of bounded differences." Surveys in
  Combinatorics, LMS Lecture Notes 141, 148-188.
* Bousquet & Elisseeff (2002), "Stability and Generalization." JMLR 2,
  Theorem 12 (high-probability generalization for stable algorithms).

This module composes the existing FormalSLT building blocks
(`stability_genGap_hasBoundedDifferences` from `AlgorithmicStability` and
`mcdiarmid_of_hasBoundedDifferences_sharp` from `Concentration.SharpMcDiarmid`)
into:

1. `mcdiarmid_inequality_iid_const_width`: McDiarmid concentration tail under
   the i.i.d. product measure with constant bounded-differences width `c` and
   sharp exponent `exp(-2ε²/(nc²))`.

2. `bousquet_elisseeff_centered_tail`: combines the bounded-differences property
   of the generalization-gap functional `S ↦ R(A(S)) - L̂(A(S))` with the i.i.d.
   McDiarmid tail to give centered concentration
   `P[ R(A(S)) - L̂(A(S)) ≥ E[..] + ε ] ≤ exp(-2ε²/(n(2β+2B/n)²))`.

3. `bousquet_elisseeff_confidence_threshold` and
   `bousquet_elisseeff_confidence`: δ-confidence form via inversion of
   `exp(-2ε²/(nc²)) ≤ δ`. The first takes ε as a threshold hypothesis; the
   second gives the explicit `(2β + 2B/n)·√(-(n·log δ)/2)` form.

4. `bousquet_elisseeff_expectedGap_variant`: a sharp McDiarmid expected-gap
   variant combining the centered tail with a hypothesis on the expected gap.
   Bousquet-Elisseeff (2002) Theorem 9 derives `E[R(A(S)) - L̂(A(S))] ≤ β`
   from uniform stability and i.i.d.; the finite-Z analogue is fully proved in
   `expectedFiniteStabilityGap_le_uniformStability_finiteProduct`, and the
   product-measure version is available as
   `expectedStabilityGap_le_uniformStability_piMeasure` under explicit
   integrability assumptions.

5. `bousquet_elisseeff_uniform_stability_corollary`: a clean restatement for
   stability `β = c₀/n`, exhibiting the textbook `O(1/√n)` high-probability
   rate.
6. `bousquet_elisseeff_expectedGap_variant_of_boundedLoss` and
   `bousquet_elisseeff_uniform_stability_corollary_of_boundedLoss`: finite-class
   bounded-loss wrappers that discharge the expected-gap, measurability, and
   integrability hypotheses from a measurable algorithm and measurable bounded
   scalar losses.

## Scope and boundaries

* The McDiarmid statement in this file consumes the sharp product-measure
  bounded-differences theorem from `FormalSLT/Concentration/SharpMcDiarmid.lean`.

* `bousquet_elisseeff_expectedGap_variant` takes `E[gap] ≤ β`
  (the iid expectation bound, Bousquet-Elisseeff Theorem 9) as an explicit
  hypothesis. The finite-Z version is closed by
  `expectedFiniteStabilityGap_le_uniformStability_finiteProduct`; the
  product-measure version is closed by
  `expectedStabilityGap_le_uniformStability_piMeasure` with explicit
  integrability assumptions.

* `bousquet_elisseeff_uniform_stability_corollary` instantiates with the
  scalar form `β = c₀ / n`. Some regularized ERM settings satisfy such a
  uniform-stability rate, but deriving those algorithm-specific stability
  facts is left to follow-up work; the corollary here is the
  high-probability bound *given* such a stability constant.

No `sorry`, no `admit`, no custom `axiom`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal ENNReal

namespace FormalSLT.AlgorithmicStability

open FormalSLT.Risk
open FormalSLT.Azuma.BoundedDifferences (HasBoundedDifferences)
open FormalSLT.Concentration (mcdiarmid_of_hasBoundedDifferences_sharp)

variable {ι Z : Type*}

/-! ### Step 1: McDiarmid's inequality (i.i.d., constant-width, sharp constant)

Source: McDiarmid (1989), "On the method of bounded differences." -/

/-- McDiarmid's inequality for a function of `n` independent inputs with
**constant** bounded-differences width `c`. Under the i.i.d. product measure
`μⁿ`, for any `ε ≥ 0`:

    μⁿ { S : Fin n → Z | ∫ f dμⁿ + ε ≤ f S }  ≤  exp(-2ε² / (n c²)).

This is the constant-width specialization of the sharp product-measure
bounded-differences theorem in `FormalSLT/Concentration/SharpMcDiarmid.lean`.

Source: McDiarmid (1989), Theorem 3.1. -/
theorem mcdiarmid_inequality_iid_const_width
    {n : ℕ} [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {f : (Fin n → Z) → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hbdd : HasBoundedDifferences f (fun _ : Fin n => c))
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ)))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | ∫ s, f s ∂(Measure.pi (fun _ : Fin n => μ)) + ε ≤ f S}
      ≤ Real.exp (-2 * ε ^ 2 / ((n : ℝ) * c ^ 2)) := by
  have hSharp := mcdiarmid_of_hasBoundedDifferences_sharp hbdd hf hfi
    (fun _ => hc) hε
  have h_sum_real :
      (∑ _k : Fin n, c ^ 2) = (n : ℝ) * c ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hexp_eq :
      -2 * ε ^ 2 / (∑ _k : Fin n, c ^ 2)
        = -2 * ε ^ 2 / ((n : ℝ) * c ^ 2) := by
    rw [h_sum_real]
  rw [hexp_eq] at hSharp
  exact hSharp

/-- Addendum: the same constant-width iid concentration theorem routed through
the q049 `FormalSLT.Azuma.SharpMcDiarmid` API.

This keeps the Bousquet-Elisseeff module's existing McDiarmid wrapper in place
and records the sharp exposure-martingale route side-by-side. -/
theorem sharp_mcdiarmid_inequality_iid_const_width_addendum
    {n : ℕ} [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {f : (Fin n → Z) → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hbdd : HasBoundedDifferences f (fun _ : Fin n => c))
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ)))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | ∫ s, f s ∂(Measure.pi (fun _ : Fin n => μ)) + ε ≤ f S}
      ≤ Real.exp (-2 * ε ^ 2 / ((n : ℝ) * c ^ 2)) :=
  FormalSLT.Azuma.ExposureMartingale.sharp_mcdiarmid_inequality_iid_const_width
    (ν := μ) hc hbdd hf hfi hε

/-! ### Step 2: Bousquet-Elisseeff centered concentration -/

/-- **Bousquet-Elisseeff-style centered tail, sharp McDiarmid variant.**

If `A` has uniform stability `β` and the loss `ℓ` is bounded by `B` with
each `ℓ i` integrable against `μ`, then under the iid product measure
`μⁿ`, the generalization-gap functional
`F : S ↦ R(A(S)) - L̂(A(S))` concentrates around its mean:

    μⁿ { S | E[F] + ε ≤ F(S) }  ≤  exp(-2ε² / (n (2β + 2B/n)²)).

The proof is `stability_genGap_hasBoundedDifferences` composed with
`mcdiarmid_inequality_iid_const_width`.

The measurability and integrability of `F` are taken as explicit
hypotheses because no measurability hypothesis is imposed on the
algorithm `A : (Fin n → Z) → ι`; for finite `ι` with measurable
preimages, both follow from the boundedness `|F S| ≤ 2B`. -/
theorem bousquet_elisseeff_centered_tail
    [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β B : ℝ}
    (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hstab : UniformStability A ℓ β)
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (hℓ_int : ∀ i, Integrable (ℓ i) μ)
    (hF_meas : StronglyMeasurable (fun S : Fin n → Z =>
        ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S))
    (hF_int : Integrable (fun S : Fin n → Z =>
        ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S)
      (Measure.pi (fun _ : Fin n => μ)))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | ∫ s, (∫ z, ℓ (A s) z ∂μ - trainingLoss A ℓ s)
                ∂(Measure.pi (fun _ : Fin n => μ)) + ε
              ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S}
      ≤ Real.exp (-2 * ε ^ 2 / ((n : ℝ) * (2 * β + 2 * B / n) ^ 2)) := by
  have hbdd : HasBoundedDifferences
      (fun S : Fin n → Z => ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S)
      (fun _ : Fin n => 2 * β + 2 * B / (n : ℝ)) :=
    stability_genGap_hasBoundedDifferences μ hn hstab hℓ_bdd hℓ_int
  have hn_real : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hc : (0 : ℝ) ≤ 2 * β + 2 * B / n :=
    add_nonneg (by linarith) (div_nonneg (by linarith) hn_real)
  exact mcdiarmid_inequality_iid_const_width hc hbdd hF_meas hF_int hε

/-! ### Step 3: δ-confidence form -/

/-- **Threshold form of the δ-confidence bound.**

Given the centered-tail McDiarmid bound `P ≤ exp(-2ε²/(nc²))`, any
`ε` with `ε² ≥ (n c² / 2) (-log δ)` makes the right-hand side `≤ δ`. This
is the algebraic inversion step extracted from
`bousquet_elisseeff_centered_tail`.

The hypothesis `0 < c` ensures the denominator is non-zero so that the
inversion `exp x ≤ δ ⇔ x ≤ log δ` (for `0 < δ`) applies. The public
δ-form theorems supply this from `0 < B`. -/
private lemma exp_neg_two_sq_div_le_of_threshold
    {n : ℕ} (hn : 0 < n) {c ε δ : ℝ}
    (hc : 0 < c) (hδ_pos : 0 < δ)
    (h_threshold : ((n : ℝ) * c ^ 2 / 2) * (- Real.log δ) ≤ ε ^ 2) :
    Real.exp (-2 * ε ^ 2 / ((n : ℝ) * c ^ 2)) ≤ δ := by
  have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hdenom_pos : (0 : ℝ) < (n : ℝ) * c ^ 2 := by positivity
  have hhalf_pos : (0 : ℝ) < ((n : ℝ) * c ^ 2 / 2) := by positivity
  -- threshold: (nc²/2) · (-log δ) ≤ ε² ⇒ -log δ ≤ 2ε²/(nc²)
  have h_log_le : -Real.log δ ≤ ε ^ 2 / (((n : ℝ) * c ^ 2) / 2) :=
    (le_div_iff₀ hhalf_pos).mpr (by linarith [h_threshold])
  have h_log_le' : -Real.log δ ≤ 2 * ε ^ 2 / ((n : ℝ) * c ^ 2) := by
    have h_eq : ε ^ 2 / (((n : ℝ) * c ^ 2) / 2)
        = 2 * ε ^ 2 / ((n : ℝ) * c ^ 2) := by field_simp [hdenom_pos.ne']
    rwa [h_eq] at h_log_le
  -- 2ε²/(nc²) ≥ -log δ means -2ε²/(nc²) ≤ log δ.
  have h_neg_le : -2 * ε ^ 2 / ((n : ℝ) * c ^ 2) ≤ Real.log δ := by
    have h_neg_form : -2 * ε ^ 2 / ((n : ℝ) * c ^ 2)
        = -(2 * ε ^ 2 / ((n : ℝ) * c ^ 2)) := by ring
    linarith [h_neg_form, h_log_le']
  -- Apply exp_le_iff: exp x ≤ δ ↔ x ≤ log δ (for δ > 0).
  calc Real.exp (-2 * ε ^ 2 / ((n : ℝ) * c ^ 2))
      ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr h_neg_le
    _ = δ := Real.exp_log hδ_pos

/-- **Bousquet-Elisseeff-style δ-confidence form (threshold version).**

For any `ε` with `ε² ≥ (n (2β + 2B/n)² / 2) · (-log δ)`,

    μⁿ { S | E[F] + ε ≤ F(S) }  ≤  δ.

Proof: bound the centered tail by `exp(-2ε²/(n(2β+2B/n)²))` and invert. -/
theorem bousquet_elisseeff_confidence_threshold
    [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β B : ℝ}
    (hβ : 0 ≤ β) (hB : 0 < B)
    (hstab : UniformStability A ℓ β)
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (hℓ_int : ∀ i, Integrable (ℓ i) μ)
    (hF_meas : StronglyMeasurable (fun S : Fin n → Z =>
        ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S))
    (hF_int : Integrable (fun S : Fin n → Z =>
        ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S)
      (Measure.pi (fun _ : Fin n => μ)))
    {δ ε : ℝ} (hδ_pos : 0 < δ) (hε : 0 ≤ ε)
    (h_threshold :
      ((n : ℝ) * (2 * β + 2 * B / n) ^ 2 / 2) * (- Real.log δ) ≤ ε ^ 2) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | ∫ s, (∫ z, ℓ (A s) z ∂μ - trainingLoss A ℓ s)
                ∂(Measure.pi (fun _ : Fin n => μ)) + ε
              ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S}
      ≤ δ := by
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- 0 < B implies 0 < 2 * β + 2 * B / n (since β ≥ 0, n > 0)
  have hc_pos : (0 : ℝ) < 2 * β + 2 * B / n := by
    have hBn : 0 < 2 * B / n := div_pos (by linarith) hn_real_pos
    linarith
  have h_centered := bousquet_elisseeff_centered_tail
    hn hβ hB.le hstab hℓ_bdd hℓ_int hF_meas hF_int hε
  have h_inv := exp_neg_two_sq_div_le_of_threshold (n := n) (c := 2 * β + 2 * B / n)
    (ε := ε) (δ := δ) hn hc_pos hδ_pos h_threshold
  exact le_trans h_centered h_inv

/-- **Bousquet-Elisseeff-style δ-confidence form (explicit ε).**

Setting `ε := (2β + 2B/n) · √(-(n · log δ)/2)` realizes the threshold
exactly, giving the textbook form

    μⁿ { S | E[F] + (2β + 2B/n) · √(-(n · log δ)/2) ≤ F(S) }  ≤  δ.

For `0 < δ ≤ 1` we have `-log δ ≥ 0` so the square root is real. -/
theorem bousquet_elisseeff_confidence
    [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β B : ℝ}
    (hβ : 0 ≤ β) (hB : 0 < B)
    (hstab : UniformStability A ℓ β)
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (hℓ_int : ∀ i, Integrable (ℓ i) μ)
    (hF_meas : StronglyMeasurable (fun S : Fin n → Z =>
        ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S))
    (hF_int : Integrable (fun S : Fin n → Z =>
        ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S)
      (Measure.pi (fun _ : Fin n => μ)))
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | ∫ s, (∫ z, ℓ (A s) z ∂μ - trainingLoss A ℓ s)
                ∂(Measure.pi (fun _ : Fin n => μ))
              + (2 * β + 2 * B / n) *
                Real.sqrt (- (n : ℝ) * Real.log δ / 2)
              ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S}
      ≤ δ := by
  have hn_real : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hc : (0 : ℝ) ≤ 2 * β + 2 * B / n :=
    add_nonneg (by linarith) (div_nonneg (by linarith) hn_real)
  have h_log_nonpos : Real.log δ ≤ 0 := Real.log_nonpos hδ_pos.le hδ_le
  have h_neg_log_nonneg : 0 ≤ -Real.log δ := by linarith
  have h_inner_nonneg : 0 ≤ - (n : ℝ) * Real.log δ / 2 := by
    have : 0 ≤ (n : ℝ) * (-Real.log δ) := by positivity
    linarith
  have h_sqrt_nonneg : 0 ≤ Real.sqrt (- (n : ℝ) * Real.log δ / 2) :=
    Real.sqrt_nonneg _
  have hε_nonneg : 0 ≤ (2 * β + 2 * B / n) *
      Real.sqrt (- (n : ℝ) * Real.log δ / 2) :=
    mul_nonneg hc h_sqrt_nonneg
  -- Compute ε² = (2β + 2B/n)² · (-(n log δ)/2).
  have h_sq : ((2 * β + 2 * B / n) * Real.sqrt (- (n : ℝ) * Real.log δ / 2)) ^ 2
      = (2 * β + 2 * B / n) ^ 2 * (- (n : ℝ) * Real.log δ / 2) := by
    rw [mul_pow, Real.sq_sqrt h_inner_nonneg]
  -- Threshold check: (n (2β+2B/n)² / 2) · (-log δ) ≤ ε².
  have h_threshold :
      ((n : ℝ) * (2 * β + 2 * B / n) ^ 2 / 2) * (- Real.log δ)
        ≤ ((2 * β + 2 * B / n) * Real.sqrt (- (n : ℝ) * Real.log δ / 2)) ^ 2 := by
    rw [h_sq]
    have h_eq :
        (2 * β + 2 * B / n) ^ 2 * (- (n : ℝ) * Real.log δ / 2)
          = ((n : ℝ) * (2 * β + 2 * B / n) ^ 2 / 2) * (- Real.log δ) := by ring
    rw [h_eq]
  exact bousquet_elisseeff_confidence_threshold
    hn hβ hB hstab hℓ_bdd hℓ_int hF_meas hF_int hδ_pos hε_nonneg h_threshold

/-! ### Step 4: Expected-gap high-probability variant -/

/-- **Bousquet-Elisseeff-style high-probability stability bound,
sharp McDiarmid expected-gap variant.**

If
* `A` has uniform stability `β`,
* the loss is bounded `|ℓ i z| ≤ B`,
* the expected generalization gap satisfies `E[R(A(S)) - L̂(A(S))] ≤ β`
  (this is Bousquet-Elisseeff Theorem 9, proved in finite-Z form here as
  `expectedFiniteStabilityGap_le_uniformStability_finiteProduct`),

then the upper-tail bad-event mass is at most `δ` over `S ~ μⁿ`:

    R(A(S)) - L̂(A(S))  ≤  β  +  (2β + 2B/n) · √(-(n · log δ)/2).

This is deliberately stated as a variant rather than the literal published
Theorem 12: it takes the measure-theoretic expected-gap bound plus
measurability and integrability of the gap functional as explicit hypotheses. -/
theorem bousquet_elisseeff_expectedGap_variant
    [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β B : ℝ}
    (hβ : 0 ≤ β) (hB : 0 < B)
    (hstab : UniformStability A ℓ β)
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (hℓ_int : ∀ i, Integrable (ℓ i) μ)
    (hF_meas : StronglyMeasurable (fun S : Fin n → Z =>
        ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S))
    (hF_int : Integrable (fun S : Fin n → Z =>
        ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S)
      (Measure.pi (fun _ : Fin n => μ)))
    (h_expected_gap :
      ∫ s, (∫ z, ℓ (A s) z ∂μ - trainingLoss A ℓ s)
        ∂(Measure.pi (fun _ : Fin n => μ)) ≤ β)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | β + (2 * β + 2 * B / n) *
                Real.sqrt (- (n : ℝ) * Real.log δ / 2)
              ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S}
      ≤ δ := by
  set μn : Measure (Fin n → Z) := Measure.pi (fun _ : Fin n => μ)
  set EF : ℝ := ∫ s, (∫ z, ℓ (A s) z ∂μ - trainingLoss A ℓ s) ∂μn
  have h_centered := bousquet_elisseeff_confidence
    hn hβ hB hstab hℓ_bdd hℓ_int hF_meas hF_int hδ_pos hδ_le
  -- The high-prob bound centered at E[F] also holds when shifted to β,
  -- since β ≥ E[F] enlarges the threshold and shrinks the tail set.
  have h_set_subset :
      {S : Fin n → Z | β + (2 * β + 2 * B / n) *
                Real.sqrt (- (n : ℝ) * Real.log δ / 2)
              ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S}
        ⊆ {S | EF + (2 * β + 2 * B / n) *
                Real.sqrt (- (n : ℝ) * Real.log δ / 2)
              ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S} := by
    intro S hS
    have hS' : β + (2 * β + 2 * B / n) *
        Real.sqrt (- (n : ℝ) * Real.log δ / 2)
          ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S := hS
    show EF + (2 * β + 2 * B / n) *
        Real.sqrt (- (n : ℝ) * Real.log δ / 2)
          ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S
    have h_le : EF ≤ β := h_expected_gap
    linarith
  -- Apply monotonicity of measure under set inclusion.
  exact le_trans (measureReal_mono h_set_subset (measure_ne_top _ _)) h_centered

/-- Compatibility form of `bousquet_elisseeff_expectedGap_variant` with the
larger Azuma-style threshold used by FormalSLT v0.1.

The statement is retained for source compatibility. New code should use the
sharper McDiarmid endpoint `bousquet_elisseeff_expectedGap_variant`. -/
@[deprecated bousquet_elisseeff_expectedGap_variant (since := "2026-08-19")]
theorem bousquet_elisseeff_azuma_expectedGap_variant
    [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β B : ℝ}
    (hβ : 0 ≤ β) (hB : 0 < B)
    (hstab : UniformStability A ℓ β)
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (hℓ_int : ∀ i, Integrable (ℓ i) μ)
    (hF_meas : StronglyMeasurable (fun S : Fin n → Z =>
        ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S))
    (hF_int : Integrable (fun S : Fin n → Z =>
        ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S)
      (Measure.pi (fun _ : Fin n => μ)))
    (h_expected_gap :
      ∫ s, (∫ z, ℓ (A s) z ∂μ - trainingLoss A ℓ s)
        ∂(Measure.pi (fun _ : Fin n => μ)) ≤ β)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | β + (2 * β + 2 * B / n) *
                Real.sqrt (- 2 * (n : ℝ) * Real.log δ)
              ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S}
      ≤ δ := by
  have hsharp := bousquet_elisseeff_expectedGap_variant
    hn hβ hB hstab hℓ_bdd hℓ_int hF_meas hF_int h_expected_gap hδ_pos hδ_le
  have hn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : Real.log δ ≤ 0 := Real.log_nonpos hδ_pos.le hδ_le
  have hinner :
      - (n : ℝ) * Real.log δ / 2 ≤ - 2 * (n : ℝ) * Real.log δ := by
    nlinarith
  have hsqrt :
      Real.sqrt (- (n : ℝ) * Real.log δ / 2) ≤
        Real.sqrt (- 2 * (n : ℝ) * Real.log δ) :=
    Real.sqrt_le_sqrt hinner
  have hcoeff : 0 ≤ 2 * β + 2 * B / (n : ℝ) := by positivity
  have hthreshold :
      β + (2 * β + 2 * B / n) *
          Real.sqrt (- (n : ℝ) * Real.log δ / 2) ≤
        β + (2 * β + 2 * B / n) *
          Real.sqrt (- 2 * (n : ℝ) * Real.log δ) := by
    simpa [add_comm] using
      (add_le_add_left (mul_le_mul_of_nonneg_left hsqrt hcoeff) β)
  have hsubset :
      {S : Fin n → Z | β + (2 * β + 2 * B / n) *
              Real.sqrt (- 2 * (n : ℝ) * Real.log δ)
            ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S} ⊆
        {S | β + (2 * β + 2 * B / n) *
              Real.sqrt (- (n : ℝ) * Real.log δ / 2)
            ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S} := by
    intro S hS
    exact hthreshold.trans hS
  exact le_trans (measureReal_mono hsubset (measure_ne_top _ _)) hsharp

/-! ### Step 4b: Bounded-loss high-probability wrappers -/

/-- A bounded measurable hypothesis loss is integrable under a probability
measure.

This is the per-hypothesis adapter used by the finite-class high-probability
stability wrappers below. It assumes scalar real-valued losses and does not
claim anything about infinite hypothesis spaces. -/
theorem boundedLoss_hypothesisLoss_integrable
    [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ}
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (i : ι) :
    Integrable (ℓ i) μ := by
  refine Integrable.of_bound (hℓ_meas i).aestronglyMeasurable B ?_
  exact Filter.Eventually.of_forall (by
    intro z
    simpa [Real.norm_eq_abs] using hℓ_bdd i z)

/-- Training loss is measurable for a finite measurable hypothesis interface.

The hypotheses are deliberately finite-class: measurable algorithm
`A : (Fin n → Z) → ι`, measurable singleton index type `ι`, and measurable
per-hypothesis scalar losses. -/
theorem finiteClass_trainingLoss_measurable
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace Z]
    {n : ℕ} {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ}
    (hA : Measurable A)
    (hℓ_meas : ∀ i, Measurable (ℓ i)) :
    Measurable (fun S : Fin n → Z => trainingLoss A ℓ S) := by
  have hℓ_joint : Measurable (fun P : ι × Z => ℓ P.1 P.2) :=
    finiteClass_loss_measurable ℓ hℓ_meas
  have hcoord : ∀ k : Fin n, Measurable (fun S : Fin n → Z => ℓ (A S) (S k)) := by
    intro k
    have hpair : Measurable (fun S : Fin n → Z => (A S, S k)) :=
      Measurable.prod hA (measurable_pi_apply k)
    exact hℓ_joint.comp hpair
  have hsum : Measurable (fun S : Fin n → Z => ∑ k : Fin n, ℓ (A S) (S k)) := by
    simpa using
      (Finset.measurable_sum Finset.univ (by
        intro k _hk
        exact hcoord k))
  have hmul := hsum.const_mul ((n : ℝ)⁻¹)
  simpa [trainingLoss] using hmul

/-- The algorithm-selected stability gap is strongly measurable for a finite
measurable hypothesis interface.

This is a measurability adapter, not a concentration theorem. It supplies the
`StronglyMeasurable` hypothesis required by the sharp stability tail
theorem when `A` is measurable and the hypothesis class is finite. -/
theorem finiteClass_stabilityGap_stronglyMeasurable
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace Z]
    (μ : Measure Z)
    {n : ℕ} {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ}
    (hA : Measurable A)
    (hℓ_meas : ∀ i, Measurable (ℓ i)) :
    StronglyMeasurable (fun S : Fin n → Z =>
      ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S) := by
  have hrisk_index : Measurable (fun i : ι => risk μ ℓ i) :=
    measurable_of_finite (fun i : ι => risk μ ℓ i)
  have hrisk_meas : Measurable (fun S : Fin n → Z => risk μ ℓ (A S)) :=
    hrisk_index.comp hA
  have htrain_meas : Measurable (fun S : Fin n → Z => trainingLoss A ℓ S) :=
    finiteClass_trainingLoss_measurable hA hℓ_meas
  have hgap : Measurable (fun S : Fin n → Z =>
      risk μ ℓ (A S) - trainingLoss A ℓ S) :=
    hrisk_meas.sub htrain_meas
  simpa [risk] using hgap.stronglyMeasurable

/-- The algorithm-selected stability gap is integrable under `μⁿ` when losses
are bounded and the finite-class measurable interface is available.

This adapter packages the selected-risk and empirical-coordinate integrability
facts proved in `AlgorithmicStability` into the exact integrability hypothesis
required by the high-probability stability theorem. -/
theorem boundedLoss_stabilityGap_integrable
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    {n : ℕ} {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {B : ℝ}
    (hA : Measurable A)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B) :
    Integrable (fun S : Fin n → Z =>
      ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S)
      (Measure.pi (fun _ : Fin n => μ)) := by
  let μn : Measure (Fin n → Z) := Measure.pi (fun _ : Fin n => μ)
  have hselected_int :
      Integrable (fun P : (Fin n → Z) × Z => ℓ (A P.1) P.2) (μn.prod μ) := by
    simpa [μn] using
      (boundedLoss_selectedLoss_integrable (ι := ι) (Z := Z)
        μ hA hℓ_meas hℓ_bdd)
  have hrisk_int : Integrable (fun S : Fin n → Z => risk μ ℓ (A S)) μn := by
    unfold risk
    exact hselected_int.integral_prod_left
  have hcoord_int : ∀ k : Fin n,
      Integrable (fun S : Fin n → Z => ℓ (A S) (S k)) μn := by
    intro k
    simpa [μn] using
      (boundedLoss_coordinateSelectedLoss_integrable (ι := ι) (Z := Z)
        μ k hA hℓ_meas hℓ_bdd)
  have hsum_int : Integrable (fun S : Fin n → Z => ∑ k : Fin n, ℓ (A S) (S k)) μn := by
    simpa using
      (integrable_finsetSum (μ := μn) (s := (Finset.univ : Finset (Fin n)))
        (f := fun k S => ℓ (A S) (S k))
        (by intro k _hk; exact hcoord_int k))
  have htrain_int : Integrable (fun S : Fin n → Z => trainingLoss A ℓ S) μn := by
    unfold trainingLoss
    exact hsum_int.const_mul _
  change Integrable
    ((fun S : Fin n → Z => risk μ ℓ (A S)) - fun S => trainingLoss A ℓ S) μn
  exact hrisk_int.sub htrain_int

/-- Bounded-loss Bousquet-Elisseeff high-probability stability wrapper.

This finite-class wrapper discharges the expected-gap, measurability, and
integrability hypotheses of
`bousquet_elisseeff_expectedGap_variant` from:
measurable `A`, measurable scalar losses, bounded loss, and uniform stability. -/
theorem bousquet_elisseeff_expectedGap_variant_of_boundedLoss
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β B : ℝ}
    (hβ : 0 ≤ β) (hB : 0 < B)
    (hstab : UniformStability A ℓ β)
    (hA : Measurable A)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | β + (2 * β + 2 * B / n) *
                Real.sqrt (- (n : ℝ) * Real.log δ / 2)
              ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S}
      ≤ δ := by
  have hℓ_int : ∀ i, Integrable (ℓ i) μ :=
    boundedLoss_hypothesisLoss_integrable (μ := μ) hℓ_meas hℓ_bdd
  have hF_meas : StronglyMeasurable (fun S : Fin n → Z =>
      ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S) :=
    finiteClass_stabilityGap_stronglyMeasurable (ι := ι) (Z := Z)
      μ hA hℓ_meas
  have hF_int : Integrable (fun S : Fin n → Z =>
      ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S)
      (Measure.pi (fun _ : Fin n => μ)) :=
    boundedLoss_stabilityGap_integrable (ι := ι) (Z := Z)
      μ hA hℓ_meas hℓ_bdd
  have h_expected_gap :
      ∫ s, (∫ z, ℓ (A s) z ∂μ - trainingLoss A ℓ s)
        ∂(Measure.pi (fun _ : Fin n => μ)) ≤ β := by
    simpa [risk] using
      (expectedStabilityGap_le_uniformStability_piMeasure_of_boundedLoss
        (ι := ι) (Z := Z) μ hn hstab hA hℓ_meas hℓ_bdd)
  exact bousquet_elisseeff_expectedGap_variant
    hn hβ hB hstab hℓ_bdd hℓ_int hF_meas hF_int h_expected_gap
    hδ_pos hδ_le

/-- Compatibility bounded-loss wrapper with the larger Azuma-style threshold
used by FormalSLT v0.1.

The statement is retained for source compatibility. New code should use the
sharper `bousquet_elisseeff_expectedGap_variant_of_boundedLoss`. -/
@[deprecated bousquet_elisseeff_expectedGap_variant_of_boundedLoss
  (since := "2026-08-19")]
theorem bousquet_elisseeff_azuma_expectedGap_variant_of_boundedLoss
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β B : ℝ}
    (hβ : 0 ≤ β) (hB : 0 < B)
    (hstab : UniformStability A ℓ β)
    (hA : Measurable A)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | β + (2 * β + 2 * B / n) *
                Real.sqrt (- 2 * (n : ℝ) * Real.log δ)
              ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S}
      ≤ δ := by
  have hsharp := bousquet_elisseeff_expectedGap_variant_of_boundedLoss
    (ι := ι) (Z := Z) (μ := μ)
    hn hβ hB hstab hA hℓ_meas hℓ_bdd hδ_pos hδ_le
  have hn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : Real.log δ ≤ 0 := Real.log_nonpos hδ_pos.le hδ_le
  have hinner :
      - (n : ℝ) * Real.log δ / 2 ≤ - 2 * (n : ℝ) * Real.log δ := by
    nlinarith
  have hsqrt :
      Real.sqrt (- (n : ℝ) * Real.log δ / 2) ≤
        Real.sqrt (- 2 * (n : ℝ) * Real.log δ) :=
    Real.sqrt_le_sqrt hinner
  have hcoeff : 0 ≤ 2 * β + 2 * B / (n : ℝ) := by positivity
  have hthreshold :
      β + (2 * β + 2 * B / n) *
          Real.sqrt (- (n : ℝ) * Real.log δ / 2) ≤
        β + (2 * β + 2 * B / n) *
          Real.sqrt (- 2 * (n : ℝ) * Real.log δ) := by
    simpa [add_comm] using
      (add_le_add_left (mul_le_mul_of_nonneg_left hsqrt hcoeff) β)
  have hsubset :
      {S : Fin n → Z | β + (2 * β + 2 * B / n) *
              Real.sqrt (- 2 * (n : ℝ) * Real.log δ)
            ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S} ⊆
        {S | β + (2 * β + 2 * B / n) *
              Real.sqrt (- (n : ℝ) * Real.log δ / 2)
            ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S} := by
    intro S hS
    exact hthreshold.trans hS
  exact le_trans (measureReal_mono hsubset (measure_ne_top _ _)) hsharp

/-! ### Step 5: ERM corollary (uniform stability `β = c₀ / n`) -/

/-- **Corollary: `O(1/n)` uniform stability ⇒ `O(1/√n)` high-probability gap.**

If `A` has uniform stability `β = c₀ / n` and the expected gap is at most
`c₀ / n`, then with probability
`≥ 1 - δ`:

    R(A(S)) - L̂(A(S))  ≤  c₀/n  +  (2 c₀/n + 2 B/n) · √(-(n · log δ)/2)
                       =  c₀/n  +  (2 (c₀ + B)/n) · √(-(n · log δ)/2).

So the gap is `O(1/√n)` for fixed `δ`, matching the textbook rate.

The proof is a direct application of
`bousquet_elisseeff_expectedGap_variant` with
`β := c₀ / n`. We do not derive uniform stability here for any specific
algorithm; the corollary applies uniform stability as input.

Source: Bousquet & Elisseeff (2002), using the same stability-concentration
template with an explicit expected-gap hypothesis. -/
theorem bousquet_elisseeff_uniform_stability_corollary
    [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {c₀ B : ℝ}
    (hc₀ : 0 ≤ c₀) (hB : 0 < B)
    (hstab : UniformStability A ℓ (c₀ / n))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (hℓ_int : ∀ i, Integrable (ℓ i) μ)
    (hF_meas : StronglyMeasurable (fun S : Fin n → Z =>
        ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S))
    (hF_int : Integrable (fun S : Fin n → Z =>
        ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S)
      (Measure.pi (fun _ : Fin n => μ)))
    (h_expected_gap :
      ∫ s, (∫ z, ℓ (A s) z ∂μ - trainingLoss A ℓ s)
        ∂(Measure.pi (fun _ : Fin n => μ)) ≤ c₀ / n)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | c₀ / n
              + (2 * (c₀ / n) + 2 * B / n) *
                  Real.sqrt (- (n : ℝ) * Real.log δ / 2)
              ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S}
      ≤ δ := by
  have hn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hβ : (0 : ℝ) ≤ c₀ / n := div_nonneg hc₀ hn_real.le
  exact bousquet_elisseeff_expectedGap_variant hn hβ hB hstab hℓ_bdd hℓ_int
    hF_meas hF_int h_expected_gap hδ_pos hδ_le

/-- Bounded-loss `c₀ / n` high-probability stability corollary.

This is the finite-class, measurable-algorithm wrapper around
`bousquet_elisseeff_uniform_stability_corollary`: bounded measurable losses
and measurable `A` discharge the expected-gap and integrability bookkeeping. -/
theorem bousquet_elisseeff_uniform_stability_corollary_of_boundedLoss
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {c₀ B : ℝ}
    (hc₀ : 0 ≤ c₀) (hB : 0 < B)
    (hstab : UniformStability A ℓ (c₀ / n))
    (hA : Measurable A)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | c₀ / n
              + (2 * (c₀ / n) + 2 * B / n) *
                  Real.sqrt (- (n : ℝ) * Real.log δ / 2)
              ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S}
      ≤ δ := by
  have hn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hβ : (0 : ℝ) ≤ c₀ / n := div_nonneg hc₀ hn_real.le
  exact bousquet_elisseeff_expectedGap_variant_of_boundedLoss
    hn hβ hB hstab hA hℓ_meas hℓ_bdd hδ_pos hδ_le

end FormalSLT.AlgorithmicStability
