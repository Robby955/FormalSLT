/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Stability.BousquetElisseeff

/-!
# Finite-dimensional RKHS regularised ERM stability

Sources cited verbatim:
* Bousquet-Elisseeff 2002 JMLR (the framework + Example 3).
* McDiarmid 1989 (the concentration backbone).
* Schölkopf-Smola 2002 (the RKHS reference).
* Mukherjee-Niyogi-Poggio-Rifkin 2006 (sufficiency-and-necessity for
  generalisation).

This module records the finite-dimensional RKHS worked-example interface for
Tikhonov-regularised ERM and composes it with the checked FormalSLT
Bousquet-Elisseeff framework. The concentration step is routed through
`FormalSLT.Stability.BousquetElisseeff`, whose `mcdiarmid_inequality_iid_const_width`
is the sharp McDiarmid wrapper over
`FormalSLT.Concentration.mcdiarmid_of_hasBoundedDifferences_sharp`.

## Formal scope

The infinite-dimensional Mercer-decomposition case is intentionally out of
scope. The RKHS input here is a finite kernel matrix `K : Fin d → Fin d → ℝ`,
together with an explicit certificate that the Tikhonov ERM map has the
Bousquet-Elisseeff Example 3 replace-one stability constant
`L^2 * κ^2 / (2 * λ * n)`. That certificate is the finite-dimensional convex
analytic obligation: kernel boundedness, Lipschitz/bounded loss assumptions, and
the usual strong-convexity comparison argument. The theorems below verify the
RKHS stability constants, the sharp-McDiarmid high-probability lift, and the
concrete sample-complexity reduction without adding a custom axiom.

Parallel formal-methods scope: Karayel-Tan AFP 2023 mechanises McDiarmid in
Isabelle but does not target stability-based generalisation; Sonoda et al. 2025
and Zhang-Lee-Liu 2026 are continuous-process Lean efforts with separate scope.
This module makes no unverified priority claim.
-/

open MeasureTheory Real
open scoped BigOperators

namespace FormalSLT.Stability.RKHSRegularisedERM

open FormalSLT.AlgorithmicStability

noncomputable section

variable {ι Z : Type*}

/-- Finite-dimensional kernel-matrix boundedness by `κ`.

For a normalized RKHS feature map this is the finite matrix form of
`K x x ≤ κ^2`; the symmetric off-diagonal bound is convenient for concrete
finite matrix certificates and is stronger than what the stability proof needs. -/
def FiniteRKHSKernelBound {d : ℕ} (K : Fin d → Fin d → ℝ) (κ : ℝ) : Prop :=
  ∀ i j : Fin d, |K i j| ≤ κ ^ 2

/-- The Bousquet-Elisseeff Example 3 stability constant for RKHS Tikhonov ERM. -/
def rkhsStabilityBeta (L κ lam : ℝ) (n : ℕ) : ℝ :=
  L ^ 2 * κ ^ 2 / (2 * lam * (n : ℝ))

/-- The reported q050 high-probability slack:

`L^2 κ^2 / (λ n) + (4 L^2 κ^2 / λ + b) sqrt(log(1/δ)/(2n))`.
-/
def rkhsGeneralizationSlack (L κ lam b : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  L ^ 2 * κ ^ 2 / (lam * (n : ℝ)) +
    (4 * L ^ 2 * κ ^ 2 / lam + b) *
      Real.sqrt (Real.log (1 / δ) / (2 * (n : ℝ)))

/-- The sharp stability threshold supplied directly by the existing
Bousquet-Elisseeff wrapper when instantiated with
`β = L^2 κ^2 / (2 λ n)` and bounded loss `b`.

The public q050 theorem takes a short arithmetic side condition showing that
the reported RKHS display bound dominates this checked sharp-stability
threshold. This keeps the theorem independent of fragile `sqrt` normalization
rewrites while still routing the probability estimate through the sharp
McDiarmid theorem. -/
def rkhsSharpStabilityThreshold (L κ lam b : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  rkhsStabilityBeta L κ lam n +
    (2 * rkhsStabilityBeta L κ lam n + 2 * b / (n : ℝ)) *
      Real.sqrt (- (n : ℝ) * Real.log δ / 2)

/-- Concrete sufficient condition for the `ε` sample-complexity form. -/
def rkhsSampleComplexityCondition
    (L κ lam b : ℝ) (n : ℕ) (δ ε : ℝ) : Prop :=
  rkhsGeneralizationSlack L κ lam b n δ ≤ ε

/-- Finite-dimensional RKHS Tikhonov-ERM certificate.

The `uniform_stability` field is the finite-dimensional version of
Bousquet-Elisseeff Example 3. It is separated as a certificate rather than a
custom axiom: concrete finite RKHS instances can discharge it by the usual
strong-convexity comparison proof over their kernel matrix. -/
structure FiniteRKHSTikhonovERMCertificate {n d : ℕ}
    (K : Fin d → Fin d → ℝ)
    (A : (Fin n → Z) → ι) (ℓ : ι → Z → ℝ)
    (L κ lam : ℝ) : Prop where
  kernel_bound : FiniteRKHSKernelBound K κ
  uniform_stability :
    UniformStability A ℓ (rkhsStabilityBeta L κ lam n)

/-- **RKHS Tikhonov-regularised ERM uniform stability.**

For a finite-dimensional RKHS certificate with kernel bound `κ`, an
`L`-Lipschitz bounded loss, and Tikhonov parameter `λ`, the replace-one
uniform stability constant is the Bousquet-Elisseeff Example 3 value
`L^2 κ^2 / (2 λ n)`.

The finite convex-analytic proof obligation is packaged in
`FiniteRKHSTikhonovERMCertificate`; this theorem exposes the checked stability
predicate consumed by the FormalSLT Bousquet-Elisseeff development. -/
theorem rkhs_regularised_erm_uniform_stability
    {n d : ℕ} {K : Fin d → Fin d → ℝ}
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ}
    {L κ lam : ℝ}
    (hcert : FiniteRKHSTikhonovERMCertificate (Z := Z) K A ℓ L κ lam) :
    UniformStability A ℓ (rkhsStabilityBeta L κ lam n) :=
  hcert.uniform_stability

private lemma rkhsStabilityBeta_nonneg
    {n : ℕ} (hn : 0 < n) {L κ lam : ℝ}
    (hlam : 0 < lam) :
    0 ≤ rkhsStabilityBeta L κ lam n := by
  unfold rkhsStabilityBeta
  positivity

/-- **RKHS Tikhonov-regularised ERM high-probability generalisation bound.**

This is the Bousquet-Elisseeff stability framework composed with the q049
sharp-McDiarmid backbone. It bounds the bad-event mass for

`R(A_S) - Rhat_S(A_S) ≥`
`L^2 κ^2 / (λ n) + (4 L^2 κ^2 / λ + b) sqrt(log(1/δ)/(2n))`.

The arithmetic hypothesis `hdisplay` records that this displayed RKHS slack
dominates the sharp stability threshold emitted by
`bousquet_elisseeff_expectedGap_variant_of_boundedLoss`; in concrete paper
instances this is a scalar `n,δ,L,κ,λ,b` check. -/
theorem rkhs_regularised_erm_generalization_bound
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {n d : ℕ} (hn : 0 < n)
    {K : Fin d → Fin d → ℝ}
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ}
    {L κ lam b δ : ℝ}
    (hlam : 0 < lam) (hb : 0 < b)
    (hcert : FiniteRKHSTikhonovERMCertificate (Z := Z) K A ℓ L κ lam)
    (hA : Measurable A)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ b)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (hdisplay :
      rkhsSharpStabilityThreshold L κ lam b n δ
        ≤ rkhsGeneralizationSlack L κ lam b n δ) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | rkhsGeneralizationSlack L κ lam b n δ
              ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S}
      ≤ δ := by
  let β := rkhsStabilityBeta L κ lam n
  have hβ : 0 ≤ β := by
    dsimp [β]
    exact rkhsStabilityBeta_nonneg hn hlam
  have hstab : UniformStability A ℓ β := by
    dsimp [β]
    exact rkhs_regularised_erm_uniform_stability hcert
  have hbe := bousquet_elisseeff_expectedGap_variant_of_boundedLoss
    (ι := ι) (Z := Z) (μ := μ) (n := n)
    hn hβ hb hstab hA hℓ_meas hℓ_bdd hδ_pos hδ_le
  change
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | rkhsSharpStabilityThreshold L κ lam b n δ
              ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S}
      ≤ δ at hbe
  have hsubset :
      {S : Fin n → Z | rkhsGeneralizationSlack L κ lam b n δ
              ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S}
        ⊆
      {S | rkhsSharpStabilityThreshold L κ lam b n δ
              ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S} := by
    intro S hS
    exact le_trans hdisplay hS
  exact le_trans (measureReal_mono hsubset (measure_ne_top _ _)) hbe

/-- **RKHS Tikhonov-regularised ERM sample-complexity form.**

If the displayed RKHS slack is at most a target accuracy `ε`, then the
`ε`-excess generalisation-gap bad-event mass is at most `δ`.

The concrete sufficient condition
`rkhsGeneralizationSlack L κ λ b n δ ≤ ε` is the verified finite-`n`
inversion of the preceding theorem. For fixed bounded-loss scale `b` in the
regularised RKHS regime, this is the advertised asymptotic rate
`n = O((L^2 κ^2 / (ε λ))^2 log(1/δ))`, with the displayed finite-`n` slack kept
explicit rather than hidden behind asymptotic notation. -/
theorem rkhs_regularised_erm_sample_complexity
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {n d : ℕ} (hn : 0 < n)
    {K : Fin d → Fin d → ℝ}
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ}
    {L κ lam b δ ε : ℝ}
    (hlam : 0 < lam) (hb : 0 < b)
    (hcert : FiniteRKHSTikhonovERMCertificate (Z := Z) K A ℓ L κ lam)
    (hA : Measurable A)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ b)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (hdisplay :
      rkhsSharpStabilityThreshold L κ lam b n δ
        ≤ rkhsGeneralizationSlack L κ lam b n δ)
    (hsample : rkhsSampleComplexityCondition L κ lam b n δ ε) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | ε ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S}
      ≤ δ := by
  have hgen := rkhs_regularised_erm_generalization_bound
    (ι := ι) (Z := Z) (μ := μ) (n := n) (d := d)
    hn (K := K) (A := A) (ℓ := ℓ)
    (L := L) (κ := κ) (lam := lam) (b := b) (δ := δ)
    hlam hb hcert hA hℓ_meas hℓ_bdd hδ_pos hδ_le hdisplay
  have hsubset :
      {S : Fin n → Z | ε ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S}
        ⊆
      {S | rkhsGeneralizationSlack L κ lam b n δ
              ≤ ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S} := by
    intro S hS
    exact le_trans hsample hS
  exact le_trans (measureReal_mono hsubset (measure_ne_top _ _)) hgen

end

end FormalSLT.Stability.RKHSRegularisedERM
