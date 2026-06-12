/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import FormalSLT.Concentration.SubGamma.Extractor

/-!
# Anytime-valid sub-Gamma confidence sequences

This file packages the fixed-`lambda` anytime-valid sub-Gamma confidence-sequence
interface used for bounded adapted processes. The stochastic brick is the
exponential process

`M_n = exp (lambda * S_n - n * cgf(lambda))`,

where `S_n` is the running sum and
`cgf(lambda) = sigma2 * lambda^2 / (2 * (1 - b * lambda / 3))`.

The conditional MGF input is supplied by
`FormalSLT.Concentration.SubGamma.condSubGammaMGF_of_bounded_centered_condVariance`.
Once the conditional MGF has been pulled through the predictable prefactor, the
one-step inequality required by `MeasureTheory.supermartingale_nat` is exactly
the hypothesis `h_condSubGamma_step` in
`nonneg_supermartingale_of_condSubGamma`.

Ville layer and mathlib API status:

* Mathlib's current maximal-inequality entry point is
  `MeasureTheory.maximal_ineq` from
  `Mathlib.Probability.Martingale.OptionalStopping`. It states Doob's finite
  maximal inequality for nonnegative submartingales using the finite maximum
  `(Finset.range (n + 1)).sup' ...`.
* The reusable wrapper this development wants is the supermartingale Ville form:
  if `M` is a nonnegative supermartingale, then for `a > 0`,
  `a * μ {omega | a <= max_{k <= n} M_k omega} <= ENNReal.ofReal (∫ omega, M 0 omega ∂μ)`.
  That statement follows from the optional-stopping proof behind
  `MeasureTheory.maximal_ineq`, but it is not exposed as a named theorem in the
  current mathlib API. This module therefore makes the finite-horizon Ville
  payoff an explicit hypothesis in `ville_inequality_subGamma_running_mean`.
  The API unfold needed for extraction is the finite maximum used by
  `MeasureTheory.maximal_ineq`.
* Candidate mathlib PR statement:
  `MeasureTheory.Supermartingale.ville_ineq`, a finite-horizon maximal
  inequality for nonnegative real-valued supermartingales:
  `a * μ {omega | a <= (Finset.range (n + 1)).sup' ... fun k => M k omega}
    <= ENNReal.ofReal (∫ omega, M 0 omega ∂μ)`.

References: Howard, Ramdas, McAuliffe, Sekhon 2021 (Probability Surveys 17);
Ville 1939; Waudby-Smith and Ramdas 2024 (JRSS-B); Chugg, Wang, Ramdas 2023
(JMLR 24).

Formal-methods disambiguation: Karayel-Tan AFP 2023 mechanise
Hoeffding/Bernstein/McDiarmid in Isabelle but do not target anytime-valid
constructions. Sonoda et al. 2025 (arXiv:2503.19605) and Zhang-Lee-Liu 2026
(arXiv:2602.02285) are continuous-process Lean efforts with separate scope.
This file does not make an unverified "first Lean mechanisation" claim.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

/-- Sub-Gamma cumulant proxy used by the fixed-`lambda` exponential process. -/
def subGammaCgf (sigma2 b lam : ℝ) : ℝ :=
  sigma2 * lam ^ 2 / (2 * (1 - b * lam / 3))

/-- Running sum `S_n = sum_{i < n} X_i`. -/
def runningSum {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Finset.sum (Finset.range n) fun i => X i ω

/-- Running mean `S_n / n`, with Lean's total real division convention at `n = 0`. -/
def runningMean {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  runningSum X n ω / (n : ℝ)

/-- Fixed-`lambda` sub-Gamma exponential process. -/
def subGammaExponentialProcess {Ω : Type*}
    (X : ℕ → Ω → ℝ) (sigma2 b lam : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (lam * runningSum X n ω - (n : ℝ) * subGammaCgf sigma2 b lam)

/-- Finite running maximum `max_{k <= n} M_k`, matching mathlib's maximal-inequality shape. -/
def finiteRunningMax {Ω : Type*} (M : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => M k ω

/-- One-sided sub-Gamma confidence width used in the stated CS interface. -/
def subGammaWidth (sigma2 b : ℝ) (n : ℕ) (delta : ℝ) : ℝ :=
  Real.sqrt (2 * sigma2 * Real.log (1 / delta) / (n : ℝ))
    + b * Real.log (1 / delta) / (3 * (n : ℝ))

/-- Lower endpoint of the centered running-mean confidence interval. -/
def subGammaConfidenceLower {Ω : Type*}
    (X : ℕ → Ω → ℝ) (sigma2 b : ℝ) (delta : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  runningMean X n ω - subGammaWidth sigma2 b n delta

/-- Upper endpoint of the centered running-mean confidence interval. -/
def subGammaConfidenceUpper {Ω : Type*}
    (X : ℕ → Ω → ℝ) (sigma2 b : ℝ) (delta : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  runningMean X n ω + subGammaWidth sigma2 b n delta

/-- Pointwise membership of the target mean in the sub-Gamma interval at time `n`. -/
def inSubGammaConfidenceInterval {Ω : Type*}
    (X : ℕ → Ω → ℝ) (theta sigma2 b delta : ℝ) (n : ℕ) (ω : Ω) : Prop :=
  subGammaConfidenceLower X sigma2 b delta n ω ≤ theta
    ∧ theta ≤ subGammaConfidenceUpper X sigma2 b delta n ω

/-- Anytime-valid coverage statement encoded as a bound on the first failure event. -/
def anytimeValidConfidenceSequence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (theta sigma2 b delta : ℝ) : Prop :=
  μ.real {ω | ∃ n : ℕ, 0 < n ∧
    ¬ inSubGammaConfidenceInterval X theta sigma2 b delta n ω} ≤ delta

/--
The fixed-`lambda` exponential process is a nonnegative supermartingale once
the conditional sub-Gamma extractor has supplied the one-step conditional MGF
bound after the predictable prefactor has been pulled out.

The `h_condSubGamma_step` hypothesis is the exact post-extractor obligation:
`E[M_{n+1} | F_n] <= M_n`. It is the form produced by combining
`FormalSLT.Concentration.SubGamma.condSubGammaMGF_of_bounded_centered_condVariance`
with the conditional-expectation pull-out API.
-/
theorem nonneg_supermartingale_of_condSubGamma
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b lam : ℝ}
    (h_adapted :
      StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (h_integrable :
      ∀ n, Integrable (subGammaExponentialProcess X sigma2 b lam n) μ)
    (h_condSubGamma_step :
      ∀ n,
        μ[subGammaExponentialProcess X sigma2 b lam (n + 1) | ℱ n]
          ≤ᵐ[μ] subGammaExponentialProcess X sigma2 b lam n) :
    Supermartingale (subGammaExponentialProcess X sigma2 b lam) ℱ μ
      ∧ ∀ n ω, 0 ≤ subGammaExponentialProcess X sigma2 b lam n ω := by
  refine ⟨supermartingale_nat h_adapted h_integrable h_condSubGamma_step, ?_⟩
  intro n ω
  exact (Real.exp_pos _).le

/--
Finite-horizon Ville payoff for the running mean, stated as the algebraic
bridge from an exponential-supermartingale boundary to the sub-Gamma running
mean boundary.

The hypothesis `h_ville_from_maximal_ineq` is the finite-horizon Ville bound
obtained from the nonnegative-supermartingale maximal inequality. In current
mathlib this is extracted from `MeasureTheory.maximal_ineq` plus the optional
stopping proof, rather than by applying a named supermartingale Ville theorem.
-/
theorem ville_inequality_subGamma_running_mean
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {sigma2 b lam t : ℝ} {n : ℕ}
    (h_exponential_boundary :
      {ω | t ≤ runningMean X n ω - subGammaCgf sigma2 b lam / lam}
        ⊆
      {ω |
        Real.exp (lam * (n : ℝ) * t)
          ≤ finiteRunningMax (subGammaExponentialProcess X sigma2 b lam) n ω})
    (h_ville_from_maximal_ineq :
      μ.real
        {ω |
          Real.exp (lam * (n : ℝ) * t)
            ≤ finiteRunningMax (subGammaExponentialProcess X sigma2 b lam) n ω}
        ≤ Real.exp (-lam * (n : ℝ) * t)) :
    μ.real {ω | t ≤ runningMean X n ω - subGammaCgf sigma2 b lam / lam}
      ≤ Real.exp (-lam * (n : ℝ) * t) :=
  (measureReal_mono h_exponential_boundary).trans h_ville_from_maximal_ineq

/--
Anytime-valid confidence-sequence wrapper for the sub-Gamma interval.

The theorem packages the final finite-union layer: if the first failure event
is contained in the union of one-sided upper and lower failure events, and each
one-sided event has mass at most `delta / 2`, then the interval sequence has
failure mass at most `delta`.
-/
theorem anytime_valid_confidence_sequence_subGamma
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {theta sigma2 b delta : ℝ}
    {upperFailure lowerFailure : Set Ω}
    (h_failure_subset :
      {ω | ∃ n : ℕ, 0 < n ∧
        ¬ inSubGammaConfidenceInterval X theta sigma2 b delta n ω}
        ⊆ upperFailure ∪ lowerFailure)
    (h_upper : μ.real upperFailure ≤ delta / 2)
    (h_lower : μ.real lowerFailure ≤ delta / 2) :
    anytimeValidConfidenceSequence μ X theta sigma2 b delta := by
  unfold anytimeValidConfidenceSequence
  have htarget_le_union :
      μ.real
        {ω | ∃ n : ℕ, 0 < n ∧
          ¬ inSubGammaConfidenceInterval X theta sigma2 b delta n ω}
        ≤ μ.real (upperFailure ∪ lowerFailure) :=
    measureReal_mono h_failure_subset
  have hunion_le :
      μ.real (upperFailure ∪ lowerFailure)
        ≤ μ.real upperFailure + μ.real lowerFailure :=
    measureReal_union_le upperFailure lowerFailure
  calc
    μ.real
        {ω | ∃ n : ℕ, 0 < n ∧
          ¬ inSubGammaConfidenceInterval X theta sigma2 b delta n ω}
        ≤ μ.real (upperFailure ∪ lowerFailure) := htarget_le_union
    _ ≤ μ.real upperFailure + μ.real lowerFailure := hunion_le
    _ ≤ delta / 2 + delta / 2 := add_le_add h_upper h_lower
    _ = delta := by ring

end

end FormalSLT.AnytimeValid
