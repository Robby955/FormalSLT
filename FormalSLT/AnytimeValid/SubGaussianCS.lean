/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import FormalSLT.Concentration.SubGamma.Extractor
import FormalSLT.AnytimeValid.VilleMaximalIneq

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
  Mathlib does not expose this as a named theorem, so it is proved in-tree as
  `FormalSLT.AnytimeValid.ville_maximal_ineq` (file `VilleMaximalIneq.lean`), via the
  optional-stopping route behind `MeasureTheory.maximal_ineq` applied to `-M`. Its
  sub-Gamma specialization `ville_subGamma_maximal_bound` discharges the Ville payoff
  that `ville_inequality_subGamma_running_mean` previously carried as a hypothesis.
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
Ville's inequality for the sub-Gamma exponential process: the finite-horizon running maximum of
`M = subGammaExponentialProcess` reaches `exp (lam * n * t)` with probability at most
`exp (-lam * n * t)`.

This is the bound that `ville_inequality_subGamma_running_mean` previously carried as the
hypothesis `h_ville_from_maximal_ineq`. It is now derived from the in-tree supermartingale Ville
maximal inequality `ville_maximal_ineq`: the process is nonnegative (it is `Real.exp`), so the
maximal inequality gives `exp (lam n t) * μ.real {…} ≤ ∫ M 0`; here `M 0 ≡ 1` and `μ` is a
probability measure, so `∫ M 0 = 1`; dividing by `exp (lam n t) > 0` yields `exp (-lam n t)`.
-/
theorem ville_subGamma_maximal_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ} {sigma2 b lam : ℝ}
    (hsup : Supermartingale (subGammaExponentialProcess X sigma2 b lam) ℱ μ)
    (n : ℕ) (t : ℝ) :
    μ.real {ω | Real.exp (lam * (n : ℝ) * t)
        ≤ finiteRunningMax (subGammaExponentialProcess X sigma2 b lam) n ω}
      ≤ Real.exp (-lam * (n : ℝ) * t) := by
  have hnonneg : 0 ≤ subGammaExponentialProcess X sigma2 b lam := fun _ _ => (Real.exp_pos _).le
  have ha : (0 : ℝ) < Real.exp (lam * (n : ℝ) * t) := Real.exp_pos _
  have hA0 : Real.exp (lam * (n : ℝ) * t) ≠ 0 := ne_of_gt ha
  have hmax := ville_maximal_ineq (a := Real.exp (lam * (n : ℝ) * t)) hsup hnonneg n
  have hM0 : ∫ ω, subGammaExponentialProcess X sigma2 b lam 0 ω ∂μ = 1 := by
    have hbody :
        (fun ω => subGammaExponentialProcess X sigma2 b lam 0 ω) =ᵐ[μ] fun _ => (1 : ℝ) :=
      Filter.Eventually.of_forall fun ω => by simp [subGammaExponentialProcess, runningSum]
    rw [integral_congr_ae hbody]
    simp [integral_const]
  rw [hM0] at hmax
  rw [show Real.exp (-lam * (n : ℝ) * t) = (Real.exp (lam * (n : ℝ) * t))⁻¹ by
        rw [← Real.exp_neg]; congr 1; ring]
  simp only [finiteRunningMax]
  set A := Real.exp (lam * (n : ℝ) * t)
  have key : ∀ q : ℝ, A * q ≤ 1 → q ≤ A⁻¹ := fun q hq => by
    calc q = A⁻¹ * (A * q) := by rw [← mul_assoc, inv_mul_cancel₀ hA0, one_mul]
      _ ≤ A⁻¹ * 1 := mul_le_mul_of_nonneg_left hq (inv_pos.mpr ha).le
      _ = A⁻¹ := mul_one _
  exact key _ hmax

/--
Finite-horizon Ville bound for the running mean: if the sub-Gamma exponential process is a
supermartingale (and `μ` is a probability measure), the centered running-mean confidence
boundary has mass at most `exp (-lam * n * t)`. The Ville payoff is supplied by
`ville_subGamma_maximal_bound` — it is no longer carried as a hypothesis.
-/
theorem ville_inequality_subGamma_running_mean
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b lam t : ℝ} {n : ℕ}
    (hsup : Supermartingale (subGammaExponentialProcess X sigma2 b lam) ℱ μ)
    (h_exponential_boundary :
      {ω | t ≤ runningMean X n ω - subGammaCgf sigma2 b lam / lam}
        ⊆
      {ω | Real.exp (lam * (n : ℝ) * t)
          ≤ finiteRunningMax (subGammaExponentialProcess X sigma2 b lam) n ω}) :
    μ.real {ω | t ≤ runningMean X n ω - subGammaCgf sigma2 b lam / lam}
      ≤ Real.exp (-lam * (n : ℝ) * t) :=
  (measureReal_mono h_exponential_boundary).trans (ville_subGamma_maximal_bound hsup n t)

/--
End-to-end form with no carried Ville hypothesis: from adaptedness, integrability, and the
one-step conditional sub-Gamma bound `E[M_{k+1} | F_k] ≤ M_k`, the centered running-mean
confidence boundary has sub-Gamma tail mass at most `exp (-lam * n * t)`. Composes
`nonneg_supermartingale_of_condSubGamma` (which builds the supermartingale from the conditional
MGF step) with `ville_inequality_subGamma_running_mean`.
-/
theorem ville_inequality_subGamma_running_mean_of_condSubGamma
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b lam t : ℝ} {n : ℕ}
    (h_adapted : StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (h_integrable : ∀ k, Integrable (subGammaExponentialProcess X sigma2 b lam k) μ)
    (h_condSubGamma_step : ∀ k,
      μ[subGammaExponentialProcess X sigma2 b lam (k + 1) | ℱ k]
        ≤ᵐ[μ] subGammaExponentialProcess X sigma2 b lam k)
    (h_exponential_boundary :
      {ω | t ≤ runningMean X n ω - subGammaCgf sigma2 b lam / lam}
        ⊆
      {ω | Real.exp (lam * (n : ℝ) * t)
          ≤ finiteRunningMax (subGammaExponentialProcess X sigma2 b lam) n ω}) :
    μ.real {ω | t ≤ runningMean X n ω - subGammaCgf sigma2 b lam / lam}
      ≤ Real.exp (-lam * (n : ℝ) * t) :=
  ville_inequality_subGamma_running_mean
    (nonneg_supermartingale_of_condSubGamma h_adapted h_integrable h_condSubGamma_step).1
    h_exponential_boundary

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
