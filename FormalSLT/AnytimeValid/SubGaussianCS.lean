/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import FormalSLT.Concentration.SubGamma.Extractor
import FormalSLT.Concentration.SubGamma.CondExpProduct
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
The one-step conditional sub-Gamma supermartingale bound, derived from the per-increment
model rather than carried as a hypothesis.

From the conditional sub-Gamma increment model on `X` (bounded `|X_k| ≤ b`, conditionally
centered `μ[X_k | F_k] = 0`, conditional second moment `μ[X_k² | F_k] ≤ σ²`), the fixed-`lambda`
exponential process satisfies `E[M_{n+1} | F_n] ≤ M_n`. This is exactly the
`h_condSubGamma_step` obligation taken by `nonneg_supermartingale_of_condSubGamma`.

The proof factors `M_{n+1} = (M_n · exp(-cgf)) · exp(lambda · X_n)`, pulls the predictable
prefactor `Z = M_n · exp(-cgf)` out of the conditional expectation
(`FormalSLT.Concentration.SubGamma.condExp_mul_bounded_left`), and bounds the residual MGF
`E[exp(lambda · X_n) | F_n] ≤ exp(cgf)` via
`FormalSLT.Concentration.SubGamma.condSubGammaMGF_of_bounded_centered_condVariance`.
Since `Z ≥ 0` and `exp(-cgf) · exp(cgf) = 1`, the product collapses back to `M_n`.
-/
theorem condSubGamma_supermartingale_step
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b lam : ℝ}
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam : 0 ≤ lam) (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (h_adapted : StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    ∀ n,
      μ[subGammaExponentialProcess X sigma2 b lam (n + 1) | ℱ n]
        ≤ᵐ[μ] subGammaExponentialProcess X sigma2 b lam n := by
  intro n
  set cgf : ℝ := subGammaCgf sigma2 b lam with hcgf_def
  -- Predictable prefactor `Z = M_n · exp(-cgf)` and residual `Y = exp(lambda · X_n)`.
  set Z : Ω → ℝ := fun ω => subGammaExponentialProcess X sigma2 b lam n ω * Real.exp (-cgf)
    with hZ_def
  set Y : Ω → ℝ := fun ω => Real.exp (lam * X n ω) with hY_def
  -- Step 1: pointwise factorization `M_{n+1} = Z · Y`.
  have hfact : subGammaExponentialProcess X sigma2 b lam (n + 1) = fun ω => Z ω * Y ω := by
    funext ω
    simp only [subGammaExponentialProcess, runningSum, Finset.sum_range_succ, hZ_def, hY_def]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  -- Step 3: `Z` is `F_n`-strongly-measurable (predictable prefactor of `M_n`).
  have hZ_meas : StronglyMeasurable[ℱ n] Z := (h_adapted n).mul_const _
  -- Step 4: `Z` is a.s. bounded. On `S_n ≤ n·b` we have `M_n ≤ exp(lam·n·b − n·cgf)`.
  set C : ℝ := Real.exp (lam * (n : ℝ) * b - (n : ℝ) * cgf) * Real.exp (-cgf) with hC_def
  have hZ_bdd : ∀ᵐ ω ∂μ, |Z ω| ≤ C := by
    filter_upwards [ae_all_iff.2 hbound] with ω hω
    have hsum_le : runningSum X n ω ≤ (n : ℝ) * b := by
      have hle : ∀ i ∈ Finset.range n, X i ω ≤ b := fun i _ => (abs_le.mp (hω i)).2
      calc runningSum X n ω = Finset.sum (Finset.range n) (fun i => X i ω) := rfl
        _ ≤ Finset.sum (Finset.range n) (fun _ => b) := Finset.sum_le_sum hle
        _ = (n : ℝ) * b := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hMn_le : subGammaExponentialProcess X sigma2 b lam n ω
        ≤ Real.exp (lam * (n : ℝ) * b - (n : ℝ) * cgf) := by
      rw [subGammaExponentialProcess, ← hcgf_def]
      apply Real.exp_le_exp.2
      have : lam * runningSum X n ω ≤ lam * ((n : ℝ) * b) :=
        mul_le_mul_of_nonneg_left hsum_le hlam
      nlinarith
    have hZnonneg : 0 ≤ Z ω :=
      mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    rw [abs_of_nonneg hZnonneg, hZ_def, hC_def]
    exact mul_le_mul_of_nonneg_right hMn_le (Real.exp_pos _).le
  -- Step 5: `Y = exp(lambda · X_n)` is integrable.
  have hY_int : Integrable Y μ :=
    FormalSLT.Concentration.SubGamma.integrable_exp_mul_of_bounded (hX_meas n) (hbound n)
  -- Step 6: pull the predictable prefactor out of the conditional expectation.
  have hpull :
      μ[fun ω => Z ω * Y ω | ℱ n] =ᵐ[μ] fun ω => Z ω * (μ[Y | ℱ n]) ω :=
    FormalSLT.Concentration.SubGamma.condExp_mul_bounded_left (ℱ.le n) hZ_meas hZ_bdd hY_int
  -- Step 7: residual conditional MGF bound `E[exp(lambda · X_n) | F_n] ≤ exp(cgf)`.
  have hmgf : μ[Y | ℱ n] ≤ᵐ[μ] fun _ => Real.exp cgf := by
    have h :=
      FormalSLT.Concentration.SubGamma.condSubGammaMGF_of_bounded_centered_condVariance
        hb hσ (hX_meas n) (hX_int n) (hbound n) (hcenter n) (hvar n) lam hlam hblam
    -- The extractor RHS constant is definitionally `Real.exp cgf`.
    simpa [hY_def, hcgf_def, subGammaCgf] using h
  -- Step 8: combine a.e. `E[M_{n+1}|F_n] = Z · E[Y|F_n] ≤ Z · exp(cgf) = M_n`.
  rw [hfact]
  filter_upwards [hpull, hmgf] with ω hpull' hmgf'
  rw [hpull']
  have hZnonneg : 0 ≤ Z ω :=
    mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  calc Z ω * (μ[Y | ℱ n]) ω
      ≤ Z ω * Real.exp cgf := mul_le_mul_of_nonneg_left hmgf' hZnonneg
    _ = subGammaExponentialProcess X sigma2 b lam n ω := by
        rw [hZ_def]
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

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
The running-mean boundary-crossing event is contained in the exponential-process running-max
boundary event, for any positive tilt `lam`. This is the deterministic content that
`ville_inequality_subGamma_running_mean` previously carried as the hypothesis
`h_exponential_boundary`: it is now derived from the definitions of `runningMean`,
`subGammaExponentialProcess`, and `finiteRunningMax`.

At `n = 0` both sides reduce to `1`. For `n ≥ 1`, multiplying the boundary inequality
`t ≤ S_n / n - cgf / lam` by `lam * n > 0` gives `lam * n * t ≤ lam * S_n - n * cgf`, and the
running max dominates the time-`n` exponential term.
-/
theorem subGamma_runningMean_boundary_subset
    {Ω : Type*} {X : ℕ → Ω → ℝ} {sigma2 b lam t : ℝ} {n : ℕ}
    (hlam : 0 < lam) :
    {ω | t ≤ runningMean X n ω - subGammaCgf sigma2 b lam / lam}
      ⊆
    {ω | Real.exp (lam * (n : ℝ) * t)
        ≤ finiteRunningMax (subGammaExponentialProcess X sigma2 b lam) n ω} := by
  intro ω hω
  simp only [Set.mem_setOf_eq, runningMean] at hω
  simp only [Set.mem_setOf_eq]
  have hle :
      subGammaExponentialProcess X sigma2 b lam n ω
        ≤ finiteRunningMax (subGammaExponentialProcess X sigma2 b lam) n ω :=
    Finset.le_sup' (fun k => subGammaExponentialProcess X sigma2 b lam k ω)
      (Finset.self_mem_range_succ n)
  refine le_trans ?_ hle
  simp only [subGammaExponentialProcess, Real.exp_le_exp]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [runningSum]
  · have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hlam0 : lam ≠ 0 := hlam.ne'
    have hnn : (0 : ℝ) ≤ lam * (n : ℝ) := by positivity
    calc lam * (n : ℝ) * t
        ≤ lam * (n : ℝ) * (runningSum X n ω / (n : ℝ) - subGammaCgf sigma2 b lam / lam) :=
          mul_le_mul_of_nonneg_left hω hnn
      _ = lam * runningSum X n ω - (n : ℝ) * subGammaCgf sigma2 b lam := by
          field_simp

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
End-to-end form with the deterministic boundary hypothesis discharged: for a positive tilt
`lam`, from adaptedness, integrability, and the one-step conditional sub-Gamma bound, the
centered running-mean confidence boundary has sub-Gamma tail mass at most `exp (-lam * n * t)`.
The `h_exponential_boundary` set-inclusion is now supplied by
`subGamma_runningMean_boundary_subset`, so the only remaining stochastic input is the
supermartingale step `h_condSubGamma_step`.
-/
theorem ville_inequality_subGamma_running_mean_of_condSubGamma_pos
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b lam t : ℝ} {n : ℕ}
    (hlam : 0 < lam)
    (h_adapted : StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (h_integrable : ∀ k, Integrable (subGammaExponentialProcess X sigma2 b lam k) μ)
    (h_condSubGamma_step : ∀ k,
      μ[subGammaExponentialProcess X sigma2 b lam (k + 1) | ℱ k]
        ≤ᵐ[μ] subGammaExponentialProcess X sigma2 b lam k) :
    μ.real {ω | t ≤ runningMean X n ω - subGammaCgf sigma2 b lam / lam}
      ≤ Real.exp (-lam * (n : ℝ) * t) :=
  ville_inequality_subGamma_running_mean
    (nonneg_supermartingale_of_condSubGamma h_adapted h_integrable h_condSubGamma_step).1
    (subGamma_runningMean_boundary_subset hlam)

/--
End-to-end anytime-valid sub-Gamma confidence-sequence tail bound with NO carried stochastic
hypotheses. From the conditional sub-Gamma increment model on `X` (bounded `|X_k| ≤ b`,
conditionally centered `μ[X_k | F_k] = 0`, conditional second moment `μ[X_k² | F_k] ≤ σ²`) and a
positive tilt `lam`, the centered running-mean confidence boundary has sub-Gamma tail mass at most
`exp (-lam · n · t)`. Both previously-carried hypotheses are discharged internally:
`subGamma_runningMean_boundary_subset` supplies the deterministic boundary inclusion, and
`condSubGamma_supermartingale_step` supplies the one-step supermartingale bound from the model.
-/
theorem ville_inequality_subGamma_running_mean_of_increment_model
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b lam t : ℝ} {n : ℕ}
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (h_adapted : StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (h_integrable : ∀ k, Integrable (subGammaExponentialProcess X sigma2 b lam k) μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    μ.real {ω | t ≤ runningMean X n ω - subGammaCgf sigma2 b lam / lam}
      ≤ Real.exp (-lam * (n : ℝ) * t) :=
  ville_inequality_subGamma_running_mean_of_condSubGamma_pos hlam h_adapted h_integrable
    (condSubGamma_supermartingale_step hb hσ hlam.le hblam hX_meas hX_int h_adapted
      hbound hcenter hvar)

/--
Anytime-valid confidence-sequence wrapper for the sub-Gamma interval.

SCOPE: this is the final finite-union (subadditivity) step ONLY, not an
end-to-end derivation of an anytime-valid sub-Gamma confidence sequence. The two
one-sided failure sets `upperFailure` / `lowerFailure` are FREE hypotheses: their
mass bounds `≤ delta / 2` are assumed, never wired to the exponential process.
The load-bearing one-sided Ville coverage is therefore the hypothesis here, not a
conclusion. Given a containment of the first-failure event in their union and the
two one-sided mass bounds, the interval sequence has failure mass at most `delta`.

For the genuine end-to-end results (where the one-sided coverage is DERIVED from
the conditional sub-Gamma increment model), use
`ville_inequality_subGamma_running_mean_of_increment_model` (this file) and the
witnessed headline `MixtureCS.mixture_confidence_sequence_uniformPrior`.
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
