/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# KL divergence and PAC-Bayes change-of-measure

Defines the **KL divergence** (relative entropy) for finite distributions
and proves the two key lemmas for PAC-Bayes bounds:

1. `klDiv_nonneg` — Gibbs inequality: KL(ρ‖π) ≥ 0 for any two
   probability distributions on a finite type (with full-support prior).
2. `donsker_varadhan` — the variational inequality:
   ∑ ρ_i · f_i ≤ KL(ρ‖π) + log(∑ π_i · exp(f_i))
3. Posterior-risk adapters: deterministic finite sums that specialize
   Donsker-Varadhan to posterior generalization gaps
   `λ · (R_ρ - R̂_ρ)`.
4. Finite Markov/confidence adapters for the prior exponential moment. These
   are still not McAllester/Catoni sample bounds; the iid exponential-moment
   estimate remains a separate proof layer.

## Proof technique

Both results use only `Real.log_le_sub_one_of_pos` (i.e., log x ≤ x - 1
for x > 0). No abstract Jensen machinery is needed:
- Gibbs inequality sums the per-term bound `ρ_i · log(ρ_i/π_i) ≥ ρ_i - π_i`.
- Donsker-Varadhan applies Gibbs to the Gibbs posterior
  `q_i = π_i · exp(f_i) / Z`.
-/

namespace FormalSLT.PACBayesKL

open Finset Real BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Finite PMF predicates -/

/-- A function is a probability mass function: non-negative and sums to 1. -/
structure IsPMF (ρ : ι → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ ρ i
  sum_one : ∑ i, ρ i = 1

/-- Full-support PMF: strictly positive everywhere. -/
structure IsFullSupportPMF (π : ι → ℝ) : Prop extends IsPMF π where
  pos : ∀ i, 0 < π i

/-! ### KL divergence -/

/-- KL divergence (relative entropy) for finite distributions.
`klDiv ρ π = ∑ i, ρ i * log(ρ i / π i)`.
With Lean's `x / 0 = 0` and `log 0 = 0` conventions, terms with
`ρ i = 0` contribute zero. Under posterior-support inclusion in the prior,
`PACBayes.FinitePMFBridge` identifies this finite sum with mathlib's
`InformationTheory.klDiv`. Without that condition, this totalized real sum is
not the standard extended-real KL divergence. -/
noncomputable def klDiv (ρ π : ι → ℝ) : ℝ :=
  ∑ i, ρ i * Real.log (ρ i / π i)

/-! ### Posterior averages and generalization gaps -/

omit [DecidableEq ι] in
/-- Posterior average of a real-valued quantity over a finite hypothesis class. -/
noncomputable def posteriorAverage (ρ : ι → ℝ) (g : ι → ℝ) : ℝ :=
  ∑ i, ρ i * g i

omit [DecidableEq ι] in
/-- Posterior population risk, represented as a finite posterior average. -/
noncomputable def posteriorRisk (ρ : ι → ℝ) (riskFn : ι → ℝ) : ℝ :=
  posteriorAverage ρ riskFn

omit [DecidableEq ι] in
/-- Posterior empirical risk, represented as a finite posterior average. -/
noncomputable def posteriorEmpiricalRisk (ρ : ι → ℝ) (empiricalRiskFn : ι → ℝ) : ℝ :=
  posteriorAverage ρ empiricalRiskFn

omit [DecidableEq ι] in
/-- Posterior generalization gap `R_ρ - R̂_ρ`. -/
noncomputable def posteriorGeneralizationGap
    (ρ : ι → ℝ) (riskFn empiricalRiskFn : ι → ℝ) : ℝ :=
  posteriorRisk ρ riskFn - posteriorEmpiricalRisk ρ empiricalRiskFn

omit [DecidableEq ι] in
/-- Posterior gaps are posterior averages of pointwise gaps. -/
theorem posteriorGeneralizationGap_eq_sum
    (ρ : ι → ℝ) (riskFn empiricalRiskFn : ι → ℝ) :
    posteriorGeneralizationGap ρ riskFn empiricalRiskFn =
      ∑ i, ρ i * (riskFn i - empiricalRiskFn i) := by
  unfold posteriorGeneralizationGap posteriorRisk posteriorEmpiricalRisk posteriorAverage
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-! ### Per-term lower bound -/

/-- Key per-term inequality: `ρ * log(ρ/π) ≥ ρ - π` when `ρ ≥ 0` and `π > 0`.
Uses only `log x ≤ x - 1` for `x > 0`. -/
private lemma klDiv_term_ge (hρ : 0 ≤ ρ_i) (hπ : 0 < π_i) :
    ρ_i * Real.log (ρ_i / π_i) ≥ ρ_i - π_i := by
  rcases eq_or_lt_of_le hρ with h0 | hρ_pos
  · -- Case ρ_i = 0: LHS = 0 ≥ 0 - π_i = -π_i
    subst h0
    simp [hπ.le]
  · -- Case ρ_i > 0: use log(π/ρ) ≤ π/ρ - 1
    have hρπ : 0 < π_i / ρ_i := div_pos hπ hρ_pos
    have h_log := Real.log_le_sub_one_of_pos hρπ
    -- log(π/ρ) ≤ π/ρ - 1, multiply both sides by -ρ (flip sign)
    have h1 : -(ρ_i * Real.log (π_i / ρ_i)) ≥ -(ρ_i * (π_i / ρ_i - 1)) := by
      linarith [mul_le_mul_of_nonneg_left h_log hρ_pos.le]
    -- -ρ·log(π/ρ) = ρ·log(ρ/π)
    have h_neg_log : -(ρ_i * Real.log (π_i / ρ_i)) = ρ_i * Real.log (ρ_i / π_i) := by
      rw [Real.log_div (ne_of_gt hπ) (ne_of_gt hρ_pos),
          Real.log_div (ne_of_gt hρ_pos) (ne_of_gt hπ)]
      ring
    -- -ρ·(π/ρ - 1) = ρ - π
    have h_arith : -(ρ_i * (π_i / ρ_i - 1)) = ρ_i - π_i := by
      field_simp
      ring
    linarith

/-! ### Gibbs inequality -/

omit [DecidableEq ι] in
/-- **Gibbs inequality**: KL(ρ‖π) ≥ 0 for any PMF ρ and full-support PMF π.
Proof sums the per-term bound and uses ∑ρ = ∑π = 1. -/
theorem klDiv_nonneg {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsFullSupportPMF π) :
    0 ≤ klDiv ρ π := by
  unfold klDiv
  have h_terms : ∀ i ∈ Finset.univ, ρ i - π i ≤ ρ i * Real.log (ρ i / π i) :=
    fun i _ => (klDiv_term_ge (hρ.nonneg i) (hπ.pos i)).le
  have h_sum_ge : ∑ i, (ρ i - π i) ≤ ∑ i, ρ i * Real.log (ρ i / π i) :=
    Finset.sum_le_sum h_terms
  have h_diff_zero : ∑ i : ι, (ρ i - π i) = 0 := by
    rw [Finset.sum_sub_distrib]; rw [hρ.sum_one, hπ.toIsPMF.sum_one, sub_self]
  linarith

/-! ### Donsker-Varadhan variational inequality -/

/-- The Gibbs posterior: `q_i = π_i · exp(f_i) / Z` where Z is the normalizer. -/
private noncomputable def gibbsPosterior (π : ι → ℝ) (f : ι → ℝ) (i : ι) : ℝ :=
  π i * Real.exp (f i) / ∑ j, π j * Real.exp (f j)

omit [DecidableEq ι] in
private lemma gibbsPosterior_pos (hπ : IsFullSupportPMF π) (f : ι → ℝ)
    [Nonempty ι] (i : ι) : 0 < gibbsPosterior π f i := by
  unfold gibbsPosterior
  apply div_pos
  · exact mul_pos (hπ.pos i) (Real.exp_pos _)
  · apply Finset.sum_pos
    · intro j _; exact mul_pos (hπ.pos j) (Real.exp_pos _)
    · exact Finset.univ_nonempty

omit [DecidableEq ι] in
private lemma gibbsPosterior_sum_one (hπ : IsFullSupportPMF π) (f : ι → ℝ)
    [Nonempty ι] : ∑ i, gibbsPosterior π f i = 1 := by
  unfold gibbsPosterior
  set Z := ∑ j : ι, π j * Real.exp (f j)
  have hZ : (0 : ℝ) < Z :=
    Finset.sum_pos (fun j _ => mul_pos (hπ.pos j) (Real.exp_pos _)) Finset.univ_nonempty
  have hZ_ne : Z ≠ 0 := ne_of_gt hZ
  -- ∑ (a_i / Z) = (∑ a_i) / Z = Z / Z = 1
  rw [show ∑ i : ι, π i * Real.exp (f i) / Z = (∑ i : ι, π i * Real.exp (f i)) / Z from by
    simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]]
  exact div_self hZ_ne

omit [DecidableEq ι] in
private lemma gibbsPosterior_isPMF (hπ : IsFullSupportPMF π) (f : ι → ℝ)
    [Nonempty ι] : IsPMF (gibbsPosterior π f) where
  nonneg i := le_of_lt (gibbsPosterior_pos hπ f i)
  sum_one := gibbsPosterior_sum_one hπ f

omit [DecidableEq ι] in
private lemma gibbsPosterior_isFullSupport (hπ : IsFullSupportPMF π) (f : ι → ℝ)
    [Nonempty ι] : IsFullSupportPMF (gibbsPosterior π f) where
  nonneg i := le_of_lt (gibbsPosterior_pos hπ f i)
  sum_one := gibbsPosterior_sum_one hπ f
  pos i := gibbsPosterior_pos hπ f i

omit [DecidableEq ι] in
/-- Key identity: KL(ρ‖q) = KL(ρ‖π) + log Z - ∑ ρ_i · f_i,
where q is the Gibbs posterior and Z = ∑ π_i · exp(f_i). -/
private lemma klDiv_gibbs_eq {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsFullSupportPMF π)
    (f : ι → ℝ) [Nonempty ι] :
    klDiv ρ (gibbsPosterior π f)
      = klDiv ρ π + Real.log (∑ i, π i * Real.exp (f i)) - ∑ i, ρ i * f i := by
  unfold klDiv gibbsPosterior
  set Z := ∑ j, π j * Real.exp (f j)
  have hZ : 0 < Z :=
    Finset.sum_pos (fun j _ => mul_pos (hπ.pos j) (Real.exp_pos _)) Finset.univ_nonempty
  -- Per-term: ρ_i * log(ρ_i / (π_i·exp(f_i)/Z)) = ρ_i * log(ρ_i/π_i) + ρ_i * log Z - ρ_i * f_i
  suffices h_per : ∀ i, ρ i * Real.log (ρ i / (π i * Real.exp (f i) / Z))
      = ρ i * Real.log (ρ i / π i) + ρ i * Real.log Z - ρ i * f i by
    simp_rw [h_per]
    -- Show equality by direct sum manipulation
    have h_split : ∑ i : ι, (ρ i * Real.log (ρ i / π i) + ρ i * Real.log Z - ρ i * f i)
        = ∑ i : ι, (ρ i * Real.log (ρ i / π i) + ρ i * Real.log Z)
          - ∑ i : ι, ρ i * f i :=
      Finset.sum_sub_distrib
        (fun i => ρ i * Real.log (ρ i / π i) + ρ i * Real.log Z) (fun i => ρ i * f i)
    have h_add : ∑ i : ι, (ρ i * Real.log (ρ i / π i) + ρ i * Real.log Z)
        = ∑ i : ι, ρ i * Real.log (ρ i / π i) + ∑ i : ι, ρ i * Real.log Z :=
      Finset.sum_add_distrib
    -- ∑ ρ_i * log Z = (∑ ρ_i) * log Z = log Z
    have h_logZ : ∑ i : ι, ρ i * Real.log Z = Real.log Z := by
      rw [← Finset.sum_mul]; rw [hρ.sum_one, one_mul]
    linarith [h_split, h_add, h_logZ]
  intro i
  rcases eq_or_lt_of_le (hρ.nonneg i) with h0 | hρ_pos
  · simp [← h0]
  · have hπi := hπ.pos i
    have hρi_ne : ρ i ≠ 0 := ne_of_gt hρ_pos
    have hπi_ne : π i ≠ 0 := ne_of_gt hπi
    -- log(ρ/(π·e^f/Z)) = log(ρ·Z/(π·e^f)) = log(ρ/π) + log Z - f
    rw [show ρ i / (π i * Real.exp (f i) / Z) = ρ i * Z / (π i * Real.exp (f i)) by
      field_simp]
    rw [Real.log_div (mul_ne_zero hρi_ne (ne_of_gt hZ))
        (mul_ne_zero hπi_ne (ne_of_gt (Real.exp_pos _)))]
    rw [Real.log_mul hρi_ne (ne_of_gt hZ)]
    rw [Real.log_mul hπi_ne (ne_of_gt (Real.exp_pos _))]
    rw [Real.log_exp]
    -- Goal: log ρ + log Z - log π - f = log Z - f + log(ρ/π)
    rw [Real.log_div hρi_ne hπi_ne]
    ring

omit [DecidableEq ι] in
/-- **Donsker-Varadhan variational inequality**:
For any PMF ρ, full-support PMF π, and function f,
  ∑ ρ_i · f_i ≤ KL(ρ‖π) + log(∑ π_i · exp(f_i)).

This is the key change-of-measure lemma for PAC-Bayes bounds. -/
theorem donsker_varadhan [Nonempty ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsFullSupportPMF π) (f : ι → ℝ) :
    ∑ i, ρ i * f i ≤ klDiv ρ π + Real.log (∑ i, π i * Real.exp (f i)) := by
  -- KL(ρ‖q) ≥ 0 where q is the Gibbs posterior
  have h_kl_q := klDiv_nonneg hρ (gibbsPosterior_isFullSupport hπ f)
  -- KL(ρ‖q) = KL(ρ‖π) + log Z - ∑ ρ_i · f_i
  have h_eq := klDiv_gibbs_eq hρ hπ f
  linarith

/-! ### Posterior change-of-measure adapters -/

omit [DecidableEq ι] in
/-- Donsker-Varadhan specialized to posterior averages. -/
theorem posterior_change_of_measure [Nonempty ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsFullSupportPMF π) (f : ι → ℝ) :
    posteriorAverage ρ f
      ≤ klDiv ρ π + Real.log (∑ i, π i * Real.exp (f i)) := by
  simpa [posteriorAverage] using donsker_varadhan hρ hπ f

omit [DecidableEq ι] in
/-- Donsker-Varadhan applied to a scaled posterior generalization gap.

This is a deterministic finite change-of-measure statement. It does not
claim an iid sample bound or introduce confidence parameters; those require
the separate exponential-moment and Markov steps. -/
theorem posterior_generalization_gap_change_of_measure [Nonempty ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsFullSupportPMF π)
    (lambda : ℝ) (riskFn empiricalRiskFn : ι → ℝ) :
    lambda * posteriorGeneralizationGap ρ riskFn empiricalRiskFn
      ≤ klDiv ρ π +
        Real.log (∑ i, π i * Real.exp (lambda * (riskFn i - empiricalRiskFn i))) := by
  have h :=
    posterior_change_of_measure hρ hπ
      (fun i => lambda * (riskFn i - empiricalRiskFn i))
  have h_lhs :
      posteriorAverage ρ (fun i => lambda * (riskFn i - empiricalRiskFn i)) =
        lambda * posteriorGeneralizationGap ρ riskFn empiricalRiskFn := by
    unfold posteriorAverage
    rw [posteriorGeneralizationGap_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  simpa [h_lhs] using h

omit [DecidableEq ι] in
/-- Division form of the posterior-gap change-of-measure adapter.

For positive `lambda`, the deterministic finite change-of-measure inequality
can be read as a direct upper bound on the posterior generalization gap. This
is the algebraic form used before introducing a probabilistic confidence
parameter. -/
theorem posterior_generalization_gap_le_complexity_div_lambda [Nonempty ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsFullSupportPMF π)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (riskFn empiricalRiskFn : ι → ℝ) :
    posteriorGeneralizationGap ρ riskFn empiricalRiskFn
      ≤ (klDiv ρ π +
          Real.log (∑ i, π i * Real.exp (lambda * (riskFn i - empiricalRiskFn i)))) /
        lambda := by
  have h :=
    posterior_generalization_gap_change_of_measure
      hρ hπ lambda riskFn empiricalRiskFn
  rw [le_div_iff₀ hlambda]
  rw [mul_comm]
  exact h

omit [DecidableEq ι] in
/-- Posterior-risk form of the finite PAC-Bayes change-of-measure adapter.

This states the same deterministic finite result as a risk bound:

`R_ρ ≤ R̂_ρ + (KL(ρ‖π) + log E_π exp(λ(R_i - R̂_i))) / λ`.

The remaining McAllester/Catoni sample-bound layer is the probabilistic
exponential-moment bound on the log term plus a Markov/confidence step. -/
theorem posterior_risk_le_empiricalRisk_plus_complexity_div_lambda [Nonempty ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsFullSupportPMF π)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (riskFn empiricalRiskFn : ι → ℝ) :
    posteriorRisk ρ riskFn
      ≤ posteriorEmpiricalRisk ρ empiricalRiskFn +
        (klDiv ρ π +
          Real.log (∑ i, π i * Real.exp (lambda * (riskFn i - empiricalRiskFn i)))) /
        lambda := by
  have hgap :=
    posterior_generalization_gap_le_complexity_div_lambda
      hρ hπ hlambda riskFn empiricalRiskFn
  unfold posteriorGeneralizationGap at hgap
  linarith

omit [DecidableEq ι] in
/-- Posterior-gap bound after an external prior log-moment estimate.

This theorem is the deterministic adapter for later high-probability
PAC-Bayes proofs: once a product-measure argument supplies

`log E_π exp(λ(R_i - R̂_i)) ≤ logMomentBound`,

the posterior gap is bounded by `(KL + logMomentBound) / λ`. -/
theorem posterior_generalization_gap_le_of_log_moment_bound [Nonempty ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsFullSupportPMF π)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (riskFn empiricalRiskFn : ι → ℝ) {logMomentBound : ℝ}
    (hlog :
      Real.log (∑ i, π i * Real.exp (lambda * (riskFn i - empiricalRiskFn i)))
        ≤ logMomentBound) :
    posteriorGeneralizationGap ρ riskFn empiricalRiskFn
      ≤ (klDiv ρ π + logMomentBound) / lambda := by
  have hgap :=
    posterior_generalization_gap_le_complexity_div_lambda
      hρ hπ hlambda riskFn empiricalRiskFn
  have hcomplexity :
      (klDiv ρ π +
          Real.log (∑ i, π i * Real.exp (lambda * (riskFn i - empiricalRiskFn i)))) /
        lambda
        ≤ (klDiv ρ π + logMomentBound) / lambda := by
    rw [div_le_div_iff_of_pos_right hlambda]
    linarith
  exact le_trans hgap hcomplexity

omit [DecidableEq ι] in
/-- Posterior-risk bound after an external prior log-moment estimate. -/
theorem posterior_risk_le_empiricalRisk_plus_of_log_moment_bound [Nonempty ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsFullSupportPMF π)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (riskFn empiricalRiskFn : ι → ℝ) {logMomentBound : ℝ}
    (hlog :
      Real.log (∑ i, π i * Real.exp (lambda * (riskFn i - empiricalRiskFn i)))
        ≤ logMomentBound) :
    posteriorRisk ρ riskFn
      ≤ posteriorEmpiricalRisk ρ empiricalRiskFn +
        (klDiv ρ π + logMomentBound) / lambda := by
  have hgap :=
    posterior_generalization_gap_le_of_log_moment_bound
      hρ hπ hlambda riskFn empiricalRiskFn hlog
  unfold posteriorGeneralizationGap at hgap
  linarith

/-! ### Finite Markov/confidence adapter for prior exponential moments -/

omit [DecidableEq ι] in
/-- Prior exponential moment at one sample outcome.

For a fixed sample `ω`, this is
`E_{i~π} exp(λ (R_i - Rhat_i(ω)))` in finite-sum form. -/
noncomputable def priorExpMoment {Ω : Type*} (π : ι → ℝ) (lambda : ℝ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ) (ω : Ω) : ℝ :=
  ∑ i, π i * Real.exp (lambda * (riskFn i - empiricalRiskFn ω i))

omit [DecidableEq ι] in
/-- Expected prior exponential moment over a finite sample distribution. -/
noncomputable def expectedPriorExpMoment {Ω : Type*} [Fintype Ω]
    (ν : Ω → ℝ) (π : ι → ℝ) (lambda : ℝ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ) : ℝ :=
  ∑ ω, ν ω * priorExpMoment π lambda riskFn empiricalRiskFn ω

omit [DecidableEq ι] in
/-- Finite sample mass of outcomes whose prior exponential moment exceeds a threshold. -/
noncomputable def priorExpMomentTailMass {Ω : Type*} [Fintype Ω]
    (ν : Ω → ℝ) (π : ι → ℝ) (lambda : ℝ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ) (threshold : ℝ) : ℝ :=
  ∑ ω ∈ (Finset.univ.filter fun ω =>
      threshold ≤ priorExpMoment π lambda riskFn empiricalRiskFn ω), ν ω

omit [DecidableEq ι] in
/-- The prior exponential moment is nonnegative under a nonnegative prior. -/
theorem priorExpMoment_nonneg {Ω : Type*} {π : ι → ℝ} (hπ : IsPMF π)
    (lambda : ℝ) (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ) (ω : Ω) :
    0 ≤ priorExpMoment π lambda riskFn empiricalRiskFn ω := by
  unfold priorExpMoment
  exact Finset.sum_nonneg
    (fun i _ => mul_nonneg (hπ.nonneg i) (le_of_lt (Real.exp_pos _)))

omit [DecidableEq ι] in
/-- Finite Markov bound for the prior exponential moment.

This is the probabilistic tail step needed after an expected prior-moment
estimate has been proved. It is finite-support only; the product-measure iid
moment estimate remains a separate theorem. -/
theorem priorExpMoment_tailMass_le_expected_div {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    {ν : Ω → ℝ} {π : ι → ℝ} (hν : IsPMF ν) (hπ : IsPMF π)
    (lambda : ℝ) (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    priorExpMomentTailMass ν π lambda riskFn empiricalRiskFn threshold
      ≤ expectedPriorExpMoment ν π lambda riskFn empiricalRiskFn / threshold := by
  unfold priorExpMomentTailMass expectedPriorExpMoment
  calc
    (∑ ω ∈ (Finset.univ.filter fun ω =>
        threshold ≤ priorExpMoment π lambda riskFn empiricalRiskFn ω), ν ω)
        ≤ ∑ ω ∈ (Finset.univ.filter fun ω =>
            threshold ≤ priorExpMoment π lambda riskFn empiricalRiskFn ω),
            (ν ω * priorExpMoment π lambda riskFn empiricalRiskFn ω) / threshold := by
          apply Finset.sum_le_sum
          intro ω hω
          have hTail :
              threshold ≤ priorExpMoment π lambda riskFn empiricalRiskFn ω :=
            (Finset.mem_filter.mp hω).2
          have hScaled :
              ν ω * threshold ≤
                ν ω * priorExpMoment π lambda riskFn empiricalRiskFn ω :=
            mul_le_mul_of_nonneg_left hTail (hν.nonneg ω)
          exact (le_div_iff₀ hthreshold).mpr hScaled
    _ ≤ ∑ ω, (ν ω * priorExpMoment π lambda riskFn empiricalRiskFn ω) / threshold := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro ω hω
            exact (Finset.mem_filter.mp hω).1
          · intro ω _ _
            exact div_nonneg
              (mul_nonneg (hν.nonneg ω)
                (priorExpMoment_nonneg hπ lambda riskFn empiricalRiskFn ω))
              (le_of_lt hthreshold)
    _ = (∑ ω, ν ω * priorExpMoment π lambda riskFn empiricalRiskFn ω) / threshold := by
          rw [Finset.sum_div]

omit [DecidableEq ι] in
/-- Finite Markov confidence adapter for a bounded expected prior moment.

If the sample expectation of the prior exponential moment is at most `C`,
then the finite sample mass of outcomes where the prior moment exceeds
`C / δ` is at most `δ`. This supplies the Markov/confidence layer that later
PAC-Bayes sample-bound proofs consume after proving an iid exponential-moment
bound for `C`. -/
theorem priorExpMoment_tailMass_le_delta_of_expected_bound {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    {ν : Ω → ℝ} {π : ι → ℝ} (hν : IsPMF ν) (hπ : IsPMF π)
    (lambda : ℝ) (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    {C delta : ℝ} (hC : 0 < C) (hdelta : 0 < delta)
    (hExpected :
      expectedPriorExpMoment ν π lambda riskFn empiricalRiskFn ≤ C) :
    priorExpMomentTailMass ν π lambda riskFn empiricalRiskFn (C / delta)
      ≤ delta := by
  have hthreshold : 0 < C / delta := div_pos hC hdelta
  have hmarkov :=
    priorExpMoment_tailMass_le_expected_div
      hν hπ lambda riskFn empiricalRiskFn hthreshold
  have hdiv :
      expectedPriorExpMoment ν π lambda riskFn empiricalRiskFn / (C / delta)
        ≤ C / (C / delta) := by
    exact div_le_div_of_nonneg_right hExpected (le_of_lt hthreshold)
  have hCdiv : C / (C / delta) = delta := by
    field_simp [ne_of_gt hC, ne_of_gt hdelta]
  linarith

end FormalSLT.PACBayesKL
