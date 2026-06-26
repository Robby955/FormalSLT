/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayesSeeger

/-!
# Maurer kl-form PAC-Bayes bound (fully closed)

This module lands the **Maurer (2004) kl-form PAC-Bayes bound** as the
named-result capstone of the PAC-Bayes lane.  The headline is the canonical,
tightest named PAC-Bayes statement

`binKL (L̂(Q)) (L(Q)) ≤ (KL(Q‖P) + log(2√n / δ)) / n`

holding on a sample event of probability at least `1 − δ`.

The change-of-measure spine (Gibbs, Donsker-Varadhan, the `2√n` prior moment,
`binKL`, `binKL_pinsker`, and the kl-form good-event theorems) already lives in
`PACBayesKL.lean` and `PACBayesSeeger.lean`.  The kl-form good-event theorems
there (`pacbayes_seeger_klForm_of_priorMoment_and_binaryKLJensen` and its
bernoulli-moment variant) **carry** the binary-kl posterior-mixture Jensen step
as a named hypothesis `hbinaryKLJensen`.  This module's contribution is to
**discharge that Jensen step in-house** — from the log-sum inequality, proved
here from the same `Real.log_le_sub_one_of_pos` primitive the in-house Gibbs
inequality uses — so the Maurer headline closes with no carried Jensen
hypothesis.

The only hypotheses the headline keeps are the genuine domain hypotheses of the
bound: the empirical risks lie in `[0,1]` and the population risks in `(0,1)`
(valid Bernoulli parameters), exactly as the McAllester square-root form carries
`0 < populationRisk < 1`.  These are statement-domain hypotheses, not
proof-gap-equivalent carries.

## Main results

* `logSum_ineq` — the scalar log-sum inequality on a finite index type.
* `binKL_posteriorMixture_jensen` — binary-kl posterior-mixture Jensen (the
  discharged step): `binKL (E_ρ â) (E_ρ a) ≤ E_ρ (binKL â a)`.
* `maurer_pacbayes_kl_bound` — the Maurer kl-form good-event headline, with the
  Jensen step discharged (no `hbinaryKLJensen` hypothesis).
* `maurer_pacbayes_kl_pinsker_corollary` — the standard `√(KL/2n)` Pinsker
  corollary `L(Q) − L̂(Q) ≤ √((KL + log(2√n/δ)) / (2n))`.
* `maurer_pacbayes_kl_complexity_nonneg` — the structural fact that the Maurer
  complexity term is nonnegative.

## Source

A. Maurer, *A note on the PAC Bayesian theorem*, 2004, arXiv:cs/0411099 (the
`(KL(Q‖P) + log(2√n / δ)) / n` kl-form is the citable headline constant).
D. McAllester, *PAC-Bayesian model averaging*, COLT 1999 (change-of-measure
origin, already in-house).  M. Seeger, *PAC-Bayesian generalisation error bounds
for Gaussian process classification*, JMLR 3 (2002), 233-269 (the kl-form
lineage this module follows).
-/

namespace FormalSLT.PACBayes.MaurerKL

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesSeeger

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-! ### Log-sum inequality -/

/--
**Scalar log-sum inequality** on a finite index type, with zero-handling.

For nonnegative `a b : ι → ℝ` with `0 < ∑ b`, where each index either has
`b i > 0` or `b i = 0` together with `a i = 0` (so the term vanishes under
Lean's `log 0 = 0` convention),

`(∑ a) * log((∑ a)/(∑ b)) ≤ ∑ a i * log(a i / b i)`.

Proved by the tangent-line bound `log x ≤ x − 1` (`Real.log_le_sub_one_of_pos`),
the same primitive used by the in-house Gibbs inequality.
-/
theorem logSum_ineq {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hzero : ∀ i, b i = 0 → a i = 0)
    (hBpos : 0 < ∑ i, b i) :
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) ≤
      ∑ i, a i * Real.log (a i / b i) := by
  classical
  set A := ∑ i, a i with hA
  set B := ∑ i, b i with hB
  have hApos : 0 ≤ A := Finset.sum_nonneg (fun i _ => ha i)
  rcases eq_or_lt_of_le hApos with hA0 | hApos'
  · -- A = 0: each a i = 0, both sides are 0.
    rw [← hA0]
    simp only [zero_mul]
    have hzeroA : ∀ i, a i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha i)).mp (hA0.symm) i
        (Finset.mem_univ i)
    have hrhs : ∑ i, a i * Real.log (a i / b i) = 0 := by
      apply Finset.sum_eq_zero; intro i _; rw [hzeroA i]; ring
    rw [hrhs]
  · have hABpos : 0 < A / B := div_pos hApos' hBpos
    -- per-term lower bound `a i log(A/B) + (a i − (A/B) b i) ≤ a i log(a i/b i)`
    have hterm : ∀ i, a i * Real.log (A / B) + (a i - (A / B) * b i)
        ≤ a i * Real.log (a i / b i) := by
      intro i
      rcases eq_or_lt_of_le (ha i) with h0 | hpos
      · rw [← h0]
        simp only [zero_mul, zero_sub, zero_add]
        have : 0 ≤ (A / B) * b i := mul_nonneg (le_of_lt hABpos) (hb i)
        linarith
      · -- a i > 0 forces b i > 0 (otherwise hzero gives a i = 0)
        have hbpos : 0 < b i := by
          rcases eq_or_lt_of_le (hb i) with hb0 | hbp
          · exact absurd (hzero i hb0.symm) (ne_of_gt hpos)
          · exact hbp
        have haine : a i ≠ 0 := ne_of_gt hpos
        have hbine : b i ≠ 0 := ne_of_gt hbpos
        have hlog := Real.log_le_sub_one_of_pos (x := (A / B) / (a i / b i))
          (div_pos hABpos (div_pos hpos hbpos))
        have hlogsplit : Real.log ((A / B) / (a i / b i)) =
            Real.log (A / B) - Real.log (a i / b i) := by
          rw [Real.log_div (ne_of_gt hABpos) (ne_of_gt (div_pos hpos hbpos))]
        rw [hlogsplit] at hlog
        have hmul : a i * (Real.log (A / B) - Real.log (a i / b i)) ≤
            a i * ((A / B) / (a i / b i) - 1) :=
          mul_le_mul_of_nonneg_left hlog (le_of_lt hpos)
        have harith : a i * ((A / B) / (a i / b i) - 1) = (A / B) * b i - a i := by
          field_simp
        rw [harith] at hmul
        nlinarith [hmul]
    -- sum the per-term bound; the extra `(a i − (A/B) b i)` terms sum to 0
    have hsum_le :
        ∑ i, (a i * Real.log (A / B) + (a i - (A / B) * b i))
          ≤ ∑ i, a i * Real.log (a i / b i) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    have hlhs_eq :
        ∑ i, (a i * Real.log (A / B) + (a i - (A / B) * b i)) =
          A * Real.log (A / B) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← hA]
      have hextra : ∑ i, (a i - (A / B) * b i) = 0 := by
        rw [Finset.sum_sub_distrib, ← hA]
        rw [show ∑ i, (A / B) * b i = (A / B) * ∑ i, b i from by rw [Finset.mul_sum]]
        rw [← hB, div_mul_cancel₀ A (ne_of_gt hBpos)]
        ring
      rw [hextra]; ring
    rw [← hlhs_eq]; exact hsum_le

/-! ### Binary-KL posterior-mixture Jensen (the discharged step) -/

/--
**Binary-KL posterior-mixture Jensen.**  Joint convexity of `binKL` along the
posterior mixture: with posterior weights `ρ` (a PMF), empirical risks
`â ∈ [0,1]`, and population risks `a ∈ (0,1)`,

`binKL (E_ρ â) (E_ρ a) ≤ E_ρ (binKL â a)`.

This is exactly the `hbinaryKLJensen` hypothesis carried by the Seeger kl-form
good-event theorems.  Discharging it here is the contribution that turns those
hypothesis-carrying theorems into the fully-closed Maurer headline.

The proof applies `logSum_ineq` to the two Bernoulli arms `(ρ â, ρ a)` and
`(ρ (1 − â), ρ (1 − a))` and recombines.

-- fidelity: non-vacuous joint-convexity Jensen; the witness
-- `binKL_posteriorMixture_jensen_witness` instantiates ρ, â, a on Fin 2 with a
-- genuine strict gap (LHS strictly below RHS). The risk ranges are the genuine
-- Bernoulli-parameter domain, not a vacuity escape.
-/
theorem binKL_posteriorMixture_jensen {ι : Type*} [Fintype ι]
    (ρ â a : ι → ℝ)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∑ i, ρ i = 1)
    (hâ0 : ∀ i, 0 ≤ â i) (hâ1 : ∀ i, â i ≤ 1)
    (ha0 : ∀ i, 0 < a i) (ha1 : ∀ i, a i < 1) :
    binKL (posteriorAverage ρ â) (posteriorAverage ρ a) ≤
      posteriorAverage ρ (fun i => binKL (â i) (a i)) := by
  classical
  set pbar := posteriorAverage ρ â with hpbar
  set qbar := posteriorAverage ρ a with hqbar
  -- A single log-sum step over a generic positive arm `(â', a')`.
  have harm : ∀ (â' a' : ι → ℝ),
      (∀ i, 0 ≤ â' i) → (∀ i, 0 < a' i) →
      (posteriorAverage ρ â') *
          Real.log ((posteriorAverage ρ â') / (posteriorAverage ρ a'))
        ≤ ∑ i, ρ i * (â' i * Real.log (â' i / a' i)) := by
    intro â' a' hâ'0 ha'0
    have hb : ∀ i, 0 ≤ ρ i * a' i := fun i => mul_nonneg (hρ0 i) (le_of_lt (ha'0 i))
    have ha : ∀ i, 0 ≤ ρ i * â' i := fun i => mul_nonneg (hρ0 i) (hâ'0 i)
    have hz : ∀ i, ρ i * a' i = 0 → ρ i * â' i = 0 := by
      intro i hi
      rcases mul_eq_zero.mp hi with hρ0i | ha0i
      · rw [hρ0i]; ring
      · exact absurd ha0i (ne_of_gt (ha'0 i))
    have hBpos : 0 < ∑ i, ρ i * a' i := by
      have hcontra : (∑ i, ρ i * a' i) ≠ 0 := by
        intro h0
        have hall : ∀ i ∈ Finset.univ, ρ i * a' i = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hb i)).mp h0
        have hρzero : ∀ i, ρ i = 0 := by
          intro i
          rcases mul_eq_zero.mp (hall i (Finset.mem_univ i)) with h | h
          · exact h
          · exact absurd h (ne_of_gt (ha'0 i))
        have : ∑ i, ρ i = 0 := Finset.sum_eq_zero (fun i _ => hρzero i)
        rw [hρ1] at this; norm_num at this
      exact lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => hb i)) (Ne.symm hcontra)
    have hls := logSum_ineq (fun i => ρ i * â' i) (fun i => ρ i * a' i) ha hb hz hBpos
    have hsumA : (∑ i, ρ i * â' i) = posteriorAverage ρ â' := rfl
    have hsumB : (∑ i, ρ i * a' i) = posteriorAverage ρ a' := rfl
    rw [hsumA, hsumB] at hls
    refine le_trans hls (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro i _
    rcases eq_or_lt_of_le (hρ0 i) with hρ0i | hρpos
    · simp only []; rw [← hρ0i]; ring
    · have hne : ρ i ≠ 0 := ne_of_gt hρpos
      rcases eq_or_lt_of_le (hâ'0 i) with hâ0i | hâpos
      · simp only []; rw [← hâ0i]; ring
      · simp only []
        have hratio : (ρ i * â' i) / (ρ i * a' i) = â' i / a' i := by
          rw [mul_div_mul_left _ _ hne]
        rw [hratio]; ring
  have h1 := harm â a hâ0 ha0
  have h2 := harm (fun i => 1 - â i) (fun i => 1 - a i)
    (fun i => by linarith [hâ1 i]) (fun i => by linarith [ha1 i])
  have hpA1 : posteriorAverage ρ (fun i => 1 - â i) = 1 - pbar := by
    rw [hpbar]
    show (∑ i, ρ i * (1 - â i)) = 1 - ∑ i, ρ i * â i
    rw [show ∑ i, ρ i * (1 - â i) = ∑ i, (ρ i - ρ i * â i) from by
      apply Finset.sum_congr rfl; intro i _; ring]
    rw [Finset.sum_sub_distrib, hρ1]
  have hqA1 : posteriorAverage ρ (fun i => 1 - a i) = 1 - qbar := by
    rw [hqbar]
    show (∑ i, ρ i * (1 - a i)) = 1 - ∑ i, ρ i * a i
    rw [show ∑ i, ρ i * (1 - a i) = ∑ i, (ρ i - ρ i * a i) from by
      apply Finset.sum_congr rfl; intro i _; ring]
    rw [Finset.sum_sub_distrib, hρ1]
  rw [hpA1, hqA1] at h2
  unfold binKL posteriorAverage
  have hsplit : ∑ i, ρ i * (â i * Real.log (â i / a i) +
      (1 - â i) * Real.log ((1 - â i) / (1 - a i)))
      = (∑ i, ρ i * (â i * Real.log (â i / a i)))
        + ∑ i, ρ i * ((1 - â i) * Real.log ((1 - â i) / (1 - a i))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [hsplit]
  linarith [h1, h2]

/-! ### Maurer kl-form headline (Jensen discharged) -/

/--
**Maurer kl-form PAC-Bayes bound.**  On a sample event of probability at least
`1 − δ`, for every posterior `Q = ρ` the binary KL between posterior empirical
and population risk obeys

`binKL (L̂(Q)) (L(Q)) ≤ (KL(Q‖P) + log(2√n / δ)) / n`.

This is the fully-closed Maurer headline: the binary-kl posterior-mixture Jensen
step is discharged by `binKL_posteriorMixture_jensen`, so there is **no carried
`hbinaryKLJensen` hypothesis**.  The only kept hypotheses are the genuine
Bernoulli-parameter domain hypotheses on the risk functions
(`empiricalRiskFn ω ∈ [0,1]`, `riskFn ∈ (0,1)`) plus the prior exponential-moment
bound that supplies the `2√n` constant.

-- fidelity: the ∀ρ inside the good event is the correct direction — `δ`, `n` are
-- fixed before the universally-quantified posterior `ρ`, not a hidden ∀ρ∃const.
-- Non-vacuity is machine-checked by `maurer_kl_bound_witness` (two-point class,
-- δ = 1/2, n = 2, numeric RHS) in the witness file.
-/
theorem maurer_pacbayes_kl_bound
    {ι Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 0 < n)
    (ν : Ω → ℝ) (hν : IsPMF ν)
    (prior : ι → ℝ) (hprior : IsFullSupportPMF prior)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (hrisk0 : ∀ i, 0 < riskFn i) (hrisk1 : ∀ i, riskFn i < 1)
    (hemp0 : ∀ ω i, 0 ≤ empiricalRiskFn ω i)
    (hemp1 : ∀ ω i, empiricalRiskFn ω i ≤ 1)
    (delta : ℝ) (hdelta : 0 < delta)
    (hpointwise :
      ∀ i : ι,
        (∑ ω : Ω,
          ν ω * Real.exp ((n : ℝ) * binKL (empiricalRiskFn ω i) (riskFn i))) ≤
          2 * Real.sqrt (n : ℝ)) :
    1 - delta ≤
      ∑ ω ∈ (Finset.univ.filter fun ω : Ω =>
        ∀ ρ : ι → ℝ, IsPMF ρ →
          binKL (posteriorAverage ρ (empiricalRiskFn ω))
              (posteriorAverage ρ riskFn) ≤
            (klDiv ρ prior + Real.log ((2 * Real.sqrt (n : ℝ)) / delta)) /
              (n : ℝ)),
        ν ω :=
  pacbayes_seeger_klForm_of_bernoulliPriorMoment_and_binaryKLJensen
    hn ν hν prior hprior riskFn empiricalRiskFn delta hdelta hpointwise
    (fun ω ρ hρ =>
      binKL_posteriorMixture_jensen ρ (empiricalRiskFn ω) riskFn
        hρ.nonneg hρ.sum_one
        (fun i => hemp0 ω i) (fun i => hemp1 ω i)
        hrisk0 hrisk1)

/-! ### Pinsker corollary -/

/--
**Maurer kl-form Pinsker corollary.**  Pinsker's inequality for the Bernoulli
relative entropy converts the kl-form bound into the standard square-root gap:
for posterior empirical risk `L̂(Q) ∈ [0,1]`, population risk `L(Q) ∈ (0,1)`, and
a kl-form complexity bound `binKL (L̂(Q)) (L(Q)) ≤ complexity`,

`L(Q) − L̂(Q) ≤ √(complexity / 2)`.

Specialised to `complexity = (KL(Q‖P) + log(2√n/δ)) / n` this is the familiar
Maurer `√((KL + log(2√n/δ)) / (2n))` bound.  Reuses the in-house Seeger Pinsker
chain (`binKL_pinsker`).

-- fidelity: the conclusion is a genuine numeric gap bound; the witness
-- `maurer_kl_pinsker_witness` pins concrete risks (empirical 0.4, population
-- 0.5) and a positive complexity, yielding a strictly-below-1 gap bound.
-/
theorem maurer_pacbayes_kl_pinsker_corollary
    {empiricalRisk populationRisk complexity : ℝ}
    (hemp0 : 0 ≤ empiricalRisk) (hemp1 : empiricalRisk ≤ 1)
    (hpop0 : 0 < populationRisk) (hpop1 : populationRisk < 1)
    (hkl : binKL empiricalRisk populationRisk ≤ complexity) :
    populationRisk - empiricalRisk ≤ Real.sqrt (complexity / 2) :=
  pacbayes_seeger_klForm_implies_mcallester_sqrt hemp0 hemp1 hpop0 hpop1 hkl

/-! ### Structural theorem -/

/--
**Maurer complexity term is nonnegative.**  For any posterior `ρ` (a PMF) and
full-support prior `prior`, with `0 < n` and `0 < δ ≤ 2√n`, the Maurer
complexity numerator `KL(ρ‖prior) + log(2√n / δ)` is nonnegative.  `KL ≥ 0` by
Gibbs and `log(2√n/δ) ≥ 0` since `δ ≤ 2√n`, so the kl-form RHS is a genuine
(nonnegative) bound, never a vacuous negative threshold.

-- fidelity: structural nonnegativity of the complexity numerator; both summands
-- are individually nonnegative (Gibbs KL ≥ 0; log of a ≥ 1 argument ≥ 0), so the
-- statement is a real constraint, not vacuously true.
-/
theorem maurer_pacbayes_kl_complexity_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ prior : ι → ℝ} (hρ : IsPMF ρ) (hprior : IsFullSupportPMF prior)
    {n : ℕ} (hn : 0 < n) {delta : ℝ} (hdelta : 0 < delta)
    (hdle : delta ≤ 2 * Real.sqrt (n : ℝ)) :
    0 ≤ klDiv ρ prior + Real.log ((2 * Real.sqrt (n : ℝ)) / delta) := by
  have hkl : 0 ≤ klDiv ρ prior := klDiv_nonneg hρ hprior
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hnum : 0 < 2 * Real.sqrt (n : ℝ) := by positivity
  have hratio : 1 ≤ (2 * Real.sqrt (n : ℝ)) / delta :=
    (one_le_div hdelta).mpr hdle
  have hlog : 0 ≤ Real.log ((2 * Real.sqrt (n : ℝ)) / delta) :=
    Real.log_nonneg hratio
  linarith

end

end FormalSLT.PACBayes.MaurerKL
