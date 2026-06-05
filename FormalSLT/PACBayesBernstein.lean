/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayesKL
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Finite PAC-Bayes Bernstein layer

## Scope

This module adds a finite PAC-Bayes Bernstein confidence layer with an abstract
variance proxy.

## Assumptions

* a finite hypothesis class with a full-support prior;
* a supplied per-hypothesis variance proxy;
* a normalized Bernstein prior-moment certificate.

The margin-variance extractor is an input here, not a claim about a particular
classifier margin loss.

## Main declarations

* `posteriorMarginVarianceProxy` — posterior average of a supplied variance
  proxy.
* `priorBernsteinExpMoment` — normalized prior exponential moment with
  Bernstein variance and scale terms.
* `posteriorGeneralizationGap_le_bernstein_of_priorBernsteinExpMoment_le` —
  deterministic fixed-sample PAC-Bayes Bernstein adapter.
* `finitePACBayesBernstein_fixedLambda_badEventMass_le_delta` — finite
  Markov/confidence layer for a fixed Bernstein parameter.
* `finitePACBayesBernsteinMargin_badEventMass_le_delta` — posterior-dependent
  margin-style wrapper under explicit complexity and penalty certificates.

## Current boundaries

This file does not optimize over all real `lambda`. Posterior-dependent
optimization should be supplied by a finite grid/peeling certificate, matching
the existing McAllester finite-grid pattern in `PACBayesBoundedLoss`. The file
also does not include a concrete classifier-margin variance extractor or a
continuous hypothesis-space theorem.
-/

namespace FormalSLT.PACBayesBernstein

open Finset Real BigOperators
open FormalSLT.PACBayesKL

noncomputable section

variable {ι Ω : Type*}

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-! ### Bernstein prior moment and posterior variance proxy -/

/-- Posterior average of a supplied margin-variance proxy. -/
def posteriorMarginVarianceProxy [Fintype ι]
    (ρ : ι → ℝ) (varianceProxy : ι → ℝ) : ℝ :=
  ∑ i, ρ i * varianceProxy i

/--
Normalized Bernstein prior exponential moment at one sample outcome.

For each hypothesis `i`, the exponent is

`lambda * (R_i - Rhat_i(ω)) -
  lambda^2 * varianceProxy_i / (2 * (1 - scale * lambda))`.

If the sample expectation of this prior moment is at most one, Markov's
inequality supplies the finite confidence layer below.
-/
def priorBernsteinExpMoment [Fintype ι] (π : ι → ℝ)
    (lambda scale : ℝ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (varianceProxy : ι → ℝ) (ω : Ω) : ℝ :=
  ∑ i, π i *
    Real.exp
      (lambda * (riskFn i - empiricalRiskFn ω i) -
        lambda ^ 2 * varianceProxy i / (2 * (1 - scale * lambda)))

/-- Expected normalized Bernstein prior moment over a finite sample law. -/
def expectedPriorBernsteinExpMoment [Fintype Ω] [Fintype ι]
    (ν : Ω → ℝ) (π : ι → ℝ)
    (lambda scale : ℝ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (varianceProxy : ι → ℝ) : ℝ :=
  ∑ ω, ν ω *
    priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn varianceProxy ω

/--
Expected normalized PAC-Bayes Bernstein prior moment from per-hypothesis MGF
budgets.

This is the algebraic bridge used before plugging in a concrete iid
concentration lemma: each hypothesis supplies the Bernstein exponential budget,
then the prior-weighted normalized moment has expectation at most one.
-/
theorem expectedPriorBernsteinExpMoment_le_one_of_mgf_bound
    [Fintype Ω] [Fintype ι]
    {π : ι → ℝ} (hπ : IsPMF π)
    (ν : Ω → ℝ) (lambda scale : ℝ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (varianceProxy : ι → ℝ)
    (hmgf :
      ∀ i : ι,
        (∑ ω : Ω, ν ω *
          Real.exp (lambda * (riskFn i - empiricalRiskFn ω i))) ≤
        Real.exp
          (lambda ^ 2 * varianceProxy i /
            (2 * (1 - scale * lambda)))) :
    expectedPriorBernsteinExpMoment ν π lambda scale riskFn empiricalRiskFn
      varianceProxy ≤ 1 := by
  classical
  let budget : ι → ℝ :=
    fun i =>
      lambda ^ 2 * varianceProxy i /
        (2 * (1 - scale * lambda))
  have hexp_split : ∀ a b : ℝ, Real.exp (a - b) = Real.exp a * Real.exp (-b) := by
    intro a b
    rw [← Real.exp_add]
    ring_nf
  have hswap :
      expectedPriorBernsteinExpMoment ν π lambda scale riskFn empiricalRiskFn
          varianceProxy =
        ∑ i : ι,
          π i * Real.exp (-(budget i)) *
            (∑ ω : Ω, ν ω *
              Real.exp (lambda * (riskFn i - empiricalRiskFn ω i))) := by
    unfold expectedPriorBernsteinExpMoment priorBernsteinExpMoment
    calc
      (∑ ω : Ω,
          ν ω *
            ∑ i : ι,
              π i *
                Real.exp
                  (lambda * (riskFn i - empiricalRiskFn ω i) -
                    lambda ^ 2 * varianceProxy i /
                      (2 * (1 - scale * lambda))))
          =
        ∑ ω : Ω, ∑ i : ι,
          ν ω *
            (π i *
              Real.exp
                (lambda * (riskFn i - empiricalRiskFn ω i) -
                  budget i)) := by
            apply Finset.sum_congr rfl
            intro ω _hω
            rw [Finset.mul_sum]
      _ =
        ∑ i : ι, ∑ ω : Ω,
          ν ω *
            (π i *
              Real.exp
                (lambda * (riskFn i - empiricalRiskFn ω i) -
                  budget i)) := by
            rw [Finset.sum_comm]
      _ =
        ∑ i : ι,
          π i * Real.exp (-(budget i)) *
            (∑ ω : Ω, ν ω *
              Real.exp (lambda * (riskFn i - empiricalRiskFn ω i))) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ω _hω
            rw [hexp_split]
            ring
  rw [hswap]
  calc
    (∑ i : ι,
        π i * Real.exp (-(budget i)) *
          (∑ ω : Ω, ν ω *
            Real.exp (lambda * (riskFn i - empiricalRiskFn ω i))))
        ≤
      ∑ i : ι,
        π i * Real.exp (-(budget i)) *
          Real.exp (budget i) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact mul_le_mul_of_nonneg_left
          (hmgf i)
          (mul_nonneg (hπ.nonneg i) (le_of_lt (Real.exp_pos _)))
    _ = ∑ i : ι, π i := by
        apply Finset.sum_congr rfl
        intro i _hi
        calc
          π i * Real.exp (-(budget i)) * Real.exp (budget i)
              = π i * (Real.exp (-(budget i)) * Real.exp (budget i)) := by ring
          _ = π i * 1 := by
              congr 1
              rw [← Real.exp_add]
              ring_nf
              simp
          _ = π i := by ring
    _ = 1 := hπ.sum_one

/-- Finite sample mass of outcomes whose Bernstein prior moment exceeds a threshold. -/
def priorBernsteinExpMomentTailMass [Fintype Ω] [Fintype ι]
    (ν : Ω → ℝ) (π : ι → ℝ)
    (lambda scale : ℝ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (varianceProxy : ι → ℝ) (threshold : ℝ) : ℝ :=
  ∑ ω ∈ (Finset.univ.filter fun ω =>
      threshold ≤
        priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn varianceProxy ω),
    ν ω

/-- The normalized Bernstein prior moment is nonnegative under a nonnegative prior. -/
theorem priorBernsteinExpMoment_nonneg [Fintype ι]
    {π : ι → ℝ} (hπ : IsPMF π)
    (lambda scale : ℝ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (varianceProxy : ι → ℝ) (ω : Ω) :
    0 ≤ priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn varianceProxy ω := by
  unfold priorBernsteinExpMoment
  exact Finset.sum_nonneg
    (fun i _hi => mul_nonneg (hπ.nonneg i) (le_of_lt (Real.exp_pos _)))

private theorem priorBernsteinExpMoment_pos [Fintype ι] [Nonempty ι]
    {π : ι → ℝ} (hπ : IsFullSupportPMF π)
    (lambda scale : ℝ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (varianceProxy : ι → ℝ) (ω : Ω) :
    0 < priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn varianceProxy ω := by
  unfold priorBernsteinExpMoment
  exact Finset.sum_pos
    (fun i _hi => mul_pos (hπ.pos i) (Real.exp_pos _))
    Finset.univ_nonempty

/-! ### Markov confidence adapter -/

/-- Finite Markov bound for the normalized Bernstein prior moment. -/
theorem priorBernsteinExpMoment_tailMass_le_expected_div
    [Fintype Ω] [DecidableEq Ω] [Fintype ι]
    {ν : Ω → ℝ} {π : ι → ℝ} (hν : IsPMF ν) (hπ : IsPMF π)
    (lambda scale : ℝ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (varianceProxy : ι → ℝ)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    priorBernsteinExpMomentTailMass ν π lambda scale riskFn empiricalRiskFn
        varianceProxy threshold
      ≤ expectedPriorBernsteinExpMoment ν π lambda scale riskFn empiricalRiskFn
          varianceProxy / threshold := by
  unfold priorBernsteinExpMomentTailMass expectedPriorBernsteinExpMoment
  calc
    (∑ ω ∈ (Finset.univ.filter fun ω =>
        threshold ≤ priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn
          varianceProxy ω), ν ω)
        ≤ ∑ ω ∈ (Finset.univ.filter fun ω =>
            threshold ≤ priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn
              varianceProxy ω),
            (ν ω *
              priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn
                varianceProxy ω) / threshold := by
          apply Finset.sum_le_sum
          intro ω hω
          have hTail :
              threshold ≤ priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn
                varianceProxy ω :=
            (Finset.mem_filter.mp hω).2
          have hScaled :
              ν ω * threshold ≤
                ν ω * priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn
                  varianceProxy ω :=
            mul_le_mul_of_nonneg_left hTail (hν.nonneg ω)
          exact (le_div_iff₀ hthreshold).mpr hScaled
    _ ≤ ∑ ω,
          (ν ω *
            priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn
              varianceProxy ω) / threshold := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro ω hω
            exact (Finset.mem_filter.mp hω).1
          · intro ω _hω _hnot
            exact div_nonneg
              (mul_nonneg (hν.nonneg ω)
                (priorBernsteinExpMoment_nonneg hπ lambda scale riskFn empiricalRiskFn
                  varianceProxy ω))
              (le_of_lt hthreshold)
    _ =
        (∑ ω, ν ω *
          priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn varianceProxy ω) /
          threshold := by
          rw [Finset.sum_div]

/--
Finite Markov confidence adapter for a normalized Bernstein expected moment.

If the expected normalized prior moment is at most one, then the finite sample
mass where the moment exceeds `1 / delta` is at most `delta`.
-/
theorem priorBernsteinExpMoment_tailMass_le_delta_of_expected_bound
    [Fintype Ω] [DecidableEq Ω] [Fintype ι]
    {ν : Ω → ℝ} {π : ι → ℝ} (hν : IsPMF ν) (hπ : IsPMF π)
    (lambda scale : ℝ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (varianceProxy : ι → ℝ)
    {delta : ℝ} (hdelta : 0 < delta)
    (hExpected :
      expectedPriorBernsteinExpMoment ν π lambda scale riskFn empiricalRiskFn
        varianceProxy ≤ 1) :
    priorBernsteinExpMomentTailMass ν π lambda scale riskFn empiricalRiskFn
        varianceProxy (1 / delta)
      ≤ delta := by
  have hthreshold : 0 < 1 / delta := div_pos zero_lt_one hdelta
  have hmarkov :=
    priorBernsteinExpMoment_tailMass_le_expected_div
      hν hπ lambda scale riskFn empiricalRiskFn varianceProxy hthreshold
  have hdiv :
      expectedPriorBernsteinExpMoment ν π lambda scale riskFn empiricalRiskFn
          varianceProxy / (1 / delta)
        ≤ 1 / (1 / delta) := by
    exact div_le_div_of_nonneg_right hExpected (le_of_lt hthreshold)
  have hdelta_eq : (1 : ℝ) / (1 / delta) = delta := by
    field_simp [ne_of_gt hdelta]
  linarith

/-! ### Deterministic PAC-Bayes Bernstein adapter -/

/--
Deterministic finite PAC-Bayes Bernstein adapter.

For a fixed sample outcome `ω`, if the normalized Bernstein prior moment is at
most `exp(alpha)`, then every finite posterior `ρ` satisfies a fixed-`lambda`
Bernstein posterior-gap bound with posterior-averaged variance proxy.
-/
theorem posteriorGeneralizationGap_le_bernstein_of_priorBernsteinExpMoment_le
    [Fintype ι] [Nonempty ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ) (hπ : IsFullSupportPMF π)
    {lambda scale alpha : ℝ}
    (hlambda : 0 < lambda) (hscale : scale * lambda < 1)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (varianceProxy : ι → ℝ) (ω : Ω)
    (hconf :
      priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn varianceProxy ω
        ≤ Real.exp alpha) :
    posteriorGeneralizationGap ρ riskFn (empiricalRiskFn ω)
      ≤ (klDiv ρ π + alpha) / lambda +
        lambda * posteriorMarginVarianceProxy ρ varianceProxy /
          (2 * (1 - scale * lambda)) := by
  classical
  set denom : ℝ := 2 * (1 - scale * lambda)
  have hdenom_ne : denom ≠ 0 := by
    have hpos : 0 < denom := by
      dsimp [denom]
      nlinarith
    exact ne_of_gt hpos
  have hmoment_pos :
      0 < priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn
        varianceProxy ω :=
    priorBernsteinExpMoment_pos hπ lambda scale riskFn empiricalRiskFn varianceProxy ω
  have hlog :
      Real.log (priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn
        varianceProxy ω) ≤ alpha := by
    calc
      Real.log (priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn
        varianceProxy ω)
          ≤ Real.log (Real.exp alpha) := Real.log_le_log hmoment_pos hconf
      _ = alpha := Real.log_exp alpha
  let phi : ι → ℝ := fun i =>
    lambda * (riskFn i - empiricalRiskFn ω i) -
      lambda ^ 2 * varianceProxy i / denom
  have hdv := donsker_varadhan hρ hπ phi
  have hmoment :
      (∑ i, π i * Real.exp (phi i)) =
        priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn varianceProxy ω := by
    unfold phi priorBernsteinExpMoment denom
    rfl
  have hleft :
      (∑ i, ρ i * phi i) =
        lambda * posteriorGeneralizationGap ρ riskFn (empiricalRiskFn ω) -
          lambda ^ 2 * posteriorMarginVarianceProxy ρ varianceProxy / denom := by
    unfold phi posteriorMarginVarianceProxy
    rw [posteriorGeneralizationGap_eq_sum]
    calc
      (∑ i : ι,
          ρ i *
            (lambda * (riskFn i - empiricalRiskFn ω i) -
              lambda ^ 2 * varianceProxy i / denom))
          =
        ∑ i : ι,
          (ρ i * (lambda * (riskFn i - empiricalRiskFn ω i)) -
            ρ i * (lambda ^ 2 * varianceProxy i / denom)) := by
            refine Finset.sum_congr rfl (fun i _hi => ?_)
            ring
      _ =
        (∑ i : ι, ρ i * (lambda * (riskFn i - empiricalRiskFn ω i))) -
          ∑ i : ι, ρ i * (lambda ^ 2 * varianceProxy i / denom) := by
            rw [Finset.sum_sub_distrib]
      _ =
        lambda * (∑ i : ι, ρ i * (riskFn i - empiricalRiskFn ω i)) -
          lambda ^ 2 * (∑ i : ι, ρ i * varianceProxy i) / denom := by
            congr 1
            · rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun i _hi => ?_)
              ring
            · calc
                (∑ i : ι, ρ i * (lambda ^ 2 * varianceProxy i / denom))
                    =
                  ∑ i : ι, (lambda ^ 2 * (ρ i * varianceProxy i)) / denom := by
                    refine Finset.sum_congr rfl (fun i _hi => ?_)
                    ring
                _ =
                  (∑ i : ι, lambda ^ 2 * (ρ i * varianceProxy i)) / denom := by
                    rw [Finset.sum_div]
                _ =
                  lambda ^ 2 * (∑ i : ι, ρ i * varianceProxy i) / denom := by
                    rw [Finset.mul_sum]
  have hscaled :
      lambda * posteriorGeneralizationGap ρ riskFn (empiricalRiskFn ω) -
          lambda ^ 2 * posteriorMarginVarianceProxy ρ varianceProxy / denom
        ≤ klDiv ρ π + alpha := by
    rw [← hleft]
    exact hdv.trans (by rw [hmoment]; linarith)
  have hgap0 :
      posteriorGeneralizationGap ρ riskFn (empiricalRiskFn ω)
        ≤ (klDiv ρ π + alpha +
            lambda ^ 2 * posteriorMarginVarianceProxy ρ varianceProxy / denom) /
          lambda := by
    rw [le_div_iff₀ hlambda]
    linarith
  calc
    posteriorGeneralizationGap ρ riskFn (empiricalRiskFn ω)
        ≤ (klDiv ρ π + alpha +
            lambda ^ 2 * posteriorMarginVarianceProxy ρ varianceProxy / denom) /
          lambda := hgap0
    _ =
        (klDiv ρ π + alpha) / lambda +
          lambda * posteriorMarginVarianceProxy ρ varianceProxy / denom := by
          field_simp [hlambda.ne', hdenom_ne]

/-! ### Fixed-parameter finite bad-event theorem -/

/-- Samples where some posterior violates the fixed-`lambda` Bernstein bound. -/
def finitePACBayesBernsteinFixedLambdaBadSamples
    [Fintype Ω] [Fintype ι]
    (π : ι → ℝ) (lambda scale delta : ℝ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (varianceProxy : ι → ℝ) : Finset Ω :=
  Finset.univ.filter fun ω =>
    ∃ ρ : ι → ℝ,
      IsPMF ρ ∧
        posteriorGeneralizationGap ρ riskFn (empiricalRiskFn ω) >
          (klDiv ρ π + Real.log (1 / delta)) / lambda +
            lambda * posteriorMarginVarianceProxy ρ varianceProxy /
              (2 * (1 - scale * lambda))

/--
Finite fixed-`lambda` PAC-Bayes Bernstein bad-event theorem.

If the expected normalized Bernstein prior moment is at most one, the finite
sample mass of outcomes where some posterior violates the fixed-`lambda`
Bernstein bound is at most `delta`.
-/
theorem finitePACBayesBernstein_fixedLambda_badEventMass_le_delta
    [Fintype Ω] [DecidableEq Ω] [Fintype ι] [Nonempty ι]
    {ν : Ω → ℝ} (hν : IsPMF ν)
    {π : ι → ℝ} (hπ : IsFullSupportPMF π)
    (lambda scale delta : ℝ)
    (hlambda : 0 < lambda) (hscale : scale * lambda < 1)
    (hdelta : 0 < delta)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (varianceProxy : ι → ℝ)
    (hExpected :
      expectedPriorBernsteinExpMoment ν π lambda scale riskFn empiricalRiskFn
        varianceProxy ≤ 1) :
    (∑ ω ∈
        finitePACBayesBernsteinFixedLambdaBadSamples π lambda scale delta
          riskFn empiricalRiskFn varianceProxy,
        ν ω) ≤ delta := by
  classical
  set threshold : ℝ := 1 / delta with hthreshold_def
  have hthreshold_pos : 0 < threshold := by
    simpa [threshold, hthreshold_def] using div_pos zero_lt_one hdelta
  have hsubset :
      finitePACBayesBernsteinFixedLambdaBadSamples π lambda scale delta
          riskFn empiricalRiskFn varianceProxy
        ⊆
      (Finset.univ.filter fun ω =>
        threshold ≤
          priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn
            varianceProxy ω) := by
    intro ω hω
    rw [finitePACBayesBernsteinFixedLambdaBadSamples, Finset.mem_filter] at hω
    rw [Finset.mem_filter]
    rcases hω.2 with ⟨ρ, hρ, hbad⟩
    refine ⟨Finset.mem_univ ω, ?_⟩
    by_contra hnot
    have hconf :
        priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn
            varianceProxy ω ≤ threshold :=
      le_of_not_ge hnot
    have hconf_exp :
        priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn
            varianceProxy ω ≤ Real.exp (Real.log (1 / delta)) := by
      have hthreshold_eq :
          threshold = Real.exp (Real.log (1 / delta)) := by
        rw [hthreshold_def, Real.exp_log (div_pos zero_lt_one hdelta)]
      exact hconf.trans_eq hthreshold_eq
    have hbound :=
      posteriorGeneralizationGap_le_bernstein_of_priorBernsteinExpMoment_le
        hρ hπ hlambda hscale riskFn empiricalRiskFn varianceProxy ω hconf_exp
    linarith
  have hmass_le :
      (∑ ω ∈
          finitePACBayesBernsteinFixedLambdaBadSamples π lambda scale delta
            riskFn empiricalRiskFn varianceProxy,
          ν ω)
        ≤
      ∑ ω ∈ (Finset.univ.filter fun ω =>
        threshold ≤
          priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn
            varianceProxy ω), ν ω := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro ω _hω _hnot
      exact hν.nonneg ω)
  have hmarkov :=
    priorBernsteinExpMoment_tailMass_le_delta_of_expected_bound
      hν hπ.toIsPMF lambda scale riskFn empiricalRiskFn varianceProxy hdelta hExpected
  exact hmass_le.trans (by
    simpa [threshold, hthreshold_def, priorBernsteinExpMomentTailMass] using hmarkov)

/-! ### Posterior-dependent margin-style wrapper -/

/-- Samples where some posterior violates a supplied posterior-dependent penalty. -/
def finitePACBayesBernsteinPenaltyBadSamples
    [Fintype Ω] [Fintype ι]
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (posteriorPenalty : (ι → ℝ) → ℝ) : Finset Ω :=
  Finset.univ.filter fun ω =>
    ∃ ρ : ι → ℝ,
      IsPMF ρ ∧
        posteriorGeneralizationGap ρ riskFn (empiricalRiskFn ω) >
          posteriorPenalty ρ

/--
Finite PAC-Bayes Bernstein margin-style bad-event theorem.

The theorem is posterior-dependent through `posteriorPenalty`. A user supplies:

* a complexity certificate bounding `KL(ρ‖π) + log(1/δ)`;
* a penalty certificate showing the fixed-`lambda` Bernstein penalty is at most
  the chosen posterior-dependent penalty.

Instantiating `posteriorPenalty ρ` with

`sqrt (2 * V_ρ * complexityOf ρ) + scale * complexityOf ρ`

gives the usual Bernstein shape, provided the caller proves the corresponding
finite-`lambda` optimization or grid certificate.
-/
theorem finitePACBayesBernsteinPenalty_badEventMass_le_delta
    [Fintype Ω] [DecidableEq Ω] [Fintype ι] [Nonempty ι]
    {ν : Ω → ℝ} (hν : IsPMF ν)
    {π : ι → ℝ} (hπ : IsFullSupportPMF π)
    (lambda scale delta : ℝ)
    (hlambda : 0 < lambda) (hscale : scale * lambda < 1)
    (hdelta : 0 < delta)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (varianceProxy : ι → ℝ)
    (complexityOf posteriorPenalty : (ι → ℝ) → ℝ)
    (hcomplexity :
      ∀ ρ : ι → ℝ, IsPMF ρ →
        klDiv ρ π + Real.log (1 / delta) ≤ complexityOf ρ)
    (hpenalty :
      ∀ ρ : ι → ℝ, IsPMF ρ →
        complexityOf ρ / lambda +
            lambda * posteriorMarginVarianceProxy ρ varianceProxy /
              (2 * (1 - scale * lambda))
          ≤ posteriorPenalty ρ)
    (hExpected :
      expectedPriorBernsteinExpMoment ν π lambda scale riskFn empiricalRiskFn
        varianceProxy ≤ 1) :
    (∑ ω ∈
        finitePACBayesBernsteinPenaltyBadSamples riskFn empiricalRiskFn posteriorPenalty,
        ν ω) ≤ delta := by
  classical
  have hsubset :
      finitePACBayesBernsteinPenaltyBadSamples riskFn empiricalRiskFn posteriorPenalty
        ⊆
      finitePACBayesBernsteinFixedLambdaBadSamples π lambda scale delta
        riskFn empiricalRiskFn varianceProxy := by
    intro ω hω
    rw [finitePACBayesBernsteinPenaltyBadSamples, Finset.mem_filter] at hω
    rw [finitePACBayesBernsteinFixedLambdaBadSamples, Finset.mem_filter]
    rcases hω.2 with ⟨ρ, hρ, hbad⟩
    refine ⟨Finset.mem_univ ω, ρ, hρ, ?_⟩
    have hbase :
        (klDiv ρ π + Real.log (1 / delta)) / lambda +
            lambda * posteriorMarginVarianceProxy ρ varianceProxy /
              (2 * (1 - scale * lambda))
          ≤ complexityOf ρ / lambda +
            lambda * posteriorMarginVarianceProxy ρ varianceProxy /
              (2 * (1 - scale * lambda)) := by
      exact add_le_add
        (div_le_div_of_nonneg_right (hcomplexity ρ hρ) (le_of_lt hlambda))
        (le_refl _)
    have hpen := hpenalty ρ hρ
    linarith
  have hmass_le :
      (∑ ω ∈
          finitePACBayesBernsteinPenaltyBadSamples riskFn empiricalRiskFn posteriorPenalty,
          ν ω)
        ≤
      ∑ ω ∈
          finitePACBayesBernsteinFixedLambdaBadSamples π lambda scale delta
            riskFn empiricalRiskFn varianceProxy,
          ν ω := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro ω _hω _hnot
      exact hν.nonneg ω)
  exact hmass_le.trans
    (finitePACBayesBernstein_fixedLambda_badEventMass_le_delta
      hν hπ lambda scale delta hlambda hscale hdelta riskFn empiricalRiskFn
      varianceProxy hExpected)

/--
Finite Bernstein-of-margin wrapper with the textbook square-root-plus-linear
penalty form, under an explicit finite-parameter certificate.
-/
theorem finitePACBayesBernsteinMargin_badEventMass_le_delta
    [Fintype Ω] [DecidableEq Ω] [Fintype ι] [Nonempty ι]
    {ν : Ω → ℝ} (hν : IsPMF ν)
    {π : ι → ℝ} (hπ : IsFullSupportPMF π)
    (lambda scale delta : ℝ)
    (hlambda : 0 < lambda) (hscale : scale * lambda < 1)
    (hdelta : 0 < delta)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (varianceProxy : ι → ℝ)
    (complexityOf : (ι → ℝ) → ℝ)
    (hcomplexity :
      ∀ ρ : ι → ℝ, IsPMF ρ →
        klDiv ρ π + Real.log (1 / delta) ≤ complexityOf ρ)
    (hpenalty :
      ∀ ρ : ι → ℝ, IsPMF ρ →
        complexityOf ρ / lambda +
            lambda * posteriorMarginVarianceProxy ρ varianceProxy /
              (2 * (1 - scale * lambda))
          ≤
        Real.sqrt (2 * posteriorMarginVarianceProxy ρ varianceProxy * complexityOf ρ) +
          scale * complexityOf ρ)
    (hExpected :
      expectedPriorBernsteinExpMoment ν π lambda scale riskFn empiricalRiskFn
        varianceProxy ≤ 1) :
    (∑ ω ∈
        finitePACBayesBernsteinPenaltyBadSamples riskFn empiricalRiskFn
          (fun ρ =>
            Real.sqrt (2 * posteriorMarginVarianceProxy ρ varianceProxy * complexityOf ρ) +
              scale * complexityOf ρ),
        ν ω) ≤ delta :=
  finitePACBayesBernsteinPenalty_badEventMass_le_delta
    hν hπ lambda scale delta hlambda hscale hdelta riskFn empiricalRiskFn varianceProxy
    complexityOf
    (fun ρ =>
      Real.sqrt (2 * posteriorMarginVarianceProxy ρ varianceProxy * complexityOf ρ) +
        scale * complexityOf ρ)
    hcomplexity hpenalty hExpected

end

end FormalSLT.PACBayesBernstein
