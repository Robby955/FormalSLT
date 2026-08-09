/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.IndicatorBernsteinConfidence

/-!
# Observable low-risk PAC-Bayes--Bernstein bounds for indicator losses

This module turns the population-variance confidence theorem for finite
indicator losses into an observable posterior-risk bound.  The key elementary
inequality is `R * (1 - R) <= R`, so the posterior average of the exact
Bernoulli variance proxies is at most the posterior population risk divided by
the sample size.  Rearranging the resulting self-bounding inequality gives a
first-order bound in the empirical risk and PAC-Bayes complexity.

For the fixed sample-level tilt `lambda = 2n/3`, outside the existing
indicator-Bernstein exceptional set every posterior satisfies

`R_rho <= (7/4) * Rhat_rho + (21/(8n)) * (KL(rho||pi) + log(1/delta))`.

This is a finite, i.i.d., fixed-sample, fixed-tilt corollary using population
Bernoulli variance and the self-bounding inequality above.  It is not an
empirical-Bernstein theorem: no sample-variance estimator appears on the
right-hand side.

All declarations are fully proved with no `sorry`, `admit`, custom axiom, or
custom constant.
-/

namespace FormalSLT.PACBayes.IndicatorBernsteinLowRisk

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.IndicatorVariance
open FormalSLT.PACBayes.IndicatorBernsteinMoment
open FormalSLT.PACBayes.IndicatorBernsteinConfidence

noncomputable section

variable {ι Z : Type*}

/-- The exact indicator variance proxy is at most population risk divided by
the positive sample size. -/
theorem indicatorBernsteinVarianceProxy_le_risk_div
    [Fintype Z] {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (bad : ι → Z → Bool) (i : ι) :
    indicatorBernsteinVarianceProxy n p bad i ≤
      indicatorPopulationRisk p bad i / (n : ℝ) := by
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  unfold indicatorBernsteinVarianceProxy
  apply (div_le_div_iff_of_pos_right hn_real).2
  nlinarith [sq_nonneg (indicatorPopulationRisk p bad i)]

/-- Averaging the pointwise self-bound under a posterior PMF gives
`V_rho <= R_rho / n`. -/
theorem posteriorIndicatorBernsteinVarianceProxy_le_risk_div
    [Fintype ι] [Fintype Z] {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (bad : ι → Z → Bool)
    (ρ : ι → ℝ) (hρ : IsPMF ρ) :
    posteriorMarginVarianceProxy ρ
        (indicatorBernsteinVarianceProxy n p bad) ≤
      posteriorRisk ρ (indicatorPopulationRisk p bad) / (n : ℝ) := by
  unfold posteriorMarginVarianceProxy posteriorRisk posteriorAverage
  calc
    (∑ i : ι, ρ i * indicatorBernsteinVarianceProxy n p bad i) ≤
        ∑ i : ι, ρ i * (indicatorPopulationRisk p bad i / (n : ℝ)) := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left
          (indicatorBernsteinVarianceProxy_le_risk_div hn p bad i)
          (hρ.nonneg i)
    _ = (∑ i : ι, ρ i * indicatorPopulationRisk p bad i) / (n : ℝ) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring

/-- A posterior average of indicator population risks is at most one. -/
theorem posteriorIndicatorPopulationRisk_le_one
    [Fintype ι] [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p) (bad : ι → Z → Bool)
    (ρ : ι → ℝ) (hρ : IsPMF ρ) :
    posteriorRisk ρ (indicatorPopulationRisk p bad) ≤ 1 := by
  unfold posteriorRisk posteriorAverage
  calc
    (∑ i : ι, ρ i * indicatorPopulationRisk p bad i) ≤
        ∑ i : ι, ρ i * 1 := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left
          (indicatorPopulationRisk_le_one p hp bad i) (hρ.nonneg i)
    _ = 1 := by simp [hρ.sum_one]

/-- Algebraic rearrangement of the low-risk Bernstein inequality.  The
restriction `lambda < 6n/5` is exactly what makes the coefficient of the
population risk strictly smaller than one. -/
private theorem selfBoundingBernstein_rearrange
    {n : ℕ} (hn : 0 < n)
    {R Rhat C lambda : ℝ}
    (hlambda : 0 < lambda)
    (hlambda_lt : lambda < 6 * (n : ℝ) / 5)
    (hbound :
      R - Rhat ≤ C / lambda +
        lambda * (R / (n : ℝ)) /
          (2 * (1 - (1 / (3 * (n : ℝ))) * lambda))) :
    R ≤
      (6 * (n : ℝ) - 2 * lambda) /
          (6 * (n : ℝ) - 5 * lambda) * Rhat +
        (6 * (n : ℝ) - 2 * lambda) /
          (lambda * (6 * (n : ℝ) - 5 * lambda)) * C := by
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have hlambda_three : lambda < 3 * (n : ℝ) := by
    nlinarith [hlambda_lt]
  have hden_pos : 0 < 6 * (n : ℝ) - 2 * lambda := by
    nlinarith
  have hthree_pos : 0 < 3 * (n : ℝ) - lambda := by
    nlinarith
  have hrearrange_pos : 0 < 6 * (n : ℝ) - 5 * lambda := by
    nlinarith [hlambda_lt]
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_real
  have hlambda_ne : lambda ≠ 0 := ne_of_gt hlambda
  have hden_ne : 6 * (n : ℝ) - 2 * lambda ≠ 0 := ne_of_gt hden_pos
  have hthree_ne : 3 * (n : ℝ) - lambda ≠ 0 := ne_of_gt hthree_pos
  have hden_ne' : (n : ℝ) * 6 - lambda * 2 ≠ 0 := by nlinarith
  have hthree_ne' : (n : ℝ) * 3 - lambda ≠ 0 := by nlinarith
  have hrearrange_ne : 6 * (n : ℝ) - 5 * lambda ≠ 0 :=
    ne_of_gt hrearrange_pos
  have hcoefficient :
      lambda * (R / (n : ℝ)) /
          (2 * (1 - (1 / (3 * (n : ℝ))) * lambda)) =
        (3 * lambda / (6 * (n : ℝ) - 2 * lambda)) * R := by
    field_simp [hn_ne, hden_ne, hthree_ne, hden_ne', hthree_ne']
    ring
  rw [hcoefficient] at hbound
  have hlinear :
      (1 - 3 * lambda / (6 * (n : ℝ) - 2 * lambda)) * R ≤
        Rhat + C / lambda := by
    linarith
  have hratio :
      1 - 3 * lambda / (6 * (n : ℝ) - 2 * lambda) =
        (6 * (n : ℝ) - 5 * lambda) /
          (6 * (n : ℝ) - 2 * lambda) := by
    calc
      1 - 3 * lambda / (6 * (n : ℝ) - 2 * lambda) =
          (6 * (n : ℝ) - 2 * lambda) /
              (6 * (n : ℝ) - 2 * lambda) -
            3 * lambda / (6 * (n : ℝ) - 2 * lambda) := by
        rw [div_self hden_ne]
      _ = ((6 * (n : ℝ) - 2 * lambda) - 3 * lambda) /
          (6 * (n : ℝ) - 2 * lambda) := by
        rw [div_sub_div_same]
      _ = (6 * (n : ℝ) - 5 * lambda) /
          (6 * (n : ℝ) - 2 * lambda) := by ring
  rw [hratio] at hlinear
  have hlinear' :
      ((6 * (n : ℝ) - 5 * lambda) * R) /
          (6 * (n : ℝ) - 2 * lambda) ≤
        Rhat + C / lambda := by
    convert hlinear using 1
    all_goals ring
  have hcleared₀ := (div_le_iff₀ hden_pos).1 hlinear'
  have hcleared :
      (6 * (n : ℝ) - 5 * lambda) * R ≤
        (6 * (n : ℝ) - 2 * lambda) * Rhat +
          (6 * (n : ℝ) - 2 * lambda) / lambda * C := by
    calc
      (6 * (n : ℝ) - 5 * lambda) * R ≤
          (Rhat + C / lambda) * (6 * (n : ℝ) - 2 * lambda) := hcleared₀
      _ = (6 * (n : ℝ) - 2 * lambda) * Rhat +
          (6 * (n : ℝ) - 2 * lambda) / lambda * C := by ring
  have htarget :
      (6 * (n : ℝ) - 2 * lambda) /
            (6 * (n : ℝ) - 5 * lambda) * Rhat +
          (6 * (n : ℝ) - 2 * lambda) /
            (lambda * (6 * (n : ℝ) - 5 * lambda)) * C =
        ((6 * (n : ℝ) - 2 * lambda) * Rhat +
            (6 * (n : ℝ) - 2 * lambda) / lambda * C) /
          (6 * (n : ℝ) - 5 * lambda) := by
    field_simp [hlambda_ne, hrearrange_ne]
  rw [htarget]
  apply (le_div_iff₀ hrearrange_pos).2
  nlinarith [hcleared]

/-- General observable low-risk corollary outside the existing fixed-tilt
indicator-Bernstein exceptional set. -/
theorem indicator_posteriorRisk_le_lowRisk_of_not_mem
    [Fintype ι] [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (π : ι → ℝ) (bad : ι → Z → Bool)
    (lambda delta : ℝ)
    (hlambda : 0 < lambda)
    (hlambda_lt : lambda < 6 * (n : ℝ) / 5)
    (S : Fin n → Z)
    (hS : S ∉ indicatorFinitePACBayesBernsteinBadSamples
      n p π bad lambda delta)
    (ρ : ι → ℝ) (hρ : IsPMF ρ) :
    posteriorRisk ρ (indicatorPopulationRisk p bad) ≤
      (6 * (n : ℝ) - 2 * lambda) /
          (6 * (n : ℝ) - 5 * lambda) *
        posteriorEmpiricalRisk ρ
          (fun i => finiteEmpiricalRisk (indicatorLoss bad) i S) +
      (6 * (n : ℝ) - 2 * lambda) /
          (lambda * (6 * (n : ℝ) - 5 * lambda)) *
        (klDiv ρ π + Real.log (1 / delta)) := by
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have hlambda_three : lambda < 3 * (n : ℝ) := by
    nlinarith [hlambda_lt]
  have hscale_pos :
      0 < 2 * (1 - indicatorBernsteinScale n * lambda) := by
    unfold indicatorBernsteinScale
    rw [one_div_mul_eq_div]
    have : lambda / (3 * (n : ℝ)) < 1 := by
      rw [div_lt_one (by positivity)]
      exact hlambda_three
    positivity
  have hvariance :=
    posteriorIndicatorBernsteinVarianceProxy_le_risk_div
      hn p bad ρ hρ
  have hvariance_term :
      lambda * posteriorMarginVarianceProxy ρ
            (indicatorBernsteinVarianceProxy n p bad) /
          (2 * (1 - indicatorBernsteinScale n * lambda)) ≤
        lambda *
            (posteriorRisk ρ (indicatorPopulationRisk p bad) / (n : ℝ)) /
          (2 * (1 - indicatorBernsteinScale n * lambda)) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hvariance (le_of_lt hlambda))
      (le_of_lt hscale_pos)
  have hgap := indicator_posteriorGeneralizationGap_le_of_not_mem
    n p π bad lambda delta S hS ρ hρ
  unfold posteriorGeneralizationGap at hgap
  apply selfBoundingBernstein_rearrange hn hlambda hlambda_lt
  unfold indicatorBernsteinScale at hgap hvariance_term
  linarith

/-- At the clean fixed tilt `lambda = 2n/3`, the observable low-risk bound has
coefficients `7/4` and `21/(8n)`. -/
theorem indicator_posteriorRisk_le_twoThirds_of_not_mem
    [Fintype ι] [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (π : ι → ℝ) (bad : ι → Z → Bool)
    (delta : ℝ) (S : Fin n → Z)
    (hS : S ∉ indicatorFinitePACBayesBernsteinBadSamples
      n p π bad (2 * (n : ℝ) / 3) delta)
    (ρ : ι → ℝ) (hρ : IsPMF ρ) :
    posteriorRisk ρ (indicatorPopulationRisk p bad) ≤
      (7 / 4 : ℝ) *
          posteriorEmpiricalRisk ρ
            (fun i => finiteEmpiricalRisk (indicatorLoss bad) i S) +
        21 / (8 * (n : ℝ)) *
          (klDiv ρ π + Real.log (1 / delta)) := by
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have h := indicator_posteriorRisk_le_lowRisk_of_not_mem
    hn p π bad (2 * (n : ℝ) / 3) delta
    (by positivity) (by nlinarith) S hS ρ hρ
  convert h using 1
  all_goals field_simp
  all_goals ring

/-- Public certificate form: truncate the observable low-risk bound by the
universal upper bound one for posterior indicator risk. -/
theorem indicator_posteriorRisk_le_min_one_twoThirds_of_not_mem
    [Fintype ι] [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (π : ι → ℝ) (bad : ι → Z → Bool)
    (delta : ℝ) (S : Fin n → Z)
    (hS : S ∉ indicatorFinitePACBayesBernsteinBadSamples
      n p π bad (2 * (n : ℝ) / 3) delta)
    (ρ : ι → ℝ) (hρ : IsPMF ρ) :
    posteriorRisk ρ (indicatorPopulationRisk p bad) ≤
      min 1
        ((7 / 4 : ℝ) *
            posteriorEmpiricalRisk ρ
              (fun i => finiteEmpiricalRisk (indicatorLoss bad) i S) +
          21 / (8 * (n : ℝ)) *
            (klDiv ρ π + Real.log (1 / delta))) := by
  exact le_min
    (posteriorIndicatorPopulationRisk_le_one p hp bad ρ hρ)
    (indicator_posteriorRisk_le_twoThirds_of_not_mem
      hn p π bad delta S hS ρ hρ)

/-- The existing indicator-Bernstein exceptional set at `lambda = 2n/3` has
product-law mass at most `delta`.  Together with the two theorems above this is
the finite high-confidence observable low-risk certificate. -/
theorem indicator_finitePACBayesBernstein_twoThirds_badEventMass_le_delta
    [Fintype ι] [Nonempty ι] [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    {π : ι → ℝ} (hπ : IsFullSupportPMF π)
    (bad : ι → Z → Bool)
    (delta : ℝ) (hdelta : 0 < delta) :
    (∑ S ∈ indicatorFinitePACBayesBernsteinBadSamples
        n p π bad (2 * (n : ℝ) / 3) delta,
        finiteProductSampleWeight p S) ≤ delta := by
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  exact indicator_finitePACBayesBernstein_fixedLambda_badEventMass_le_delta
    hn p hp hπ bad (2 * (n : ℝ) / 3) delta
    (by positivity) (by nlinarith) hdelta

end

end FormalSLT.PACBayes.IndicatorBernsteinLowRisk
