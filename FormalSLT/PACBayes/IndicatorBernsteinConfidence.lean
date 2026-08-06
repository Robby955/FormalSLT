/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.IndicatorBernsteinMoment

/-!
# Finite PAC-Bayes Bernstein confidence bounds for indicator losses

This module closes the finite indicator-loss Bernstein chain.  It combines the
exact variance identity, the finite-product MGF, the prior-averaged normalized
moment, and the finite PAC-Bayes change-of-measure adapter.

For a finite hypothesis class and a full-support prior, the main theorem bounds
the product-law mass of samples on which some posterior violates the explicit
fixed-tilt Bernstein inequality.  Thus the bound holds simultaneously for all
finite posteriors outside a bad set of mass at most `delta`.

The result is finite, i.i.d., fixed-sample, fixed-tilt, and uses population
Bernoulli variance `R_i * (1 - R_i) / n`.  It is not empirical Bernstein,
continuous-hypothesis, time-uniform, or optimized over the tilt.

Mathematical sources: Boucheron, Lugosi, and Massart (2013), *Concentration
Inequalities*, for the Bernstein MGF route; Donsker and Varadhan (1975) for the
change-of-measure principle; and Tolstikhin and Seldin (2013),
"PAC-Bayes-Empirical-Bernstein Inequality," for the variance-sensitive
PAC-Bayes context.
-/

namespace FormalSLT.PACBayes.IndicatorBernsteinConfidence

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.IndicatorVariance
open FormalSLT.PACBayes.FiniteProductBernstein
open FormalSLT.PACBayes.IndicatorBernsteinMoment

noncomputable section

variable {ι Z : Type*}

/--
Samples on which some finite posterior violates the indicator-specialized
fixed-tilt PAC-Bayes Bernstein inequality.
-/
def indicatorFinitePACBayesBernsteinBadSamples
    [Fintype ι] [Fintype Z]
    (n : ℕ) (p : Z → ℝ) (π : ι → ℝ)
    (bad : ι → Z → Bool) (lambda delta : ℝ) : Finset (Fin n → Z) :=
  finitePACBayesBernsteinFixedLambdaBadSamples π lambda
    (indicatorBernsteinScale n) delta
    (indicatorPopulationRisk p bad)
    (fun S i => finiteEmpiricalRisk (indicatorLoss bad) i S)
    (indicatorBernsteinVarianceProxy n p bad)

/--
Outside the specialized bad-sample set, every finite posterior satisfies the
explicit indicator PAC-Bayes Bernstein inequality.
-/
theorem indicator_posteriorGeneralizationGap_le_of_not_mem
    [Fintype ι] [Fintype Z]
    (n : ℕ) (p : Z → ℝ) (π : ι → ℝ)
    (bad : ι → Z → Bool) (lambda delta : ℝ)
    (S : Fin n → Z)
    (hS : S ∉ indicatorFinitePACBayesBernsteinBadSamples
      n p π bad lambda delta)
    (ρ : ι → ℝ) (hρ : IsPMF ρ) :
    posteriorGeneralizationGap ρ
        (indicatorPopulationRisk p bad)
        (fun i => finiteEmpiricalRisk (indicatorLoss bad) i S) ≤
      (klDiv ρ π + Real.log (1 / delta)) / lambda +
        lambda * posteriorMarginVarianceProxy ρ
          (indicatorBernsteinVarianceProxy n p bad) /
            (2 * (1 - indicatorBernsteinScale n * lambda)) := by
  classical
  by_contra hbound
  apply hS
  simp only [indicatorFinitePACBayesBernsteinBadSamples,
    finitePACBayesBernsteinFixedLambdaBadSamples, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨ρ, hρ, lt_of_not_ge hbound⟩

/--
Finite i.i.d. PAC-Bayes Bernstein confidence theorem for indicator losses.

Under a finite data PMF and full-support finite prior, the product-law mass of
samples on which any posterior violates the fixed-`lambda` Bernstein bound is
at most `delta`.  The scale is `1/(3n)` and the per-hypothesis variance proxy is
the exact Bernoulli quantity `R_i * (1 - R_i) / n`.
-/
theorem indicator_finitePACBayesBernstein_fixedLambda_badEventMass_le_delta
    [Fintype ι] [Nonempty ι] [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    {π : ι → ℝ} (hπ : IsFullSupportPMF π)
    (bad : ι → Z → Bool)
    (lambda delta : ℝ)
    (hlambda : 0 < lambda)
    (hlambda_lt : lambda < 3 * (n : ℝ))
    (hdelta : 0 < delta) :
    (∑ S ∈ indicatorFinitePACBayesBernsteinBadSamples
        n p π bad lambda delta,
        finiteProductSampleWeight p S) ≤ delta := by
  classical
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale : indicatorBernsteinScale n * lambda < 1 := by
    unfold indicatorBernsteinScale
    rw [one_div_mul_eq_div, div_lt_one (by positivity)]
    exact hlambda_lt
  exact finitePACBayesBernstein_fixedLambda_badEventMass_le_delta
    (finiteProductSampleWeight_isPMF hp) hπ
    lambda (indicatorBernsteinScale n) delta
    hlambda hscale hdelta
    (indicatorPopulationRisk p bad)
    (fun (S : Fin n → Z) i => finiteEmpiricalRisk (indicatorLoss bad) i S)
    (indicatorBernsteinVarianceProxy n p bad)
    (indicator_expectedPriorBernsteinExpMoment_le_one
      hn p hp π hπ.toIsPMF bad hlambda hlambda_lt)

end

end FormalSLT.PACBayes.IndicatorBernsteinConfidence
