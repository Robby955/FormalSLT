/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteEmpiricalVariancePACBayes
import FormalSLT.Probability.FiniteUnionBound

/-!
# Finite weighted tilt catalogs for empirical-variance PAC-Bayes bounds

This module makes a fixed finite family of empirical-variance tilts
simultaneously valid.  Each catalog entry `j` receives confidence budget
`delta * weight j`.  A finite weighted union bound then controls the union of
the entrywise exceptional sets by `delta` whenever the positive weights sum to
at most one.

Outside that single exceptional set, every posterior satisfies every catalog
bound.  Consequently a selector may choose the tilt after seeing both the
sample and the posterior.  The catalog, the weights, and the selector rule are
declared before the sample; this is not unrestricted optimization over a
real-valued tilt.

## Scope and non-claims

- This is a finite union bound over a catalog fixed in advance.  It is not a
  master e-process and not a mixture argument.
- It does not optimize over all real tilts.  Only the finitely many `eta j`
  named by the catalog are covered.
- It is fixed-sample.  There is no time-uniform or anytime-valid claim here.
- The rearranged endpoint keeps the explicit admissibility condition
  `eta j * n < 2 * (n - 1)`, which is what keeps the denominator positive.
- The bounded quantity is a variance, not a risk.  Both `posteriorAverage rho
  (finitePopulationVariance p ell)` and its empirical counterpart are posterior
  averages of per-hypothesis variances, taken after each hypothesis's variance
  is computed.  Neither is the variance of the posterior-averaged loss, and
  neither is a final risk bound.

The only new probability composition is the finite weighted union bound:
entrywise control comes from
`finiteEmpiricalVariancePACBayes_badEventMass_le_delta`, and
`finiteWeightedUnionBound_sum_le_of_exists_mem` combines those fixed events.
This module does not introduce a new MGF argument.

No `sorry`, no `admit`, no custom axioms.
-/

namespace FormalSLT.PACBayes.FiniteEmpiricalVarianceTiltCatalog

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariancePACBayes
open FormalSLT.PACBayes.FiniteProductBernstein
open FormalSLT.Probability.FiniteUnionBound

noncomputable section

variable {κ ι Z : Type*}

/-- The union of the fixed-tilt empirical-variance bad-sample sets obtained by
assigning entry `j` the confidence budget `delta * weight j`. -/
def finiteEmpiricalVarianceWeightedCatalogBadSamples
    [Fintype κ] [Fintype Z] [Fintype ι]
    (n : ℕ) (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (eta weight : κ → ℝ) (delta : ℝ) : Finset (Fin n → Z) := by
  classical
  exact (Finset.univ : Finset κ).biUnion fun j =>
    finiteEmpiricalVariancePACBayesBadSamples
      n p prior ell (eta j) (delta * weight j)

/-- Membership in the catalog event is exactly membership in at least one
entrywise exceptional set. -/
theorem finiteEmpiricalVariance_mem_weightedCatalog_iff
    [Fintype κ] [Fintype Z] [Fintype ι]
    (n : ℕ) (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (eta weight : κ → ℝ) (delta : ℝ) (S : Fin n → Z) :
    S ∈ finiteEmpiricalVarianceWeightedCatalogBadSamples
        n p prior ell eta weight delta ↔
      ∃ j, S ∈ finiteEmpiricalVariancePACBayesBadSamples
        n p prior ell (eta j) (delta * weight j) := by
  classical
  simp [finiteEmpiricalVarianceWeightedCatalogBadSamples]

/-- A sample is outside the catalog event exactly when it is outside every
entrywise exceptional set. -/
theorem finiteEmpiricalVariance_not_mem_weightedCatalog_iff
    [Fintype κ] [Fintype Z] [Fintype ι]
    (n : ℕ) (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (eta weight : κ → ℝ) (delta : ℝ) (S : Fin n → Z) :
    S ∉ finiteEmpiricalVarianceWeightedCatalogBadSamples
        n p prior ell eta weight delta ↔
      ∀ j, S ∉ finiteEmpiricalVariancePACBayesBadSamples
        n p prior ell (eta j) (delta * weight j) := by
  constructor
  · intro hcatalog j hentry
    exact hcatalog
      ((finiteEmpiricalVariance_mem_weightedCatalog_iff
        n p prior ell eta weight delta S).2 ⟨j, hentry⟩)
  · intro hentry hcatalog
    rcases (finiteEmpiricalVariance_mem_weightedCatalog_iff
      n p prior ell eta weight delta S).1 hcatalog with ⟨j, hj⟩
    exact hentry j hj

/-- Every entrywise bad-sample set is contained in the weighted catalog's
single exceptional set. -/
theorem finiteEmpiricalVarianceFixedTiltBadSamples_subset_weightedCatalog
    [Fintype κ] [Fintype Z] [Fintype ι]
    (n : ℕ) (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (eta weight : κ → ℝ) (delta : ℝ) (j : κ) :
    finiteEmpiricalVariancePACBayesBadSamples
        n p prior ell (eta j) (delta * weight j) ⊆
      finiteEmpiricalVarianceWeightedCatalogBadSamples
        n p prior ell eta weight delta := by
  classical
  intro S hS
  unfold finiteEmpiricalVarianceWeightedCatalogBadSamples
  rw [Finset.mem_biUnion]
  exact ⟨j, Finset.mem_univ j, hS⟩

/--
The weighted catalog exceptional set has product-law mass at most `delta`.

Each entry has mass at most `delta * weight j` by the fixed-tilt confidence
theorem.  The finite weighted union bound and `sum_j weight j <= 1` complete
the calculation.  As in the parent fixed-tilt mass theorem, the formal
assumption is only `0 < delta`; applications use `delta < 1` when interpreting
`1 - delta` as a nontrivial confidence level.
-/
theorem finiteEmpiricalVariance_weightedCatalog_badEventMass_le_delta
    [Fintype κ] [Fintype Z] [DecidableEq Z] [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    (eta weight : κ → ℝ) (delta : ℝ)
    (heta : ∀ j, 0 < eta j)
    (hweight : ∀ j, 0 < weight j)
    (hweight_sum : ∑ j, weight j ≤ 1)
    (hdelta : 0 < delta) :
    (∑ S ∈ finiteEmpiricalVarianceWeightedCatalogBadSamples
        n p prior ell eta weight delta,
        finiteProductSampleWeight p S) ≤ delta := by
  classical
  have hUnion :
      (∑ S ∈ finiteEmpiricalVarianceWeightedCatalogBadSamples
          n p prior ell eta weight delta,
          finiteProductSampleWeight p S) ≤
        ∑ j : κ, ∑ S ∈ finiteEmpiricalVariancePACBayesBadSamples
            n p prior ell (eta j) (delta * weight j),
            finiteProductSampleWeight p S := by
    refine finiteWeightedUnionBound_sum_le_of_exists_mem _ _ _
      (finiteProductSampleWeight_isPMF hp).nonneg ?_
    intro S hS
    exact (finiteEmpiricalVariance_mem_weightedCatalog_iff
      n p prior ell eta weight delta S).1 hS
  have hentry : ∀ j : κ,
      (∑ S ∈ finiteEmpiricalVariancePACBayesBadSamples
          n p prior ell (eta j) (delta * weight j),
          finiteProductSampleWeight p S) ≤ delta * weight j := fun j =>
    finiteEmpiricalVariancePACBayes_badEventMass_le_delta
      hn p hp hprior ell hell (heta j) (mul_pos hdelta (hweight j))
  have hbudget : (∑ j : κ, delta * weight j) ≤ delta := by
    calc
      (∑ j : κ, delta * weight j) = delta * ∑ j, weight j := by
        rw [Finset.mul_sum]
      _ ≤ delta * 1 := mul_le_mul_of_nonneg_left hweight_sum (le_of_lt hdelta)
      _ = delta := by ring
  exact hUnion.trans
    ((Finset.sum_le_sum fun j _ => hentry j).trans hbudget)

/-- Outside the weighted catalog event, the unrearranged variance gap bound
holds simultaneously for every catalog entry and every posterior. -/
theorem finiteEmpiricalVariance_posteriorGap_le_weightedCatalog_of_not_mem
    [Fintype κ] [Fintype Z] [Fintype ι]
    (n : ℕ) (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (eta weight : κ → ℝ) (delta : ℝ)
    (S : Fin n → Z)
    (hS : S ∉ finiteEmpiricalVarianceWeightedCatalogBadSamples
      n p prior ell eta weight delta)
    (j : κ) (rho : ι → ℝ) (hrho : IsPMF rho) :
    posteriorGeneralizationGap rho
        (finitePopulationVariance p ell)
        (fun i => finiteEmpiricalVariance ell i S) ≤
      (klDiv rho prior + Real.log (1 / (delta * weight j))) / (eta j * (n : ℝ)) +
        (eta j * (n : ℝ)) * posteriorMarginVarianceProxy rho
          (fun i => finitePopulationVariance p ell i / ((n : ℝ) - 1)) / 2 := by
  exact finiteEmpiricalVariance_posteriorGap_le_of_not_mem
    n p prior ell (eta j) (delta * weight j) S
      (by
        intro hbad
        exact hS
          (finiteEmpiricalVarianceFixedTiltBadSamples_subset_weightedCatalog
            n p prior ell eta weight delta j hbad))
      rho hrho

/-- Outside the weighted catalog event, the rearranged posterior
population-variance bound holds for every catalog entry and every posterior.

The admissibility condition `eta j * n < 2 * (n - 1)` is stated per entry, so a
catalog may mix tilts as long as each one keeps the denominator positive. -/
theorem posteriorPopulationVariance_le_empiricalVariance_weightedCatalog_of_not_mem
    [Fintype κ] [Fintype Z] [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (eta weight : κ → ℝ) (delta : ℝ)
    (heta : ∀ j, 0 < eta j)
    (heta_upper : ∀ j, eta j * (n : ℝ) < 2 * ((n : ℝ) - 1))
    (S : Fin n → Z)
    (hS : S ∉ finiteEmpiricalVarianceWeightedCatalogBadSamples
      n p prior ell eta weight delta)
    (j : κ) (rho : ι → ℝ) (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationVariance p ell) ≤
      (posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) +
          (klDiv rho prior + Real.log (1 / (delta * weight j))) /
            (eta j * (n : ℝ))) /
        (1 - eta j * (n : ℝ) / (2 * ((n : ℝ) - 1))) := by
  exact posteriorPopulationVariance_le_empiricalVariance_of_not_mem
    hn p prior ell (heta j) (heta_upper j) S
      (by
        intro hbad
        exact hS
          (finiteEmpiricalVarianceFixedTiltBadSamples_subset_weightedCatalog
            n p prior ell eta weight delta j hbad))
      rho hrho

/-- A catalog selector may depend on both the observed sample and the
posterior, because the good event is simultaneous in the catalog entry and the
posterior. -/
theorem posteriorPopulationVariance_le_empiricalVariance_weightedCatalog_selected_of_not_mem
    [Fintype κ] [Fintype Z] [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (eta weight : κ → ℝ) (delta : ℝ)
    (heta : ∀ j, 0 < eta j)
    (heta_upper : ∀ j, eta j * (n : ℝ) < 2 * ((n : ℝ) - 1))
    (select : (Fin n → Z) → (ι → ℝ) → κ)
    (S : Fin n → Z)
    (hS : S ∉ finiteEmpiricalVarianceWeightedCatalogBadSamples
      n p prior ell eta weight delta)
    (rho : ι → ℝ) (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationVariance p ell) ≤
      (posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) +
          (klDiv rho prior +
              Real.log (1 / (delta * weight (select S rho)))) /
            (eta (select S rho) * (n : ℝ))) /
        (1 - eta (select S rho) * (n : ℝ) / (2 * ((n : ℝ) - 1))) := by
  exact posteriorPopulationVariance_le_empiricalVariance_weightedCatalog_of_not_mem
    hn p prior ell eta weight delta heta heta_upper S hS (select S rho) rho hrho

end

end FormalSLT.PACBayes.FiniteEmpiricalVarianceTiltCatalog
