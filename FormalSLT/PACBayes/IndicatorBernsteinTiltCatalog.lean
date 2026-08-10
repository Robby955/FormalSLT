/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.IndicatorBernsteinLowRisk
import FormalSLT.Probability.FiniteUnionBound

/-!
# Finite weighted tilt catalogs for indicator PAC-Bayes--Bernstein bounds

This module makes a fixed finite family of indicator-Bernstein tilts
simultaneously valid.  Each catalog entry `j` receives confidence budget
`delta * weight j`.  A finite weighted union bound then controls the union of
the entrywise exceptional sets by `delta` whenever the positive weights sum to
at most one.

Outside that single exceptional set, every posterior satisfies every catalog
bound.  Consequently, a selector may choose the tilt after seeing both the
sample and the posterior.  The catalog, weights, and selector rule are fixed
in advance; this is not unrestricted optimization over a real-valued tilt.

The variance term remains the exact Bernoulli population variance.  The
observable theorem reuses the self-bounding inequality `R * (1 - R) <= R`; it
is not an empirical-Bernstein theorem.

The only new probability composition is the finite weighted union bound:
entrywise control comes from
`indicator_finitePACBayesBernstein_fixedLambda_badEventMass_le_delta`, and
`finiteProbabilityUnionBound_proof` combines those fixed events.  This module
does not introduce a new MGF argument.
-/

namespace FormalSLT.PACBayes.IndicatorBernsteinTiltCatalog

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.IndicatorVariance
open FormalSLT.PACBayes.FiniteProductBernstein
open FormalSLT.PACBayes.IndicatorBernsteinMoment
open FormalSLT.PACBayes.IndicatorBernsteinConfidence
open FormalSLT.PACBayes.IndicatorBernsteinLowRisk
open FormalSLT.Probability.FiniteUnionBound

noncomputable section

variable {κ ι Z : Type*}

/-- The union of the indicator-Bernstein bad-sample sets obtained by assigning
entry `j` the confidence budget `delta * weight j`. -/
def indicatorFinitePACBayesBernsteinWeightedCatalogBadSamples
    [Fintype κ] [Fintype ι] [Fintype Z]
    (n : ℕ) (p : Z → ℝ) (π : ι → ℝ)
    (bad : ι → Z → Bool)
    (lambda weight : κ → ℝ) (delta : ℝ) : Finset (Fin n → Z) := by
  classical
  exact (Finset.univ : Finset κ).biUnion fun j =>
    indicatorFinitePACBayesBernsteinBadSamples
      n p π bad (lambda j) (delta * weight j)

/-- Membership in the catalog event is exactly membership in at least one
entrywise exceptional set. -/
theorem indicator_mem_weightedCatalog_iff
    [Fintype κ] [Fintype ι] [Fintype Z]
    (n : ℕ) (p : Z → ℝ) (π : ι → ℝ)
    (bad : ι → Z → Bool)
    (lambda weight : κ → ℝ) (delta : ℝ) (S : Fin n → Z) :
    S ∈ indicatorFinitePACBayesBernsteinWeightedCatalogBadSamples
        n p π bad lambda weight delta ↔
      ∃ j, S ∈ indicatorFinitePACBayesBernsteinBadSamples
        n p π bad (lambda j) (delta * weight j) := by
  classical
  simp [indicatorFinitePACBayesBernsteinWeightedCatalogBadSamples]

/-- A sample is outside the catalog event exactly when it is outside every
entrywise exceptional set. -/
theorem indicator_not_mem_weightedCatalog_iff
    [Fintype κ] [Fintype ι] [Fintype Z]
    (n : ℕ) (p : Z → ℝ) (π : ι → ℝ)
    (bad : ι → Z → Bool)
    (lambda weight : κ → ℝ) (delta : ℝ) (S : Fin n → Z) :
    S ∉ indicatorFinitePACBayesBernsteinWeightedCatalogBadSamples
        n p π bad lambda weight delta ↔
      ∀ j, S ∉ indicatorFinitePACBayesBernsteinBadSamples
        n p π bad (lambda j) (delta * weight j) := by
  constructor
  · intro hcatalog j hentry
    apply hcatalog
    exact (indicator_mem_weightedCatalog_iff
      n p π bad lambda weight delta S).2 ⟨j, hentry⟩
  · intro hentry hcatalog
    rcases (indicator_mem_weightedCatalog_iff
      n p π bad lambda weight delta S).1 hcatalog with ⟨j, hj⟩
    exact hentry j hj

/-- Every entrywise bad-sample set is contained in the weighted catalog's
single exceptional set. -/
theorem indicatorFixedTiltBadSamples_subset_weightedCatalog
    [Fintype κ] [Fintype ι] [Fintype Z]
    (n : ℕ) (p : Z → ℝ) (π : ι → ℝ)
    (bad : ι → Z → Bool)
    (lambda weight : κ → ℝ) (delta : ℝ) (j : κ) :
    indicatorFinitePACBayesBernsteinBadSamples
        n p π bad (lambda j) (delta * weight j) ⊆
      indicatorFinitePACBayesBernsteinWeightedCatalogBadSamples
        n p π bad lambda weight delta := by
  classical
  intro S hS
  unfold indicatorFinitePACBayesBernsteinWeightedCatalogBadSamples
  rw [Finset.mem_biUnion]
  exact ⟨j, Finset.mem_univ j, hS⟩

/-- Outside the weighted catalog event, the fixed-tilt indicator-Bernstein gap
bound holds simultaneously for every catalog entry and every posterior. -/
theorem indicator_posteriorGeneralizationGap_le_weightedCatalog_of_not_mem
    [Fintype κ] [Fintype ι] [Fintype Z]
    (n : ℕ) (p : Z → ℝ) (π : ι → ℝ)
    (bad : ι → Z → Bool)
    (lambda weight : κ → ℝ) (delta : ℝ)
    (S : Fin n → Z)
    (hS : S ∉ indicatorFinitePACBayesBernsteinWeightedCatalogBadSamples
      n p π bad lambda weight delta)
    (j : κ) (ρ : ι → ℝ) (hρ : IsPMF ρ) :
    posteriorGeneralizationGap ρ
        (indicatorPopulationRisk p bad)
        (fun i => finiteEmpiricalRisk (indicatorLoss bad) i S) ≤
      (klDiv ρ π + Real.log (1 / (delta * weight j))) / lambda j +
        lambda j * posteriorMarginVarianceProxy ρ
          (indicatorBernsteinVarianceProxy n p bad) /
            (2 * (1 - indicatorBernsteinScale n * lambda j)) := by
  exact indicator_posteriorGeneralizationGap_le_of_not_mem
    n p π bad (lambda j) (delta * weight j) S
      (by
        intro hbad
        exact hS
          (indicatorFixedTiltBadSamples_subset_weightedCatalog
            n p π bad lambda weight delta j hbad))
      ρ hρ

private lemma finiteEventMass_univ_eq_sum
    [Fintype Z] [DecidableEq Z]
    (ν : Z → ℝ) (event : Finset Z) :
    finiteEventMass (Finset.univ : Finset Z) ν event =
      ∑ z ∈ event, ν z := by
  classical
  unfold finiteEventMass
  rw [← Finset.sum_filter]
  simp

/--
The weighted catalog exceptional set has product-law mass at most `delta`.

Each entry has mass at most `delta * weight j` by the fixed-tilt confidence
theorem.  The finite weighted union bound and `sum_j weight j <= 1` complete
the calculation.  As in the parent low-level mass theorem, the formal
assumption is only `0 < delta`; applications use `delta < 1` when interpreting
`1 - delta` as a nontrivial confidence level.
-/
theorem indicator_finitePACBayesBernstein_weightedCatalog_badEventMass_le_delta
    [Fintype κ] [Fintype ι] [Nonempty ι] [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    {π : ι → ℝ} (hπ : IsFullSupportPMF π)
    (bad : ι → Z → Bool)
    (lambda weight : κ → ℝ) (delta : ℝ)
    (hlambda : ∀ j, 0 < lambda j)
    (hlambda_lt : ∀ j, lambda j < 3 * (n : ℝ))
    (hweight : ∀ j, 0 < weight j)
    (hweight_sum : ∑ j, weight j ≤ 1)
    (hdelta : 0 < delta) :
    (∑ S ∈ indicatorFinitePACBayesBernsteinWeightedCatalogBadSamples
        n p π bad lambda weight delta,
        finiteProductSampleWeight p S) ≤ delta := by
  classical
  let events : κ → Finset (Fin n → Z) := fun j =>
    indicatorFinitePACBayesBernsteinBadSamples
      n p π bad (lambda j) (delta * weight j)
  have hUnion :
      finiteUnionEventMass (Finset.univ : Finset (Fin n → Z))
          (finiteProductSampleWeight p) events (Finset.univ : Finset κ) ≤
        finiteEventMassSum (Finset.univ : Finset (Fin n → Z))
          (finiteProductSampleWeight p) events (Finset.univ : Finset κ) :=
    finiteProbabilityUnionBound_proof
      (support := (Finset.univ : Finset (Fin n → Z)))
      (w := finiteProductSampleWeight p)
      (events := events) (s := (Finset.univ : Finset κ))
      (finiteProductSampleWeight_isPMF hp).nonneg
  have hentry : ∀ j,
      finiteEventMass (Finset.univ : Finset (Fin n → Z))
          (finiteProductSampleWeight p) (events j) ≤ delta * weight j := by
    intro j
    have hmass :=
      indicator_finitePACBayesBernstein_fixedLambda_badEventMass_le_delta
        hn p hp hπ bad (lambda j) (delta * weight j)
        (hlambda j) (hlambda_lt j) (mul_pos hdelta (hweight j))
    simpa [events, finiteEventMass_univ_eq_sum] using hmass
  have hsum :
      finiteEventMassSum (Finset.univ : Finset (Fin n → Z))
          (finiteProductSampleWeight p) events (Finset.univ : Finset κ) ≤
        ∑ j, delta * weight j := by
    unfold finiteEventMassSum
    exact Finset.sum_le_sum fun j _ => hentry j
  have hbudget : (∑ j, delta * weight j) ≤ delta := by
    calc
      (∑ j, delta * weight j) = delta * ∑ j, weight j := by
        rw [Finset.mul_sum]
      _ ≤ delta * 1 := mul_le_mul_of_nonneg_left hweight_sum (le_of_lt hdelta)
      _ = delta := by ring
  have hmass :
      finiteEventMass (Finset.univ : Finset (Fin n → Z))
          (finiteProductSampleWeight p)
          (indicatorFinitePACBayesBernsteinWeightedCatalogBadSamples
            n p π bad lambda weight delta) ≤ delta := by
    simpa [finiteUnionEventMass,
      indicatorFinitePACBayesBernsteinWeightedCatalogBadSamples, events] using
      hUnion.trans (hsum.trans hbudget)
  simpa [finiteEventMass_univ_eq_sum] using hmass

/-- Outside the weighted catalog event, the observable low-risk posterior bound
holds for every catalog entry. -/
theorem indicator_posteriorRisk_le_weightedLowRiskCatalog_of_not_mem
    [Fintype κ] [Fintype ι] [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (π : ι → ℝ) (bad : ι → Z → Bool)
    (lambda weight : κ → ℝ) (delta : ℝ)
    (hlambda : ∀ j, 0 < lambda j)
    (hlambda_lt : ∀ j, lambda j < 6 * (n : ℝ) / 5)
    (S : Fin n → Z)
    (hS : S ∉ indicatorFinitePACBayesBernsteinWeightedCatalogBadSamples
      n p π bad lambda weight delta)
    (j : κ) (ρ : ι → ℝ) (hρ : IsPMF ρ) :
    posteriorRisk ρ (indicatorPopulationRisk p bad) ≤
      (6 * (n : ℝ) - 2 * lambda j) /
          (6 * (n : ℝ) - 5 * lambda j) *
        posteriorEmpiricalRisk ρ
          (fun i => finiteEmpiricalRisk (indicatorLoss bad) i S) +
      (6 * (n : ℝ) - 2 * lambda j) /
          (lambda j * (6 * (n : ℝ) - 5 * lambda j)) *
        (klDiv ρ π + Real.log (1 / (delta * weight j))) := by
  apply indicator_posteriorRisk_le_lowRisk_of_not_mem
    hn p π bad (lambda j) (delta * weight j)
    (hlambda j) (hlambda_lt j) S
  · intro hbad
    exact hS
      (indicatorFixedTiltBadSamples_subset_weightedCatalog
        n p π bad lambda weight delta j hbad)
  · exact hρ

/-- A catalog selector may depend on both the observed sample and the posterior,
because the good event is simultaneous in both the catalog entry and posterior.
-/
theorem indicator_posteriorRisk_le_weightedLowRiskCatalog_selected_of_not_mem
    [Fintype κ] [Fintype ι] [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (π : ι → ℝ) (bad : ι → Z → Bool)
    (lambda weight : κ → ℝ) (delta : ℝ)
    (hlambda : ∀ j, 0 < lambda j)
    (hlambda_lt : ∀ j, lambda j < 6 * (n : ℝ) / 5)
    (select : (Fin n → Z) → (ι → ℝ) → κ)
    (S : Fin n → Z)
    (hS : S ∉ indicatorFinitePACBayesBernsteinWeightedCatalogBadSamples
      n p π bad lambda weight delta)
    (ρ : ι → ℝ) (hρ : IsPMF ρ) :
    posteriorRisk ρ (indicatorPopulationRisk p bad) ≤
      (6 * (n : ℝ) - 2 * lambda (select S ρ)) /
          (6 * (n : ℝ) - 5 * lambda (select S ρ)) *
        posteriorEmpiricalRisk ρ
          (fun i => finiteEmpiricalRisk (indicatorLoss bad) i S) +
      (6 * (n : ℝ) - 2 * lambda (select S ρ)) /
          (lambda (select S ρ) *
            (6 * (n : ℝ) - 5 * lambda (select S ρ))) *
        (klDiv ρ π +
          Real.log (1 / (delta * weight (select S ρ)))) := by
  exact indicator_posteriorRisk_le_weightedLowRiskCatalog_of_not_mem
    hn p π bad lambda weight delta hlambda hlambda_lt S hS
      (select S ρ) ρ hρ

end

end FormalSLT.PACBayes.IndicatorBernsteinTiltCatalog
