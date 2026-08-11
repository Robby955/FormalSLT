/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteEmpiricalBernsteinRisk
import FormalSLT.Probability.FiniteUnionBound

/-!
# Finite weighted parameter catalogs for empirical-Bernstein risk

This module makes finite, predeclared families of empirical-variance tilts
`eta` and population-risk tilts `lambda` simultaneously valid. Each family
has its own positive weights and confidence budget. A finite weighted union
bound controls the variance catalog by `deltaVariance` and the risk catalog by
`deltaRisk`; their union is controlled by `deltaVariance + deltaRisk` without
an independence assumption.

Outside the combined event, every finite posterior satisfies every pair of
catalog bounds. Hence the two catalog entries may be selected after observing
both the sample and the posterior. This is finite-catalog adaptation only: the
catalogs, weights, and selectors are fixed in advance, and no theorem here
authorizes optimization over all real tilts.
-/

namespace FormalSLT.PACBayes.FiniteEmpiricalBernsteinRiskCatalog

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteProductBernstein
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVariancePACBayes
open FormalSLT.PACBayes.FiniteBoundedLossBernstein
open FormalSLT.PACBayes.FiniteEmpiricalBernsteinRisk
open FormalSLT.Probability.FiniteUnionBound

noncomputable section

variable {κv κr Z ι : Type*}

/-- Union of the empirical-variance bad sets obtained by allocating entry `j`
the confidence budget `deltaVariance * weightVariance j`. -/
def finiteEmpiricalVarianceWeightedCatalogBadSamples
    [Fintype κv] [Fintype Z] [DecidableEq Z] [Fintype ι]
    (n : ℕ) (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (eta weightVariance : κv → ℝ) (deltaVariance : ℝ) : Finset (Fin n → Z) := by
  classical
  exact (Finset.univ : Finset κv).biUnion fun j =>
    finiteEmpiricalVariancePACBayesBadSamples
      n p prior ell (eta j) (deltaVariance * weightVariance j)

/-- Union of the population-risk Bernstein bad sets obtained by allocating
entry `k` the confidence budget `deltaRisk * weightRisk k`. -/
def finiteBoundedLossBernsteinWeightedCatalogBadSamples
    [Fintype κr] [Fintype Z] [DecidableEq Z] [Fintype ι]
    (n : ℕ) (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (lambda weightRisk : κr → ℝ) (deltaRisk : ℝ) : Finset (Fin n → Z) := by
  classical
  exact (Finset.univ : Finset κr).biUnion fun k =>
    finiteBoundedLossBernsteinBadSamples
      n p prior ell (lambda k) (deltaRisk * weightRisk k)

/-- The single exceptional set for the separately weighted variance and risk
parameter catalogs. -/
def finiteEmpiricalBernsteinRiskWeightedCatalogBadSamples
    [Fintype κv] [Fintype κr] [Fintype Z] [DecidableEq Z] [Fintype ι]
    (n : ℕ) (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (eta weightVariance : κv → ℝ) (deltaVariance : ℝ)
    (lambda weightRisk : κr → ℝ) (deltaRisk : ℝ) : Finset (Fin n → Z) :=
  finiteEmpiricalVarianceWeightedCatalogBadSamples
      n p prior ell eta weightVariance deltaVariance ∪
    finiteBoundedLossBernsteinWeightedCatalogBadSamples
      n p prior ell lambda weightRisk deltaRisk

/-- Every fixed empirical-variance entry lies inside the variance catalog. -/
theorem finiteEmpiricalVarianceBadSamples_subset_weightedCatalog
    [Fintype κv] [Fintype Z] [DecidableEq Z] [Fintype ι]
    (n : ℕ) (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (eta weightVariance : κv → ℝ) (deltaVariance : ℝ) (j : κv) :
    finiteEmpiricalVariancePACBayesBadSamples
        n p prior ell (eta j) (deltaVariance * weightVariance j) ⊆
      finiteEmpiricalVarianceWeightedCatalogBadSamples
        n p prior ell eta weightVariance deltaVariance := by
  classical
  intro S hS
  unfold finiteEmpiricalVarianceWeightedCatalogBadSamples
  rw [Finset.mem_biUnion]
  exact ⟨j, Finset.mem_univ j, hS⟩

/-- Every fixed population-risk entry lies inside the risk catalog. -/
theorem finiteBoundedLossBernsteinBadSamples_subset_weightedCatalog
    [Fintype κr] [Fintype Z] [DecidableEq Z] [Fintype ι]
    (n : ℕ) (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (lambda weightRisk : κr → ℝ) (deltaRisk : ℝ) (k : κr) :
    finiteBoundedLossBernsteinBadSamples
        n p prior ell (lambda k) (deltaRisk * weightRisk k) ⊆
      finiteBoundedLossBernsteinWeightedCatalogBadSamples
        n p prior ell lambda weightRisk deltaRisk := by
  classical
  intro S hS
  unfold finiteBoundedLossBernsteinWeightedCatalogBadSamples
  rw [Finset.mem_biUnion]
  exact ⟨k, Finset.mem_univ k, hS⟩

private lemma finiteEventMass_univ_eq_sum
    [Fintype Z] [DecidableEq Z]
    (nu : Z → ℝ) (event : Finset Z) :
    finiteEventMass (Finset.univ : Finset Z) nu event =
      ∑ z ∈ event, nu z := by
  classical
  unfold finiteEventMass
  rw [← Finset.sum_filter]
  simp

private theorem weightedCatalog_mass_le_delta
    [Fintype κv] [Fintype Z] [DecidableEq Z]
    (nu : Z → ℝ) (hnu : ∀ z, 0 ≤ nu z)
    (events : κv → Finset Z)
    (weight : κv → ℝ) (delta : ℝ)
    (hentry : ∀ j, (∑ z ∈ events j, nu z) ≤ delta * weight j)
    (hweight_sum : ∑ j, weight j ≤ 1)
    (hdelta : 0 < delta) :
    (∑ z ∈ (Finset.univ : Finset κv).biUnion events, nu z) ≤ delta := by
  classical
  have hUnion :
      finiteUnionEventMass (Finset.univ : Finset Z) nu events
          (Finset.univ : Finset κv) ≤
        finiteEventMassSum (Finset.univ : Finset Z) nu events
          (Finset.univ : Finset κv) :=
    finiteProbabilityUnionBound_proof
      (support := (Finset.univ : Finset Z))
      (w := nu) (events := events) (s := (Finset.univ : Finset κv)) hnu
  have hsum :
      finiteEventMassSum (Finset.univ : Finset Z) nu events
          (Finset.univ : Finset κv) ≤
        ∑ j, delta * weight j := by
    unfold finiteEventMassSum
    apply Finset.sum_le_sum
    intro j _hj
    simpa [finiteEventMass_univ_eq_sum] using hentry j
  have hbudget : (∑ j, delta * weight j) ≤ delta := by
    calc
      (∑ j, delta * weight j) = delta * ∑ j, weight j := by
        rw [Finset.mul_sum]
      _ ≤ delta * 1 := mul_le_mul_of_nonneg_left hweight_sum hdelta.le
      _ = delta := by ring
  have hmass := hUnion.trans (hsum.trans hbudget)
  simpa [finiteUnionEventMass, finiteEventMass_univ_eq_sum] using hmass

/-- The separately weighted empirical-variance catalog has product-law mass
at most `deltaVariance`. -/
theorem finiteEmpiricalVariance_weightedCatalog_badEventMass_le_delta
    [Fintype κv] [Fintype Z] [DecidableEq Z] [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    (eta weightVariance : κv → ℝ) (deltaVariance : ℝ)
    (heta : ∀ j, 0 < eta j)
    (hweightVariance : ∀ j, 0 < weightVariance j)
    (hweightVariance_sum : ∑ j, weightVariance j ≤ 1)
    (hdeltaVariance : 0 < deltaVariance) :
    (∑ S ∈ finiteEmpiricalVarianceWeightedCatalogBadSamples
        n p prior ell eta weightVariance deltaVariance,
        finiteProductSampleWeight p S) ≤ deltaVariance := by
  classical
  let events : κv → Finset (Fin n → Z) := fun j =>
    finiteEmpiricalVariancePACBayesBadSamples
      n p prior ell (eta j) (deltaVariance * weightVariance j)
  apply weightedCatalog_mass_le_delta
      (nu := finiteProductSampleWeight p) (events := events)
      (weight := weightVariance) (delta := deltaVariance)
  · exact (finiteProductSampleWeight_isPMF hp).nonneg
  · intro j
    exact finiteEmpiricalVariancePACBayes_badEventMass_le_delta
      hn p hp hprior ell hell (heta j)
        (mul_pos hdeltaVariance (hweightVariance j))
  · exact hweightVariance_sum
  · exact hdeltaVariance

/-- The separately weighted population-risk catalog has product-law mass at
most `deltaRisk`. -/
theorem finiteBoundedLossBernstein_weightedCatalog_badEventMass_le_delta
    [Fintype κr] [Fintype Z] [DecidableEq Z] [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    (lambda weightRisk : κr → ℝ) (deltaRisk : ℝ)
    (hlambda : ∀ k, 0 < lambda k)
    (hlambda_lt : ∀ k, lambda k < 3 * (n : ℝ))
    (hweightRisk : ∀ k, 0 < weightRisk k)
    (hweightRisk_sum : ∑ k, weightRisk k ≤ 1)
    (hdeltaRisk : 0 < deltaRisk) :
    (∑ S ∈ finiteBoundedLossBernsteinWeightedCatalogBadSamples
        n p prior ell lambda weightRisk deltaRisk,
        finiteProductSampleWeight p S) ≤ deltaRisk := by
  classical
  let events : κr → Finset (Fin n → Z) := fun k =>
    finiteBoundedLossBernsteinBadSamples
      n p prior ell (lambda k) (deltaRisk * weightRisk k)
  apply weightedCatalog_mass_le_delta
      (nu := finiteProductSampleWeight p) (events := events)
      (weight := weightRisk) (delta := deltaRisk)
  · exact (finiteProductSampleWeight_isPMF hp).nonneg
  · intro k
    have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
    exact finiteBoundedLossBernstein_badEventMass_le_delta
      hnpos p hp hprior ell hell (hlambda k) (hlambda_lt k)
        (mul_pos hdeltaRisk (hweightRisk k))
  · exact hweightRisk_sum
  · exact hdeltaRisk

/-- The combined weighted-catalog bad set has mass at most the sum of the two
declared confidence budgets. No independence is used. -/
theorem finiteEmpiricalBernsteinRisk_weightedCatalog_badEventMass_le
    [Fintype κv] [Fintype κr] [Fintype Z] [DecidableEq Z]
    [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    (eta weightVariance : κv → ℝ) (deltaVariance : ℝ)
    (lambda weightRisk : κr → ℝ) (deltaRisk : ℝ)
    (heta : ∀ j, 0 < eta j)
    (hlambda : ∀ k, 0 < lambda k)
    (hlambda_lt : ∀ k, lambda k < 3 * (n : ℝ))
    (hweightVariance : ∀ j, 0 < weightVariance j)
    (hweightVariance_sum : ∑ j, weightVariance j ≤ 1)
    (hweightRisk : ∀ k, 0 < weightRisk k)
    (hweightRisk_sum : ∑ k, weightRisk k ≤ 1)
    (hdeltaVariance : 0 < deltaVariance)
    (hdeltaRisk : 0 < deltaRisk) :
    (∑ S ∈ finiteEmpiricalBernsteinRiskWeightedCatalogBadSamples
        n p prior ell eta weightVariance deltaVariance
          lambda weightRisk deltaRisk,
        finiteProductSampleWeight p S) ≤ deltaVariance + deltaRisk := by
  classical
  let varianceBad := finiteEmpiricalVarianceWeightedCatalogBadSamples
    n p prior ell eta weightVariance deltaVariance
  let riskBad := finiteBoundedLossBernsteinWeightedCatalogBadSamples
    n p prior ell lambda weightRisk deltaRisk
  have hvariance :
      (∑ S ∈ varianceBad, finiteProductSampleWeight p S) ≤ deltaVariance := by
    exact finiteEmpiricalVariance_weightedCatalog_badEventMass_le_delta
      hn p hp hprior ell hell eta weightVariance deltaVariance
        heta hweightVariance hweightVariance_sum hdeltaVariance
  have hrisk :
      (∑ S ∈ riskBad, finiteProductSampleWeight p S) ≤ deltaRisk := by
    exact finiteBoundedLossBernstein_weightedCatalog_badEventMass_le_delta
      hn p hp hprior ell hell lambda weightRisk deltaRisk
        hlambda hlambda_lt hweightRisk hweightRisk_sum hdeltaRisk
  have hnonneg (S : Fin n → Z) : 0 ≤ finiteProductSampleWeight p S :=
    (finiteProductSampleWeight_isPMF hp).nonneg S
  have hintersection :
      0 ≤ ∑ S ∈ varianceBad ∩ riskBad, finiteProductSampleWeight p S :=
    Finset.sum_nonneg (fun S _ => hnonneg S)
  have hunion :
      (∑ S ∈ varianceBad ∪ riskBad, finiteProductSampleWeight p S) +
          ∑ S ∈ varianceBad ∩ riskBad, finiteProductSampleWeight p S =
        (∑ S ∈ varianceBad, finiteProductSampleWeight p S) +
          ∑ S ∈ riskBad, finiteProductSampleWeight p S :=
    Finset.sum_union_inter
  have hunion_le :
      (∑ S ∈ varianceBad ∪ riskBad, finiteProductSampleWeight p S) ≤
        deltaVariance + deltaRisk := by
    linarith
  simpa [finiteEmpiricalBernsteinRiskWeightedCatalogBadSamples,
    varianceBad, riskBad] using hunion_le

/-- Outside the combined catalog event, every posterior satisfies the
observable empirical-Bernstein risk bound for every pair of catalog entries. -/
theorem posteriorRisk_le_empiricalRisk_add_empiricalVariance_weightedCatalog_of_not_mem
    [Fintype κv] [Fintype κr] [Fintype Z] [DecidableEq Z] [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (eta weightVariance : κv → ℝ) (deltaVariance : ℝ)
    (lambda weightRisk : κr → ℝ) (deltaRisk : ℝ)
    (heta : ∀ j, 0 < eta j)
    (heta_upper : ∀ j, eta j * (n : ℝ) < 2 * ((n : ℝ) - 1))
    (hlambda : ∀ k, 0 < lambda k)
    (hlambda_lt : ∀ k, lambda k < 3 * (n : ℝ))
    (S : Fin n → Z)
    (hS : S ∉ finiteEmpiricalBernsteinRiskWeightedCatalogBadSamples
      n p prior ell eta weightVariance deltaVariance lambda weightRisk deltaRisk)
    (j : κv) (k : κr) (rho : ι → ℝ) (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationRisk p ell) ≤
      posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S) +
        (klDiv rho prior + Real.log (1 / (deltaRisk * weightRisk k))) / lambda k +
        lambda k *
            ((posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) +
                (klDiv rho prior +
                    Real.log (1 / (deltaVariance * weightVariance j))) /
                  (eta j * (n : ℝ))) /
              (1 - eta j * (n : ℝ) / (2 * ((n : ℝ) - 1)))) /
          (2 * (n : ℝ) * (1 - lambda k / (3 * (n : ℝ)))) := by
  apply posteriorRisk_le_empiricalRisk_add_empiricalVariance_of_not_mem
    hn p prior ell (heta j) (heta_upper j) (hlambda k) (hlambda_lt k) S
  · intro hbad
    apply hS
    rw [finiteEmpiricalBernsteinRiskWeightedCatalogBadSamples,
      Finset.mem_union]
    rw [finiteEmpiricalBernsteinRiskBadSamples, Finset.mem_union] at hbad
    rcases hbad with hvariance | hrisk
    · exact Or.inl
        (finiteEmpiricalVarianceBadSamples_subset_weightedCatalog
          n p prior ell eta weightVariance deltaVariance j hvariance)
    · exact Or.inr
        (finiteBoundedLossBernsteinBadSamples_subset_weightedCatalog
          n p prior ell lambda weightRisk deltaRisk k hrisk)
  · exact hrho

/-- The variance and risk tilts may be selected after observing both the sample
and posterior because the catalog event is simultaneous in all entries and
all finite posteriors. -/
theorem posteriorRisk_le_empiricalRisk_add_empiricalVariance_weightedCatalog_selected_of_not_mem
    [Fintype κv] [Fintype κr] [Fintype Z] [DecidableEq Z] [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (eta weightVariance : κv → ℝ) (deltaVariance : ℝ)
    (lambda weightRisk : κr → ℝ) (deltaRisk : ℝ)
    (heta : ∀ j, 0 < eta j)
    (heta_upper : ∀ j, eta j * (n : ℝ) < 2 * ((n : ℝ) - 1))
    (hlambda : ∀ k, 0 < lambda k)
    (hlambda_lt : ∀ k, lambda k < 3 * (n : ℝ))
    (selectVariance : (Fin n → Z) → (ι → ℝ) → κv)
    (selectRisk : (Fin n → Z) → (ι → ℝ) → κr)
    (S : Fin n → Z)
    (hS : S ∉ finiteEmpiricalBernsteinRiskWeightedCatalogBadSamples
      n p prior ell eta weightVariance deltaVariance lambda weightRisk deltaRisk)
    (rho : ι → ℝ) (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationRisk p ell) ≤
      posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S) +
        (klDiv rho prior +
            Real.log (1 /
              (deltaRisk * weightRisk (selectRisk S rho)))) /
          lambda (selectRisk S rho) +
        lambda (selectRisk S rho) *
            ((posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) +
                (klDiv rho prior +
                    Real.log (1 /
                      (deltaVariance * weightVariance (selectVariance S rho)))) /
                  (eta (selectVariance S rho) * (n : ℝ))) /
              (1 - eta (selectVariance S rho) * (n : ℝ) /
                (2 * ((n : ℝ) - 1)))) /
          (2 * (n : ℝ) *
            (1 - lambda (selectRisk S rho) / (3 * (n : ℝ)))) := by
  exact
    posteriorRisk_le_empiricalRisk_add_empiricalVariance_weightedCatalog_of_not_mem
      hn p prior ell eta weightVariance deltaVariance lambda weightRisk deltaRisk
        heta heta_upper hlambda hlambda_lt S hS
        (selectVariance S rho) (selectRisk S rho) rho hrho

end

end FormalSLT.PACBayes.FiniteEmpiricalBernsteinRiskCatalog
