/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayesKL
import FormalSLT.PACBayes.FiniteJointMeanVarianceMGF
import FormalSLT.PACBayes.FiniteProductBernstein
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Finite joint mean/empirical-variance PAC-Bayes catalog

This module lifts the fixed-n joint mean and empirical-variance normalized MGF
to a one-event, one-KL posterior catalog layer.  A finite catalog of joint
pairs `c ↦ (t c, eta c)` receives positive weights `w c` with total weight at
most one.  The prior-and-catalog master mixture

`S ↦ ∑ c, w c * ∑ i, prior i * exp (score (t c) (eta c) i S)`

has sample expectation at most `∑ c, w c`, hence at most one.  Thresholding
this single statistic at `1 / delta` produces one finite bad-sample set of
product-law mass at most `delta`.  Outside that one event, every catalog entry
retains a prior score moment of at most `1 / (delta * w c)`, so a
Donsker-Varadhan step gives every posterior a retained-variance inequality
with one KL term, simultaneously in the entry and the posterior.  A selector
may therefore pick the catalog entry after seeing both the sample and the
posterior.

## Scope and non-claims

- Everything is fixed-n, finite, iid, and finite-catalog.  The catalog, the
  weights, and the selector rule are declared before the sample.
- There is one shared confidence event and one KL term in each selected-pair
  bound.  This does not mean one syntactic Donsker-Varadhan invocation covers
  all entries at once: the change of measure is applied per entry, on the one
  shared good event.
- The normalized fixed-time score is not an e-process, and no time-uniform or
  anytime-valid claim is made here.  Broader time-uniform empirical-Bernstein
  PAC-Bayes results already exist in the literature, in particular Jang,
  Jun, Neu, and Orabona (COLT 2023) and Chugg, Wang, and Ramdas (JMLR 2023).
  The contribution of this module is checked mechanization and an event-first
  API, not statistical priority.
- The posterior variance quantities are posterior averages of per-hypothesis
  variances.  They are not variances of the posterior-averaged loss.
- The two-event empirical-Bernstein risk pipeline in
  `FiniteEmpiricalBernsteinRiskCatalog` is a distinct result with separate
  variance and risk events and two KL appearances; this module neither
  replaces it nor relabels it.

No `sorry`, no `admit`, no custom axioms.
-/

namespace FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteJointMeanVarianceMGF
open FormalSLT.PACBayes.FiniteProductBernstein

noncomputable section

variable {κ ι Z : Type*}

/-- Per-hypothesis normalized fixed-n joint mean/empirical-variance score.
This is exactly the exponent of `finiteJointMeanVariance_normalizedMGF_le_one`:
lower-tail mean deviation, empirical-variance penalty, retained Bennett
normalizer, and transported variance correction. -/
def finiteJointMeanVarianceScore [Fintype Z] (n : ℕ)
    (p : Z → ℝ) (ell : ι → Z → ℝ) (t eta : ℝ) (i : ι) (S : Fin n → Z) : ℝ :=
  t * (n : ℝ) *
      (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
    eta * (n : ℝ) * finiteEmpiricalVariance ell i S -
    (n : ℝ) * Real.log
      (1 + (Real.exp t - 1 - t) * finitePopulationVariance p ell i) +
    Real.exp (-t) * finiteJointMeanVarianceKappa n eta *
      finitePopulationVariance p ell i

/-- The per-hypothesis normalized joint score has sample expectation at most
one.  This is a restatement of the normalized fixed-n joint MGF. -/
theorem finiteJointMeanVarianceScore_expectation_le_one
    [Fintype Z] [DecidableEq Z]
    {n : ℕ} {t eta : ℝ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : ι → Z → ℝ) (i : ι)
    (hell : ∀ z : Z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa n eta) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp (finiteJointMeanVarianceScore n p ell t eta i S)) ≤ 1 := by
  simpa only [finiteJointMeanVarianceScore] using
    finiteJointMeanVariance_normalizedMGF_le_one hn p hp ell i hell ht heta hkappa

/-- Prior moment of the joint score at one sample and one catalog pair. -/
def finiteJointMeanVariancePriorMoment [Fintype Z] [Fintype ι] (n : ℕ)
    (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (t eta : ℝ) (S : Fin n → Z) : ℝ :=
  ∑ i : ι, prior i * Real.exp (finiteJointMeanVarianceScore n p ell t eta i S)

/-- The prior score moment is nonnegative under a nonnegative prior. -/
theorem finiteJointMeanVariancePriorMoment_nonneg
    [Fintype Z] [Fintype ι] (n : ℕ)
    (p : Z → ℝ) {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ) (t eta : ℝ) (S : Fin n → Z) :
    0 ≤ finiteJointMeanVariancePriorMoment n p prior ell t eta S :=
  Finset.sum_nonneg fun i _ =>
    mul_nonneg (hprior.nonneg i) (Real.exp_pos _).le

/-- The prior score moment is positive under a full-support prior. -/
theorem finiteJointMeanVariancePriorMoment_pos
    [Fintype Z] [Fintype ι] [Nonempty ι] (n : ℕ)
    (p : Z → ℝ) {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ) (t eta : ℝ) (S : Fin n → Z) :
    0 < finiteJointMeanVariancePriorMoment n p prior ell t eta S :=
  Finset.sum_pos
    (fun i _ => mul_pos (hprior.pos i) (Real.exp_pos _))
    Finset.univ_nonempty

/-- The prior score moment has sample expectation at most one. -/
theorem finiteJointMeanVariance_priorMoment_expectation_le_one
    [Fintype Z] [DecidableEq Z] [Fintype ι]
    {n : ℕ} {t eta : ℝ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa n eta) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          finiteJointMeanVariancePriorMoment n p prior ell t eta S) ≤ 1 := by
  unfold finiteJointMeanVariancePriorMoment
  calc
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          ∑ i : ι, prior i *
            Real.exp (finiteJointMeanVarianceScore n p ell t eta i S))
        = ∑ S : Fin n → Z, ∑ i : ι,
            finiteProductSampleWeight p S *
              (prior i *
                Real.exp (finiteJointMeanVarianceScore n p ell t eta i S)) := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          rw [Finset.mul_sum]
    _ = ∑ i : ι, ∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            (prior i *
              Real.exp (finiteJointMeanVarianceScore n p ell t eta i S)) :=
        Finset.sum_comm
    _ = ∑ i : ι, prior i *
          ∑ S : Fin n → Z,
            finiteProductSampleWeight p S *
              Real.exp (finiteJointMeanVarianceScore n p ell t eta i S) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun S _ => ?_)
        ring
    _ ≤ ∑ i : ι, prior i * 1 := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        exact mul_le_mul_of_nonneg_left
          (finiteJointMeanVarianceScore_expectation_le_one
            hn p hp ell i (hell i) ht heta hkappa)
          (hprior.nonneg i)
    _ = 1 := by simp [hprior.sum_one]

/-- Prior-and-catalog master mixture at one sample: catalog-weighted total of
the per-entry prior score moments. -/
def finiteJointMeanVarianceMasterMixture
    [Fintype κ] [Fintype Z] [Fintype ι] (n : ℕ)
    (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (t eta w : κ → ℝ) (S : Fin n → Z) : ℝ :=
  ∑ c : κ, w c * finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S

/-- The master mixture is nonnegative under nonnegative weights and prior. -/
theorem finiteJointMeanVarianceMasterMixture_nonneg
    [Fintype κ] [Fintype Z] [Fintype ι] (n : ℕ)
    (p : Z → ℝ) {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ) {t eta w : κ → ℝ}
    (hw : ∀ c, 0 ≤ w c) (S : Fin n → Z) :
    0 ≤ finiteJointMeanVarianceMasterMixture n p prior ell t eta w S :=
  Finset.sum_nonneg fun c _ =>
    mul_nonneg (hw c)
      (finiteJointMeanVariancePriorMoment_nonneg n p hprior ell (t c) (eta c) S)

/-- The master mixture has sample expectation at most the total catalog
weight. -/
theorem finiteJointMeanVariance_masterMixture_expectation_le_weightSum
    [Fintype κ] [Fintype Z] [DecidableEq Z] [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {t eta w : κ → ℝ}
    (ht : ∀ c, 0 ≤ t c) (heta : ∀ c, 0 ≤ eta c)
    (hkappa : ∀ c, 0 ≤ finiteJointMeanVarianceKappa n (eta c))
    (hw : ∀ c, 0 ≤ w c) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          finiteJointMeanVarianceMasterMixture n p prior ell t eta w S) ≤
      ∑ c : κ, w c := by
  unfold finiteJointMeanVarianceMasterMixture
  calc
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          ∑ c : κ, w c *
            finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S)
        = ∑ S : Fin n → Z, ∑ c : κ,
            finiteProductSampleWeight p S *
              (w c *
                finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S) := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          rw [Finset.mul_sum]
    _ = ∑ c : κ, ∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            (w c *
              finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S) :=
        Finset.sum_comm
    _ = ∑ c : κ, w c *
          ∑ S : Fin n → Z,
            finiteProductSampleWeight p S *
              finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun S _ => ?_)
        ring
    _ ≤ ∑ c : κ, w c * 1 := by
        refine Finset.sum_le_sum (fun c _ => ?_)
        exact mul_le_mul_of_nonneg_left
          (finiteJointMeanVariance_priorMoment_expectation_le_one
            hn p hp hprior ell hell (ht c) (heta c) (hkappa c))
          (hw c)
    _ = ∑ c : κ, w c := by simp

/-- The master mixture has sample expectation at most one when the positive
catalog weights total at most one. -/
theorem finiteJointMeanVariance_masterMixture_expectation_le_one
    [Fintype κ] [Fintype Z] [DecidableEq Z] [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {t eta w : κ → ℝ}
    (ht : ∀ c, 0 ≤ t c) (heta : ∀ c, 0 ≤ eta c)
    (hkappa : ∀ c, 0 ≤ finiteJointMeanVarianceKappa n (eta c))
    (hw : ∀ c, 0 ≤ w c) (hw_sum : ∑ c, w c ≤ 1) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          finiteJointMeanVarianceMasterMixture n p prior ell t eta w S) ≤ 1 :=
  (finiteJointMeanVariance_masterMixture_expectation_le_weightSum
    hn p hp hprior ell hell ht heta hkappa hw).trans hw_sum

/-- The one bad-sample set of the whole catalog: samples where the master
mixture reaches the threshold `1 / delta`. -/
def finiteJointMeanVarianceCatalogBadSamples
    [Fintype κ] [Fintype Z] [Fintype ι] (n : ℕ)
    (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (t eta w : κ → ℝ) (delta : ℝ) : Finset (Fin n → Z) :=
  Finset.univ.filter fun S =>
    1 / delta ≤ finiteJointMeanVarianceMasterMixture n p prior ell t eta w S

/-- A sample is outside the catalog event exactly when its master mixture is
below the threshold. -/
theorem finiteJointMeanVariance_not_mem_catalogBadSamples_iff
    [Fintype κ] [Fintype Z] [Fintype ι] (n : ℕ)
    (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (t eta w : κ → ℝ) (delta : ℝ) (S : Fin n → Z) :
    S ∉ finiteJointMeanVarianceCatalogBadSamples n p prior ell t eta w delta ↔
      finiteJointMeanVarianceMasterMixture n p prior ell t eta w S <
        1 / delta := by
  simp [finiteJointMeanVarianceCatalogBadSamples, not_le]

/-- The single catalog bad-sample set has product-law mass at most `delta`.

This is one Markov step on the master mixture.  As elsewhere in this
directory, the formal assumption is only `0 < delta`; applications use
`delta < 1` when reading `1 - delta` as a nontrivial confidence level. -/
theorem finiteJointMeanVariance_catalogBadSamples_mass_le_delta
    [Fintype κ] [Fintype Z] [DecidableEq Z] [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {t eta w : κ → ℝ}
    (ht : ∀ c, 0 ≤ t c) (heta : ∀ c, 0 ≤ eta c)
    (hkappa : ∀ c, 0 ≤ finiteJointMeanVarianceKappa n (eta c))
    (hw : ∀ c, 0 ≤ w c) (hw_sum : ∑ c, w c ≤ 1)
    {delta : ℝ} (hdelta : 0 < delta) :
    (∑ S ∈ finiteJointMeanVarianceCatalogBadSamples n p prior ell t eta w delta,
        finiteProductSampleWeight p S) ≤ delta := by
  have hthreshold : (0 : ℝ) < 1 / delta := by positivity
  have hweight : ∀ S : Fin n → Z, 0 ≤ finiteProductSampleWeight p S :=
    (finiteProductSampleWeight_isPMF hp).nonneg
  have hmix : ∀ S : Fin n → Z,
      0 ≤ finiteJointMeanVarianceMasterMixture n p prior ell t eta w S :=
    fun S =>
      finiteJointMeanVarianceMasterMixture_nonneg n p hprior ell hw S
  have hexpected :=
    finiteJointMeanVariance_masterMixture_expectation_le_one
      hn p hp hprior ell hell ht heta hkappa hw hw_sum
  calc
    (∑ S ∈ finiteJointMeanVarianceCatalogBadSamples n p prior ell t eta w delta,
        finiteProductSampleWeight p S)
        ≤ ∑ S ∈ finiteJointMeanVarianceCatalogBadSamples
              n p prior ell t eta w delta,
            (finiteProductSampleWeight p S *
              finiteJointMeanVarianceMasterMixture n p prior ell t eta w S) /
              (1 / delta) := by
          apply Finset.sum_le_sum
          intro S hS
          have hTail :
              1 / delta ≤
                finiteJointMeanVarianceMasterMixture n p prior ell t eta w S :=
            (Finset.mem_filter.mp hS).2
          have hScaled :
              finiteProductSampleWeight p S * (1 / delta) ≤
                finiteProductSampleWeight p S *
                  finiteJointMeanVarianceMasterMixture n p prior ell t eta w S :=
            mul_le_mul_of_nonneg_left hTail (hweight S)
          exact (le_div_iff₀ hthreshold).mpr hScaled
    _ ≤ ∑ S : Fin n → Z,
          (finiteProductSampleWeight p S *
            finiteJointMeanVarianceMasterMixture n p prior ell t eta w S) /
            (1 / delta) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro S hS
            exact (Finset.mem_filter.mp hS).1
          · intro S _ _
            exact div_nonneg (mul_nonneg (hweight S) (hmix S)) hthreshold.le
    _ = (∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            finiteJointMeanVarianceMasterMixture n p prior ell t eta w S) /
          (1 / delta) := by
          rw [Finset.sum_div]
    _ ≤ 1 / (1 / delta) :=
          div_le_div_of_nonneg_right hexpected hthreshold.le
    _ = delta := one_div_one_div delta

/-- Outside the one catalog event, every catalog entry keeps its prior score
moment at most `1 / (delta * w c)`. -/
theorem finiteJointMeanVariance_priorMoment_le_of_not_mem
    [Fintype κ] [Fintype Z] [Fintype ι] (n : ℕ)
    (p : Z → ℝ) {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ) {t eta w : κ → ℝ}
    (hw : ∀ c, 0 < w c) {delta : ℝ}
    (S : Fin n → Z)
    (hS : S ∉ finiteJointMeanVarianceCatalogBadSamples n p prior ell t eta w delta)
    (c : κ) :
    finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S ≤
      1 / (delta * w c) := by
  have hlt :=
    (finiteJointMeanVariance_not_mem_catalogBadSamples_iff
      n p prior ell t eta w delta S).1 hS
  have hsingle :
      w c * finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S ≤
        finiteJointMeanVarianceMasterMixture n p prior ell t eta w S := by
    unfold finiteJointMeanVarianceMasterMixture
    exact Finset.single_le_sum
      (f := fun c' =>
        w c' * finiteJointMeanVariancePriorMoment n p prior ell (t c') (eta c') S)
      (fun c' _ => mul_nonneg (hw c').le
        (finiteJointMeanVariancePriorMoment_nonneg n p hprior ell (t c') (eta c') S))
      (Finset.mem_univ c)
  have hchain :
      w c * finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S <
        1 / delta :=
    lt_of_le_of_lt hsingle hlt
  have hdivided :
      finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S <
        (1 / delta) / w c := by
    rw [lt_div_iff₀ (hw c)]
    calc
      finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S * w c =
          w c * finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S := by
        ring
      _ < 1 / delta := hchain
  calc
    finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S ≤
        (1 / delta) / w c := hdivided.le
    _ = 1 / (delta * w c) := by rw [div_div]

/-- Outside the one catalog event, every posterior and every catalog entry
satisfy the Donsker-Varadhan score bound with one KL term. -/
theorem finiteJointMeanVariance_posteriorScore_le_of_not_mem
    [Fintype κ] [Fintype Z] [Fintype ι] [Nonempty ι] (n : ℕ)
    (p : Z → ℝ) {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ) {t eta w : κ → ℝ}
    (hw : ∀ c, 0 < w c) {delta : ℝ}
    (S : Fin n → Z)
    (hS : S ∉ finiteJointMeanVarianceCatalogBadSamples n p prior ell t eta w delta)
    (c : κ) {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho
        (fun i => finiteJointMeanVarianceScore n p ell (t c) (eta c) i S) ≤
      klDiv rho prior + Real.log (1 / (delta * w c)) := by
  have hdv :
      (∑ i, rho i * finiteJointMeanVarianceScore n p ell (t c) (eta c) i S) ≤
        klDiv rho prior +
          Real.log
            (finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S) := by
    simpa [finiteJointMeanVariancePriorMoment] using
      donsker_varadhan hrho hprior
        (fun i => finiteJointMeanVarianceScore n p ell (t c) (eta c) i S)
  have hmoment_pos :=
    finiteJointMeanVariancePriorMoment_pos n p hprior ell (t c) (eta c) S
  have hmoment_le :=
    finiteJointMeanVariance_priorMoment_le_of_not_mem
      n p hprior.toIsPMF ell hw S hS c
  have hlog :
      Real.log
          (finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S) ≤
        Real.log (1 / (delta * w c)) :=
    Real.log_le_log hmoment_pos hmoment_le
  simp only [posteriorAverage]
  linarith

/-- Raw retained-variance posterior inequality on the one catalog event.

Outside the single bad-sample set, for every posterior `rho` and every catalog
entry `c`, the scaled posterior generalization gap is controlled by one KL
term, the entry's share of the confidence budget, the empirical-variance
penalty, the retained Bennett normalizer at the posterior variance, and the
transported variance correction.  Both `posteriorAverage rho
(finitePopulationVariance p ell)` and the empirical counterpart are posterior
averages of per-hypothesis variances.  The population-variance log term uses
concavity of the logarithm, so it is stated at the posterior-averaged
variance. -/
theorem finiteJointMeanVariance_posteriorGap_le_of_not_mem
    [Fintype κ] [Fintype Z] [Fintype ι] [Nonempty ι] (n : ℕ)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ) {t eta w : κ → ℝ}
    (hw : ∀ c, 0 < w c) {delta : ℝ}
    (S : Fin n → Z)
    (hS : S ∉ finiteJointMeanVarianceCatalogBadSamples n p prior ell t eta w delta)
    (c : κ) {rho : ι → ℝ} (hrho : IsPMF rho) :
    t c * (n : ℝ) *
        (posteriorAverage rho (finitePopulationRisk p ell) -
          posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S)) ≤
      klDiv rho prior + Real.log (1 / (delta * w c)) +
        eta c * (n : ℝ) *
          posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) +
        (n : ℝ) *
          Real.log
            (1 + (Real.exp (t c) - 1 - t c) *
              posteriorAverage rho (finitePopulationVariance p ell)) -
        Real.exp (-t c) * finiteJointMeanVarianceKappa n (eta c) *
          posteriorAverage rho (finitePopulationVariance p ell) := by
  classical
  have hpsi : 0 ≤ Real.exp (t c) - 1 - t c := by
    have h := Real.add_one_le_exp (t c)
    linarith
  have hV : ∀ i, 0 ≤ finitePopulationVariance p ell i := fun i =>
    finitePopulationVariance_nonneg p hp ell i
  have hscore :=
    finiteJointMeanVariance_posteriorScore_le_of_not_mem
      n p hprior ell hw S hS c hrho
  have hexpand :
      posteriorAverage rho
          (fun i => finiteJointMeanVarianceScore n p ell (t c) (eta c) i S) =
        t c * (n : ℝ) *
            (posteriorAverage rho (finitePopulationRisk p ell) -
              posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S)) -
          eta c * (n : ℝ) *
            posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) -
          (n : ℝ) *
            posteriorAverage rho (fun i =>
              Real.log
                (1 + (Real.exp (t c) - 1 - t c) *
                  finitePopulationVariance p ell i)) +
          Real.exp (-t c) * finiteJointMeanVarianceKappa n (eta c) *
            posteriorAverage rho (finitePopulationVariance p ell) := by
    simp only [posteriorAverage, finiteJointMeanVarianceScore]
    calc
      (∑ i, rho i *
          (t c * (n : ℝ) *
              (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
            eta c * (n : ℝ) * finiteEmpiricalVariance ell i S -
            (n : ℝ) * Real.log
              (1 + (Real.exp (t c) - 1 - t c) *
                finitePopulationVariance p ell i) +
            Real.exp (-t c) * finiteJointMeanVarianceKappa n (eta c) *
              finitePopulationVariance p ell i))
          = ∑ i,
              (t c * (n : ℝ) * (rho i * finitePopulationRisk p ell i) -
                t c * (n : ℝ) * (rho i * finiteEmpiricalRisk ell i S) -
                eta c * (n : ℝ) * (rho i * finiteEmpiricalVariance ell i S) -
                (n : ℝ) *
                  (rho i * Real.log
                    (1 + (Real.exp (t c) - 1 - t c) *
                      finitePopulationVariance p ell i)) +
                Real.exp (-t c) * finiteJointMeanVarianceKappa n (eta c) *
                  (rho i * finitePopulationVariance p ell i)) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            ring
      _ = t c * (n : ℝ) *
              ((∑ i, rho i * finitePopulationRisk p ell i) -
                ∑ i, rho i * finiteEmpiricalRisk ell i S) -
            eta c * (n : ℝ) *
              ∑ i, rho i * finiteEmpiricalVariance ell i S -
            (n : ℝ) *
              ∑ i, rho i * Real.log
                (1 + (Real.exp (t c) - 1 - t c) *
                  finitePopulationVariance p ell i) +
            Real.exp (-t c) * finiteJointMeanVarianceKappa n (eta c) *
              ∑ i, rho i * finitePopulationVariance p ell i := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.sum_sub_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
              ← Finset.mul_sum, ← Finset.mul_sum]
            ring
  have hjensen :
      posteriorAverage rho (fun i =>
          Real.log
            (1 + (Real.exp (t c) - 1 - t c) *
              finitePopulationVariance p ell i)) ≤
        Real.log
          (1 + (Real.exp (t c) - 1 - t c) *
            posteriorAverage rho (finitePopulationVariance p ell)) := by
    have hmem : ∀ i ∈ (Finset.univ : Finset ι),
        (1 + (Real.exp (t c) - 1 - t c) * finitePopulationVariance p ell i) ∈
          Set.Ioi (0 : ℝ) := by
      intro i _
      have hprod :
          0 ≤ (Real.exp (t c) - 1 - t c) * finitePopulationVariance p ell i :=
        mul_nonneg hpsi (hV i)
      exact Set.mem_Ioi.mpr (by linarith)
    have hj := ConcaveOn.le_map_sum (f := Real.log) (s := Set.Ioi 0)
      (t := Finset.univ) (w := rho)
      (p := fun i =>
        1 + (Real.exp (t c) - 1 - t c) * finitePopulationVariance p ell i)
      strictConcaveOn_log_Ioi.concaveOn
      (fun i _ => hrho.nonneg i) hrho.sum_one hmem
    simp only [smul_eq_mul] at hj
    have hcombo :
        (∑ i, rho i *
            (1 + (Real.exp (t c) - 1 - t c) * finitePopulationVariance p ell i)) =
          1 + (Real.exp (t c) - 1 - t c) *
            posteriorAverage rho (finitePopulationVariance p ell) := by
      calc
        (∑ i, rho i *
            (1 + (Real.exp (t c) - 1 - t c) * finitePopulationVariance p ell i))
            = ∑ i,
                (rho i +
                  (Real.exp (t c) - 1 - t c) *
                    (rho i * finitePopulationVariance p ell i)) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              ring
        _ = (∑ i, rho i) +
              (Real.exp (t c) - 1 - t c) *
                ∑ i, rho i * finitePopulationVariance p ell i := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ = 1 + (Real.exp (t c) - 1 - t c) *
              posteriorAverage rho (finitePopulationVariance p ell) := by
              rw [hrho.sum_one]
              rfl
    rw [hcombo] at hj
    simpa [posteriorAverage] using hj
  have hlog_scaled :
      (n : ℝ) *
          posteriorAverage rho (fun i =>
            Real.log
              (1 + (Real.exp (t c) - 1 - t c) *
                finitePopulationVariance p ell i)) ≤
        (n : ℝ) *
          Real.log
            (1 + (Real.exp (t c) - 1 - t c) *
              posteriorAverage rho (finitePopulationVariance p ell)) :=
    mul_le_mul_of_nonneg_left hjensen (Nat.cast_nonneg n)
  rw [hexpand] at hscore
  linarith

/-- Division form of the retained-variance posterior inequality for a strictly
positive mean tilt. -/
theorem finiteJointMeanVariance_posteriorGap_div_le_of_not_mem
    [Fintype κ] [Fintype Z] [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ) {t eta w : κ → ℝ}
    (hw : ∀ c, 0 < w c) {delta : ℝ}
    (S : Fin n → Z)
    (hS : S ∉ finiteJointMeanVarianceCatalogBadSamples n p prior ell t eta w delta)
    (c : κ) (htc : 0 < t c) {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationRisk p ell) -
        posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S) ≤
      (klDiv rho prior + Real.log (1 / (delta * w c)) +
          eta c * (n : ℝ) *
            posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) +
          (n : ℝ) *
            Real.log
              (1 + (Real.exp (t c) - 1 - t c) *
                posteriorAverage rho (finitePopulationVariance p ell)) -
          Real.exp (-t c) * finiteJointMeanVarianceKappa n (eta c) *
            posteriorAverage rho (finitePopulationVariance p ell)) /
        (t c * (n : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hpos : 0 < t c * (n : ℝ) := mul_pos htc hnR
  have hraw :=
    finiteJointMeanVariance_posteriorGap_le_of_not_mem
      n p hp hprior ell hw S hS c hrho
  rw [le_div_iff₀ hpos]
  calc
    (posteriorAverage rho (finitePopulationRisk p ell) -
          posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S)) *
        (t c * (n : ℝ)) =
      t c * (n : ℝ) *
        (posteriorAverage rho (finitePopulationRisk p ell) -
          posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S)) := by
      ring
    _ ≤ _ := hraw

/-- The catalog entry may be selected after observing both the sample and the
posterior, because the good event is one shared event that is simultaneous in
the entry and the posterior. -/
theorem finiteJointMeanVariance_posteriorGap_le_selected_of_not_mem
    [Fintype κ] [Fintype Z] [Fintype ι] [Nonempty ι] (n : ℕ)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ) {t eta w : κ → ℝ}
    (hw : ∀ c, 0 < w c) {delta : ℝ}
    (select : (Fin n → Z) → (ι → ℝ) → κ)
    (S : Fin n → Z)
    (hS : S ∉ finiteJointMeanVarianceCatalogBadSamples n p prior ell t eta w delta)
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    t (select S rho) * (n : ℝ) *
        (posteriorAverage rho (finitePopulationRisk p ell) -
          posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S)) ≤
      klDiv rho prior + Real.log (1 / (delta * w (select S rho))) +
        eta (select S rho) * (n : ℝ) *
          posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) +
        (n : ℝ) *
          Real.log
            (1 + (Real.exp (t (select S rho)) - 1 - t (select S rho)) *
              posteriorAverage rho (finitePopulationVariance p ell)) -
        Real.exp (-t (select S rho)) *
          finiteJointMeanVarianceKappa n (eta (select S rho)) *
          posteriorAverage rho (finitePopulationVariance p ell) :=
  finiteJointMeanVariance_posteriorGap_le_of_not_mem
    n p hp hprior ell hw S hS (select S rho) hrho

/-- Division form of the selector endpoint for catalogs whose mean tilts are
all strictly positive. -/
theorem finiteJointMeanVariance_posteriorGap_div_le_selected_of_not_mem
    [Fintype κ] [Fintype Z] [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ) {t eta w : κ → ℝ}
    (hw : ∀ c, 0 < w c) {delta : ℝ}
    (ht_pos : ∀ c, 0 < t c)
    (select : (Fin n → Z) → (ι → ℝ) → κ)
    (S : Fin n → Z)
    (hS : S ∉ finiteJointMeanVarianceCatalogBadSamples n p prior ell t eta w delta)
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationRisk p ell) -
        posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S) ≤
      (klDiv rho prior + Real.log (1 / (delta * w (select S rho))) +
          eta (select S rho) * (n : ℝ) *
            posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) +
          (n : ℝ) *
            Real.log
              (1 + (Real.exp (t (select S rho)) - 1 - t (select S rho)) *
                posteriorAverage rho (finitePopulationVariance p ell)) -
          Real.exp (-t (select S rho)) *
            finiteJointMeanVarianceKappa n (eta (select S rho)) *
            posteriorAverage rho (finitePopulationVariance p ell)) /
        (t (select S rho) * (n : ℝ)) :=
  finiteJointMeanVariance_posteriorGap_div_le_of_not_mem
    hn p hp hprior ell hw S hS (select S rho) (ht_pos (select S rho)) hrho

end

end FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes
