/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Countable fixed-sample joint mean/variance mixture

This module extends the fixed-sample joint mean/Bessel-variance PAC-Bayes
master mixture from a finite catalog to a predeclared `Nat`-indexed catalog.
The weights are nonnegative and summable, with total mass at most one.

The real-valued `tsum` requires care: a nonsummable real series is defined to
have sum zero.  Summable catalog weights alone do not control arbitrarily large
score moments on samples of product-law mass zero.  The bad-sample set therefore
contains every zero-mass sample.  This costs no probability.  On every
positive-mass sample, the per-entry expectation bound controls each score
moment by the reciprocal sample mass, which proves the weighted moment series
is summable and makes component extraction sound.

## Scope and non-claims

- The sample size is fixed and the data/hypothesis spaces remain finite.
- The catalog is countable but predeclared; this is not all-real optimization.
- The fixed-time score is not an e-process.  No time-uniform claim is made.
- The mass theorem formally assumes `delta > 0`; the usual nontrivial
  confidence interpretation additionally takes `delta < 1`.
- This file supplies the countable master event and component bound.  Posterior
  and exact-residual selector endpoints are a separate downstream layer.

No `sorry`, no `admit`, no custom axioms.
-/

namespace FormalSLT.PACBayes.CountableJointMeanVariancePACBayes

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteProductBernstein
open FormalSLT.PACBayes.FiniteJointMeanVarianceMGF
open FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes

noncomputable section

variable {ι Z : Type*}

/-- `Nat`-indexed weighted mixture of the fixed-sample prior score moments. -/
def countableJointMeanVarianceMasterMixture
    [Fintype Z] [Fintype ι] (n : ℕ)
    (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (t eta w : ℕ → ℝ) (S : Fin n → Z) : ℝ :=
  ∑' c, w c *
    finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S

/-- The countable master mixture is nonnegative under nonnegative weights and
a probability prior.  This remains true even before summability is proved. -/
theorem countableJointMeanVarianceMasterMixture_nonneg
    [Fintype Z] [Fintype ι] (n : ℕ)
    (p : Z → ℝ) {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ) {t eta w : ℕ → ℝ}
    (hw : ∀ c, 0 ≤ w c) (S : Fin n → Z) :
    0 ≤ countableJointMeanVarianceMasterMixture n p prior ell t eta w S := by
  unfold countableJointMeanVarianceMasterMixture
  exact tsum_nonneg fun c =>
    mul_nonneg (hw c)
      (finiteJointMeanVariancePriorMoment_nonneg
        n p hprior ell (t c) (eta c) S)

/-- On a sample of positive product-law mass, summable catalog weights make
the weighted prior-moment series summable.  The proof uses the per-entry
expectation bound to control every moment at this sample by the reciprocal
sample mass. -/
theorem countableJointMeanVariance_weightedPriorMoments_summable_of_sampleWeight_pos
    [Fintype Z] [DecidableEq Z] [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {t eta w : ℕ → ℝ}
    (ht : ∀ c, 0 ≤ t c) (heta : ∀ c, 0 ≤ eta c)
    (hkappa : ∀ c, 0 ≤ finiteJointMeanVarianceKappa n (eta c))
    (hw : ∀ c, 0 ≤ w c) (hw_summable : Summable w)
    {S : Fin n → Z} (hSpos : 0 < finiteProductSampleWeight p S) :
    Summable fun c => w c *
      finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S := by
  have hmoment_le : ∀ c,
      finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S ≤
        1 / finiteProductSampleWeight p S := by
    intro c
    have hexpect :=
      finiteJointMeanVariance_priorMoment_expectation_le_one
        hn p hp hprior ell hell (ht c) (heta c) (hkappa c)
    have hweight_nonneg : ∀ S' : Fin n → Z,
        0 ≤ finiteProductSampleWeight p S' :=
      (finiteProductSampleWeight_isPMF hp).nonneg
    have hmoment_nonneg : ∀ S' : Fin n → Z,
        0 ≤ finiteJointMeanVariancePriorMoment
          n p prior ell (t c) (eta c) S' := fun S' =>
      finiteJointMeanVariancePriorMoment_nonneg
        n p hprior ell (t c) (eta c) S'
    have hsingle :
        finiteProductSampleWeight p S *
            finiteJointMeanVariancePriorMoment
              n p prior ell (t c) (eta c) S ≤
          ∑ S' : Fin n → Z,
            finiteProductSampleWeight p S' *
              finiteJointMeanVariancePriorMoment
                n p prior ell (t c) (eta c) S' :=
      Finset.single_le_sum
        (fun S' _ => mul_nonneg (hweight_nonneg S') (hmoment_nonneg S'))
        (Finset.mem_univ S)
    rw [le_div_iff₀ hSpos]
    calc
      finiteJointMeanVariancePriorMoment
            n p prior ell (t c) (eta c) S *
          finiteProductSampleWeight p S =
        finiteProductSampleWeight p S *
          finiteJointMeanVariancePriorMoment
            n p prior ell (t c) (eta c) S := by ring
      _ ≤ ∑ S' : Fin n → Z,
          finiteProductSampleWeight p S' *
            finiteJointMeanVariancePriorMoment
              n p prior ell (t c) (eta c) S' := hsingle
      _ ≤ 1 := hexpect
  have hdom : Summable fun c => w c * (1 / finiteProductSampleWeight p S) :=
    hw_summable.mul_right _
  exact hdom.of_nonneg_of_le
    (fun c => mul_nonneg (hw c)
      (finiteJointMeanVariancePriorMoment_nonneg
        n p hprior ell (t c) (eta c) S))
    (fun c => mul_le_mul_of_nonneg_left (hmoment_le c) (hw c))

private theorem countableJointMeanVariance_weightedSampleMoments_summable
    [Fintype Z] [DecidableEq Z] [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {t eta w : ℕ → ℝ}
    (ht : ∀ c, 0 ≤ t c) (heta : ∀ c, 0 ≤ eta c)
    (hkappa : ∀ c, 0 ≤ finiteJointMeanVarianceKappa n (eta c))
    (hw : ∀ c, 0 ≤ w c) (hw_summable : Summable w)
    (S : Fin n → Z) :
    Summable fun c =>
      finiteProductSampleWeight p S *
        (w c * finiteJointMeanVariancePriorMoment
          n p prior ell (t c) (eta c) S) := by
  by_cases hzero : finiteProductSampleWeight p S = 0
  · simp [hzero]
  · have hSpos : 0 < finiteProductSampleWeight p S :=
      lt_of_le_of_ne ((finiteProductSampleWeight_isPMF hp).nonneg S) (Ne.symm hzero)
    exact (countableJointMeanVariance_weightedPriorMoments_summable_of_sampleWeight_pos
      hn p hp hprior ell hell ht heta hkappa hw hw_summable hSpos).mul_left _

/-- The expected countable master mixture is at most the total countable
weight.  The finite sample sum and countable catalog sum are interchanged only
after proving the required product-weighted summability on every sample. -/
theorem countableJointMeanVariance_masterMixture_expectation_le_weightTsum
    [Fintype Z] [DecidableEq Z] [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {t eta w : ℕ → ℝ}
    (ht : ∀ c, 0 ≤ t c) (heta : ∀ c, 0 ≤ eta c)
    (hkappa : ∀ c, 0 ≤ finiteJointMeanVarianceKappa n (eta c))
    (hw : ∀ c, 0 ≤ w c) (hw_summable : Summable w) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          countableJointMeanVarianceMasterMixture n p prior ell t eta w S) ≤
      ∑' c, w c := by
  let term : (Fin n → Z) → ℕ → ℝ := fun S c =>
    finiteProductSampleWeight p S *
      (w c * finiteJointMeanVariancePriorMoment
        n p prior ell (t c) (eta c) S)
  have hterm_summable : ∀ S : Fin n → Z, Summable (term S) := fun S =>
    countableJointMeanVariance_weightedSampleMoments_summable
      hn p hp hprior ell hell ht heta hkappa hw hw_summable S
  have hswap :
      (∑ S : Fin n → Z, ∑' c, term S c) =
        ∑' c, ∑ S : Fin n → Z, term S c := by
    simpa using
      (Summable.tsum_finsetSum
        (s := (Finset.univ : Finset (Fin n → Z)))
        (f := term) (fun S _ => hterm_summable S)).symm
  have hentry_nonneg : ∀ c,
      0 ≤ ∑ S : Fin n → Z, term S c := by
    intro c
    exact Finset.sum_nonneg fun S _ =>
      mul_nonneg ((finiteProductSampleWeight_isPMF hp).nonneg S)
        (mul_nonneg (hw c)
          (finiteJointMeanVariancePriorMoment_nonneg
            n p hprior ell (t c) (eta c) S))
  have hentry_le : ∀ c,
      (∑ S : Fin n → Z, term S c) ≤ w c := by
    intro c
    have hexpect :=
      finiteJointMeanVariance_priorMoment_expectation_le_one
        hn p hp hprior ell hell (ht c) (heta c) (hkappa c)
    calc
      (∑ S : Fin n → Z, term S c) =
          w c * ∑ S : Fin n → Z,
            finiteProductSampleWeight p S *
              finiteJointMeanVariancePriorMoment
                n p prior ell (t c) (eta c) S := by
            unfold term
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun S _ => ?_)
            ring
      _ ≤ w c * 1 := mul_le_mul_of_nonneg_left hexpect (hw c)
      _ = w c := by ring
  have hentry_summable : Summable fun c => ∑ S : Fin n → Z, term S c :=
    hw_summable.of_nonneg_of_le hentry_nonneg hentry_le
  calc
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          countableJointMeanVarianceMasterMixture n p prior ell t eta w S) =
        ∑ S : Fin n → Z, ∑' c, term S c := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          unfold countableJointMeanVarianceMasterMixture term
          rw [tsum_mul_left]
    _ = ∑' c, ∑ S : Fin n → Z, term S c := hswap
    _ ≤ ∑' c, w c :=
      hentry_summable.tsum_le_tsum hentry_le hw_summable

/-- A normalized countable catalog has master-mixture expectation at most one. -/
theorem countableJointMeanVariance_masterMixture_expectation_le_one
    [Fintype Z] [DecidableEq Z] [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {t eta w : ℕ → ℝ}
    (ht : ∀ c, 0 ≤ t c) (heta : ∀ c, 0 ≤ eta c)
    (hkappa : ∀ c, 0 ≤ finiteJointMeanVarianceKappa n (eta c))
    (hw : ∀ c, 0 ≤ w c) (hw_summable : Summable w)
    (hw_total : (∑' c, w c) ≤ 1) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          countableJointMeanVarianceMasterMixture n p prior ell t eta w S) ≤ 1 :=
  (countableJointMeanVariance_masterMixture_expectation_le_weightTsum
    hn p hp hprior ell hell ht heta hkappa hw hw_summable).trans hw_total

/-- One support-aware bad-sample set for the whole countable catalog.  Product-
law null samples are included so that every good sample has a genuinely
summable real master mixture. -/
def countableJointMeanVarianceCatalogBadSamples
    [Fintype Z] [Fintype ι] (n : ℕ)
    (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (t eta w : ℕ → ℝ) (delta : ℝ) : Finset (Fin n → Z) :=
  Finset.univ.filter fun S =>
    finiteProductSampleWeight p S = 0 ∨
      1 / delta ≤
        countableJointMeanVarianceMasterMixture n p prior ell t eta w S

/-- Outside the support-aware event, the sample has positive product-law mass
and the countable master mixture is below the Markov threshold. -/
theorem countableJointMeanVariance_not_mem_catalogBadSamples_iff
    [Fintype Z] [Fintype ι] (n : ℕ)
    (p : Z → ℝ) (hp : IsPMF p)
    (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (t eta w : ℕ → ℝ) (delta : ℝ) (S : Fin n → Z) :
    S ∉ countableJointMeanVarianceCatalogBadSamples
        n p prior ell t eta w delta ↔
      0 < finiteProductSampleWeight p S ∧
        countableJointMeanVarianceMasterMixture n p prior ell t eta w S <
          1 / delta := by
  rw [countableJointMeanVarianceCatalogBadSamples]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_le]
  constructor
  · rintro ⟨hne, hlt⟩
    exact ⟨lt_of_le_of_ne ((finiteProductSampleWeight_isPMF hp).nonneg S)
      (Ne.symm hne), hlt⟩
  · rintro ⟨hpos, hlt⟩
    exact ⟨ne_of_gt hpos, hlt⟩

/-- The single support-aware bad-sample set has product-law mass at most
`delta`. -/
theorem countableJointMeanVariance_catalogBadSamples_mass_le_delta
    [Fintype Z] [DecidableEq Z] [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {t eta w : ℕ → ℝ}
    (ht : ∀ c, 0 ≤ t c) (heta : ∀ c, 0 ≤ eta c)
    (hkappa : ∀ c, 0 ≤ finiteJointMeanVarianceKappa n (eta c))
    (hw : ∀ c, 0 ≤ w c) (hw_summable : Summable w)
    (hw_total : (∑' c, w c) ≤ 1)
    {delta : ℝ} (hdelta : 0 < delta) :
    (∑ S ∈ countableJointMeanVarianceCatalogBadSamples
        n p prior ell t eta w delta,
      finiteProductSampleWeight p S) ≤ delta := by
  have hthreshold : (0 : ℝ) < 1 / delta := by positivity
  have hweight : ∀ S : Fin n → Z, 0 ≤ finiteProductSampleWeight p S :=
    (finiteProductSampleWeight_isPMF hp).nonneg
  have hmix : ∀ S : Fin n → Z,
      0 ≤ countableJointMeanVarianceMasterMixture n p prior ell t eta w S :=
    countableJointMeanVarianceMasterMixture_nonneg n p hprior ell hw
  have hexpected :=
    countableJointMeanVariance_masterMixture_expectation_le_one
      hn p hp hprior ell hell ht heta hkappa hw hw_summable hw_total
  calc
    (∑ S ∈ countableJointMeanVarianceCatalogBadSamples
        n p prior ell t eta w delta,
      finiteProductSampleWeight p S) ≤
        ∑ S ∈ countableJointMeanVarianceCatalogBadSamples
            n p prior ell t eta w delta,
          (finiteProductSampleWeight p S *
            countableJointMeanVarianceMasterMixture
              n p prior ell t eta w S) / (1 / delta) := by
          apply Finset.sum_le_sum
          intro S hS
          rcases (Finset.mem_filter.mp hS).2 with hzero | htail
          · simp [hzero]
          · have hScaled :
                finiteProductSampleWeight p S * (1 / delta) ≤
                  finiteProductSampleWeight p S *
                    countableJointMeanVarianceMasterMixture
                      n p prior ell t eta w S :=
              mul_le_mul_of_nonneg_left htail (hweight S)
            exact (le_div_iff₀ hthreshold).mpr hScaled
    _ ≤ ∑ S : Fin n → Z,
          (finiteProductSampleWeight p S *
            countableJointMeanVarianceMasterMixture
              n p prior ell t eta w S) / (1 / delta) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro S hS
            exact (Finset.mem_filter.mp hS).1
          · intro S _ _
            exact div_nonneg (mul_nonneg (hweight S) (hmix S)) hthreshold.le
    _ = (∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            countableJointMeanVarianceMasterMixture
              n p prior ell t eta w S) / (1 / delta) := by
          rw [Finset.sum_div]
    _ ≤ 1 / (1 / delta) :=
      div_le_div_of_nonneg_right hexpected hthreshold.le
    _ = delta := one_div_one_div delta

/-- Outside the one countable-catalog event, every entry keeps its prior score
moment below its declared share of the confidence budget. -/
theorem countableJointMeanVariance_priorMoment_le_of_not_mem
    [Fintype Z] [DecidableEq Z] [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {t eta w : ℕ → ℝ}
    (ht : ∀ c, 0 ≤ t c) (heta : ∀ c, 0 ≤ eta c)
    (hkappa : ∀ c, 0 ≤ finiteJointMeanVarianceKappa n (eta c))
    (hw : ∀ c, 0 < w c) (hw_summable : Summable w)
    {delta : ℝ} (S : Fin n → Z)
    (hS : S ∉ countableJointMeanVarianceCatalogBadSamples
      n p prior ell t eta w delta)
    (c : ℕ) :
    finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S ≤
      1 / (delta * w c) := by
  have hgood :=
    (countableJointMeanVariance_not_mem_catalogBadSamples_iff
      n p hp prior ell t eta w delta S).1 hS
  have hsummable :=
    countableJointMeanVariance_weightedPriorMoments_summable_of_sampleWeight_pos
      hn p hp hprior ell hell ht heta hkappa (fun j => (hw j).le)
        hw_summable hgood.1
  have hsingle :
      w c * finiteJointMeanVariancePriorMoment
          n p prior ell (t c) (eta c) S ≤
        countableJointMeanVarianceMasterMixture n p prior ell t eta w S := by
    unfold countableJointMeanVarianceMasterMixture
    exact hsummable.le_tsum c fun j _ =>
      mul_nonneg (hw j).le
        (finiteJointMeanVariancePriorMoment_nonneg
          n p hprior ell (t j) (eta j) S)
  have hchain :
      w c * finiteJointMeanVariancePriorMoment
          n p prior ell (t c) (eta c) S < 1 / delta :=
    lt_of_le_of_lt hsingle hgood.2
  have hdivided :
      finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S <
        (1 / delta) / w c := by
    rw [lt_div_iff₀ (hw c)]
    calc
      finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S * w c =
          w c * finiteJointMeanVariancePriorMoment
            n p prior ell (t c) (eta c) S := by ring
      _ < 1 / delta := hchain
  calc
    finiteJointMeanVariancePriorMoment n p prior ell (t c) (eta c) S ≤
        (1 / delta) / w c := hdivided.le
    _ = 1 / (delta * w c) := by rw [div_div]

end

end FormalSLT.PACBayes.CountableJointMeanVariancePACBayes
