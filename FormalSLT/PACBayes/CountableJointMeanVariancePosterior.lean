/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.CountableJointMeanVariancePACBayes
import FormalSLT.PACBayes.FiniteJointMeanVarianceResidual

/-!
# Posterior bounds for the countable joint mean/variance catalog

This module lifts the support-aware fixed-sample countable master event to
Donsker--Varadhan posterior bounds. On one good sample, every posterior and
every positive-weight catalog entry satisfy the raw score and retained-
variance gap inequalities. The exact residual envelope then gives the
explicit `xi / t` risk bound, including a selector that may depend on both the
sample and the posterior.

The proof reduces each selected countable entry to a singleton instance of the
checked finite-catalog posterior theorem. It therefore uses the same one
master event and exactly one posterior KL term; it does not take another union
bound or introduce another confidence event.

## Scope and non-claims

- The tilt-pair catalog is `Nat`-indexed and fixed before the sample.
- The data and hypothesis spaces remain finite, and each posterior is a finite
  PMF on the hypothesis space.
- This is countable catalog selection, not a posterior on a countable
  hypothesis space and not all-real optimization.
- The fixed-time score is not an e-process. No time-uniform claim is made.
- The mass theorem remains the one proved by the countable foundation; it
  separately requires `0 < delta`, nonnegative summable weights, and total
  weight at most one.
- The conditional posterior endpoints require strictly positive summable
  weights and a supplied sample outside that event. They can be stated for any
  `delta`; the usual nontrivial confidence interpretation uses
  `0 < delta < 1`.
- The displayed KL is FormalSLT's finite real-valued sum. With the finite
  discrete measurable-space instances, `MeasurableSingletonClass`, and the
  full-support prior assumed here, `FinitePMFBridge` identifies it with
  mathlib's measure-theoretic `InformationTheory.klDiv` after conversion to
  `PMF`.

No `sorry`, no `admit`, no custom axioms.
-/

namespace FormalSLT.PACBayes.CountableJointMeanVariancePosterior

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteProductBernstein
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteJointMeanVarianceMGF
open FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes
open FormalSLT.PACBayes.FiniteJointMeanVarianceResidual
open FormalSLT.PACBayes.CountableJointMeanVariancePACBayes

noncomputable section

variable {ι Z : Type*}

/-- Every entry of a countable good sample is also outside the corresponding
singleton finite-catalog event. This private bridge lets the posterior layer
reuse the finite Donsker--Varadhan and residual proofs verbatim. -/
private theorem finiteSingleton_not_mem_of_countable_not_mem
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
    S ∉ finiteJointMeanVarianceCatalogBadSamples
      n p prior ell
        (fun _ : Unit => t c) (fun _ : Unit => eta c)
        (fun _ : Unit => w c) delta := by
  have hgood :=
    (countableJointMeanVariance_not_mem_catalogBadSamples_iff
      n p hp prior ell t eta w delta S).1 hS
  have hsummable :=
    countableJointMeanVariance_weightedPriorMoments_summable_of_sampleWeight_pos
      hn p hp hprior ell hell ht heta hkappa (fun j => (hw j).le)
        hw_summable hgood.1
  have hsingle :
      w c * finiteJointMeanVariancePriorMoment
          n p prior ell (t c) (eta c) S < 1 / delta := by
    exact lt_of_le_of_lt
      (hsummable.le_tsum c fun j _ =>
        mul_nonneg (hw j).le
          (finiteJointMeanVariancePriorMoment_nonneg
            n p hprior ell (t j) (eta j) S))
      hgood.2
  rw [finiteJointMeanVariance_not_mem_catalogBadSamples_iff]
  simpa [finiteJointMeanVarianceMasterMixture] using hsingle

/-- On the one countable-catalog event, every finite-hypothesis posterior and
every catalog entry obey the Donsker--Varadhan score bound with one KL term. -/
theorem countableJointMeanVariance_posteriorScore_le_of_not_mem
    [Fintype Z] [DecidableEq Z] [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {t eta w : ℕ → ℝ}
    (ht : ∀ c, 0 ≤ t c) (heta : ∀ c, 0 ≤ eta c)
    (hkappa : ∀ c, 0 ≤ finiteJointMeanVarianceKappa n (eta c))
    (hw : ∀ c, 0 < w c) (hw_summable : Summable w)
    {delta : ℝ} (S : Fin n → Z)
    (hS : S ∉ countableJointMeanVarianceCatalogBadSamples
      n p prior ell t eta w delta)
    (c : ℕ) {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho
        (fun i => finiteJointMeanVarianceScore n p ell (t c) (eta c) i S) ≤
      klDiv rho prior + Real.log (1 / (delta * w c)) := by
  have hsingleton := finiteSingleton_not_mem_of_countable_not_mem
    hn p hp hprior.toIsPMF ell hell ht heta hkappa hw hw_summable S hS c
  simpa using
    (finiteJointMeanVariance_posteriorScore_le_of_not_mem
      (κ := Unit) (t := fun _ : Unit => t c)
      (eta := fun _ : Unit => eta c) (w := fun _ : Unit => w c)
      n p hprior ell (fun _ => hw c) S hsingleton () hrho)

/-- Raw retained-variance posterior inequality for every countable entry on the
same support-aware master event. -/
theorem countableJointMeanVariance_posteriorGap_le_of_not_mem
    [Fintype Z] [DecidableEq Z] [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {t eta w : ℕ → ℝ}
    (ht : ∀ c, 0 ≤ t c) (heta : ∀ c, 0 ≤ eta c)
    (hkappa : ∀ c, 0 ≤ finiteJointMeanVarianceKappa n (eta c))
    (hw : ∀ c, 0 < w c) (hw_summable : Summable w)
    {delta : ℝ} (S : Fin n → Z)
    (hS : S ∉ countableJointMeanVarianceCatalogBadSamples
      n p prior ell t eta w delta)
    (c : ℕ) {rho : ι → ℝ} (hrho : IsPMF rho) :
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
  have hsingleton := finiteSingleton_not_mem_of_countable_not_mem
    hn p hp hprior.toIsPMF ell hell ht heta hkappa hw hw_summable S hS c
  simpa using
    (finiteJointMeanVariance_posteriorGap_le_of_not_mem
      (κ := Unit) (t := fun _ : Unit => t c)
      (eta := fun _ : Unit => eta c) (w := fun _ : Unit => w c)
      n p hp hprior ell (fun _ => hw c) S hsingleton () hrho)

/-- Exact-residual posterior-risk bound for every entry of the countable
catalog, using the same one event and one KL term. -/
theorem countableJointMeanVariance_posteriorRisk_le_with_xi_of_not_mem
    [Fintype Z] [DecidableEq Z] [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {t eta w : ℕ → ℝ}
    (ht : ∀ c, 0 ≤ t c) (heta : ∀ c, 0 ≤ eta c)
    (hkappa : ∀ c, 0 ≤ finiteJointMeanVarianceKappa n (eta c))
    (hw : ∀ c, 0 < w c) (hw_summable : Summable w)
    {delta : ℝ} (S : Fin n → Z)
    (hS : S ∉ countableJointMeanVarianceCatalogBadSamples
      n p prior ell t eta w delta)
    (c : ℕ) (htc : 0 < t c)
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationRisk p ell) ≤
      posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S) +
        (klDiv rho prior + Real.log (1 / (delta * w c))) /
          (t c * (n : ℝ)) +
        (eta c / t c) *
          posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) +
        finiteJointMeanVarianceXi n (t c) (eta c) / t c := by
  have hsingleton := finiteSingleton_not_mem_of_countable_not_mem
    hn p hp hprior.toIsPMF ell hell ht heta hkappa hw hw_summable S hS c
  simpa using
    (finiteJointMeanVariance_posteriorRisk_le_with_xi_of_not_mem
      (κ := Unit) (t := fun _ : Unit => t c)
      (eta := fun _ : Unit => eta c) (w := fun _ : Unit => w c)
      hn p hp hprior ell hell (fun _ => hw c) S hsingleton () htc
        (hkappa c) hrho)

/-- A sample- and posterior-dependent natural-number selector may choose any
positive-tilt catalog entry after observing the same countable good event. -/
theorem countableJointMeanVariance_posteriorRisk_le_with_xi_selected_of_not_mem
    [Fintype Z] [DecidableEq Z] [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {t eta w : ℕ → ℝ}
    (ht_pos : ∀ c, 0 < t c) (heta : ∀ c, 0 ≤ eta c)
    (hkappa : ∀ c, 0 ≤ finiteJointMeanVarianceKappa n (eta c))
    (hw : ∀ c, 0 < w c) (hw_summable : Summable w)
    (select : (Fin n → Z) → (ι → ℝ) → ℕ)
    {delta : ℝ} (S : Fin n → Z)
    (hS : S ∉ countableJointMeanVarianceCatalogBadSamples
      n p prior ell t eta w delta)
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationRisk p ell) ≤
      posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S) +
        (klDiv rho prior +
            Real.log (1 / (delta * w (select S rho)))) /
          (t (select S rho) * (n : ℝ)) +
        (eta (select S rho) / t (select S rho)) *
          posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) +
        finiteJointMeanVarianceXi n
            (t (select S rho)) (eta (select S rho)) /
          t (select S rho) := by
  exact countableJointMeanVariance_posteriorRisk_le_with_xi_of_not_mem
    hn p hp hprior ell hell (fun c => (ht_pos c).le) heta hkappa hw
      hw_summable S hS (select S rho) (ht_pos (select S rho)) hrho

end

end FormalSLT.PACBayes.CountableJointMeanVariancePosterior
