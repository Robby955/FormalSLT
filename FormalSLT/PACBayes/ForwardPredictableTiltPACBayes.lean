/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.AnytimeValid.ForwardPredictableTiltEmpiricalBernstein
import FormalSLT.PACBayes.TimeUniformScorePACBayes

/-!
# Predictable-tilt empirical-Bernstein PAC-Bayes bounds

This module lifts the lower-tail predictable-tilt empirical-Bernstein process
to a finite-hypothesis PAC-Bayes statement. Each hypothesis is assigned one
predictable tilt rule before the path is observed. A single outer-mass event
then controls every natural time and every posterior PMF, including a posterior
selected after observing the path.

The checked inequality retains the weighted linear and quadratic sums produced
by the predictable tilts. It does not select a new tilt schedule after observing
the path, and it does not claim an unweighted hybrid-Bessel boundary.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.TimeUniformScore
open scoped BigOperators

namespace FormalSLT.PACBayes.ForwardPredictableTiltPACBayes

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ mΩ}

/-- Per-hypothesis lower-tail empirical-Bernstein score for a predictable tilt
rule. Its exponential is the corresponding lower-tail e-process. -/
def forwardPredictableTiltPACBayesScore
    (X mean lambda : ι → ℕ → Ω → ℝ)
    (i : ι) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n,
    (lambda i k ω * (mean i k ω - X i k ω) -
      forwardEmpiricalBernsteinPsi (lambda i k ω) *
        (X i k ω - forwardPredictorProcess (X i) k ω) ^ 2)

/-- Posterior average of the predictable-tilt weighted conditional-mean minus
observation gaps. -/
def forwardPredictableTiltPosteriorMeanGap
    (posterior : ι → ℝ) (X mean lambda : ι → ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  posteriorAverage posterior fun i ↦
    ∑ k ∈ Finset.range n,
      lambda i k ω * (mean i k ω - X i k ω)

/-- Posterior average of the observable predictable quadratic penalties. -/
def forwardPredictableTiltPosteriorQuadraticPenalty
    (posterior : ι → ℝ) (X lambda : ι → ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  posteriorAverage posterior fun i ↦
    ∑ k ∈ Finset.range n,
      forwardEmpiricalBernsteinPsi (lambda i k ω) *
        (X i k ω - forwardPredictorProcess (X i) k ω) ^ 2

omit [DecidableEq ι] [Nonempty ι] in
/-- Exact decomposition of the posterior score into its weighted mean gap and
observable quadratic penalty. -/
theorem posteriorAverage_forwardPredictableTiltPACBayesScore
    (posterior : ι → ℝ) (X mean lambda : ι → ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    posteriorAverage posterior
        (fun i ↦ forwardPredictableTiltPACBayesScore X mean lambda i n ω) =
      forwardPredictableTiltPosteriorMeanGap
          posterior X mean lambda n ω -
        forwardPredictableTiltPosteriorQuadraticPenalty
          posterior X lambda n ω := by
  unfold forwardPredictableTiltPACBayesScore
    forwardPredictableTiltPosteriorMeanGap
    forwardPredictableTiltPosteriorQuadraticPenalty
  unfold posteriorAverage
  simp_rw [Finset.sum_sub_distrib, mul_sub]
  rw [Finset.sum_sub_distrib]

/-- Failure of the predictable-tilt PAC-Bayes score inequality at some time and
posterior. The tilt rules themselves remain fixed inputs to the event. -/
def forwardPredictableTiltPACBayesAnyPosteriorFailure
    (prior : ι → ℝ) (X mean lambda : ι → ℕ → Ω → ℝ)
    (delta : ℝ) : Set Ω :=
  timeUniformScorePACBayesAnyPosteriorFailure prior
    (forwardPredictableTiltPACBayesScore X mean lambda) delta

omit [DecidableEq ι] in
/-- One outer-mass event controls every time and every posterior PMF for the
predeclared family of predictable tilt rules. -/
theorem forwardPredictableTiltPACBayesAnyPosteriorFailure_mass_le_delta
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {X mean lambda : ι → ℕ → Ω → ℝ} {L delta : ℝ}
    (hL1 : L < 1) (hdelta : 0 < delta)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hmean_adapted : ∀ i, StronglyAdapted ℱ (mean i))
    (hlambda_adapted : ∀ i, StronglyAdapted ℱ (lambda i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hlambda_range : ∀ i k ω,
      0 ≤ lambda i k ω ∧ lambda i k ω ≤ L)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] mean i k) :
    μ.real
        (forwardPredictableTiltPACBayesAnyPosteriorFailure
          prior X mean lambda delta) ≤
      delta := by
  unfold forwardPredictableTiltPACBayesAnyPosteriorFailure
  apply timeUniformScorePACBayes_allPosteriors_bound
    (μ := μ) (ℱ := ℱ) hprior ?_ hdelta
  intro i
  have hE :=
    forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_eProcess_of_bounded
      (F := ℱ) (X := X i) (mean := mean i) (lambda := lambda i)
      hL1 (hX_adapted i) (hmean_adapted i) (hlambda_adapted i)
      (hX_unit i) (hlambda_range i) (hmean i)
  have hprocess :
      (fun n ω ↦ Real.exp
        (forwardPredictableTiltPACBayesScore X mean lambda i n ω)) =
        forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
          (X i) (mean i) (lambda i) := by
    funext n ω
    symm
    simpa [forwardPredictableTiltPACBayesScore] using
      (forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_eq
        (X i) (mean i) (lambda i) n ω)
  rw [hprocess]
  exact hE

omit [DecidableEq ι] [Nonempty ι] in
/-- Outside the common failure event, the weighted posterior mean gap is
controlled simultaneously for every posterior and every natural time. -/
theorem forwardPredictableTiltPACBayes_allPosteriors_of_not_mem
    {prior : ι → ℝ} {X mean lambda : ι → ℕ → Ω → ℝ} {delta : ℝ}
    {ω : Ω}
    (hω : ω ∉ forwardPredictableTiltPACBayesAnyPosteriorFailure
      prior X mean lambda delta) :
    ∀ posterior : ι → ℝ, IsPMF posterior → ∀ n : ℕ,
      forwardPredictableTiltPosteriorMeanGap
          posterior X mean lambda n ω <
        klDiv posterior prior + Real.log (1 / delta) +
          forwardPredictableTiltPosteriorQuadraticPenalty
            posterior X lambda n ω := by
  intro posterior hposterior n
  have hscore :
      posteriorAverage posterior
          (fun i ↦ forwardPredictableTiltPACBayesScore X mean lambda i n ω) <
        klDiv posterior prior + Real.log (1 / delta) := by
    apply lt_of_not_ge
    intro hfail
    apply hω
    exact ⟨n, posterior, hposterior, hfail⟩
  rw [posteriorAverage_forwardPredictableTiltPACBayesScore] at hscore
  linarith

omit [DecidableEq ι] [Nonempty ι] in
/-- A path- and time-dependent posterior may be substituted into the common
event. This is pointwise posterior selection, not post-hoc tilt-rule selection. -/
theorem forwardPredictableTiltPACBayes_selected_of_not_mem
    {prior : ι → ℝ} {X mean lambda : ι → ℕ → Ω → ℝ} {delta : ℝ}
    {ω : Ω}
    (hω : ω ∉ forwardPredictableTiltPACBayesAnyPosteriorFailure
      prior X mean lambda delta)
    (posterior : Ω → ℕ → ι → ℝ)
    (hposterior : ∀ ω n, IsPMF (posterior ω n))
    (n : ℕ) :
    forwardPredictableTiltPosteriorMeanGap
        (posterior ω n) X mean lambda n ω <
      klDiv (posterior ω n) prior + Real.log (1 / delta) +
        forwardPredictableTiltPosteriorQuadraticPenalty
          (posterior ω n) X lambda n ω :=
  forwardPredictableTiltPACBayes_allPosteriors_of_not_mem
    hω (posterior ω n) (hposterior ω n) n

omit [DecidableEq ι] in
/-- One outer-probability good event carries the predictable-tilt PAC-Bayes
bound simultaneously for every natural time and every posterior PMF. -/
theorem exists_forwardPredictableTiltPACBayes_event
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {X mean lambda : ι → ℕ → Ω → ℝ} {L delta : ℝ}
    (hL1 : L < 1) (hdelta : 0 < delta)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hmean_adapted : ∀ i, StronglyAdapted ℱ (mean i))
    (hlambda_adapted : ∀ i, StronglyAdapted ℱ (lambda i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hlambda_range : ∀ i k ω,
      0 ≤ lambda i k ω ∧ lambda i k ω ≤ L)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] mean i k) :
    ∃ goodEvent : Set Ω,
      μ.real goodEventᶜ ≤ delta ∧
        ∀ ω ∈ goodEvent, ∀ posterior : ι → ℝ, IsPMF posterior →
          ∀ n : ℕ,
            forwardPredictableTiltPosteriorMeanGap
                posterior X mean lambda n ω <
              klDiv posterior prior + Real.log (1 / delta) +
                forwardPredictableTiltPosteriorQuadraticPenalty
                  posterior X lambda n ω := by
  let badEvent := forwardPredictableTiltPACBayesAnyPosteriorFailure
    prior X mean lambda delta
  refine ⟨badEventᶜ, ?_, ?_⟩
  · simpa [badEvent] using
      (forwardPredictableTiltPACBayesAnyPosteriorFailure_mass_le_delta
        hprior hL1 hdelta hX_adapted hmean_adapted hlambda_adapted
          hX_unit hlambda_range hmean)
  · intro ω hω
    apply forwardPredictableTiltPACBayes_allPosteriors_of_not_mem
    simpa [badEvent] using hω

end

end FormalSLT.PACBayes.ForwardPredictableTiltPACBayes
