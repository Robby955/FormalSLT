/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.ForwardBesselPACBayes
import FormalSLT.PACBayes.TimeUniformIID

/-!
# Forward-Bessel PAC-Bayes for i.i.d. bounded losses

This module specializes the finite-hypothesis forward-Bessel master process to
an i.i.d. stream and measurable `[0,1]` losses.  Increment `k` is the raw loss
at sample coordinate `k + 1`; consequently the first `n` increments are exactly
the observations used by `iidLossEmpiricalRisk`.

The stochastic process is still the predictable-residual e-process from
`ForwardBesselProcess`.  The posterior hybrid-Bessel term remains only its
observable lower-envelope penalty.  One atTop crossing event supports every
time `n >= 2`, every posterior PMF, and every predeclared tilt atom.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open scoped BigOperators

namespace FormalSLT.PACBayes.ForwardBesselPACBayesIID

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

open FormalSLT.PACBayes.TimeUniformIID
open FormalSLT.PACBayes.ForwardBesselPACBayes

variable {ι κ Z Ω : Type*}
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]

/-- Raw loss revealed by increment `k`.  The shift by one matches the natural
filtration convention used throughout the time-uniform IID modules. -/
def iidObservedLoss
    (loss : ι → Z → ℝ) (sample : ℕ → Ω → Z)
    (i : ι) (k : ℕ) (ω : Ω) : ℝ :=
  loss i (sample (k + 1) ω)

omit [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ] in
/-- The forward prefix mean of the raw-loss process is definitionally the IID
empirical risk. -/
theorem forwardPrefixMean_iidObservedLoss
    (loss : ι → Z → ℝ) (sample : ℕ → Ω → Z)
    (i : ι) (n : ℕ) (ω : Ω) :
    forwardPrefixMean (fun k ↦ iidObservedLoss loss sample i k ω) n =
      iidLossEmpiricalRisk loss sample i n ω := by
  rfl

omit [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ] in
/-- Posterior averaging preserves the raw-loss prefix/empirical-risk identity. -/
theorem posteriorAverage_forwardPrefixMean_iidObservedLoss
    (loss : ι → Z → ℝ) (sample : ℕ → Ω → Z)
    (posterior : ι → ℝ) (n : ℕ) (ω : Ω) :
    posteriorAverage posterior
        (fun i ↦ forwardPrefixMean
          (fun k ↦ iidObservedLoss loss sample i k ω) n) =
      iidPosteriorEmpiricalRisk loss sample posterior n ω := by
  rfl

omit [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ] in
/-- Raw IID losses are increment-adapted to the natural sample filtration. -/
theorem iidObservedLoss_incrementAdapted
    [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [TopologicalSpace.MetrizableSpace Z]
    [mΩ : MeasurableSpace Ω]
    {loss : ι → Z → ℝ} {sample : ℕ → Ω → Z}
    (i : ι) (hloss : StronglyMeasurable (loss i))
    (hsample : ∀ j, StronglyMeasurable (sample j)) :
    IncrementAdapted (Filtration.natural sample hsample)
      (iidObservedLoss loss sample i) := by
  have hsample_adapted := Filtration.stronglyAdapted_natural hsample
  intro k
  exact hloss.comp_measurable
    (hsample_adapted (k + 1)).measurable

omit [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ] in
/-- A raw `[0,1]` IID loss is integrable under a finite path measure. -/
theorem iidObservedLoss_integrable
    [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [TopologicalSpace.MetrizableSpace Z]
    [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {loss : ι → Z → ℝ} {sample : ℕ → Ω → Z}
    (i : ι) (k : ℕ) (hloss : StronglyMeasurable (loss i))
    (hloss_range : ∀ z, 0 ≤ loss i z ∧ loss i z ≤ 1)
    (hsample : ∀ j, StronglyMeasurable (sample j)) :
    Integrable (iidObservedLoss loss sample i k) μ := by
  refine Integrable.of_bound
    (hloss.comp_measurable
      (hsample (k + 1)).measurable).aestronglyMeasurable 1 ?_
  exact Filter.Eventually.of_forall fun ω ↦ by
    simp only [iidObservedLoss]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (hloss_range (sample (k + 1) ω)).1]
    exact (hloss_range (sample (k + 1) ω)).2

omit [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ] in
/-- The conditional mean of a raw IID loss is its population risk.  This is
derived from the existing centered-gap conditional-mean theorem. -/
theorem iidObservedLoss_condExp_eq_populationRisk
    [mZ : MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [TopologicalSpace.MetrizableSpace Z]
    [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {dataLaw : Measure Z} [IsProbabilityMeasure dataLaw]
    {loss : ι → Z → ℝ} {sample : ℕ → Ω → Z}
    (i : ι) (k : ℕ) (hloss : StronglyMeasurable (loss i))
    (hloss_range : ∀ z, 0 ≤ loss i z ∧ loss i z ≤ 1)
    (hsample : ∀ j, StronglyMeasurable (sample j))
    (hsample_indep : iIndepFun sample μ)
    (hsample_law : ∀ j, HasLaw (sample j) dataLaw μ) :
    μ[iidObservedLoss loss sample i k |
        Filtration.natural sample hsample k] =ᵐ[μ]
      fun _ ↦ iidLossPopulationRisk dataLaw loss i := by
  let ℱ : Filtration ℕ mΩ := Filtration.natural sample hsample
  have hX_int : Integrable (iidObservedLoss loss sample i k) μ :=
    iidObservedLoss_integrable i k hloss hloss_range hsample
  have hgap := iidLossGap_condExp_eq_zero
    i k hloss hloss_range hsample hsample_indep hsample_law
  have hsub := condExp_sub
    (integrable_const (iidLossPopulationRisk dataLaw loss i))
    hX_int (ℱ k)
  filter_upwards [hgap, hsub] with ω hgapω hsubω
  change μ[(fun _ : Ω ↦ iidLossPopulationRisk dataLaw loss i) -
      iidObservedLoss loss sample i k | ℱ k] ω = 0 at hgapω
  rw [hsubω,
    condExp_const (ℱ.le k) (iidLossPopulationRisk dataLaw loss i)] at hgapω
  simp only [Pi.sub_apply] at hgapω
  linarith

/-- Observable IID specialization of the generic posterior boundary. -/
def forwardIIDBesselPACBayesBoundary
    (prior : ι → ℝ) (weight : κ → ℝ) (lam : κ → ℝ)
    (loss : ι → Z → ℝ) (sample : ℕ → Ω → Z)
    (posterior : ι → ℝ) (delta : ℝ)
    (j : κ) (n : ℕ) (ω : Ω) : ℝ :=
  forwardBesselPACBayesBoundary prior weight lam
    (iidObservedLoss loss sample) posterior delta j n ω

/-- The single IID exceptional event is the generic master crossing event for
the raw observed-loss process and its population-risk mean. -/
def forwardIIDBesselPACBayesExceptionalEvent
    [MeasurableSpace Z]
    (dataLaw : Measure Z) (prior : ι → ℝ) (weight : κ → ℝ)
    (loss : ι → Z → ℝ) (sample : ℕ → Ω → Z)
    (lam : κ → ℝ) (delta : ℝ) : Set Ω :=
  forwardBesselPACBayesExceptionalEvent prior weight
    (iidObservedLoss loss sample)
    (iidLossPopulationRisk dataLaw loss) lam delta

omit [Nonempty ι] [Nonempty κ] in
/-- One atTop IID exceptional event has outer probability at most `delta`. -/
theorem forwardIIDBesselPACBayesExceptionalEvent_mass_le_delta
    [mZ : MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [TopologicalSpace.MetrizableSpace Z]
    [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {dataLaw : Measure Z} [IsProbabilityMeasure dataLaw]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {loss : ι → Z → ℝ} {sample : ℕ → Ω → Z}
    {lam : κ → ℝ} {delta : ℝ}
    (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hloss : ∀ i, StronglyMeasurable (loss i))
    (hloss_range : ∀ i z, 0 ≤ loss i z ∧ loss i z ≤ 1)
    (hsample : ∀ k, StronglyMeasurable (sample k))
    (hsample_indep : iIndepFun sample μ)
    (hsample_law : ∀ k, HasLaw (sample k) dataLaw μ) :
    μ.real
        (forwardIIDBesselPACBayesExceptionalEvent
          dataLaw prior weight loss sample lam delta) ≤
      delta := by
  let ℱ : Filtration ℕ mΩ := Filtration.natural sample hsample
  exact forwardBesselPACBayesExceptionalEvent_mass_le_delta
    (μ := μ) (ℱ := ℱ) hprior hweight hdelta hlam hlam1
    (fun i ↦ iidObservedLoss_incrementAdapted i (hloss i) hsample)
    (fun i k ω ↦ hloss_range i (sample (k + 1) ω))
    (fun i k ↦ iidObservedLoss_condExp_eq_populationRisk
      i k (hloss i) (hloss_range i) hsample hsample_indep hsample_law)

omit [DecidableEq ι] [DecidableEq κ] [Nonempty κ] in
/-- Outside the common IID event, every posterior and declared tilt satisfies
the hybrid-Bessel PAC-Bayes risk bound at every `n >= 2`. -/
theorem forwardIIDBesselPACBayes_allPosteriors_of_not_mem
    [MeasurableSpace Z]
    {dataLaw : Measure Z}
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {loss : ι → Z → ℝ} {sample : ℕ → Ω → Z}
    {lam : κ → ℝ} {delta : ℝ}
    (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hloss_range : ∀ i z, 0 ≤ loss i z ∧ loss i z ≤ 1)
    {ω : Ω}
    (hω : ω ∉ forwardIIDBesselPACBayesExceptionalEvent
      dataLaw prior weight loss sample lam delta) :
    ∀ j : κ, ∀ posterior : ι → ℝ, IsPMF posterior →
      ∀ n : ℕ, 2 ≤ n →
        iidPosteriorPopulationRisk dataLaw loss posterior <
          iidPosteriorEmpiricalRisk loss sample posterior n ω +
            forwardIIDBesselPACBayesBoundary
              prior weight lam loss sample posterior delta j n ω := by
  intro j posterior hposterior n hn
  change posteriorAverage posterior (iidLossPopulationRisk dataLaw loss) <
    posteriorAverage posterior
        (fun i ↦ forwardPrefixMean
          (fun k ↦ loss i (sample (k + 1) ω)) n) +
      forwardBesselPACBayesBoundary prior weight lam
        (fun i k ω ↦ loss i (sample (k + 1) ω))
        posterior delta j n ω
  exact forwardBesselPACBayes_allPosteriors_of_not_mem
    hprior hweight hdelta hlam hlam1
    (fun i k ω ↦ hloss_range i (sample (k + 1) ω)) hω
    j posterior hposterior n hn

omit [DecidableEq ι] [DecidableEq κ] [Nonempty κ] in
/-- Explicit path-, time-, and posterior-dependent IID selector form. -/
theorem forwardIIDBesselPACBayes_selected_of_not_mem
    [MeasurableSpace Z]
    {dataLaw : Measure Z}
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {loss : ι → Z → ℝ} {sample : ℕ → Ω → Z}
    {lam : κ → ℝ} {delta : ℝ}
    (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hloss_range : ∀ i z, 0 ≤ loss i z ∧ loss i z ≤ 1)
    {ω : Ω}
    (hω : ω ∉ forwardIIDBesselPACBayesExceptionalEvent
      dataLaw prior weight loss sample lam delta)
    (posterior : Ω → ℕ → ι → ℝ)
    (hposterior : ∀ ω n, IsPMF (posterior ω n))
    (select : Ω → ℕ → (ι → ℝ) → κ)
    (n : ℕ) (hn : 2 ≤ n) :
    iidPosteriorPopulationRisk dataLaw loss (posterior ω n) <
      iidPosteriorEmpiricalRisk loss sample (posterior ω n) n ω +
        forwardIIDBesselPACBayesBoundary
          prior weight lam loss sample (posterior ω n) delta
            (select ω n (posterior ω n)) n ω :=
  forwardIIDBesselPACBayes_allPosteriors_of_not_mem
    hprior hweight hdelta hlam hlam1 hloss_range hω
    (select ω n (posterior ω n)) (posterior ω n)
    (hposterior ω n) n hn

omit [Nonempty κ] in
/-- End-to-end IID capstone: one event of outer mass at most `delta` carries
the bound for every eligible time, posterior PMF, and declared tilt. -/
theorem exists_forwardIIDBesselPACBayes_event
    [mZ : MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [TopologicalSpace.MetrizableSpace Z]
    [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {dataLaw : Measure Z} [IsProbabilityMeasure dataLaw]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {loss : ι → Z → ℝ} {sample : ℕ → Ω → Z}
    {lam : κ → ℝ} {delta : ℝ}
    (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hloss : ∀ i, StronglyMeasurable (loss i))
    (hloss_range : ∀ i z, 0 ≤ loss i z ∧ loss i z ≤ 1)
    (hsample : ∀ k, StronglyMeasurable (sample k))
    (hsample_indep : iIndepFun sample μ)
    (hsample_law : ∀ k, HasLaw (sample k) dataLaw μ) :
    ∃ goodEvent : Set Ω,
      μ.real goodEventᶜ ≤ delta ∧
        ∀ ω ∈ goodEvent, ∀ j : κ,
          ∀ posterior : ι → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              iidPosteriorPopulationRisk dataLaw loss posterior <
                iidPosteriorEmpiricalRisk loss sample posterior n ω +
                  forwardIIDBesselPACBayesBoundary
                    prior weight lam loss sample posterior delta j n ω := by
  let badEvent := forwardIIDBesselPACBayesExceptionalEvent
    dataLaw prior weight loss sample lam delta
  refine ⟨badEventᶜ, ?_, ?_⟩
  · simpa [badEvent] using
      (forwardIIDBesselPACBayesExceptionalEvent_mass_le_delta
        (μ := μ) (dataLaw := dataLaw) hprior hweight hdelta
        hlam hlam1 hloss hloss_range hsample hsample_indep hsample_law)
  · intro ω hω
    exact forwardIIDBesselPACBayes_allPosteriors_of_not_mem
      hprior hweight hdelta hlam hlam1 hloss_range hω

end

end FormalSLT.PACBayes.ForwardBesselPACBayesIID
