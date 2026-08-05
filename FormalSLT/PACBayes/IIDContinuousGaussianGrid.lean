/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayes.IIDContinuousGaussian

/-!
# Finite catalogs of i.i.d. Gaussian PAC-Bayes bounds

This module makes finite, data-dependent model selection explicit for the
continuous-hypothesis Gaussian PAC-Bayes theorem.  A catalog entry contains a
fixed spherical-Gaussian posterior, sub-Gamma tilt, and confidence budget.  A
finite union bound produces one exceptional event on which every catalog entry
is valid simultaneously.

Consequently, a selector may choose an entry after observing the sample path.
The total failure probability is the sum of the entrywise budgets.  This is a
finite-catalog result: it does not assert simultaneous validity over every
Gaussian posterior or every real-valued tilt.
-/

open MeasureTheory ProbabilityTheory
open Finset BigOperators

namespace FormalSLT.PACBayes.IIDContinuousGaussianGrid

open IIDContinuousGaussian

noncomputable section

variable {Z Ω κ : Type*}

/-- Failure of at least one entry in a catalog of fixed Gaussian posteriors,
tilts, and confidence budgets. -/
def timeUniformIIDGaussianPACBayesGridUpperFailure [MeasurableSpace Z]
    {d : ℕ} (dataLaw : Measure Z) (prior : SphericalGaussianParams d)
    (posterior : κ → SphericalGaussianParams d)
    (loss : GaussianParameterSpace d → Z → ℝ) (sample : ℕ → Ω → Z)
    (lam delta : κ → ℝ) : Set Ω :=
  ⋃ j : κ, timeUniformIIDGaussianPACBayesUpperFailure
    dataLaw prior (posterior j) loss sample (lam j) (delta j)

/-- Failure of the catalog entry chosen from the observed sample path. -/
def timeUniformIIDGaussianPACBayesSelectedUpperFailure [MeasurableSpace Z]
    {d : ℕ} (dataLaw : Measure Z) (prior : SphericalGaussianParams d)
    (posterior : κ → SphericalGaussianParams d)
    (loss : GaussianParameterSpace d → Z → ℝ) (sample : ℕ → Ω → Z)
    (lam delta : κ → ℝ) (select : Ω → κ) : Set Ω :=
  {ω | ∃ j : κ, select ω = j ∧
    ω ∈ timeUniformIIDGaussianPACBayesUpperFailure
      dataLaw prior (posterior j) loss sample (lam j) (delta j)}

/-- Membership in the selected event is exactly failure of the entry returned
by the selector. -/
theorem mem_timeUniformIIDGaussianPACBayesSelectedUpperFailure_iff
    [MeasurableSpace Z] {d : ℕ}
    {dataLaw : Measure Z} {prior : SphericalGaussianParams d}
    {posterior : κ → SphericalGaussianParams d}
    {loss : GaussianParameterSpace d → Z → ℝ} {sample : ℕ → Ω → Z}
    {lam delta : κ → ℝ} {select : Ω → κ} {ω : Ω} :
    ω ∈ timeUniformIIDGaussianPACBayesSelectedUpperFailure
        dataLaw prior posterior loss sample lam delta select ↔
      ω ∈ timeUniformIIDGaussianPACBayesUpperFailure
        dataLaw prior (posterior (select ω)) loss sample
          (lam (select ω)) (delta (select ω)) := by
  constructor
  · rintro ⟨j, hj, hfail⟩
    subst j
    exact hfail
  · intro hfail
    exact ⟨select ω, rfl, hfail⟩

/-- Every fixed catalog failure event is contained in the simultaneous event. -/
theorem timeUniformIIDGaussianPACBayesUpperFailure_subset_grid
    [MeasurableSpace Z] {d : ℕ}
    {dataLaw : Measure Z} {prior : SphericalGaussianParams d}
    {posterior : κ → SphericalGaussianParams d}
    {loss : GaussianParameterSpace d → Z → ℝ} {sample : ℕ → Ω → Z}
    {lam delta : κ → ℝ} (j : κ) :
    timeUniformIIDGaussianPACBayesUpperFailure
        dataLaw prior (posterior j) loss sample (lam j) (delta j)
      ⊆ timeUniformIIDGaussianPACBayesGridUpperFailure
        dataLaw prior posterior loss sample lam delta := by
  exact Set.subset_iUnion (fun j : κ =>
    timeUniformIIDGaussianPACBayesUpperFailure
      dataLaw prior (posterior j) loss sample (lam j) (delta j)) j

/-- A sample-dependent selected failure is contained in the simultaneous
catalog failure event.  No measurability assumption on the selector is needed
for this set-theoretic reduction. -/
theorem timeUniformIIDGaussianPACBayesSelectedUpperFailure_subset_grid
    [MeasurableSpace Z] {d : ℕ}
    {dataLaw : Measure Z} {prior : SphericalGaussianParams d}
    {posterior : κ → SphericalGaussianParams d}
    {loss : GaussianParameterSpace d → Z → ℝ} {sample : ℕ → Ω → Z}
    {lam delta : κ → ℝ} {select : Ω → κ} :
    timeUniformIIDGaussianPACBayesSelectedUpperFailure
        dataLaw prior posterior loss sample lam delta select
      ⊆ timeUniformIIDGaussianPACBayesGridUpperFailure
        dataLaw prior posterior loss sample lam delta := by
  intro ω hω
  rcases hω with ⟨j, _hselect, hj⟩
  exact Set.mem_iUnion.2 ⟨j, hj⟩

/-- Simultaneous time-uniform i.i.d. PAC-Bayes bound for a finite catalog of
spherical-Gaussian posteriors and sub-Gamma tilts.

Each entry `j` receives its own positive budget `delta j`.  The exceptional
event on which any catalog bound fails has probability at most
`∑ j, delta j`.  All entries share the same prior, data law, bounded loss, and
i.i.d. sample stream. -/
theorem timeUniformIIDGaussianPACBayes_grid_bound
    {d : ℕ} [Fintype κ]
    [mZ : MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [TopologicalSpace.MetrizableSpace Z]
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {dataLaw : Measure Z} [IsProbabilityMeasure dataLaw]
    (prior : SphericalGaussianParams d)
    (posterior : κ → SphericalGaussianParams d)
    {loss : GaussianParameterSpace d → Z → ℝ}
    {sample : ℕ → Ω → Z} {lam delta : κ → ℝ}
    (hdelta : ∀ j, 0 < delta j)
    (hlam : ∀ j, 0 < lam j) (hlam_three : ∀ j, lam j < 3)
    (hloss_joint : StronglyMeasurable
      (fun p : GaussianParameterSpace d × Z => loss p.1 p.2))
    (hloss_range : ∀ θ z, 0 ≤ loss θ z ∧ loss θ z ≤ 1)
    (hsample : ∀ k, StronglyMeasurable (sample k))
    (hsample_indep : iIndepFun sample μ)
    (hsample_law : ∀ k, HasLaw (sample k) dataLaw μ) :
    μ.real (timeUniformIIDGaussianPACBayesGridUpperFailure
      dataLaw prior posterior loss sample lam delta) ≤ ∑ j, delta j := by
  classical
  unfold timeUniformIIDGaussianPACBayesGridUpperFailure
  calc
    μ.real (⋃ j : κ, timeUniformIIDGaussianPACBayesUpperFailure
        dataLaw prior (posterior j) loss sample (lam j) (delta j))
        ≤ ∑ j : κ, μ.real (timeUniformIIDGaussianPACBayesUpperFailure
          dataLaw prior (posterior j) loss sample (lam j) (delta j)) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ j : κ, delta j := by
      apply Finset.sum_le_sum
      intro j _hj
      exact timeUniformIIDGaussianPACBayes_bound
        (μ := μ) (dataLaw := dataLaw) prior (posterior j)
        (hdelta j) (hlam j) (hlam_three j)
        hloss_joint hloss_range hsample hsample_indep hsample_law

/-- A total confidence budget may be supplied separately from the entrywise
budgets. -/
theorem timeUniformIIDGaussianPACBayes_grid_bound_of_sum_le
    {d : ℕ} [Fintype κ]
    [mZ : MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [TopologicalSpace.MetrizableSpace Z]
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {dataLaw : Measure Z} [IsProbabilityMeasure dataLaw]
    (prior : SphericalGaussianParams d)
    (posterior : κ → SphericalGaussianParams d)
    {loss : GaussianParameterSpace d → Z → ℝ}
    {sample : ℕ → Ω → Z} {lam delta : κ → ℝ} {totalDelta : ℝ}
    (hdelta : ∀ j, 0 < delta j)
    (hlam : ∀ j, 0 < lam j) (hlam_three : ∀ j, lam j < 3)
    (hbudget : ∑ j, delta j ≤ totalDelta)
    (hloss_joint : StronglyMeasurable
      (fun p : GaussianParameterSpace d × Z => loss p.1 p.2))
    (hloss_range : ∀ θ z, 0 ≤ loss θ z ∧ loss θ z ≤ 1)
    (hsample : ∀ k, StronglyMeasurable (sample k))
    (hsample_indep : iIndepFun sample μ)
    (hsample_law : ∀ k, HasLaw (sample k) dataLaw μ) :
    μ.real (timeUniformIIDGaussianPACBayesGridUpperFailure
      dataLaw prior posterior loss sample lam delta) ≤ totalDelta := by
  exact (timeUniformIIDGaussianPACBayes_grid_bound
    (μ := μ) (dataLaw := dataLaw) prior posterior
    hdelta hlam hlam_three hloss_joint hloss_range
    hsample hsample_indep hsample_law).trans hbudget

/-- Any sample-dependent choice from the finite catalog inherits the sum of
the entrywise confidence budgets. -/
theorem timeUniformIIDGaussianPACBayes_selected_bound
    {d : ℕ} [Fintype κ]
    [mZ : MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [TopologicalSpace.MetrizableSpace Z]
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {dataLaw : Measure Z} [IsProbabilityMeasure dataLaw]
    (prior : SphericalGaussianParams d)
    (posterior : κ → SphericalGaussianParams d)
    {loss : GaussianParameterSpace d → Z → ℝ}
    {sample : ℕ → Ω → Z} {lam delta : κ → ℝ} (select : Ω → κ)
    (hdelta : ∀ j, 0 < delta j)
    (hlam : ∀ j, 0 < lam j) (hlam_three : ∀ j, lam j < 3)
    (hloss_joint : StronglyMeasurable
      (fun p : GaussianParameterSpace d × Z => loss p.1 p.2))
    (hloss_range : ∀ θ z, 0 ≤ loss θ z ∧ loss θ z ≤ 1)
    (hsample : ∀ k, StronglyMeasurable (sample k))
    (hsample_indep : iIndepFun sample μ)
    (hsample_law : ∀ k, HasLaw (sample k) dataLaw μ) :
    μ.real (timeUniformIIDGaussianPACBayesSelectedUpperFailure
      dataLaw prior posterior loss sample lam delta select) ≤ ∑ j, delta j := by
  calc
    μ.real (timeUniformIIDGaussianPACBayesSelectedUpperFailure
        dataLaw prior posterior loss sample lam delta select)
        ≤ μ.real (timeUniformIIDGaussianPACBayesGridUpperFailure
          dataLaw prior posterior loss sample lam delta) :=
      measureReal_mono
        timeUniformIIDGaussianPACBayesSelectedUpperFailure_subset_grid
        (measure_ne_top μ _)
    _ ≤ ∑ j, delta j := timeUniformIIDGaussianPACBayes_grid_bound
      (μ := μ) (dataLaw := dataLaw) prior posterior
      hdelta hlam hlam_three hloss_joint hloss_range
      hsample hsample_indep hsample_law

/-- Budgeted form of the data-dependent selector theorem. -/
theorem timeUniformIIDGaussianPACBayes_selected_bound_of_sum_le
    {d : ℕ} [Fintype κ]
    [mZ : MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [TopologicalSpace.MetrizableSpace Z]
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {dataLaw : Measure Z} [IsProbabilityMeasure dataLaw]
    (prior : SphericalGaussianParams d)
    (posterior : κ → SphericalGaussianParams d)
    {loss : GaussianParameterSpace d → Z → ℝ}
    {sample : ℕ → Ω → Z} {lam delta : κ → ℝ} {totalDelta : ℝ}
    (select : Ω → κ)
    (hdelta : ∀ j, 0 < delta j)
    (hlam : ∀ j, 0 < lam j) (hlam_three : ∀ j, lam j < 3)
    (hbudget : ∑ j, delta j ≤ totalDelta)
    (hloss_joint : StronglyMeasurable
      (fun p : GaussianParameterSpace d × Z => loss p.1 p.2))
    (hloss_range : ∀ θ z, 0 ≤ loss θ z ∧ loss θ z ≤ 1)
    (hsample : ∀ k, StronglyMeasurable (sample k))
    (hsample_indep : iIndepFun sample μ)
    (hsample_law : ∀ k, HasLaw (sample k) dataLaw μ) :
    μ.real (timeUniformIIDGaussianPACBayesSelectedUpperFailure
      dataLaw prior posterior loss sample lam delta select) ≤ totalDelta := by
  exact (timeUniformIIDGaussianPACBayes_selected_bound
    (μ := μ) (dataLaw := dataLaw) prior posterior select
    hdelta hlam hlam_three hloss_joint hloss_range
    hsample hsample_indep hsample_law).trans hbudget

/-! ### Evaluated two-candidate stochastic certificate -/

/-- A two-entry posterior catalog containing `N(0,1)` and `N(1,1)`. -/
def twoGaussianPosteriorCatalog : Bool → SphericalGaussianParams 1
  | false => standardGaussianPrior
  | true => shiftedGaussianPosterior

/-- The two catalog entries use distinct admissible sub-Gamma tilts. -/
def twoGaussianTiltCatalog : Bool → ℝ
  | false => (1 : ℝ) / 2
  | true => (1 : ℝ) / 4

/-- Each of the two entries receives half of the total `exp(-1)` budget. -/
def twoGaussianDeltaCatalog (_j : Bool) : ℝ := Real.exp (-1) / 2

/-- The two entrywise confidence budgets sum exactly to `exp(-1)`. -/
theorem twoGaussianDeltaCatalog_sum :
    ∑ j : Bool, twoGaussianDeltaCatalog j = Real.exp (-1) := by
  simp [twoGaussianDeltaCatalog]
  ring

/--
Concrete simultaneous certificate for two Gaussian posterior/tilt candidates
on the nonconstant fair-Bernoulli model.  One exceptional event controls both
`N(0,1)` at tilt `1/2` and `N(1,1)` at tilt `1/4`, with total failure
probability at most `exp(-1)`.
-/
theorem fairBoolThreshold_twoGaussianGrid_certificate :
    fairBoolStreamLaw.real
        (timeUniformIIDGaussianPACBayesGridUpperFailure
          fairBoolLaw standardGaussianPrior twoGaussianPosteriorCatalog
          gaussianThresholdBoolLoss fairBoolCoordinateSample
          twoGaussianTiltCatalog twoGaussianDeltaCatalog) ≤
      Real.exp (-1) := by
  letI := fairBoolLaw_isProbabilityMeasure
  letI := fairBoolStreamLaw_isProbabilityMeasure
  refine timeUniformIIDGaussianPACBayes_grid_bound_of_sum_le
    (μ := fairBoolStreamLaw) (dataLaw := fairBoolLaw)
    standardGaussianPrior twoGaussianPosteriorCatalog
    (loss := gaussianThresholdBoolLoss) (sample := fairBoolCoordinateSample)
    (lam := twoGaussianTiltCatalog) (delta := twoGaussianDeltaCatalog)
    (totalDelta := Real.exp (-1)) ?_ ?_ ?_ ?_
    gaussianThresholdBoolLoss_stronglyMeasurable
    gaussianThresholdBoolLoss_range ?_ fairBoolCoordinateSample_iIndep ?_
  · intro j
    simp [twoGaussianDeltaCatalog]
    positivity
  · intro j
    cases j <;> norm_num [twoGaussianTiltCatalog]
  · intro j
    cases j <;> norm_num [twoGaussianTiltCatalog]
  · exact twoGaussianDeltaCatalog_sum.le
  · intro k
    exact (measurable_pi_apply k).stronglyMeasurable
  · exact fairBoolCoordinateSample_hasLaw

/-- Every sample-dependent selector between the two worked candidates inherits
the same `exp(-1)` total failure bound. -/
theorem fairBoolThreshold_twoGaussianSelected_certificate
    (select : FairBoolStream → Bool) :
    fairBoolStreamLaw.real
        (timeUniformIIDGaussianPACBayesSelectedUpperFailure
          fairBoolLaw standardGaussianPrior twoGaussianPosteriorCatalog
          gaussianThresholdBoolLoss fairBoolCoordinateSample
          twoGaussianTiltCatalog twoGaussianDeltaCatalog select) ≤
      Real.exp (-1) := by
  letI := fairBoolStreamLaw_isProbabilityMeasure
  calc
    fairBoolStreamLaw.real
        (timeUniformIIDGaussianPACBayesSelectedUpperFailure
          fairBoolLaw standardGaussianPrior twoGaussianPosteriorCatalog
          gaussianThresholdBoolLoss fairBoolCoordinateSample
          twoGaussianTiltCatalog twoGaussianDeltaCatalog select)
        ≤ fairBoolStreamLaw.real
          (timeUniformIIDGaussianPACBayesGridUpperFailure
            fairBoolLaw standardGaussianPrior twoGaussianPosteriorCatalog
            gaussianThresholdBoolLoss fairBoolCoordinateSample
            twoGaussianTiltCatalog twoGaussianDeltaCatalog) :=
      measureReal_mono
        timeUniformIIDGaussianPACBayesSelectedUpperFailure_subset_grid
        (measure_ne_top fairBoolStreamLaw _)
    _ ≤ Real.exp (-1) := fairBoolThreshold_twoGaussianGrid_certificate

end

end FormalSLT.PACBayes.IIDContinuousGaussianGrid
