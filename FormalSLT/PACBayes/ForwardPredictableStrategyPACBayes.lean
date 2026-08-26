/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.ForwardPredictableTiltPACBayes
import FormalSLT.PACBayes.StabilityBridge

/-!
# Joint model--strategy predictable-tilt PAC-Bayes bounds

This module turns the finite predictable-tilt PAC-Bayes theorem into an
explicit model--strategy selection interface.  A finite catalog of predictable
strategies is declared before the path is observed.  One common event then
controls every time and every joint posterior on model--strategy pairs, so the
posterior may select both coordinates after observing the path.

The complexity term is the finite KL divergence from the selected joint
posterior to the product of the model prior and strategy prior.  This permits
post-data selection among the declared legal strategies; it does not permit a
strategy to inspect the current observation before choosing its current tilt,
and it does not cover a strategy invented outside the declared catalog.
Only the individual catalog members are predictable processes.  A joint
posterior selected after the path is observed is a valid reporting rule on the
common event; it is not itself a newly constructed predictable e-process.

The general normalized endpoint remains a tilt-weighted monitored mean.  A
separate corollary recovers ordinary posterior-averaged conditional risk when
the strategies are shared across models and each model has a constant
conditional mean.  The strategies in that corollary may still vary
predictably with time and observed history.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardPredictableTiltPACBayes
open FormalSLT.PACBayes.StabilityBridge
open Finset Real BigOperators

namespace FormalSLT.PACBayes.ForwardPredictableStrategyPACBayes

noncomputable section

variable {ι κ Ω : Type*}
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ mΩ}

/-! ## Product priors and lifted processes -/

/-- Independent product prior on model--strategy pairs. -/
def modelStrategyProductPrior
    (modelPrior : ι → ℝ) (strategyPrior : κ → ℝ) (p : ι × κ) : ℝ :=
  modelPrior p.1 * strategyPrior p.2

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ] in
/-- The independent product of two finite PMFs is a PMF. -/
theorem modelStrategyProductPrior_isPMF
    {modelPrior : ι → ℝ} (hmodel : IsPMF modelPrior)
    {strategyPrior : κ → ℝ} (hstrategy : IsPMF strategyPrior) :
    IsPMF (modelStrategyProductPrior modelPrior strategyPrior) := by
  classical
  refine { nonneg := ?_, sum_one := ?_ }
  · intro p
    exact mul_nonneg (hmodel.nonneg p.1) (hstrategy.nonneg p.2)
  · rw [Fintype.sum_prod_type]
    simp_rw [modelStrategyProductPrior, ← Finset.mul_sum]
    rw [hstrategy.sum_one]
    simpa using hmodel.sum_one

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ] in
/-- Full support is preserved by the independent finite product. -/
theorem modelStrategyProductPrior_isFullSupportPMF
    {modelPrior : ι → ℝ} (hmodel : IsFullSupportPMF modelPrior)
    {strategyPrior : κ → ℝ} (hstrategy : IsFullSupportPMF strategyPrior) :
    IsFullSupportPMF (modelStrategyProductPrior modelPrior strategyPrior) := by
  refine
    { toIsPMF := modelStrategyProductPrior_isPMF
        hmodel.toIsPMF hstrategy.toIsPMF
      pos := ?_ }
  intro p
  exact mul_pos (hmodel.pos p.1) (hstrategy.pos p.2)

omit [Nonempty ι] [Nonempty κ] in
/-- A selected model--strategy pair pays the sum of its model and strategy
log-prior penalties.  This makes the extra cost of post-data strategy
selection explicit for a point posterior. -/
theorem dirac_modelStrategyProductPrior_klDiv_eq
    {modelPrior : ι → ℝ} (hmodel : IsFullSupportPMF modelPrior)
    {strategyPrior : κ → ℝ} (hstrategy : IsFullSupportPMF strategyPrior)
    (i : ι) (j : κ) :
    klDiv (diracPosterior (i, j))
        (modelStrategyProductPrior modelPrior strategyPrior) =
      -Real.log (modelPrior i) + -Real.log (strategyPrior j) := by
  classical
  rw [diracPosterior_klDiv_eq_neg_log_prior]
  · rw [modelStrategyProductPrior,
      Real.log_mul (hmodel.pos i).ne' (hstrategy.pos j).ne']
    ring
  · exact mul_pos (hmodel.pos i) (hstrategy.pos j)

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ] in
/-- KL divergence is additive for independent model and strategy posteriors.
For correlated joint posteriors, the main theorems retain the full joint KL
instead of applying this specialization. -/
theorem klDiv_modelStrategyProductPrior
    {modelPosterior modelPrior : ι → ℝ}
    (hmodelPosterior : IsPMF modelPosterior)
    (hmodelPrior : IsFullSupportPMF modelPrior)
    {strategyPosterior strategyPrior : κ → ℝ}
    (hstrategyPosterior : IsPMF strategyPosterior)
    (hstrategyPrior : IsFullSupportPMF strategyPrior) :
    klDiv
        (modelStrategyProductPrior modelPosterior strategyPosterior)
        (modelStrategyProductPrior modelPrior strategyPrior) =
      klDiv modelPosterior modelPrior +
        klDiv strategyPosterior strategyPrior := by
  classical
  have hcell : ∀ i j,
      modelPosterior i * strategyPosterior j *
          Real.log
            ((modelPosterior i * strategyPosterior j) /
              (modelPrior i * strategyPrior j)) =
        strategyPosterior j *
            (modelPosterior i * Real.log (modelPosterior i / modelPrior i)) +
          modelPosterior i *
            (strategyPosterior j *
              Real.log (strategyPosterior j / strategyPrior j)) := by
    intro i j
    rcases eq_or_lt_of_le (hmodelPosterior.nonneg i) with hmodelZero | hmodelPos
    · simp [← hmodelZero]
    rcases eq_or_lt_of_le (hstrategyPosterior.nonneg j) with
      hstrategyZero | hstrategyPos
    · simp [← hstrategyZero]
    have hfactor :
        (modelPosterior i * strategyPosterior j) /
            (modelPrior i * strategyPrior j) =
          (modelPosterior i / modelPrior i) *
            (strategyPosterior j / strategyPrior j) := by
      field_simp
    rw [hfactor, Real.log_mul
      (div_ne_zero hmodelPos.ne' (hmodelPrior.pos i).ne')
      (div_ne_zero hstrategyPos.ne' (hstrategyPrior.pos j).ne')]
    ring
  unfold klDiv modelStrategyProductPrior
  rw [Fintype.sum_prod_type]
  simp_rw [hcell, Finset.sum_add_distrib]
  have hleft :
      (∑ i : ι, ∑ j : κ,
          strategyPosterior j *
            (modelPosterior i * Real.log (modelPosterior i / modelPrior i))) =
        ∑ i : ι,
          modelPosterior i * Real.log (modelPosterior i / modelPrior i) := by
    calc
      _ = ∑ i : ι, (∑ j : κ, strategyPosterior j) *
            (modelPosterior i * Real.log (modelPosterior i / modelPrior i)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.sum_mul]
      _ = _ := by rw [hstrategyPosterior.sum_one]; simp
  have hright :
      (∑ i : ι, ∑ j : κ,
          modelPosterior i *
            (strategyPosterior j *
              Real.log (strategyPosterior j / strategyPrior j))) =
        ∑ j : κ,
          strategyPosterior j *
            Real.log (strategyPosterior j / strategyPrior j) := by
    calc
      _ = ∑ i : ι, modelPosterior i *
            (∑ j : κ,
              strategyPosterior j *
                Real.log (strategyPosterior j / strategyPrior j)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
      _ = (∑ i : ι, modelPosterior i) *
            (∑ j : κ,
              strategyPosterior j *
                Real.log (strategyPosterior j / strategyPrior j)) := by
          rw [Finset.sum_mul]
      _ = _ := by rw [hmodelPosterior.sum_one, one_mul]
  rw [hleft, hright]

/-- Lift a model-indexed process to model--strategy pairs. -/
def modelStrategyProcess
    (X : ι → ℕ → Ω → ℝ) (p : ι × κ) : ℕ → Ω → ℝ :=
  X p.1

/-- Evaluate a declared strategy on the model paired with it. -/
def modelStrategyPredictableTilt
    (lambda : κ → ι → ℕ → Ω → ℝ) (p : ι × κ) : ℕ → Ω → ℝ :=
  lambda p.2 p.1

/-! ## Joint model--strategy posterior quantities -/

/-- Joint-posterior average of the predictable-tilt weighted mean gap. -/
def forwardPredictableStrategyPosteriorMeanGap
    (jointPosterior : ι × κ → ℝ)
    (X mean : ι → ℕ → Ω → ℝ)
    (lambda : κ → ι → ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  forwardPredictableTiltPosteriorMeanGap jointPosterior
    (modelStrategyProcess X) (modelStrategyProcess mean)
    (modelStrategyPredictableTilt lambda) n ω

/-- Joint-posterior average of the observable quadratic penalty. -/
def forwardPredictableStrategyPosteriorQuadraticPenalty
    (jointPosterior : ι × κ → ℝ)
    (X : ι → ℕ → Ω → ℝ)
    (lambda : κ → ι → ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  forwardPredictableTiltPosteriorQuadraticPenalty jointPosterior
    (modelStrategyProcess X) (modelStrategyPredictableTilt lambda) n ω

/-- Total joint-posterior predictable tilt accumulated through time `n`. -/
def forwardPredictableStrategyPosteriorTotalWeight
    (jointPosterior : ι × κ → ℝ)
    (lambda : κ → ι → ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  forwardPredictableTiltPosteriorTotalWeight jointPosterior
    (modelStrategyPredictableTilt lambda) n ω

/-- Normalized joint-posterior tilt-weighted conditional mean. -/
def forwardPredictableStrategyPosteriorNormalizedMean
    (jointPosterior : ι × κ → ℝ)
    (mean : ι → ℕ → Ω → ℝ)
    (lambda : κ → ι → ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  forwardPredictableTiltPosteriorNormalizedMean jointPosterior
    (modelStrategyProcess mean) (modelStrategyPredictableTilt lambda) n ω

/-- Normalized joint-posterior tilt-weighted observed mean. -/
def forwardPredictableStrategyPosteriorNormalizedObservation
    (jointPosterior : ι × κ → ℝ)
    (X : ι → ℕ → Ω → ℝ)
    (lambda : κ → ι → ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  forwardPredictableTiltPosteriorNormalizedObservation jointPosterior
    (modelStrategyProcess X) (modelStrategyPredictableTilt lambda) n ω

/-! ## Factorized posteriors with strategies shared across models -/

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ] in
/-- Posterior averaging under an independent model--strategy posterior
factorizes for a product integrand. -/
theorem posteriorAverage_modelStrategyProductPrior_separable
    (modelPosterior : ι → ℝ) (strategyPosterior : κ → ℝ)
    (f : ι → ℝ) (g : κ → ℝ) :
    posteriorAverage
        (modelStrategyProductPrior modelPosterior strategyPosterior)
        (fun p : ι × κ ↦ f p.1 * g p.2) =
      posteriorAverage modelPosterior f *
        posteriorAverage strategyPosterior g := by
  classical
  unfold posteriorAverage modelStrategyProductPrior
  rw [Fintype.sum_prod_type]
  calc
    (∑ i : ι, ∑ j : κ,
        modelPosterior i * strategyPosterior j * (f i * g j)) =
        ∑ i : ι, (modelPosterior i * f i) *
          (∑ j : κ, strategyPosterior j * g j) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = _ := by rw [Finset.sum_mul]

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ] in
/-- When every catalog strategy is shared across models, a factorized
posterior's accumulated tilt is just its strategy-posterior average. -/
theorem forwardPredictableStrategyPosteriorTotalWeight_shared_factorized
    (modelPosterior : ι → ℝ) (strategyPosterior : κ → ℝ)
    (hmodelPosterior : IsPMF modelPosterior)
    (lambda : κ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    forwardPredictableStrategyPosteriorTotalWeight
        (modelStrategyProductPrior modelPosterior strategyPosterior)
        (fun j _i ↦ lambda j) n ω =
      posteriorAverage strategyPosterior
        (fun j ↦ ∑ k ∈ Finset.range n, lambda j k ω) := by
  unfold forwardPredictableStrategyPosteriorTotalWeight
    forwardPredictableTiltPosteriorTotalWeight
    modelStrategyPredictableTilt
  calc
    posteriorAverage
        (modelStrategyProductPrior modelPosterior strategyPosterior)
        (fun p : ι × κ ↦ ∑ k ∈ Finset.range n, lambda p.2 k ω) =
      posteriorAverage
        (modelStrategyProductPrior modelPosterior strategyPosterior)
        (fun p : ι × κ ↦
          (1 : ℝ) * (∑ k ∈ Finset.range n, lambda p.2 k ω)) := by
        congr 1
        funext p
        rw [one_mul]
    _ = posteriorAverage modelPosterior (fun _i ↦ (1 : ℝ)) *
        posteriorAverage strategyPosterior
          (fun j ↦ ∑ k ∈ Finset.range n, lambda j k ω) :=
      posteriorAverage_modelStrategyProductPrior_separable
        modelPosterior strategyPosterior (fun _i ↦ (1 : ℝ))
          (fun j ↦ ∑ k ∈ Finset.range n, lambda j k ω)
    _ = _ := by
      unfold posteriorAverage
      rw [show (∑ i : ι, modelPosterior i * (1 : ℝ)) = 1 by
        simpa using hmodelPosterior.sum_one]
      exact one_mul _

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ] in
/-- If each model has a constant conditional mean and each strategy is shared
across models, strategy weights cancel from the normalized conditional mean
under a factorized posterior.  The strategies may still depend predictably on
time and the observed history. -/
theorem
    forwardPredictableStrategyPosteriorNormalizedMean_shared_constant_factorized
    (modelPosterior : ι → ℝ) (strategyPosterior : κ → ℝ)
    (hmodelPosterior : IsPMF modelPosterior)
    (risk : ι → ℝ) (lambda : κ → ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω)
    (hweight : 0 <
      forwardPredictableStrategyPosteriorTotalWeight
        (modelStrategyProductPrior modelPosterior strategyPosterior)
        (fun j _i ↦ lambda j) n ω) :
    forwardPredictableStrategyPosteriorNormalizedMean
        (modelStrategyProductPrior modelPosterior strategyPosterior)
        (fun i _k _ω ↦ risk i) (fun j _i ↦ lambda j) n ω =
      posteriorAverage modelPosterior risk := by
  have hden :=
    forwardPredictableStrategyPosteriorTotalWeight_shared_factorized
      modelPosterior strategyPosterior hmodelPosterior lambda n ω
  have hdenPos : 0 < posteriorAverage strategyPosterior
      (fun j ↦ ∑ k ∈ Finset.range n, lambda j k ω) := by
    rwa [hden] at hweight
  change
    (posteriorAverage
        (modelStrategyProductPrior modelPosterior strategyPosterior)
        (fun p : ι × κ ↦
          ∑ k ∈ Finset.range n, lambda p.2 k ω * risk p.1)) /
      forwardPredictableStrategyPosteriorTotalWeight
        (modelStrategyProductPrior modelPosterior strategyPosterior)
        (fun j _i ↦ lambda j) n ω =
      posteriorAverage modelPosterior risk
  rw [hden]
  have hnum :
      posteriorAverage
          (modelStrategyProductPrior modelPosterior strategyPosterior)
          (fun p : ι × κ ↦
            ∑ k ∈ Finset.range n, lambda p.2 k ω * risk p.1) =
        posteriorAverage modelPosterior risk *
          posteriorAverage strategyPosterior
            (fun j ↦ ∑ k ∈ Finset.range n, lambda j k ω) := by
    calc
      posteriorAverage
          (modelStrategyProductPrior modelPosterior strategyPosterior)
          (fun p : ι × κ ↦
            ∑ k ∈ Finset.range n, lambda p.2 k ω * risk p.1) =
        posteriorAverage
          (modelStrategyProductPrior modelPosterior strategyPosterior)
          (fun p : ι × κ ↦
            risk p.1 *
              (∑ k ∈ Finset.range n, lambda p.2 k ω)) := by
          apply Finset.sum_congr rfl
          intro p _hp
          apply congrArg
            (fun z : ℝ ↦
              modelStrategyProductPrior modelPosterior strategyPosterior p * z)
          change
            (∑ k ∈ Finset.range n, lambda p.2 k ω * risk p.1) =
              risk p.1 * (∑ k ∈ Finset.range n, lambda p.2 k ω)
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          ring
      _ = _ := posteriorAverage_modelStrategyProductPrior_separable
        modelPosterior strategyPosterior risk
          (fun j ↦ ∑ k ∈ Finset.range n, lambda j k ω)
  rw [hnum]
  exact (mul_div_cancel_right₀
    (posteriorAverage modelPosterior risk) hdenPos.ne')

/-! ## Common-event strategy selection -/

omit [DecidableEq ι] [DecidableEq κ] in
/-- One outer-mass event controls every time and every joint posterior on the
finite model--strategy catalog.  The joint posterior may be chosen after the
path is observed, while every strategy in the catalog remains predictable. -/
theorem exists_forwardPredictableStrategyPACBayes_event
    [IsProbabilityMeasure μ]
    {modelPrior : ι → ℝ} (hmodelPrior : IsFullSupportPMF modelPrior)
    {strategyPrior : κ → ℝ}
    (hstrategyPrior : IsFullSupportPMF strategyPrior)
    {X mean : ι → ℕ → Ω → ℝ}
    {lambda : κ → ι → ℕ → Ω → ℝ} {L delta : ℝ}
    (hL1 : L < 1) (hdelta : 0 < delta)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hmean_adapted : ∀ i, StronglyAdapted ℱ (mean i))
    (hlambda_adapted : ∀ j i, StronglyAdapted ℱ (lambda j i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hlambda_range : ∀ j i k ω,
      0 ≤ lambda j i k ω ∧ lambda j i k ω ≤ L)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] mean i k) :
    ∃ goodEvent : Set Ω,
      μ.real goodEventᶜ ≤ delta ∧
        ∀ ω ∈ goodEvent,
          ∀ jointPosterior : ι × κ → ℝ, IsPMF jointPosterior →
            ∀ n : ℕ,
              forwardPredictableStrategyPosteriorMeanGap
                  jointPosterior X mean lambda n ω <
                klDiv jointPosterior
                    (modelStrategyProductPrior modelPrior strategyPrior) +
                  Real.log (1 / delta) +
                  forwardPredictableStrategyPosteriorQuadraticPenalty
                    jointPosterior X lambda n ω := by
  rcases exists_forwardPredictableTiltPACBayes_event
      (ι := ι × κ) (μ := μ) (ℱ := ℱ)
      (prior := modelStrategyProductPrior modelPrior strategyPrior)
      (modelStrategyProductPrior_isFullSupportPMF
        hmodelPrior hstrategyPrior)
      (X := modelStrategyProcess X) (mean := modelStrategyProcess mean)
      (lambda := modelStrategyPredictableTilt lambda)
      (L := L) (delta := delta) hL1 hdelta
      (fun p ↦ hX_adapted p.1)
      (fun p ↦ hmean_adapted p.1)
      (fun p ↦ hlambda_adapted p.2 p.1)
      (fun p k ω ↦ hX_unit p.1 k ω)
      (fun p k ω ↦ hlambda_range p.2 p.1 k ω)
      (fun p k ↦ hmean p.1 k) with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro ω hω jointPosterior hposterior n
  simpa only [forwardPredictableStrategyPosteriorMeanGap,
    forwardPredictableStrategyPosteriorQuadraticPenalty] using
      hgood ω hω jointPosterior hposterior n

omit [DecidableEq ι] [DecidableEq κ] in
/-- Normalized tilt-weighted form of the joint model--strategy theorem.  Its
positive denominator is the selected joint posterior's accumulated tilt. -/
theorem exists_forwardPredictableStrategyPACBayes_normalized_event
    [IsProbabilityMeasure μ]
    {modelPrior : ι → ℝ} (hmodelPrior : IsFullSupportPMF modelPrior)
    {strategyPrior : κ → ℝ}
    (hstrategyPrior : IsFullSupportPMF strategyPrior)
    {X mean : ι → ℕ → Ω → ℝ}
    {lambda : κ → ι → ℕ → Ω → ℝ} {L delta : ℝ}
    (hL1 : L < 1) (hdelta : 0 < delta)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hmean_adapted : ∀ i, StronglyAdapted ℱ (mean i))
    (hlambda_adapted : ∀ j i, StronglyAdapted ℱ (lambda j i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hlambda_range : ∀ j i k ω,
      0 ≤ lambda j i k ω ∧ lambda j i k ω ≤ L)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] mean i k) :
    ∃ goodEvent : Set Ω,
      μ.real goodEventᶜ ≤ delta ∧
        ∀ ω ∈ goodEvent,
          ∀ jointPosterior : ι × κ → ℝ, IsPMF jointPosterior →
            ∀ n : ℕ,
              0 < forwardPredictableStrategyPosteriorTotalWeight
                    jointPosterior lambda n ω →
                forwardPredictableStrategyPosteriorNormalizedMean
                    jointPosterior mean lambda n ω <
                  forwardPredictableStrategyPosteriorNormalizedObservation
                      jointPosterior X lambda n ω +
                    (klDiv jointPosterior
                          (modelStrategyProductPrior modelPrior strategyPrior) +
                        Real.log (1 / delta) +
                        forwardPredictableStrategyPosteriorQuadraticPenalty
                          jointPosterior X lambda n ω) /
                      forwardPredictableStrategyPosteriorTotalWeight
                        jointPosterior lambda n ω := by
  rcases exists_forwardPredictableTiltPACBayes_normalized_event
      (ι := ι × κ) (μ := μ) (ℱ := ℱ)
      (prior := modelStrategyProductPrior modelPrior strategyPrior)
      (modelStrategyProductPrior_isFullSupportPMF
        hmodelPrior hstrategyPrior)
      (X := modelStrategyProcess X) (mean := modelStrategyProcess mean)
      (lambda := modelStrategyPredictableTilt lambda)
      (L := L) (delta := delta) hL1 hdelta
      (fun p ↦ hX_adapted p.1)
      (fun p ↦ hmean_adapted p.1)
      (fun p ↦ hlambda_adapted p.2 p.1)
      (fun p k ω ↦ hX_unit p.1 k ω)
      (fun p k ω ↦ hlambda_range p.2 p.1 k ω)
      (fun p k ↦ hmean p.1 k) with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro ω hω jointPosterior hposterior n hweight
  simpa only [forwardPredictableStrategyPosteriorTotalWeight,
    forwardPredictableStrategyPosteriorNormalizedMean,
    forwardPredictableStrategyPosteriorNormalizedObservation,
    forwardPredictableStrategyPosteriorQuadraticPenalty] using
      hgood ω hω jointPosterior hposterior n hweight

omit [DecidableEq ι] [DecidableEq κ] in
/-- Path- and time-dependent joint-posterior specialization.  This is the
direct post-data model-and-strategy selection endpoint: the selected pair may
depend on the observed path, and its joint KL cost remains in the bound. -/
theorem exists_forwardPredictableStrategyPACBayes_normalized_selected_event
    [IsProbabilityMeasure μ]
    {modelPrior : ι → ℝ} (hmodelPrior : IsFullSupportPMF modelPrior)
    {strategyPrior : κ → ℝ}
    (hstrategyPrior : IsFullSupportPMF strategyPrior)
    {X mean : ι → ℕ → Ω → ℝ}
    {lambda : κ → ι → ℕ → Ω → ℝ} {L delta : ℝ}
    (hL1 : L < 1) (hdelta : 0 < delta)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hmean_adapted : ∀ i, StronglyAdapted ℱ (mean i))
    (hlambda_adapted : ∀ j i, StronglyAdapted ℱ (lambda j i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hlambda_range : ∀ j i k ω,
      0 ≤ lambda j i k ω ∧ lambda j i k ω ≤ L)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] mean i k)
    (jointPosterior : Ω → ℕ → ι × κ → ℝ)
    (hposterior : ∀ ω n, IsPMF (jointPosterior ω n)) :
    ∃ goodEvent : Set Ω,
      μ.real goodEventᶜ ≤ delta ∧
        ∀ ω ∈ goodEvent, ∀ n : ℕ,
          0 < forwardPredictableStrategyPosteriorTotalWeight
                (jointPosterior ω n) lambda n ω →
            forwardPredictableStrategyPosteriorNormalizedMean
                (jointPosterior ω n) mean lambda n ω <
              forwardPredictableStrategyPosteriorNormalizedObservation
                  (jointPosterior ω n) X lambda n ω +
                (klDiv (jointPosterior ω n)
                      (modelStrategyProductPrior modelPrior strategyPrior) +
                    Real.log (1 / delta) +
                    forwardPredictableStrategyPosteriorQuadraticPenalty
                      (jointPosterior ω n) X lambda n ω) /
                  forwardPredictableStrategyPosteriorTotalWeight
                    (jointPosterior ω n) lambda n ω := by
  rcases exists_forwardPredictableStrategyPACBayes_normalized_event
      hmodelPrior hstrategyPrior hL1 hdelta hX_adapted hmean_adapted
      hlambda_adapted hX_unit hlambda_range hmean with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro ω hω n hweight
  exact hgood ω hω (jointPosterior ω n) (hposterior ω n) n hweight

omit [DecidableEq ι] [DecidableEq κ] in
/-- Factorized post-data model and strategy selection.  Independence in the
reported posterior makes the complexity exactly the sum of the model KL and
strategy KL.  Both posterior factors may depend on the observed path and time. -/
theorem
    exists_forwardPredictableStrategyPACBayes_factorized_normalized_selected_event
    [IsProbabilityMeasure μ]
    {modelPrior : ι → ℝ} (hmodelPrior : IsFullSupportPMF modelPrior)
    {strategyPrior : κ → ℝ}
    (hstrategyPrior : IsFullSupportPMF strategyPrior)
    {X mean : ι → ℕ → Ω → ℝ}
    {lambda : κ → ι → ℕ → Ω → ℝ} {L delta : ℝ}
    (hL1 : L < 1) (hdelta : 0 < delta)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hmean_adapted : ∀ i, StronglyAdapted ℱ (mean i))
    (hlambda_adapted : ∀ j i, StronglyAdapted ℱ (lambda j i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hlambda_range : ∀ j i k ω,
      0 ≤ lambda j i k ω ∧ lambda j i k ω ≤ L)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] mean i k)
    (modelPosterior : Ω → ℕ → ι → ℝ)
    (hmodelPosterior : ∀ ω n, IsPMF (modelPosterior ω n))
    (strategyPosterior : Ω → ℕ → κ → ℝ)
    (hstrategyPosterior : ∀ ω n, IsPMF (strategyPosterior ω n)) :
    ∃ goodEvent : Set Ω,
      μ.real goodEventᶜ ≤ delta ∧
        ∀ ω ∈ goodEvent, ∀ n : ℕ,
          0 < forwardPredictableStrategyPosteriorTotalWeight
                (modelStrategyProductPrior
                  (modelPosterior ω n) (strategyPosterior ω n))
                lambda n ω →
            forwardPredictableStrategyPosteriorNormalizedMean
                (modelStrategyProductPrior
                  (modelPosterior ω n) (strategyPosterior ω n))
                mean lambda n ω <
              forwardPredictableStrategyPosteriorNormalizedObservation
                  (modelStrategyProductPrior
                    (modelPosterior ω n) (strategyPosterior ω n))
                  X lambda n ω +
                ((klDiv (modelPosterior ω n) modelPrior +
                      klDiv (strategyPosterior ω n) strategyPrior) +
                    Real.log (1 / delta) +
                    forwardPredictableStrategyPosteriorQuadraticPenalty
                      (modelStrategyProductPrior
                        (modelPosterior ω n) (strategyPosterior ω n))
                      X lambda n ω) /
                  forwardPredictableStrategyPosteriorTotalWeight
                    (modelStrategyProductPrior
                      (modelPosterior ω n) (strategyPosterior ω n))
                    lambda n ω := by
  let jointPosterior : Ω → ℕ → ι × κ → ℝ := fun ω n ↦
    modelStrategyProductPrior
      (modelPosterior ω n) (strategyPosterior ω n)
  have hjointPosterior : ∀ ω n, IsPMF (jointPosterior ω n) := by
    intro ω n
    exact modelStrategyProductPrior_isPMF
      (hmodelPosterior ω n) (hstrategyPosterior ω n)
  rcases exists_forwardPredictableStrategyPACBayes_normalized_selected_event
      hmodelPrior hstrategyPrior hL1 hdelta hX_adapted hmean_adapted
      hlambda_adapted hX_unit hlambda_range hmean
      jointPosterior hjointPosterior with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro ω hω n hweight
  have hbound := hgood ω hω n hweight
  rw [klDiv_modelStrategyProductPrior
    (hmodelPosterior ω n) hmodelPrior
    (hstrategyPosterior ω n) hstrategyPrior] at hbound
  exact hbound

omit [DecidableEq ι] [DecidableEq κ] in
/-- One common event gives an ordinary posterior-averaged conditional-risk
bound for every model posterior, every strategy posterior, and every time.
Each model's conditional mean is the fixed value `risk i`.  Catalog strategies
may vary predictably with time and history, but they are shared across models;
under a factorized reporting posterior their weights therefore cancel from the
normalized conditional mean.  Model and strategy selection are charged by
separate finite KL terms.

The risk target is the posterior average of the stated constant conditional
means.  Any interpretation as population, future, or deployment risk requires
the supplied conditional-expectation premise to justify that meaning. -/
theorem
    exists_forwardPredictableStrategyPACBayes_shared_constantMean_factorized_ordinaryRisk_event
    [IsProbabilityMeasure μ]
    {modelPrior : ι → ℝ} (hmodelPrior : IsFullSupportPMF modelPrior)
    {strategyPrior : κ → ℝ}
    (hstrategyPrior : IsFullSupportPMF strategyPrior)
    {risk : ι → ℝ} {X : ι → ℕ → Ω → ℝ}
    {lambda : κ → ℕ → Ω → ℝ} {L delta : ℝ}
    (hL1 : L < 1) (hdelta : 0 < delta)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hlambda_adapted : ∀ j, StronglyAdapted ℱ (lambda j))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hlambda_range : ∀ j k ω,
      0 ≤ lambda j k ω ∧ lambda j k ω ≤ L)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] fun _ω ↦ risk i) :
    ∃ goodEvent : Set Ω,
      μ.real goodEventᶜ ≤ delta ∧
        ∀ ω ∈ goodEvent,
          ∀ modelPosterior : ι → ℝ, IsPMF modelPosterior →
            ∀ strategyPosterior : κ → ℝ, IsPMF strategyPosterior →
              ∀ n : ℕ,
                0 < forwardPredictableStrategyPosteriorTotalWeight
                      (modelStrategyProductPrior
                        modelPosterior strategyPosterior)
                      (fun j _i ↦ lambda j) n ω →
                  posteriorAverage modelPosterior risk <
                    forwardPredictableStrategyPosteriorNormalizedObservation
                        (modelStrategyProductPrior
                          modelPosterior strategyPosterior)
                        X (fun j _i ↦ lambda j) n ω +
                      ((klDiv modelPosterior modelPrior +
                            klDiv strategyPosterior strategyPrior) +
                          Real.log (1 / delta) +
                          forwardPredictableStrategyPosteriorQuadraticPenalty
                            (modelStrategyProductPrior
                              modelPosterior strategyPosterior)
                            X (fun j _i ↦ lambda j) n ω) /
                        forwardPredictableStrategyPosteriorTotalWeight
                          (modelStrategyProductPrior
                            modelPosterior strategyPosterior)
                          (fun j _i ↦ lambda j) n ω := by
  rcases exists_forwardPredictableStrategyPACBayes_normalized_event
      hmodelPrior hstrategyPrior hL1 hdelta hX_adapted
      (fun i ↦ stronglyAdapted_const ℱ (risk i))
      (fun j _i ↦ hlambda_adapted j) hX_unit
      (fun j _i k ω ↦ hlambda_range j k ω) hmean with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro ω hω modelPosterior hmodelPosterior
    strategyPosterior hstrategyPosterior n hweight
  have hbound := hgood ω hω
    (modelStrategyProductPrior modelPosterior strategyPosterior)
    (modelStrategyProductPrior_isPMF
      hmodelPosterior hstrategyPosterior) n hweight
  rw [
    forwardPredictableStrategyPosteriorNormalizedMean_shared_constant_factorized
      modelPosterior strategyPosterior hmodelPosterior risk lambda n ω hweight,
    klDiv_modelStrategyProductPrior
      hmodelPosterior hmodelPrior hstrategyPosterior hstrategyPrior] at hbound
  exact hbound

end

end FormalSLT.PACBayes.ForwardPredictableStrategyPACBayes
