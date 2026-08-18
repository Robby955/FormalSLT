/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.CountableEProcess
import FormalSLT.PACBayes.ForwardBesselPACBayes
import FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch

/-!
# Countable forward-Bessel PAC-Bayes tilt mixtures

This module replaces the finite outer tilt catalog in
`ForwardBesselPACBayes` by a predeclared `Nat`-indexed catalog.  The hypothesis
class remains finite.  A normalized positive countable tilt prior and the
finite hypothesis prior form one nested master e-process.  One Ville event
then supports every time `n >= 2`, every post-data posterior, and every
declared countable tilt atom.  Selecting atom `j` pays exactly
`log (1 / (delta * weight j))`.

The outer series is a real `tsum`.  Its pointwise summability, adaptedness,
integrability, and set-integral interchange are discharged from the bounded
forward process and normalized catalog weights.  This is countable atom
selection, not integration over all real tilts and not a data-dependent change
of the mixing weights.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open scoped BigOperators

namespace FormalSLT.PACBayes.ForwardBesselPACBayesCountable

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

open FormalSLT.PACBayes.ForwardBesselPACBayes
open FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch

variable {ι Ω : Type*}
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ mΩ}

/-- The finite hypothesis-prior component at one declared tilt. -/
def countableForwardBesselPACBayesTiltComponent
    (prior : ι → ℝ) (X : ι → ℕ → Ω → ℝ) (mean : ι → ℝ)
    (lam : ℕ → ℝ) (j : ℕ) : ℕ → Ω → ℝ :=
  finiteWeightedProcess prior fun i ↦
    forwardEmpiricalBernsteinLowerProcess (X i) (mean i) (lam j)

/-- The outer countable tilt mixture of finite hypothesis-prior components. -/
def countableForwardBesselPACBayesMasterProcess
    (prior : ι → ℝ) (weight : ℕ → ℝ)
    (X : ι → ℕ → Ω → ℝ) (mean : ι → ℝ)
    (lam : ℕ → ℝ) : ℕ → Ω → ℝ :=
  countableWeightedProcess weight
    (countableForwardBesselPACBayesTiltComponent prior X mean lam)

omit [Nonempty ι] in
/-- Every fixed tilt component is an e-process under the bounded
conditional-mean model. -/
theorem countableForwardBesselPACBayesTiltComponent_eProcess_of_bounded
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ} {lam : ℕ → ℝ}
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] fun _ ↦ mean i)
    (j : ℕ) :
    EProcess μ ℱ
      (countableForwardBesselPACBayesTiltComponent prior X mean lam j) := by
  unfold countableForwardBesselPACBayesTiltComponent
  apply finiteWeightedProcess_eProcess hprior.nonneg hprior.sum_one
  intro i
  exact forwardEmpiricalBernsteinLowerProcess_eProcess_of_bounded
    (hlam j).le (hlam1 j) (hX_adapted i) (hX_unit i) (hmean i)

/-- A deterministic finite-hypothesis bound uniform over every admissible
countable tilt atom. -/
def countableForwardBesselPACBayesComponentBound
    (prior : ι → ℝ) (mean : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ i : ι, prior i * Real.exp ((n : ℝ) * (1 + |1 - mean i|))

omit [DecidableEq ι] [Nonempty ι] in
/-- Each countable tilt component is bounded by a common finite constant at
every fixed time and path.  This supplies pointwise summability of the outer
series. -/
theorem countableForwardBesselPACBayesTiltComponent_le_bound
    {prior : ι → ℝ} (hprior : IsPMF prior)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ} {lam : ℕ → ℝ}
    (hlam : ∀ j, 0 ≤ lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (j n : ℕ) (ω : Ω) :
    countableForwardBesselPACBayesTiltComponent prior X mean lam j n ω ≤
      countableForwardBesselPACBayesComponentBound prior mean n := by
  unfold countableForwardBesselPACBayesTiltComponent
    countableForwardBesselPACBayesComponentBound finiteWeightedProcess
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hprior.nonneg i)
  have hunit_complement :
      ∀ k ω, 0 ≤ (1 - X i k ω) ∧ (1 - X i k ω) ≤ 1 := by
    intro k ω
    constructor <;> linarith [(hX_unit i k ω).1, (hX_unit i k ω).2]
  have hraw := forwardEmpiricalBernsteinProcess_le_of_mem_Icc
    (X := fun k ω ↦ 1 - X i k ω) (mean := 1 - mean i)
    (lam := lam j) (hlam j) (hlam1 j) hunit_complement n ω
  have hscale_nonneg : 0 ≤ (n : ℝ) * (1 + |1 - mean i|) := by positivity
  have hscale :
      lam j * (n : ℝ) * (1 + |1 - mean i|) ≤
        (n : ℝ) * (1 + |1 - mean i|) := by
    calc
      lam j * (n : ℝ) * (1 + |1 - mean i|) =
          lam j * ((n : ℝ) * (1 + |1 - mean i|)) := by ring
      _ ≤ 1 * ((n : ℝ) * (1 + |1 - mean i|)) :=
        mul_le_mul_of_nonneg_right (hlam1 j).le hscale_nonneg
      _ = (n : ℝ) * (1 + |1 - mean i|) := one_mul _
  exact hraw.trans (Real.exp_le_exp.mpr hscale)

omit [DecidableEq ι] [Nonempty ι] in
/-- The outer real series is summable at every time and path. -/
theorem countableForwardBesselPACBayesMasterProcess_pointwise_summable
    {prior : ι → ℝ} (hprior : IsPMF prior)
    {weight : ℕ → ℝ} (hweight_nonneg : ∀ j, 0 ≤ weight j)
    (hweight_summable : Summable weight)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ} {lam : ℕ → ℝ}
    (hlam : ∀ j, 0 ≤ lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (n : ℕ) (ω : Ω) :
    Summable fun j ↦ weight j *
      countableForwardBesselPACBayesTiltComponent prior X mean lam j n ω := by
  have hbound : Summable fun j ↦
      weight j * countableForwardBesselPACBayesComponentBound prior mean n :=
    hweight_summable.mul_right _
  exact hbound.of_nonneg_of_le
    (fun j ↦ mul_nonneg (hweight_nonneg j) (by
      unfold countableForwardBesselPACBayesTiltComponent finiteWeightedProcess
      exact Finset.sum_nonneg fun i _ ↦
        mul_nonneg (hprior.nonneg i) (Real.exp_pos _).le))
    (fun j ↦ mul_le_mul_of_nonneg_left
      (countableForwardBesselPACBayesTiltComponent_le_bound
        hprior hlam hlam1 hX_unit j n ω)
      (hweight_nonneg j))

omit [DecidableEq ι] [Nonempty ι] in
/-- The common finite-hypothesis component bound is nonnegative. -/
theorem countableForwardBesselPACBayesComponentBound_nonneg
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (mean : ι → ℝ) (n : ℕ) :
    0 ≤ countableForwardBesselPACBayesComponentBound prior mean n := by
  unfold countableForwardBesselPACBayesComponentBound
  exact Finset.sum_nonneg fun i _ ↦
    mul_nonneg (hprior.nonneg i) (Real.exp_pos _).le

omit [DecidableEq ι] [Nonempty ι] in
/-- Pointwise nonnegativity of the countable nested master process. -/
theorem countableForwardBesselPACBayesMasterProcess_nonneg
    {prior : ι → ℝ} (hprior : IsPMF prior)
    {weight : ℕ → ℝ} (hweight_nonneg : ∀ j, 0 ≤ weight j)
    (X : ι → ℕ → Ω → ℝ) (mean : ι → ℝ) (lam : ℕ → ℝ) :
    0 ≤ countableForwardBesselPACBayesMasterProcess
      prior weight X mean lam := by
  unfold countableForwardBesselPACBayesMasterProcess
  exact countableWeightedProcess_nonneg hweight_nonneg fun j n ω ↦ by
    unfold countableForwardBesselPACBayesTiltComponent finiteWeightedProcess
    exact Finset.sum_nonneg fun i _ ↦
      mul_nonneg (hprior.nonneg i) (Real.exp_pos _).le

omit [DecidableEq ι] [Nonempty ι] in
/-- The countable master process inherits the same finite uniform bound. -/
theorem countableForwardBesselPACBayesMasterProcess_le_bound
    {prior : ι → ℝ} (hprior : IsPMF prior)
    {weight : ℕ → ℝ} (hweight_nonneg : ∀ j, 0 ≤ weight j)
    (hweight_sum_one : HasSum weight 1)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ} {lam : ℕ → ℝ}
    (hlam : ∀ j, 0 ≤ lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (n : ℕ) (ω : Ω) :
    countableForwardBesselPACBayesMasterProcess
        prior weight X mean lam n ω ≤
      countableForwardBesselPACBayesComponentBound prior mean n := by
  let C := countableForwardBesselPACBayesComponentBound prior mean n
  have hseries :=
    countableForwardBesselPACBayesMasterProcess_pointwise_summable
      (X := X) (mean := mean) (lam := lam)
      hprior hweight_nonneg hweight_sum_one.summable hlam hlam1 hX_unit n ω
  have hbound_series : Summable fun j ↦ weight j * C :=
    hweight_sum_one.summable.mul_right C
  unfold countableForwardBesselPACBayesMasterProcess countableWeightedProcess
  calc
    (∑' j, weight j *
        countableForwardBesselPACBayesTiltComponent prior X mean lam j n ω) ≤
        ∑' j, weight j * C :=
      hseries.tsum_le_tsum
        (fun j ↦ mul_le_mul_of_nonneg_left
          (countableForwardBesselPACBayesTiltComponent_le_bound
            hprior hlam hlam1 hX_unit j n ω)
          (hweight_nonneg j))
        hbound_series
    _ = C := by simpa using (hweight_sum_one.mul_right C).tsum_eq

omit [Nonempty ι] in
/-- The automatically summable outer series is strongly adapted. -/
theorem countableForwardBesselPACBayesMasterProcess_stronglyAdapted
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : ℕ → ℝ} (hweight_nonneg : ∀ j, 0 ≤ weight j)
    (hweight_sum_one : HasSum weight 1)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ} {lam : ℕ → ℝ}
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] fun _ ↦ mean i) :
    StronglyAdapted ℱ
      (countableForwardBesselPACBayesMasterProcess
        prior weight X mean lam) := by
  intro n
  unfold countableForwardBesselPACBayesMasterProcess countableWeightedProcess
  refine stronglyMeasurable_of_tendsto Filter.atTop
    (f := fun N ω ↦ ∑ j ∈ Finset.range N,
      weight j *
        countableForwardBesselPACBayesTiltComponent
          prior X mean lam j n ω)
    (g := fun ω ↦ ∑' j,
      weight j *
        countableForwardBesselPACBayesTiltComponent
          prior X mean lam j n ω) ?_ ?_
  · intro N
    have hsum := Finset.stronglyMeasurable_sum (Finset.range N)
      (fun j _ ↦
        (((countableForwardBesselPACBayesTiltComponent_eProcess_of_bounded
          hprior hlam hlam1 hX_adapted hX_unit hmean j).supermartingale
            ).stronglyAdapted n).const_mul (weight j))
    convert hsum using 1
    ext ω
    simp only [Finset.sum_apply]
  · rw [tendsto_pi_nhds]
    intro ω
    exact
      (countableForwardBesselPACBayesMasterProcess_pointwise_summable
        (X := X) (mean := mean) (lam := lam)
        hprior.toIsPMF hweight_nonneg hweight_sum_one.summable
        (fun j ↦ (hlam j).le) hlam1 hX_unit n ω).hasSum.tendsto_sum_nat

omit [Nonempty ι] in
/-- The bounded countable master process is integrable at every time. -/
theorem countableForwardBesselPACBayesMasterProcess_integrable
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : ℕ → ℝ} (hweight_nonneg : ∀ j, 0 ≤ weight j)
    (hweight_sum_one : HasSum weight 1)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ} {lam : ℕ → ℝ}
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] fun _ ↦ mean i)
    (n : ℕ) :
    Integrable
      (countableForwardBesselPACBayesMasterProcess
        prior weight X mean lam n) μ := by
  let C := countableForwardBesselPACBayesComponentBound prior mean n
  have hadapted := countableForwardBesselPACBayesMasterProcess_stronglyAdapted
    hprior hweight_nonneg hweight_sum_one hlam hlam1
    hX_adapted hX_unit hmean
  refine Integrable.of_bound
    ((hadapted n).mono (ℱ.le n)).aestronglyMeasurable C ?_
  exact Filter.Eventually.of_forall fun ω ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (countableForwardBesselPACBayesMasterProcess_nonneg
        hprior.toIsPMF hweight_nonneg X mean lam n ω)]
    exact countableForwardBesselPACBayesMasterProcess_le_bound
      hprior.toIsPMF hweight_nonneg hweight_sum_one
      (fun j ↦ (hlam j).le) hlam1 hX_unit n ω

omit [DecidableEq ι] [Nonempty ι] in
/-- The component-wise set-integral norms are dominated by one summable
weight sequence. -/
theorem countableForwardBesselPACBayesMasterProcess_integralNorm_summable
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : ℕ → ℝ} (hweight_nonneg : ∀ j, 0 ≤ weight j)
    (hweight_sum_one : HasSum weight 1)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ} {lam : ℕ → ℝ}
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (n : ℕ) (s : Set Ω) (_hs : MeasurableSet s) :
    Summable fun j ↦ ∫ ω in s,
      ‖weight j *
        countableForwardBesselPACBayesTiltComponent
          prior X mean lam j n ω‖ ∂μ := by
  let C := countableForwardBesselPACBayesComponentBound prior mean n
  have hC : 0 ≤ C :=
    countableForwardBesselPACBayesComponentBound_nonneg
      hprior.toIsPMF mean n
  have hdom : Summable fun j ↦ weight j * C :=
    hweight_sum_one.summable.mul_right C
  refine hdom.of_nonneg_of_le (fun j ↦ integral_nonneg fun _ ↦ norm_nonneg _) ?_
  intro j
  have hconst_nonneg : 0 ≤ weight j * C :=
    mul_nonneg (hweight_nonneg j) hC
  have hnorm_bound : ∀ ω ∈ s,
      ‖weight j *
        countableForwardBesselPACBayesTiltComponent
          prior X mean lam j n ω‖ ≤ weight j * C := by
    intro ω _hω
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hweight_nonneg j) (by
      unfold countableForwardBesselPACBayesTiltComponent finiteWeightedProcess
      exact Finset.sum_nonneg fun i _ ↦
        mul_nonneg (hprior.nonneg i) (Real.exp_pos _).le))]
    exact mul_le_mul_of_nonneg_left
      (countableForwardBesselPACBayesTiltComponent_le_bound
        hprior.toIsPMF (fun k ↦ (hlam k).le) hlam1 hX_unit j n ω)
      (hweight_nonneg j)
  have hset := norm_setIntegral_le_of_norm_le_const
    (μ := μ) (s := s)
    (f := fun ω ↦ ‖weight j *
      countableForwardBesselPACBayesTiltComponent
        prior X mean lam j n ω‖)
    (measure_lt_top μ s) (fun ω hω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hnorm_bound ω hω)
  have hint_nonneg : 0 ≤ ∫ ω in s,
      ‖weight j *
        countableForwardBesselPACBayesTiltComponent
          prior X mean lam j n ω‖ ∂μ :=
    integral_nonneg fun _ ↦ norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hint_nonneg] at hset
  calc
    (∫ ω in s, ‖weight j *
        countableForwardBesselPACBayesTiltComponent
          prior X mean lam j n ω‖ ∂μ) ≤
        (weight j * C) * μ.real s := hset
    _ ≤ (weight j * C) * 1 :=
      mul_le_mul_of_nonneg_left measureReal_le_one hconst_nonneg
    _ = weight j * C := mul_one _

omit [Nonempty ι] in
/-- The countable prior--tilt master series is one e-process with no exported
summability obligations. -/
theorem countableForwardBesselPACBayesMasterProcess_eProcess_of_bounded
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : ℕ → ℝ} (hweight_nonneg : ∀ j, 0 ≤ weight j)
    (hweight_sum_one : HasSum weight 1)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ} {lam : ℕ → ℝ}
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] fun _ ↦ mean i) :
    EProcess μ ℱ
      (countableForwardBesselPACBayesMasterProcess
        prior weight X mean lam) := by
  unfold countableForwardBesselPACBayesMasterProcess
  apply countableWeightedProcess_eProcess
    hweight_nonneg hweight_sum_one
  · intro j
    exact countableForwardBesselPACBayesTiltComponent_eProcess_of_bounded
      hprior hlam hlam1 hX_adapted hX_unit hmean j
  · exact countableForwardBesselPACBayesMasterProcess_stronglyAdapted
      hprior hweight_nonneg hweight_sum_one hlam hlam1
      hX_adapted hX_unit hmean
  · exact countableForwardBesselPACBayesMasterProcess_integrable
      hprior hweight_nonneg hweight_sum_one hlam hlam1
      hX_adapted hX_unit hmean
  · exact countableForwardBesselPACBayesMasterProcess_integralNorm_summable
      hprior hweight_nonneg hweight_sum_one hlam hlam1
      hX_unit

/-! ## Countable-atom PAC-Bayes boundary -/

/-- Exact posterior hybrid-Bessel boundary for countable atom `j`. -/
def countableForwardBesselPACBayesBoundary
    (prior : ι → ℝ) (weight lam : ℕ → ℝ)
    (X : ι → ℕ → Ω → ℝ) (posterior : ι → ℝ)
    (delta : ℝ) (j n : ℕ) (ω : Ω) : ℝ :=
  (klDiv posterior prior + Real.log (1 / (delta * weight j)) +
      forwardEmpiricalBernsteinPsi (lam j) *
        forwardPosteriorHybridBesselPenalty posterior X n ω) /
    ((n : ℝ) * lam j)

/-- One process-crossing event for every time, posterior, and countable atom. -/
def countableForwardBesselPACBayesExceptionalEvent
    (prior : ι → ℝ) (weight : ℕ → ℝ)
    (X : ι → ℕ → Ω → ℝ) (mean : ι → ℝ)
    (lam : ℕ → ℝ) (delta : ℝ) : Set Ω :=
  atTopCrossingEvent
    (countableForwardBesselPACBayesMasterProcess
      prior weight X mean lam)
    (1 / delta)

omit [Nonempty ι] in
/-- Ville control of the single countable-tilt nested master process. -/
theorem countableForwardBesselPACBayesExceptionalEvent_mass_le_delta
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : ℕ → ℝ} (hweight_nonneg : ∀ j, 0 ≤ weight j)
    (hweight_sum_one : HasSum weight 1)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ} {lam : ℕ → ℝ}
    {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] fun _ ↦ mean i) :
    μ.real
        (countableForwardBesselPACBayesExceptionalEvent
          prior weight X mean lam delta) ≤
      delta := by
  have hE := countableForwardBesselPACBayesMasterProcess_eProcess_of_bounded
    hprior hweight_nonneg hweight_sum_one hlam hlam1
    hX_adapted hX_unit hmean
  have hville := ville_atTop_maximal_ineq
    (μ := μ) (𝒢 := ℱ)
    (M := countableForwardBesselPACBayesMasterProcess
      prior weight X mean lam)
    hE.supermartingale hE.nonneg (one_div_pos.mpr hdelta)
  rw [hE.integral_start_eq_one] at hville
  unfold countableForwardBesselPACBayesExceptionalEvent
  calc
    μ.real
        (atTopCrossingEvent
          (countableForwardBesselPACBayesMasterProcess
            prior weight X mean lam)
          (1 / delta)) =
        delta * ((1 / delta) *
          μ.real
            (atTopCrossingEvent
              (countableForwardBesselPACBayesMasterProcess
                prior weight X mean lam)
              (1 / delta))) := by
      field_simp [hdelta.ne']
    _ ≤ delta * 1 := mul_le_mul_of_nonneg_left hville hdelta.le
    _ = delta := by ring

omit [DecidableEq ι] in
/-- A failure for one posterior, time, and countable atom forces the single
countable master process into its crossing event. -/
theorem countableForwardBesselPACBayes_boundaryFailure_mem_exceptionalEvent
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : ℕ → ℝ} (hweight_pos : ∀ j, 0 < weight j)
    (hweight_sum_one : HasSum weight 1)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ} {lam : ℕ → ℝ}
    {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    {posterior : ι → ℝ} (hposterior : IsPMF posterior)
    {j n : ℕ} {ω : Ω} (hn : 2 ≤ n)
    (hfail :
      countableForwardBesselPACBayesBoundary
          prior weight lam X posterior delta j n ω ≤
        posteriorAverage posterior mean -
          posteriorAverage posterior
            (fun i ↦ forwardPrefixMean (fun k ↦ X i k ω) n)) :
    ω ∈ countableForwardBesselPACBayesExceptionalEvent
      prior weight X mean lam delta := by
  classical
  have hnpos : 0 < n := by omega
  have hdenpos : 0 < (n : ℝ) * lam j :=
    mul_pos (Nat.cast_pos.mpr hnpos) (hlam j)
  unfold countableForwardBesselPACBayesBoundary at hfail
  have hfail_mul := (div_le_iff₀ hdenpos).mp hfail
  have hscore_identity := posteriorAverage_forwardBesselPACBayesScore
    posterior X mean (lam j) hnpos ω
  have hbudget_le_score :
      klDiv posterior prior + Real.log (1 / (delta * weight j)) ≤
        posteriorAverage posterior
          (fun i ↦ forwardBesselPACBayesScore
            X mean (lam j) i n ω) := by
    rw [hscore_identity]
    nlinarith
  have hdv := posterior_change_of_measure hposterior hprior
    (fun i ↦ forwardBesselPACBayesScore X mean (lam j) i n ω)
  have hlog_le :
      Real.log (1 / (delta * weight j)) ≤
        Real.log
          (∑ i : ι, prior i *
            Real.exp (forwardBesselPACBayesScore
              X mean (lam j) i n ω)) := by
    linarith
  have hthreshold_pos : 0 < 1 / (delta * weight j) :=
    one_div_pos.mpr (mul_pos hdelta (hweight_pos j))
  have hmoment_pos :
      0 < ∑ i : ι, prior i *
        Real.exp (forwardBesselPACBayesScore
          X mean (lam j) i n ω) :=
    Finset.sum_pos
      (fun i _ ↦ mul_pos (hprior.pos i) (Real.exp_pos _))
      Finset.univ_nonempty
  have hthreshold_le_moment :
      1 / (delta * weight j) ≤
        ∑ i : ι, prior i *
          Real.exp (forwardBesselPACBayesScore
            X mean (lam j) i n ω) :=
    (Real.log_le_log_iff hthreshold_pos hmoment_pos).mp hlog_le
  have hmoment_le_inner :
      (∑ i : ι, prior i *
        Real.exp (forwardBesselPACBayesScore
          X mean (lam j) i n ω)) ≤
        countableForwardBesselPACBayesTiltComponent
          prior X mean lam j n ω := by
    unfold countableForwardBesselPACBayesTiltComponent finiteWeightedProcess
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hprior.nonneg i)
    change forwardEmpiricalBernsteinLowerBesselEnvelope
        (X i) (mean i) (lam j) n ω ≤
      forwardEmpiricalBernsteinLowerProcess
        (X i) (mean i) (lam j) n ω
    exact forwardEmpiricalBernsteinLowerBesselEnvelope_le_lowerProcess
      (hlam j).le (hlam1 j) hn ω (fun k hk ↦ hX_unit i k ω)
  have hinner :
      1 / (delta * weight j) ≤
        countableForwardBesselPACBayesTiltComponent
          prior X mean lam j n ω :=
    hthreshold_le_moment.trans hmoment_le_inner
  have hweighted :
      weight j * (1 / (delta * weight j)) ≤
        weight j *
          countableForwardBesselPACBayesTiltComponent
            prior X mean lam j n ω :=
    mul_le_mul_of_nonneg_left hinner (hweight_pos j).le
  have hseries :=
    countableForwardBesselPACBayesMasterProcess_pointwise_summable
      (X := X) (mean := mean) (lam := lam)
      hprior.toIsPMF (fun k ↦ (hweight_pos k).le)
      hweight_sum_one.summable (fun k ↦ (hlam k).le) hlam1
      hX_unit n ω
  have hsingle :
      weight j *
          countableForwardBesselPACBayesTiltComponent
            prior X mean lam j n ω ≤
        countableForwardBesselPACBayesMasterProcess
          prior weight X mean lam n ω := by
    unfold countableForwardBesselPACBayesMasterProcess countableWeightedProcess
    exact hseries.le_tsum j fun k _ ↦
      mul_nonneg (hweight_pos k).le (by
        unfold countableForwardBesselPACBayesTiltComponent finiteWeightedProcess
        exact Finset.sum_nonneg fun i _ ↦
          mul_nonneg (hprior.nonneg i) (Real.exp_pos _).le)
  rw [show weight j * (1 / (delta * weight j)) = 1 / delta by
    field_simp [hdelta.ne', (hweight_pos j).ne']] at hweighted
  unfold countableForwardBesselPACBayesExceptionalEvent
  exact ⟨n, hweighted.trans hsingle⟩

omit [DecidableEq ι] in
/-- Outside the common crossing event, the boundary holds simultaneously for
all countable atoms, all post-data posteriors, and all `n >= 2`. -/
theorem countableForwardBesselPACBayes_allPosteriors_of_not_mem
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : ℕ → ℝ} (hweight_pos : ∀ j, 0 < weight j)
    (hweight_sum_one : HasSum weight 1)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ} {lam : ℕ → ℝ}
    {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    {ω : Ω}
    (hω : ω ∉ countableForwardBesselPACBayesExceptionalEvent
      prior weight X mean lam delta) :
    ∀ j : ℕ, ∀ posterior : ι → ℝ, IsPMF posterior →
      ∀ n : ℕ, 2 ≤ n →
        posteriorAverage posterior mean <
          posteriorAverage posterior
              (fun i ↦ forwardPrefixMean (fun k ↦ X i k ω) n) +
            countableForwardBesselPACBayesBoundary
              prior weight lam X posterior delta j n ω := by
  intro j posterior hposterior n hn
  apply lt_of_not_ge
  intro hfail
  apply hω
  exact countableForwardBesselPACBayes_boundaryFailure_mem_exceptionalEvent
    hprior hweight_pos hweight_sum_one hdelta hlam hlam1 hX_unit
    hposterior hn (by linarith)

omit [DecidableEq ι] in
/-- The posterior and countable tilt atom may both be selected after observing
the path because selection is substitution into one common event. -/
theorem countableForwardBesselPACBayes_selected_of_not_mem
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : ℕ → ℝ} (hweight_pos : ∀ j, 0 < weight j)
    (hweight_sum_one : HasSum weight 1)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ} {lam : ℕ → ℝ}
    {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    {ω : Ω}
    (hω : ω ∉ countableForwardBesselPACBayesExceptionalEvent
      prior weight X mean lam delta)
    (posterior : Ω → ℕ → ι → ℝ)
    (hposterior : ∀ ω n, IsPMF (posterior ω n))
    (select : Ω → ℕ → (ι → ℝ) → ℕ)
    (n : ℕ) (hn : 2 ≤ n) :
    posteriorAverage (posterior ω n) mean <
      posteriorAverage (posterior ω n)
          (fun i ↦ forwardPrefixMean (fun k ↦ X i k ω) n) +
        countableForwardBesselPACBayesBoundary
          prior weight lam X (posterior ω n) delta
            (select ω n (posterior ω n)) n ω :=
  countableForwardBesselPACBayes_allPosteriors_of_not_mem
    hprior hweight_pos hweight_sum_one hdelta hlam hlam1 hX_unit hω
    (select ω n (posterior ω n)) (posterior ω n)
    (hposterior ω n) n hn

/-- One outer-probability event carries the countable-tilt hybrid-Bessel
PAC-Bayes boundary simultaneously over time, posterior, and atom.  The event
uses `Measure.real` outer mass; no separate measurability certificate is
asserted. -/
theorem exists_countableForwardBesselPACBayes_event
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : ℕ → ℝ} (hweight_pos : ∀ j, 0 < weight j)
    (hweight_sum_one : HasSum weight 1)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ} {lam : ℕ → ℝ}
    {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] fun _ ↦ mean i) :
    ∃ goodEvent : Set Ω,
      μ.real goodEventᶜ ≤ delta ∧
        ∀ ω ∈ goodEvent, ∀ j : ℕ,
          ∀ posterior : ι → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              posteriorAverage posterior mean <
                posteriorAverage posterior
                    (fun i ↦ forwardPrefixMean (fun k ↦ X i k ω) n) +
                  countableForwardBesselPACBayesBoundary
                    prior weight lam X posterior delta j n ω := by
  let badEvent := countableForwardBesselPACBayesExceptionalEvent
    prior weight X mean lam delta
  refine ⟨badEventᶜ, ?_, ?_⟩
  · simpa [badEvent] using
      (countableForwardBesselPACBayesExceptionalEvent_mass_le_delta
        hprior (fun j ↦ (hweight_pos j).le) hweight_sum_one hdelta
        hlam hlam1 hX_adapted hX_unit hmean)
  · intro ω hω
    exact countableForwardBesselPACBayes_allPosteriors_of_not_mem
      hprior hweight_pos hweight_sum_one hdelta hlam hlam1 hX_unit hω

/-! ## A concrete polynomial-weight, geometric-tilt catalog -/

/-- Telescoping polynomial weights for the countable forward tilt catalog. -/
def polynomialForwardTiltWeight (j : ℕ) : ℝ :=
  reverseDyadicEpochWeight j

/-- Geometric forward tilts `1 / 2^(j+1)`, beginning at `1/2`. -/
def geometricForwardTilt (j : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ (j + 1)

/-- A convenient horizon scale for atom `j`.  At this horizon,
`n * geometricForwardTilt j = 2^(j+1)`. -/
def geometricForwardTiltTime (j : ℕ) : ℕ :=
  4 ^ (j + 1)

theorem polynomialForwardTiltWeight_pos (j : ℕ) :
    0 < polynomialForwardTiltWeight j :=
  reverseDyadicEpochWeight_pos j

theorem polynomialForwardTiltWeight_hasSum :
    HasSum polynomialForwardTiltWeight 1 :=
  reverseDyadicEpochWeight_hasSum

theorem geometricForwardTilt_pos (j : ℕ) :
    0 < geometricForwardTilt j := by
  unfold geometricForwardTilt
  positivity

theorem geometricForwardTilt_le_half (j : ℕ) :
    geometricForwardTilt j ≤ 1 / 2 := by
  unfold geometricForwardTilt
  have hp : (2 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
    rw [pow_succ]
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    nlinarith
  exact one_div_le_one_div_of_le (by norm_num) hp

theorem geometricForwardTilt_lt_one (j : ℕ) :
    geometricForwardTilt j < 1 :=
  (geometricForwardTilt_le_half j).trans_lt (by norm_num)

theorem geometricForwardTiltTime_mul_tilt (j : ℕ) :
    (geometricForwardTiltTime j : ℝ) * geometricForwardTilt j =
      (2 : ℝ) ^ (j + 1) := by
  unfold geometricForwardTiltTime geometricForwardTilt
  push_cast
  rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  field_simp

/-- Selecting catalog atom `j` incurs the explicit polynomial-weight cost. -/
theorem polynomialForwardTiltWeight_log_cost
    {delta : ℝ} (hdelta : delta ≠ 0) (j : ℕ) :
    Real.log (1 / (delta * polynomialForwardTiltWeight j)) =
      Real.log ((((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta) := by
  congr 1
  unfold polynomialForwardTiltWeight reverseDyadicEpochWeight
  field_simp [hdelta]

/-- The concrete polynomial-weight, geometric-tilt catalog inherits the
single-event countable PAC-Bayes endpoint. -/
theorem exists_geometricForwardBesselPACBayes_event
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ}
    {delta : ℝ} (hdelta : 0 < delta)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] fun _ ↦ mean i) :
    ∃ goodEvent : Set Ω,
      μ.real goodEventᶜ ≤ delta ∧
        ∀ ω ∈ goodEvent, ∀ j : ℕ,
          ∀ posterior : ι → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              posteriorAverage posterior mean <
                posteriorAverage posterior
                    (fun i ↦ forwardPrefixMean (fun k ↦ X i k ω) n) +
                  countableForwardBesselPACBayesBoundary
                    prior polynomialForwardTiltWeight geometricForwardTilt
                    X posterior delta j n ω := by
  exact exists_countableForwardBesselPACBayes_event
    hprior polynomialForwardTiltWeight_pos
    polynomialForwardTiltWeight_hasSum hdelta geometricForwardTilt_pos
    geometricForwardTilt_lt_one hX_adapted hX_unit hmean

omit [DecidableEq ι] [Nonempty ι] in
/-- On a unit-valued prefix, the hybrid Bessel penalty is at most the sample
size. -/
theorem forwardHybridBesselPenalty_le_card
    (x : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n)
    (hx : ∀ i < n, 0 ≤ x i ∧ x i ≤ 1) :
    forwardHybridBesselPenalty x n ≤ (n : ℝ) := by
  unfold forwardHybridBesselPenalty
  have hq := forwardBesselQ_le_quarter_card x (by omega)
    (fun i hi ↦ hx i hi)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    min
        ((1 : ℝ) / 2 + (3 : ℝ) / 2 * forwardBesselQ x n)
        ((n : ℝ) / ((n : ℝ) - 1) * forwardBesselQ x n +
          (1 : ℝ) / 4 *
            (1 + ((harmonic (n - 2) : ℚ) : ℝ))) ≤
      (1 : ℝ) / 2 + (3 : ℝ) / 2 * forwardBesselQ x n := min_le_left _ _
    _ ≤ (n : ℝ) := by nlinarith

omit [DecidableEq ι] [Nonempty ι] in
/-- The hybrid Bessel penalty is nonnegative on a unit-valued prefix. -/
theorem forwardHybridBesselPenalty_nonneg_of_unit
    (x : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n)
    (hx : ∀ i < n, 0 ≤ x i ∧ x i ≤ 1) :
    0 ≤ forwardHybridBesselPenalty x n := by
  have hpredict : 0 ≤ forwardPredictableQuadratic x n := by
    unfold forwardPredictableQuadratic
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  exact hpredict.trans
    (forwardPredictableQuadratic_le_hybrid_bessel x hn hx)

omit [DecidableEq ι] [Nonempty ι] in
/-- A PMF average of unit-valued hybrid penalties lies in `[0,n]`. -/
theorem forwardPosteriorHybridBesselPenalty_mem_Icc
    {posterior : ι → ℝ} (hposterior : IsPMF posterior)
    {X : ι → ℕ → Ω → ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hX : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1) (ω : Ω) :
    forwardPosteriorHybridBesselPenalty posterior X n ω ∈
      Set.Icc 0 (n : ℝ) := by
  constructor
  · unfold forwardPosteriorHybridBesselPenalty posteriorAverage
    exact Finset.sum_nonneg fun i _ ↦
      mul_nonneg (hposterior.nonneg i)
        (forwardHybridBesselPenalty_nonneg_of_unit
          (fun k ↦ X i k ω) hn (fun k hk ↦ hX i k ω))
  · unfold forwardPosteriorHybridBesselPenalty posteriorAverage
    calc
      (∑ i : ι, posterior i *
          forwardHybridBesselPenalty (fun k ↦ X i k ω) n) ≤
          ∑ i : ι, posterior i * (n : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (forwardHybridBesselPenalty_le_card
            (fun k ↦ X i k ω) hn (fun k hk ↦ hX i k ω))
          (hposterior.nonneg i)
      _ = (n : ℝ) := by
        rw [← Finset.sum_mul, hposterior.sum_one, one_mul]

omit [DecidableEq ι] [Nonempty ι] in
/-- Quadratic upper bound on the empirical-Bernstein cumulant over the
geometric catalog range `[0,1/2]`. -/
theorem forwardEmpiricalBernsteinPsi_le_two_mul_sq
    {lam : ℝ} (hlamhalf : lam ≤ 1 / 2) :
    forwardEmpiricalBernsteinPsi lam ≤ 2 * lam ^ 2 := by
  have hsub : 0 < 1 - lam := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hsub
  unfold forwardEmpiricalBernsteinPsi
  have hfrac : lam ^ 2 / (1 - lam) ≤ 2 * lam ^ 2 := by
    apply (div_le_iff₀ hsub).2
    nlinarith [sq_nonneg lam]
  calc
    -Real.log (1 - lam) - lam ≤ lam ^ 2 / (1 - lam) := by
      apply (le_div_iff₀ hsub).2
      have hmul := mul_le_mul_of_nonneg_right hlog hsub.le
      rw [sub_mul, one_mul, inv_mul_cancel₀ hsub.ne'] at hmul
      nlinarith
    _ ≤ 2 * lam ^ 2 := hfrac

/-- Deterministic rate envelope for the geometric atom at complexity
`complexity j`. -/
def geometricPolynomialForwardRate
    (complexity : ℕ → ℝ) (delta : ℝ) (j : ℕ) : ℝ :=
  2 * geometricForwardTilt j +
    (complexity j +
        Real.log ((((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta)) /
      (2 : ℝ) ^ (j + 1)

/-- The logarithmic polynomial-weight selection price is negligible relative
to the geometric effective sample size. -/
theorem polynomialForwardTilt_log_cost_div_geometric_tendsto_zero
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    Filter.Tendsto
      (fun j : ℕ ↦
        Real.log ((((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta) /
          (2 : ℝ) ^ (j + 1))
      Filter.atTop (nhds 0) := by
  let g : ℕ → ℝ := fun j ↦
    ((((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta) /
      (2 : ℝ) ^ (j + 1)
  have hg0 : Filter.Tendsto g Filter.atTop (nhds 0) := by
    have h2 := tendsto_pow_const_div_const_pow_of_one_lt 2
      (by norm_num : (1 : ℝ) < 2)
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1
      (by norm_num : (1 : ℝ) < 2)
    have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0
      (by norm_num : (1 : ℝ) < 2)
    have hsum := (h2.add (h1.const_mul 3)).add (h0.const_mul 2)
    have hscaled := hsum.const_mul (1 / (2 * delta))
    convert hscaled using 1
    · funext j
      dsimp [g]
      rw [pow_succ]
      field_simp [hdelta.ne']
      ring
    · norm_num
  apply squeeze_zero (g := g)
  · intro j
    apply div_nonneg
    · apply Real.log_nonneg
      apply (le_div_iff₀ hdelta).2
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    · positivity
  · intro j
    dsimp [g]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Real.log_le_self
    positivity
  · exact hg0

/-- The explicit rate vanishes whenever the selected posterior complexities
satisfy `complexity j / 2^(j+1) -> 0`.  Since the scale time is
`4^(j+1)`, this is the transparent condition `complexity = o(sqrt n)`. -/
theorem geometricPolynomialForwardRate_tendsto_zero
    {complexity : ℕ → ℝ} {delta : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hcomplexity : Filter.Tendsto
      (fun j ↦ complexity j / (2 : ℝ) ^ (j + 1))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (geometricPolynomialForwardRate complexity delta)
      Filter.atTop (nhds 0) := by
  have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0
    (by norm_num : (1 : ℝ) < 2)
  have htilt : Filter.Tendsto geometricForwardTilt
      Filter.atTop (nhds 0) := by
    have hscaled := h0.const_mul (1 / 2)
    convert hscaled using 1
    · funext j
      unfold geometricForwardTilt
      rw [pow_succ]
      ring
    · norm_num
  have hlog :=
    polynomialForwardTilt_log_cost_div_geometric_tendsto_zero
      hdelta hdelta1
  have hsum := htilt.const_mul 2 |>.add (hcomplexity.add hlog)
  convert hsum using 1
  · funext j
    rw [geometricPolynomialForwardRate, add_div]
  · norm_num

omit [DecidableEq ι] [Nonempty ι] in
/-- At every time beyond atom `j`'s geometric scale, its exact hybrid-Bessel
boundary is bounded by the explicit deterministic rate. -/
theorem countableForwardBesselPACBayesBoundary_le_geometricRate
    {prior posterior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (hposterior : IsPMF posterior)
    {X : ι → ℕ → Ω → ℝ}
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hX : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (j n : ℕ) (hn : 2 ≤ n) (hfloor : geometricForwardTiltTime j ≤ n)
    (ω : Ω) :
    countableForwardBesselPACBayesBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt
        X posterior delta j n ω ≤
      geometricPolynomialForwardRate
        (fun _ ↦ klDiv posterior prior) delta j := by
  have hlam0 : 0 ≤ geometricForwardTilt j :=
    (geometricForwardTilt_pos j).le
  have hlamhalf := geometricForwardTilt_le_half j
  have hlam1 := geometricForwardTilt_lt_one j
  have hpenalty :=
    forwardPosteriorHybridBesselPenalty_mem_Icc hposterior hn hX ω
  have hpsi := forwardEmpiricalBernsteinPsi_le_two_mul_sq hlamhalf
  have hvar :
      forwardEmpiricalBernsteinPsi (geometricForwardTilt j) *
          forwardPosteriorHybridBesselPenalty posterior X n ω ≤
        2 * (geometricForwardTilt j) ^ 2 * (n : ℝ) :=
    (mul_le_mul_of_nonneg_right hpsi hpenalty.1).trans
      (mul_le_mul_of_nonneg_left hpenalty.2 (by positivity))
  have hden : (2 : ℝ) ^ (j + 1) ≤
      (n : ℝ) * geometricForwardTilt j := by
    have hcast : (geometricForwardTiltTime j : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hfloor
    calc
      (2 : ℝ) ^ (j + 1) =
          (geometricForwardTiltTime j : ℝ) * geometricForwardTilt j :=
        (geometricForwardTiltTime_mul_tilt j).symm
      _ ≤ (n : ℝ) * geometricForwardTilt j :=
        mul_le_mul_of_nonneg_right hcast hlam0
  have hcomplex0 : 0 ≤ klDiv posterior prior +
      Real.log ((((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta) := by
    have hratio : 1 ≤
        (((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta := by
      apply (le_div_iff₀ hdelta).2
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    exact add_nonneg (klDiv_nonneg hposterior hprior)
      (Real.log_nonneg hratio)
  have hnpos : 0 < n := by omega
  have hdenpos : 0 < (n : ℝ) * geometricForwardTilt j :=
    mul_pos (Nat.cast_pos.mpr hnpos) (geometricForwardTilt_pos j)
  have hpowpos : 0 < (2 : ℝ) ^ (j + 1) := by positivity
  unfold countableForwardBesselPACBayesBoundary
    geometricPolynomialForwardRate
  rw [polynomialForwardTiltWeight_log_cost hdelta.ne' j]
  have hcomplex :
      (klDiv posterior prior +
          Real.log ((((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta)) /
          ((n : ℝ) * geometricForwardTilt j) ≤
        (klDiv posterior prior +
          Real.log ((((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta)) /
          (2 : ℝ) ^ (j + 1) :=
    div_le_div_of_nonneg_left hcomplex0 hpowpos hden
  calc
    (klDiv posterior prior +
        Real.log ((((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta) +
        forwardEmpiricalBernsteinPsi (geometricForwardTilt j) *
          forwardPosteriorHybridBesselPenalty posterior X n ω) /
        ((n : ℝ) * geometricForwardTilt j) =
      (klDiv posterior prior +
        Real.log ((((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta)) /
          ((n : ℝ) * geometricForwardTilt j) +
        (forwardEmpiricalBernsteinPsi (geometricForwardTilt j) *
          forwardPosteriorHybridBesselPenalty posterior X n ω) /
          ((n : ℝ) * geometricForwardTilt j) := by ring
    _ ≤ (klDiv posterior prior +
        Real.log ((((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta)) /
          (2 : ℝ) ^ (j + 1) +
        (2 * (geometricForwardTilt j) ^ 2 * (n : ℝ)) /
          ((n : ℝ) * geometricForwardTilt j) :=
      add_le_add hcomplex (div_le_div_of_nonneg_right hvar hdenpos.le)
    _ = 2 * geometricForwardTilt j +
        (klDiv posterior prior +
          Real.log ((((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta)) /
          (2 : ℝ) ^ (j + 1) := by
      field_simp [show (n : ℝ) ≠ 0 by positivity,
        (geometricForwardTilt_pos j).ne']
      ring

omit [DecidableEq ι] [Nonempty ι] in
/-- Selected exact boundaries vanish along any horizon schedule above the
geometric floors, provided the selected posterior KL is `o(2^j)`, equivalently
`o(sqrt n)` at the catalog scale.  The observation path is arbitrary. -/
theorem countableForwardBesselPACBayesBoundary_tendsto_zero
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (posterior : ℕ → ι → ℝ)
    (hposterior : ∀ j, IsPMF (posterior j))
    {X : ι → ℕ → Ω → ℝ}
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hX : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (time : ℕ → ℕ) (htime_two : ∀ j, 2 ≤ time j)
    (htime_floor : ∀ j, geometricForwardTiltTime j ≤ time j)
    (hKL : Filter.Tendsto
      (fun j ↦ klDiv (posterior j) prior / (2 : ℝ) ^ (j + 1))
      Filter.atTop (nhds 0))
    (ω : Ω) :
    Filter.Tendsto
      (fun j ↦ countableForwardBesselPACBayesBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt
        X (posterior j) delta j (time j) ω)
      Filter.atTop (nhds 0) := by
  let complexity : ℕ → ℝ := fun j ↦ klDiv (posterior j) prior
  have hrate := geometricPolynomialForwardRate_tendsto_zero
    hdelta hdelta1 (complexity := complexity) hKL
  apply squeeze_zero (g := geometricPolynomialForwardRate complexity delta)
  · intro j
    unfold countableForwardBesselPACBayesBoundary
    have hpenalty := forwardPosteriorHybridBesselPenalty_mem_Icc
      (hposterior j) (htime_two j) hX ω
    have hpsi0 := forwardEmpiricalBernsteinPsi_nonneg
      (geometricForwardTilt_pos j).le (geometricForwardTilt_lt_one j)
    have hratio : 1 ≤
        (((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta := by
      apply (le_div_iff₀ hdelta).2
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    rw [polynomialForwardTiltWeight_log_cost hdelta.ne' j]
    exact div_nonneg
      (add_nonneg
        (add_nonneg (klDiv_nonneg (hposterior j) hprior)
          (Real.log_nonneg hratio))
        (mul_nonneg hpsi0 hpenalty.1))
      (mul_nonneg (Nat.cast_nonneg _) (geometricForwardTilt_pos j).le)
  · intro j
    exact countableForwardBesselPACBayesBoundary_le_geometricRate
      hprior (hposterior j) hdelta hdelta1 hX j (time j)
      (htime_two j) (htime_floor j) ω
  · exact hrate

/-! ## Explicit all-sample-size selector and vanishing width -/

/-- Catalog atom selected at sample size `n`.  For `n >= 4`, its geometric
floor lies below `n`. -/
def geometricForwardTiltIndex (n : ℕ) : ℕ :=
  (Nat.log 4 n).pred

theorem geometricForwardTiltIndex_add_one {n : ℕ} (hn : 4 ≤ n) :
    geometricForwardTiltIndex n + 1 = Nat.log 4 n := by
  unfold geometricForwardTiltIndex
  exact Nat.succ_pred_eq_of_pos (Nat.log_pos (by norm_num) hn)

/-- The selected atom is admissible at every sample size `n >= 4`. -/
theorem geometricForwardTiltIndex_floor {n : ℕ} (hn : 4 ≤ n) :
    geometricForwardTiltTime (geometricForwardTiltIndex n) ≤ n := by
  unfold geometricForwardTiltTime
  rw [geometricForwardTiltIndex_add_one hn]
  exact Nat.pow_log_le_self 4 (by omega)

/-- The explicit sample-size selector visits arbitrarily fine tilt atoms. -/
theorem geometricForwardTiltIndex_tendsto_atTop :
    Filter.Tendsto geometricForwardTiltIndex Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  filter_upwards [Filter.eventually_ge_atTop (4 ^ (b + 1))] with n hn
  have hlog : b + 1 ≤ Nat.log 4 n :=
    Nat.le_log_of_pow_le (by norm_num) hn
  unfold geometricForwardTiltIndex
  simpa using Nat.pred_le_pred hlog

omit [DecidableEq ι] [Nonempty ι] in
/-- Every atom of a finite PMF has mass at most one. -/
theorem finitePMF_apply_le_one {rho : ι → ℝ} (hrho : IsPMF rho) (i : ι) :
    rho i ≤ 1 := by
  have hsingle := Finset.single_le_sum
    (fun j (_hj : j ∈ (Finset.univ : Finset ι)) ↦ hrho.nonneg j)
    (Finset.mem_univ i)
  simpa [hrho.sum_one] using hsingle

/-- A finite prior-dependent ceiling for every posterior KL divergence. -/
def finitePriorLogBarrier (prior : ι → ℝ) : ℝ :=
  ∑ i, -Real.log (prior i)

omit [DecidableEq ι] [Nonempty ι] in
theorem finitePriorLogBarrier_nonneg {prior : ι → ℝ}
    (hprior : IsFullSupportPMF prior) :
    0 ≤ finitePriorLogBarrier prior := by
  unfold finitePriorLogBarrier
  exact Finset.sum_nonneg fun i _ ↦ neg_nonneg.mpr
    (Real.log_nonpos (hprior.pos i).le
      (finitePMF_apply_le_one hprior.toIsPMF i))

omit [DecidableEq ι] [Nonempty ι] in
/-- A single KL summand is bounded by its prior log barrier. -/
theorem klDiv_term_le_neg_log_prior
    {rho prior : ι → ℝ} (hrho : IsPMF rho)
    (hprior : IsFullSupportPMF prior) (i : ι) :
    rho i * Real.log (rho i / prior i) ≤ -Real.log (prior i) := by
  have hrho0 := hrho.nonneg i
  have hrho1 := finitePMF_apply_le_one hrho i
  have hprior0 := hprior.pos i
  have hprior1 := finitePMF_apply_le_one hprior.toIsPMF i
  have hneglog : 0 ≤ -Real.log (prior i) := neg_nonneg.mpr
    (Real.log_nonpos hprior0.le hprior1)
  rcases hrho0.eq_or_lt with hzero | hrhopos
  · rw [← hzero]
    simp only [zero_div, Real.log_zero, zero_mul]
    exact hneglog
  · rw [Real.log_div hrhopos.ne' hprior0.ne']
    have hlogrho : Real.log (rho i) ≤ 0 :=
      Real.log_nonpos hrhopos.le hrho1
    calc
      rho i * (Real.log (rho i) - Real.log (prior i)) =
          rho i * Real.log (rho i) +
            rho i * (-Real.log (prior i)) := by ring
      _ ≤ 0 + 1 * (-Real.log (prior i)) :=
        add_le_add
          (mul_nonpos_of_nonneg_of_nonpos hrho0 hlogrho)
          (mul_le_mul_of_nonneg_right hrho1 hneglog)
      _ = -Real.log (prior i) := by ring

omit [DecidableEq ι] [Nonempty ι] in
/-- Uniform finite-class KL ceiling.  The barrier is deliberately simple;
sharpness is unnecessary for proving the selected width vanishes. -/
theorem klDiv_le_finitePriorLogBarrier
    {rho prior : ι → ℝ} (hrho : IsPMF rho)
    (hprior : IsFullSupportPMF prior) :
    klDiv rho prior ≤ finitePriorLogBarrier prior := by
  unfold klDiv finitePriorLogBarrier
  exact Finset.sum_le_sum fun i _ ↦
    klDiv_term_le_neg_log_prior hrho hprior i

omit [DecidableEq ι] [Nonempty ι] in
/-- Arbitrary posterior sequences on a finite class have negligible KL at the
selected effective sample-size scale. -/
theorem klDiv_div_geometricForwardTiltIndex_tendsto_zero
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (posterior : ℕ → ι → ℝ) (hposterior : ∀ n, IsPMF (posterior n)) :
    Filter.Tendsto
      (fun n ↦ klDiv (posterior n) prior /
        (2 : ℝ) ^ (geometricForwardTiltIndex n + 1))
      Filter.atTop (nhds 0) := by
  have hindexSucc : Filter.Tendsto
      (fun n ↦ geometricForwardTiltIndex n + 1)
      Filter.atTop Filter.atTop := by
    simpa only [Function.comp_def] using
      (Filter.tendsto_add_atTop_nat 1).comp
        geometricForwardTiltIndex_tendsto_atTop
  have hden : Filter.Tendsto
      (fun n ↦ (2 : ℝ) ^ (geometricForwardTiltIndex n + 1))
      Filter.atTop Filter.atTop := by
    simpa only [Function.comp_def] using
      (tendsto_pow_atTop_atTop_of_one_lt
        (by norm_num : (1 : ℝ) < 2)).comp hindexSucc
  have hupper : Filter.Tendsto
      (fun n ↦ finitePriorLogBarrier prior /
        (2 : ℝ) ^ (geometricForwardTiltIndex n + 1))
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  apply squeeze_zero
  · intro n
    exact div_nonneg (klDiv_nonneg (hposterior n) hprior) (by positivity)
  · intro n
    exact div_le_div_of_nonneg_right
      (klDiv_le_finitePriorLogBarrier (hposterior n) hprior) (by positivity)
  · exact hupper

/-- Explicit all-sample-size rate obtained by substituting
`geometricForwardTiltIndex n` into the countable catalog. -/
def allTimeGeometricPolynomialForwardRate
    (complexity : ℕ → ℝ) (delta : ℝ) (n : ℕ) : ℝ :=
  2 * geometricForwardTilt (geometricForwardTiltIndex n) +
    (complexity n +
        Real.log ((((geometricForwardTiltIndex n : ℝ) + 1) *
          ((geometricForwardTiltIndex n : ℝ) + 2)) / delta)) /
      (2 : ℝ) ^ (geometricForwardTiltIndex n + 1)

/-- The all-sample-size rate vanishes whenever its time-indexed complexity is
negligible relative to the selected effective sample size. -/
theorem allTimeGeometricPolynomialForwardRate_tendsto_zero
    {complexity : ℕ → ℝ} {delta : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hcomplexity : Filter.Tendsto
      (fun n ↦ complexity n /
        (2 : ℝ) ^ (geometricForwardTiltIndex n + 1))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (allTimeGeometricPolynomialForwardRate complexity delta)
      Filter.atTop (nhds 0) := by
  have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0
    (by norm_num : (1 : ℝ) < 2)
  have htiltBase : Filter.Tendsto geometricForwardTilt
      Filter.atTop (nhds 0) := by
    have hscaled := h0.const_mul (1 / 2)
    convert hscaled using 1
    · funext j
      unfold geometricForwardTilt
      rw [pow_succ]
      ring
    · norm_num
  have htilt : Filter.Tendsto
      (fun n ↦ geometricForwardTilt (geometricForwardTiltIndex n))
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def] using
      htiltBase.comp geometricForwardTiltIndex_tendsto_atTop
  have hlogBase :=
    polynomialForwardTilt_log_cost_div_geometric_tendsto_zero hdelta hdelta1
  have hlog : Filter.Tendsto
      (fun n ↦ Real.log ((((geometricForwardTiltIndex n : ℝ) + 1) *
        ((geometricForwardTiltIndex n : ℝ) + 2)) / delta) /
          (2 : ℝ) ^ (geometricForwardTiltIndex n + 1))
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def] using
      hlogBase.comp geometricForwardTiltIndex_tendsto_atTop
  have hsum := htilt.const_mul 2 |>.add (hcomplexity.add hlog)
  convert hsum using 1
  · funext n
    rw [allTimeGeometricPolynomialForwardRate, add_div]
  · norm_num

omit [DecidableEq ι] [Nonempty ι] in
/-- Nonnegativity of the exact geometric-catalog boundary on unit-valued
prefixes. -/
theorem countableForwardBesselPACBayesBoundary_nonneg
    {prior posterior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (hposterior : IsPMF posterior)
    {X : ι → ℕ → Ω → ℝ} {delta : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hX : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (j n : ℕ) (hn : 2 ≤ n) (ω : Ω) :
    0 ≤ countableForwardBesselPACBayesBoundary
      prior polynomialForwardTiltWeight geometricForwardTilt
      X posterior delta j n ω := by
  unfold countableForwardBesselPACBayesBoundary
  have hpenalty := forwardPosteriorHybridBesselPenalty_mem_Icc
    hposterior hn hX ω
  have hpsi0 := forwardEmpiricalBernsteinPsi_nonneg
    (geometricForwardTilt_pos j).le (geometricForwardTilt_lt_one j)
  have hratio : 1 ≤
      (((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta := by
    apply (le_div_iff₀ hdelta).2
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  rw [polynomialForwardTiltWeight_log_cost hdelta.ne' j]
  exact div_nonneg
    (add_nonneg
      (add_nonneg (klDiv_nonneg hposterior hprior)
        (Real.log_nonneg hratio))
      (mul_nonneg hpsi0 hpenalty.1))
    (mul_nonneg (Nat.cast_nonneg _) (geometricForwardTilt_pos j).le)

omit [DecidableEq ι] [Nonempty ι] in
/-- At every `n >= 4`, the explicit selected exact boundary is controlled by
the all-sample-size deterministic rate. -/
theorem countableForwardBesselPACBayesBoundary_selected_le_allTimeRate
    {prior posterior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (hposterior : IsPMF posterior)
    {X : ι → ℕ → Ω → ℝ} {delta : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hX : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    {n : ℕ} (hn : 4 ≤ n) (ω : Ω) :
    countableForwardBesselPACBayesBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt
        X posterior delta (geometricForwardTiltIndex n) n ω ≤
      allTimeGeometricPolynomialForwardRate
        (fun _ ↦ klDiv posterior prior) delta n := by
  have hbound := countableForwardBesselPACBayesBoundary_le_geometricRate
    hprior hposterior hdelta hdelta1 hX
    (geometricForwardTiltIndex n) n (by omega)
    (geometricForwardTiltIndex_floor hn) ω
  simpa [allTimeGeometricPolynomialForwardRate,
    geometricPolynomialForwardRate] using hbound

omit [DecidableEq ι] [Nonempty ι] in
/-- For every integer sample size, the explicitly selected exact boundary
converges to zero.  The posterior may vary arbitrarily with time; finite full
support supplies the required uniform KL ceiling. -/
theorem countableForwardBesselPACBayesBoundary_selected_tendsto_zero
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (posterior : ℕ → ι → ℝ) (hposterior : ∀ n, IsPMF (posterior n))
    {X : ι → ℕ → Ω → ℝ} {delta : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hX : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (ω : Ω) :
    Filter.Tendsto
      (fun n ↦ countableForwardBesselPACBayesBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt
        X (posterior n) delta (geometricForwardTiltIndex n) n ω)
      Filter.atTop (nhds 0) := by
  let complexity : ℕ → ℝ := fun n ↦ klDiv (posterior n) prior
  have hcomplexity : Filter.Tendsto
      (fun n ↦ complexity n /
        (2 : ℝ) ^ (geometricForwardTiltIndex n + 1))
      Filter.atTop (nhds 0) :=
    klDiv_div_geometricForwardTiltIndex_tendsto_zero
      hprior posterior hposterior
  have hrate := allTimeGeometricPolynomialForwardRate_tendsto_zero
    hdelta hdelta1 hcomplexity
  apply squeeze_zero'
  · filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    exact countableForwardBesselPACBayesBoundary_nonneg
      hprior (hposterior n) hdelta hdelta1 hX
      (geometricForwardTiltIndex n) n (by omega) ω
  · filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    exact countableForwardBesselPACBayesBoundary_selected_le_allTimeRate
      hprior (hposterior n) hdelta hdelta1 hX hn ω
  · exact hrate

/-- One outer-mass event supports arbitrary path- and time-dependent finite
posteriors, the explicit atom selected at every sample size, and an exact
boundary whose width converges to zero over all integer times.  No
measurability of the posterior selector is needed: selection is substitution
into the common event. -/
theorem exists_geometricForwardBesselPACBayes_allTime_vanishing_event
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ}
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] fun _ ↦ mean i)
    (posterior : Ω → ℕ → ι → ℝ)
    (hposterior : ∀ ω n, IsPMF (posterior ω n)) :
    ∃ goodEvent : Set Ω,
      μ.real goodEventᶜ ≤ delta ∧
        (∀ ω ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
          posteriorAverage (posterior ω n) mean <
            posteriorAverage (posterior ω n)
                (fun i ↦ forwardPrefixMean (fun k ↦ X i k ω) n) +
              countableForwardBesselPACBayesBoundary
                prior polynomialForwardTiltWeight geometricForwardTilt
                X (posterior ω n) delta
                (geometricForwardTiltIndex n) n ω) ∧
        (∀ ω ∈ goodEvent,
          Filter.Tendsto
            (fun n ↦ countableForwardBesselPACBayesBoundary
              prior polynomialForwardTiltWeight geometricForwardTilt
              X (posterior ω n) delta
              (geometricForwardTiltIndex n) n ω)
            Filter.atTop (nhds 0)) := by
  obtain ⟨goodEvent, hmass, hgood⟩ :=
    exists_geometricForwardBesselPACBayes_event
      hprior hdelta hX_adapted hX_unit hmean
  refine ⟨goodEvent, hmass, ?_, ?_⟩
  · intro ω hω n hn
    exact hgood ω hω (geometricForwardTiltIndex n) (posterior ω n)
      (hposterior ω n) n hn
  · intro ω _hω
    exact countableForwardBesselPACBayesBoundary_selected_tendsto_zero
      hprior (posterior ω) (hposterior ω)
      hdelta hdelta1 hX_unit ω

end

end FormalSLT.PACBayes.ForwardBesselPACBayesCountable
