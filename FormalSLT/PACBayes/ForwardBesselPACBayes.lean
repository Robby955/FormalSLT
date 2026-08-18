/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.AnytimeValid.ForwardBesselProcess
import FormalSLT.PACBayesKL

/-!
# Time-uniform forward-Bessel PAC-Bayes bounds

This module mixes the actual predictable-residual lower-tail e-process over a
finite hypothesis prior and a finite predeclared tilt catalog.  A single
countable-time Ville event then supports every eligible time `n >= 2`, every
posterior PMF, and every declared tilt.  The boundary pays the exact confidence
and atom penalty `log (1 / (delta * weight j))` in addition to the hypothesis
`KL` term.

The observable hybrid-Bessel expression is used only as a pointwise lower
envelope of each actual predictable-residual e-process.  It is not asserted to
be an e-process or a supermartingale.  The posterior penalty is the posterior
average of the per-hypothesis hybrid minima; it is not a minimum taken after
posterior averaging.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open scoped BigOperators

namespace FormalSLT.PACBayes.ForwardBesselPACBayes

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {ι κ Ω : Type*}
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ mΩ}

/-- Posterior average of the per-hypothesis hybrid Bessel penalties.  The
minimum is taken separately for each hypothesis before posterior averaging. -/
def forwardPosteriorHybridBesselPenalty
    (posterior : ι → ℝ) (X : ι → ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  posteriorAverage posterior fun i ↦
    forwardHybridBesselPenalty (fun k ↦ X i k ω) n

/-- Per-hypothesis hybrid-Bessel score used in the finite
Donsker--Varadhan step.  Its exponential is a lower envelope of the actual
lower-tail e-process, not itself an e-process. -/
def forwardBesselPACBayesScore
    (X : ι → ℕ → Ω → ℝ) (mean : ι → ℝ) (lam : ℝ)
    (i : ι) (n : ℕ) (ω : Ω) : ℝ :=
  lam * (∑ k ∈ Finset.range n, (mean i - X i k ω)) -
    forwardEmpiricalBernsteinPsi lam *
      forwardHybridBesselPenalty (fun k ↦ X i k ω) n

omit [DecidableEq ι] [Nonempty ι] in
/-- Exact posterior score identity. -/
theorem posteriorAverage_forwardBesselPACBayesScore
    (posterior : ι → ℝ) (X : ι → ℕ → Ω → ℝ)
    (mean : ι → ℝ) (lam : ℝ) {n : ℕ} (hn : 0 < n) (ω : Ω) :
    posteriorAverage posterior
        (fun i ↦ forwardBesselPACBayesScore X mean lam i n ω) =
      (n : ℝ) * lam *
          (posteriorAverage posterior mean -
            posteriorAverage posterior
              (fun i ↦ forwardPrefixMean (fun k ↦ X i k ω) n)) -
        forwardEmpiricalBernsteinPsi lam *
          forwardPosteriorHybridBesselPenalty posterior X n ω := by
  unfold posteriorAverage forwardBesselPACBayesScore
    forwardPosteriorHybridBesselPenalty
  simp_rw [sum_mean_sub_eq_mul_sub_forwardPrefixMean
    (fun k ↦ X _ k ω) (mean _) hn]
  rw [show
      (∑ i : ι, posterior i *
        (lam * ((n : ℝ) *
            (mean i - forwardPrefixMean (fun k ↦ X i k ω) n)) -
          forwardEmpiricalBernsteinPsi lam *
            forwardHybridBesselPenalty (fun k ↦ X i k ω) n)) =
        ∑ i : ι,
          ((n : ℝ) * lam * posterior i * mean i -
            (n : ℝ) * lam * posterior i *
              forwardPrefixMean (fun k ↦ X i k ω) n -
            forwardEmpiricalBernsteinPsi lam * posterior i *
              forwardHybridBesselPenalty (fun k ↦ X i k ω) n) by
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hmean_sum :
      (∑ i : ι, (n : ℝ) * lam * posterior i * mean i) =
        (n : ℝ) * lam * ∑ i : ι, posterior i * mean i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hpref_sum :
      (∑ i : ι, (n : ℝ) * lam * posterior i *
        forwardPrefixMean (fun k ↦ X i k ω) n) =
        (n : ℝ) * lam * ∑ i : ι,
          posterior i * forwardPrefixMean (fun k ↦ X i k ω) n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hpen_sum :
      (∑ i : ι, forwardEmpiricalBernsteinPsi lam * posterior i *
        forwardHybridBesselPenalty (fun k ↦ X i k ω) n) =
        forwardEmpiricalBernsteinPsi lam * ∑ i : ι,
          posterior i * forwardHybridBesselPenalty (fun k ↦ X i k ω) n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hmean_sum, hpref_sum, hpen_sum]
  unfold posteriorAverage
  ring

/-- Nested finite mixture of the actual lower-tail predictable-residual
e-processes over hypothesis prior and tilt weights. -/
def forwardBesselPACBayesMasterProcess
    (prior : ι → ℝ) (weight : κ → ℝ)
    (X : ι → ℕ → Ω → ℝ) (mean : ι → ℝ)
    (lam : κ → ℝ) : ℕ → Ω → ℝ :=
  finiteWeightedProcess weight fun j ↦
    finiteWeightedProcess prior fun i ↦
      forwardEmpiricalBernsteinLowerProcess (X i) (mean i) (lam j)

omit [Nonempty ι] [Nonempty κ] in
/-- The nested prior--tilt mixture of actual predictable-residual processes is
one e-process under the bounded conditional-mean model. -/
theorem forwardBesselPACBayesMasterProcess_eProcess_of_bounded
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ} {lam : κ → ℝ}
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] fun _ ↦ mean i) :
    EProcess μ ℱ
      (forwardBesselPACBayesMasterProcess prior weight X mean lam) := by
  unfold forwardBesselPACBayesMasterProcess
  apply finiteWeightedProcess_eProcess
    hweight.nonneg hweight.sum_one
  intro j
  apply finiteWeightedProcess_eProcess
    hprior.nonneg hprior.sum_one
  intro i
  exact forwardEmpiricalBernsteinLowerProcess_eProcess_of_bounded
    (hlam j).le (hlam1 j) (hX_adapted i) (hX_unit i) (hmean i)

/-- Exact posterior hybrid-Bessel boundary for catalog atom `j`. -/
def forwardBesselPACBayesBoundary
    (prior : ι → ℝ) (weight : κ → ℝ) (lam : κ → ℝ)
    (X : ι → ℕ → Ω → ℝ) (posterior : ι → ℝ)
    (delta : ℝ) (j : κ) (n : ℕ) (ω : Ω) : ℝ :=
  (klDiv posterior prior + Real.log (1 / (delta * weight j)) +
      forwardEmpiricalBernsteinPsi (lam j) *
        forwardPosteriorHybridBesselPenalty posterior X n ω) /
    ((n : ℝ) * lam j)

/-- The single exceptional event: the actual nested master e-process crosses
`1 / delta` at some time. -/
def forwardBesselPACBayesExceptionalEvent
    (prior : ι → ℝ) (weight : κ → ℝ)
    (X : ι → ℕ → Ω → ℝ) (mean : ι → ℝ)
    (lam : κ → ℝ) (delta : ℝ) : Set Ω :=
  atTopCrossingEvent
    (forwardBesselPACBayesMasterProcess prior weight X mean lam)
    (1 / delta)

omit [Nonempty ι] [Nonempty κ] in
/-- Countable-time Ville control for the single nested master process. -/
theorem forwardBesselPACBayesExceptionalEvent_mass_le_delta
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ} {lam : κ → ℝ}
    {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] fun _ ↦ mean i) :
    μ.real
        (forwardBesselPACBayesExceptionalEvent
          prior weight X mean lam delta) ≤
      delta := by
  have hE := forwardBesselPACBayesMasterProcess_eProcess_of_bounded
    hprior hweight hlam hlam1 hX_adapted hX_unit hmean
  have hville := ville_atTop_maximal_ineq
    (μ := μ) (𝒢 := ℱ)
    (M := forwardBesselPACBayesMasterProcess prior weight X mean lam)
    hE.supermartingale hE.nonneg (one_div_pos.mpr hdelta)
  rw [hE.integral_start_eq_one] at hville
  unfold forwardBesselPACBayesExceptionalEvent
  calc
    μ.real
        (atTopCrossingEvent
          (forwardBesselPACBayesMasterProcess prior weight X mean lam)
          (1 / delta)) =
        delta * ((1 / delta) *
          μ.real
            (atTopCrossingEvent
              (forwardBesselPACBayesMasterProcess prior weight X mean lam)
              (1 / delta))) := by
      field_simp [hdelta.ne']
    _ ≤ delta * 1 := mul_le_mul_of_nonneg_left hville hdelta.le
    _ = delta := by ring

omit [DecidableEq ι] [DecidableEq κ] [Nonempty κ] in
/-- Donsker--Varadhan inversion for the hybrid-Bessel boundary.  A failure for
one posterior, time, and declared tilt forces the single actual master
e-process into its canonical crossing event. -/
theorem forwardBesselPACBayes_boundaryFailure_mem_exceptionalEvent
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ} {lam : κ → ℝ}
    {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    {posterior : ι → ℝ} (hposterior : IsPMF posterior)
    {j : κ} {n : ℕ} {ω : Ω} (hn : 2 ≤ n)
    (hfail :
      forwardBesselPACBayesBoundary
          prior weight lam X posterior delta j n ω ≤
        posteriorAverage posterior mean -
          posteriorAverage posterior
            (fun i ↦ forwardPrefixMean (fun k ↦ X i k ω) n)) :
    ω ∈ forwardBesselPACBayesExceptionalEvent
      prior weight X mean lam delta := by
  classical
  have hnpos : 0 < n := by omega
  have hdenpos : 0 < (n : ℝ) * lam j :=
    mul_pos (Nat.cast_pos.mpr hnpos) (hlam j)
  unfold forwardBesselPACBayesBoundary at hfail
  have hfail_mul := (div_le_iff₀ hdenpos).mp hfail
  have hscore_identity :=
    posteriorAverage_forwardBesselPACBayesScore
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
    one_div_pos.mpr (mul_pos hdelta (hweight.pos j))
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
        finiteWeightedProcess prior
          (fun i ↦ forwardEmpiricalBernsteinLowerProcess
            (X i) (mean i) (lam j)) n ω := by
    unfold finiteWeightedProcess
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
        finiteWeightedProcess prior
          (fun i ↦ forwardEmpiricalBernsteinLowerProcess
            (X i) (mean i) (lam j)) n ω :=
    hthreshold_le_moment.trans hmoment_le_inner
  have hweighted :
      weight j * (1 / (delta * weight j)) ≤
        weight j *
          finiteWeightedProcess prior
            (fun i ↦ forwardEmpiricalBernsteinLowerProcess
              (X i) (mean i) (lam j)) n ω :=
    mul_le_mul_of_nonneg_left hinner (hweight.nonneg j)
  have hsingle :
      weight j *
          finiteWeightedProcess prior
            (fun i ↦ forwardEmpiricalBernsteinLowerProcess
              (X i) (mean i) (lam j)) n ω ≤
        forwardBesselPACBayesMasterProcess
          prior weight X mean lam n ω := by
    unfold forwardBesselPACBayesMasterProcess finiteWeightedProcess
    exact Finset.single_le_sum
      (f := fun k ↦ weight k *
        (∑ i : ι, prior i *
          forwardEmpiricalBernsteinLowerProcess
            (X i) (mean i) (lam k) n ω))
      (fun k _ ↦ mul_nonneg (hweight.nonneg k)
        (Finset.sum_nonneg fun i _ ↦
          mul_nonneg (hprior.nonneg i)
            (by
              rw [forwardEmpiricalBernsteinLowerProcess_eq]
              exact (Real.exp_pos _).le)))
      (Finset.mem_univ j)
  rw [show weight j * (1 / (delta * weight j)) = 1 / delta by
    field_simp [hdelta.ne', (hweight.pos j).ne']] at hweighted
  unfold forwardBesselPACBayesExceptionalEvent
  exact ⟨n, hweighted.trans hsingle⟩

omit [DecidableEq ι] [DecidableEq κ] [Nonempty κ] in
/-- Outside the canonical master crossing event, every posterior PMF satisfies
every declared tilt boundary at every time `n >= 2`. -/
theorem forwardBesselPACBayes_allPosteriors_of_not_mem
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ} {lam : κ → ℝ}
    {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    {ω : Ω}
    (hω : ω ∉ forwardBesselPACBayesExceptionalEvent
      prior weight X mean lam delta) :
    ∀ j : κ, ∀ posterior : ι → ℝ, IsPMF posterior →
      ∀ n : ℕ, 2 ≤ n →
        posteriorAverage posterior mean <
          posteriorAverage posterior
              (fun i ↦ forwardPrefixMean (fun k ↦ X i k ω) n) +
            forwardBesselPACBayesBoundary
              prior weight lam X posterior delta j n ω := by
  intro j posterior hposterior n hn
  apply lt_of_not_ge
  intro hfail
  apply hω
  exact forwardBesselPACBayes_boundaryFailure_mem_exceptionalEvent
    hprior hweight hdelta hlam hlam1 hX_unit hposterior hn (by linarith)

omit [DecidableEq ι] [DecidableEq κ] [Nonempty κ] in
/-- Explicit posterior-and-tilt selector.  Both the posterior and the declared
tilt atom may depend on the full realized path and the current time because the
common event is already uniform over posterior, atom, and time. -/
theorem forwardBesselPACBayes_selected_of_not_mem
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ} {lam : κ → ℝ}
    {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    {ω : Ω}
    (hω : ω ∉ forwardBesselPACBayesExceptionalEvent
      prior weight X mean lam delta)
    (posterior : Ω → ℕ → ι → ℝ)
    (hposterior : ∀ ω n, IsPMF (posterior ω n))
    (select : Ω → ℕ → (ι → ℝ) → κ)
    (n : ℕ) (hn : 2 ≤ n) :
    posteriorAverage (posterior ω n) mean <
      posteriorAverage (posterior ω n)
          (fun i ↦ forwardPrefixMean (fun k ↦ X i k ω) n) +
        forwardBesselPACBayesBoundary
          prior weight lam X (posterior ω n) delta
            (select ω n (posterior ω n)) n ω :=
  forwardBesselPACBayes_allPosteriors_of_not_mem
    hprior hweight hdelta hlam hlam1 hX_unit hω
    (select ω n (posterior ω n)) (posterior ω n)
    (hposterior ω n) n hn

omit [Nonempty κ] in
/-- One outer-probability event carries the hybrid-Bessel PAC-Bayes boundary
simultaneously for every eligible time `n >= 2`, posterior PMF, and declared
tilt.  As in the underlying atTop API, this packages a `Measure.real` bound
without a separate measurability certificate for the event. -/
theorem exists_forwardBesselPACBayes_event
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ} {lam : κ → ℝ}
    {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] fun _ ↦ mean i) :
    ∃ goodEvent : Set Ω,
      μ.real goodEventᶜ ≤ delta ∧
        ∀ ω ∈ goodEvent, ∀ j : κ,
          ∀ posterior : ι → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              posteriorAverage posterior mean <
                posteriorAverage posterior
                    (fun i ↦ forwardPrefixMean (fun k ↦ X i k ω) n) +
                  forwardBesselPACBayesBoundary
                    prior weight lam X posterior delta j n ω := by
  let badEvent := forwardBesselPACBayesExceptionalEvent
    prior weight X mean lam delta
  refine ⟨badEventᶜ, ?_, ?_⟩
  · simpa [badEvent] using
      (forwardBesselPACBayesExceptionalEvent_mass_le_delta
        hprior hweight hdelta hlam hlam1 hX_adapted hX_unit hmean)
  · intro ω hω
    exact forwardBesselPACBayes_allPosteriors_of_not_mem
      hprior hweight hdelta hlam hlam1 hX_unit hω

end

end FormalSLT.PACBayes.ForwardBesselPACBayes
