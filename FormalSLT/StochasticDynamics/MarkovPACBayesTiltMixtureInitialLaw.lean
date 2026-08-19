/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.StochasticDynamics.MarkovPACBayesTiltMixture

/-!
# Random initial laws for finite Markov PAC-Bayes risk

This module removes the deterministic-start restriction from the finite weighted-tilt
Markov PAC-Bayes certificate. A supplied finite-state initial PMF mixes the already
checked Ionescu--Tulcea path laws for every deterministic start. The raw posterior/time/tilt
failure set does not depend on the initial state, so its outer mass remains at most `delta`
under the mixture with no union bound and no additional confidence penalty. One measurable
hull is taken only after this raw-mass calculation.

The result retains the scope of `MarkovPACBayesTiltMixture`: a finite state space, homogeneous
transition PMFs, fixed `[0,1]` observable and finite predictor catalog, squared one-step loss,
full-support finite predictor and tilt priors fixed before the trajectory, and declared tilts
in `(0, 3)`. The initial PMF need not have full support. The target is the encountered
transition-row conditional risk, not stationary risk. This is not a stationary or mixing
theorem, a same-trajectory training theorem, a predictable time-varying predictor or tilt
theorem, a countable or all-real tilt optimizer, or a continuous-state result.
-/

open Filter Finset Function MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open scoped BigOperators ENNReal NNReal Topology

namespace FormalSLT.StochasticDynamics

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {ι κ Z : Type*}
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]
  [Fintype Z] [DecidableEq Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- The finite random-initial Markov path law: first draw `x0` from `initial`, then use the
checked deterministic-start Ionescu--Tulcea path law from `x0`. -/
def markovPathMeasureInitial (P : Z → PMF Z) (initial : PMF Z) : Measure (ℕ → Z) :=
  ∑ z, initial z • markovPathMeasure P z

instance markovPathMeasureInitial.instIsProbabilityMeasure
    (P : Z → PMF Z) (initial : PMF Z) :
    IsProbabilityMeasure (markovPathMeasureInitial P initial) := by
  rw [isProbabilityMeasure_iff]
  simp only [markovPathMeasureInitial, Measure.finsetSum_apply,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  simpa only [tsum_fintype] using initial.tsum_coe

/-- A point-mass initial law recovers the existing deterministic-start path law. -/
@[simp]
theorem markovPathMeasureInitial_pure (P : Z → PMF Z) (x0 : Z) :
    markovPathMeasureInitial P (PMF.pure x0) = markovPathMeasure P x0 := by
  ext S hS
  simp [markovPathMeasureInitial, PMF.pure_apply]

omit [DecidableEq Z] in
/-- A common outer-mass bound under every deterministic start is preserved by an arbitrary
finite initial PMF. The set need not be measurable. -/
theorem markovPathMeasureInitial_real_le_of_forall_start
    (P : Z → PMF Z) (initial : PMF Z) (S : Set (ℕ → Z))
    {c : ℝ}
    (hS : ∀ x0, (markovPathMeasure P x0).real S ≤ c) :
    (markovPathMeasureInitial P initial).real S ≤ c := by
  have hweightsENN : ∑ z, initial z = (1 : ENNReal) := by
    simpa only [tsum_fintype] using initial.tsum_coe
  have hweights : ∑ z, (initial z).toReal = (1 : ℝ) := by
    rw [← ENNReal.toReal_sum (fun z _hz ↦ initial.apply_ne_top z), hweightsENN]
    norm_num
  rw [markovPathMeasureInitial, Measure.real, Measure.finsetSum_apply]
  simp_rw [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum (fun z _hz ↦ by
    exact ENNReal.mul_ne_top (initial.apply_ne_top z)
      (measure_ne_top (markovPathMeasure P z) S))]
  simp_rw [ENNReal.toReal_mul]
  calc
    ∑ z, (initial z).toReal * (markovPathMeasure P z).real S ≤
        ∑ z, (initial z).toReal * c := by
      apply Finset.sum_le_sum
      intro z _hz
      exact mul_le_mul_of_nonneg_left (hS z) ENNReal.toReal_nonneg
    _ = (∑ z, (initial z).toReal) * c := by rw [Finset.sum_mul]
    _ = c := by rw [hweights, one_mul]

omit [DecidableEq ι] [DecidableEq κ] [Nonempty κ] [DecidableEq Z] in
/-- The common raw posterior/time/tilt failure set has outer mass at most `delta` under any
supplied finite initial PMF. -/
theorem markovPACBayes_tiltMixture_allPosteriors_bound_initialLaw
    (P : Z → PMF Z) (initial : PMF Z) {f : Z → ℝ} {q : ι → Z → ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ i z, q i z ∈ Set.Icc (0 : ℝ) 1)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : κ → ℝ} {delta : ℝ}
    (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_three : ∀ j, lam j < 3) :
    (markovPathMeasureInitial P initial).real
      (markovPACBayesTiltMixtureAnyPosteriorUpperFailure
        prior weight P f q lam delta) ≤ delta := by
  exact markovPathMeasureInitial_real_le_of_forall_start
    P initial
    (markovPACBayesTiltMixtureAnyPosteriorUpperFailure
      prior weight P f q lam delta)
    (fun x0 ↦ markovPACBayes_tiltMixture_allPosteriors_bound
      P x0 hf hq hprior hweight hdelta hlam hlam_three)

/-- Measurable hull of the common raw Markov PAC-Bayes failure set under a supplied initial PMF. -/
def markovPACBayesTiltMixtureInitialLawExceptionalEvent
    (prior : ι → ℝ) (weight : κ → ℝ)
    (P : Z → PMF Z) (initial : PMF Z)
    (f : Z → ℝ) (q : ι → Z → ℝ)
    (lam : κ → ℝ) (delta : ℝ) : Set (ℕ → Z) :=
  toMeasurable (markovPathMeasureInitial P initial)
    (markovPACBayesTiltMixtureAnyPosteriorUpperFailure
      prior weight P f q lam delta)

omit [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
  [DecidableEq Z] in
theorem markovPACBayesTiltMixtureInitialLawExceptionalEvent_measurable
    (prior : ι → ℝ) (weight : κ → ℝ)
    (P : Z → PMF Z) (initial : PMF Z)
    (f : Z → ℝ) (q : ι → Z → ℝ)
    (lam : κ → ℝ) (delta : ℝ) :
    MeasurableSet (markovPACBayesTiltMixtureInitialLawExceptionalEvent
      prior weight P initial f q lam delta) :=
  measurableSet_toMeasurable _ _

omit [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
  [DecidableEq Z] in
theorem markovPACBayesTiltMixtureRawFailure_subset_initialLawExceptionalEvent
    (prior : ι → ℝ) (weight : κ → ℝ)
    (P : Z → PMF Z) (initial : PMF Z)
    (f : Z → ℝ) (q : ι → Z → ℝ)
    (lam : κ → ℝ) (delta : ℝ) :
    markovPACBayesTiltMixtureAnyPosteriorUpperFailure
        prior weight P f q lam delta ⊆
      markovPACBayesTiltMixtureInitialLawExceptionalEvent
        prior weight P initial f q lam delta :=
  subset_toMeasurable _ _

omit [DecidableEq ι] [DecidableEq κ] [Nonempty κ] [DecidableEq Z] in
/-- The single measurable random-initial-law exceptional event has ordinary probability at
most `delta`. -/
theorem markovPACBayesTiltMixtureInitialLawExceptionalEvent_mass_le_delta
    (P : Z → PMF Z) (initial : PMF Z) {f : Z → ℝ} {q : ι → Z → ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ i z, q i z ∈ Set.Icc (0 : ℝ) 1)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : κ → ℝ} {delta : ℝ}
    (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_three : ∀ j, lam j < 3) :
    (markovPathMeasureInitial P initial).real
      (markovPACBayesTiltMixtureInitialLawExceptionalEvent
        prior weight P initial f q lam delta) ≤ delta := by
  rw [markovPACBayesTiltMixtureInitialLawExceptionalEvent,
    Measure.real, measure_toMeasurable]
  exact markovPACBayes_tiltMixture_allPosteriors_bound_initialLaw
    P initial hf hq hprior hweight hdelta hlam hlam_three

omit [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
  [DecidableEq Z] in
/-- Outside the common random-initial-law event, every posterior, positive time, and declared
tilt obeys the Markov prequential upper-risk certificate. -/
theorem markovPosteriorAverageConditionalRisk_lt_tiltMixture_initialLaw_of_not_mem
    (prior : ι → ℝ) (weight : κ → ℝ)
    (P : Z → PMF Z) (initial : PMF Z)
    (f : Z → ℝ) (q : ι → Z → ℝ)
    {lam : κ → ℝ} {delta : ℝ} {x : ℕ → Z}
    (hx : x ∉ markovPACBayesTiltMixtureInitialLawExceptionalEvent
      prior weight P initial f q lam delta)
    (j : κ) (posterior : ι → ℝ) (hposterior : IsPMF posterior)
    (n : ℕ) (hn : 0 < n) :
    markovPosteriorAverageConditionalRisk P f q posterior n x <
      markovPosteriorEmpiricalPrequentialRisk f q posterior n x +
        subGammaCgf (1 / 4) 1 (lam j) / lam j +
        (klDiv posterior prior + Real.log (1 / (delta * weight j))) /
          ((n : ℝ) * lam j) := by
  have hxraw : x ∉ markovPACBayesTiltMixtureAnyPosteriorUpperFailure
      prior weight P f q lam delta :=
    fun hraw ↦ hx
      (markovPACBayesTiltMixtureRawFailure_subset_initialLawExceptionalEvent
        prior weight P initial f q lam delta hraw)
  have hgap :
      markovPosteriorAverageConditionalRisk P f q posterior n x -
          markovPosteriorEmpiricalPrequentialRisk f q posterior n x <
        subGammaCgf (1 / 4) 1 (lam j) / lam j +
          (klDiv posterior prior + Real.log (1 / (delta * weight j))) /
            ((n : ℝ) * lam j) := by
    exact lt_of_not_ge fun hfailure ↦
      hxraw ⟨j, posterior, hposterior, n, hn, hfailure⟩
  linarith

omit [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
  [DecidableEq Z] in
/-- A pointwise path- and posterior-dependent selector may choose one predeclared finite tilt
atom on the common random-initial-law event. -/
theorem markovPosteriorAverageConditionalRisk_lt_tiltMixture_initialLaw_selected_of_not_mem
    (prior : ι → ℝ) (weight : κ → ℝ)
    (P : Z → PMF Z) (initial : PMF Z)
    (f : Z → ℝ) (q : ι → Z → ℝ)
    {lam : κ → ℝ} {delta : ℝ} {x : ℕ → Z}
    (hx : x ∉ markovPACBayesTiltMixtureInitialLawExceptionalEvent
      prior weight P initial f q lam delta)
    (select : (ℕ → Z) → (ι → ℝ) → κ)
    (posterior : ι → ℝ) (hposterior : IsPMF posterior)
    (n : ℕ) (hn : 0 < n) :
    markovPosteriorAverageConditionalRisk P f q posterior n x <
      markovPosteriorEmpiricalPrequentialRisk f q posterior n x +
        subGammaCgf (1 / 4) 1 (lam (select x posterior)) /
          lam (select x posterior) +
        (klDiv posterior prior +
          Real.log (1 / (delta * weight (select x posterior)))) /
            ((n : ℝ) * lam (select x posterior)) := by
  exact markovPosteriorAverageConditionalRisk_lt_tiltMixture_initialLaw_of_not_mem
    prior weight P initial f q hx (select x posterior) posterior hposterior n hn

omit [DecidableEq ι] [DecidableEq κ] [Nonempty κ] [DecidableEq Z] in
/-- Publication-facing random-initial-law finite weighted-tilt Markov PAC-Bayes certificate. -/
theorem markovPACBayes_tiltMixture_prequentialRisk_certificate_initialLaw
    (P : Z → PMF Z) (initial : PMF Z) {f : Z → ℝ} {q : ι → Z → ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ i z, q i z ∈ Set.Icc (0 : ℝ) 1)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : κ → ℝ} {delta : ℝ}
    (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_three : ∀ j, lam j < 3) :
    ∃ E : Set (ℕ → Z),
      MeasurableSet E ∧
      (markovPathMeasureInitial P initial).real E ≤ delta ∧
      ∀ x ∉ E, ∀ j : κ,
        ∀ posterior : ι → ℝ, IsPMF posterior →
          ∀ n : ℕ, 0 < n →
            markovPosteriorAverageConditionalRisk P f q posterior n x <
              markovPosteriorEmpiricalPrequentialRisk f q posterior n x +
                lam j / (8 * (1 - lam j / 3)) +
                (klDiv posterior prior +
                  Real.log (1 / (delta * weight j))) /
                    ((n : ℝ) * lam j) := by
  let E := markovPACBayesTiltMixtureInitialLawExceptionalEvent
    prior weight P initial f q lam delta
  refine ⟨E, markovPACBayesTiltMixtureInitialLawExceptionalEvent_measurable
    prior weight P initial f q lam delta, ?_, ?_⟩
  · exact markovPACBayesTiltMixtureInitialLawExceptionalEvent_mass_le_delta
      P initial hf hq hprior hweight hdelta hlam hlam_three
  · intro x hx j posterior hposterior n hn
    have hbound :=
      markovPosteriorAverageConditionalRisk_lt_tiltMixture_initialLaw_of_not_mem
        prior weight P initial f q hx j posterior hposterior n hn
    rw [subGammaCgf_oneFourth_one_div (hlam j) (hlam_three j)] at hbound
    exact hbound

end

end FormalSLT.StochasticDynamics
