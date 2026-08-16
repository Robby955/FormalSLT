/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.StochasticDynamics.MarkovPACBayes
import FormalSLT.PACBayes.TimeUniformTiltMixture

/-!
# Finite weighted tilt mixtures for Markov PAC-Bayes risk

This module specializes the finite hypothesis--tilt master e-process to the
actual Ionescu--Tulcea path law of a finite homogeneous Markov chain.  One
measurable exceptional event has probability at most `delta`; on its
complement, the bound controls every positive time, every posterior on a finite
catalog of fixed predictors, and every atom in a declared finite tilt prior.
The base predictors remain fixed, while the posterior and one predeclared
finite tilt atom may be selected after observing the trajectory. This is
post-path selection from a fixed family, not a predictable time-varying tilt.

For tilt atom `j`, the exact selection cost is
`log (1 / (delta * weight j))`. It is derived from one master e-process and
one Ville event, without entrywise probability bounds or a union bound. The
pointwise selector endpoint does not require the selector to be measurable or
adapted; consequently it does not construct a selected process or add an
optional-stopping guarantee beyond the common all-atom event.

The target is the posterior average of the transition-row conditional risks
encountered along the path, not stationary risk.  The result assumes a finite
state space, deterministic initial state, fixed `[0,1]` observable and
predictor catalog, squared one-step loss, positive normalized finite tilt
weights fixed before the trajectory, and `0 < lam j < 3` for every atom. It
does not provide a joint posterior on hypothesis--tilt pairs, countable or
all-real tilt optimization, empirical-variance control, a random initial law,
same-trajectory predictor training, or a stationary or mixing conclusion.  The
Lean mass theorem only needs `0 < delta`; applications calling `1 - delta` a
confidence level should additionally choose `delta < 1`.

The statistical mechanism follows the supermartingale-mixture,
Donsker--Varadhan, and Ville recipe of Chugg, Wang, and Ramdas,
"A Unified Recipe for Deriving (Time-Uniform) PAC-Bayes Bounds" (JMLR, 2023).
The contribution is the checked Markov-path specialization and its explicit
posterior/tilt selection semantics, not a new concentration inequality or a
priority claim.
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
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- Risk-facing failure for some declared tilt, posterior, and positive time. -/
def markovPACBayesTiltMixtureAnyPosteriorUpperFailure
    (prior : ι → ℝ) (weight : κ → ℝ)
    (P : Z → PMF Z) (f : Z → ℝ) (q : ι → Z → ℝ)
    (lam : κ → ℝ) (delta : ℝ) : Set (ℕ → Z) :=
  {x | ∃ j : κ, ∃ posterior : ι → ℝ, IsPMF posterior ∧
    ∃ n : ℕ, 0 < n ∧
      subGammaCgf (1 / 4) 1 (lam j) / lam j +
          (klDiv posterior prior + Real.log (1 / (delta * weight j))) /
            ((n : ℝ) * lam j) ≤
        markovPosteriorAverageConditionalRisk P f q posterior n x -
          markovPosteriorEmpiricalPrequentialRisk f q posterior n x}

omit [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
  [Fintype Z] [MeasurableSingletonClass Z] in
/-- A Markov risk failure is a failure of the generic master-process theorem. -/
theorem markovPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_processFailure
    {prior : ι → ℝ} {weight : κ → ℝ}
    {P : Z → PMF Z} {f : Z → ℝ} {q : ι → Z → ℝ}
    {lam : κ → ℝ} {delta : ℝ} :
    markovPACBayesTiltMixtureAnyPosteriorUpperFailure
        prior weight P f q lam delta ⊆
      PACBayes.TimeUniform.timeUniformPACBayesTiltMixtureAnyPosteriorUpperFailure
        prior weight (fun i ↦ markovRiskShortfall P f (q i))
          (1 / 4) 1 lam delta := by
  intro x hx
  rcases hx with ⟨j, posterior, hposterior, n, hn, hfailure⟩
  refine ⟨j, posterior, hposterior, n, hn, ?_⟩
  rw [posteriorAverage_runningMean_markovRiskShortfall]
  exact hfailure

omit [DecidableEq ι] [DecidableEq κ] [Nonempty κ] in
/-- Finite weighted-tilt, all-time, all-posterior PAC-Bayes bound under the
actual finite Markov path law.  The raw failure set has outer mass at most
`delta`. -/
theorem markovPACBayes_tiltMixture_allPosteriors_bound
    (P : Z → PMF Z) (x0 : Z) {f : Z → ℝ} {q : ι → Z → ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ i z, q i z ∈ Set.Icc (0 : ℝ) 1)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : κ → ℝ} {delta : ℝ}
    (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_three : ∀ j, lam j < 3) :
    (markovPathMeasure P x0).real
      (markovPACBayesTiltMixtureAnyPosteriorUpperFailure
        prior weight P f q lam delta) ≤ delta := by
  refine (measureReal_mono
    (markovPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_processFailure
      (prior := prior) (weight := weight) (P := P) (f := f) (q := q)
      (lam := lam) (delta := delta))).trans ?_
  exact PACBayes.TimeUniform.timeUniformPACBayes_tiltMixture_allPosteriors_bound
    (μ := markovPathMeasure P x0)
    (ℱ := Filtration.piLE (X := fun _ : ℕ ↦ Z))
    (prior := prior) (weight := weight)
    (X := fun i ↦ markovRiskShortfall P f (q i))
    (sigma2 := (1 / 4 : ℝ)) (b := (1 : ℝ))
    (lam := lam) (delta := delta) hprior hweight hdelta
    (by norm_num) (by norm_num) hlam (fun j ↦ by simpa using hlam_three j)
    (fun i k ↦ measurable_markovRiskShortfall P f (q i) k)
    (fun i k ↦ integrable_markovRiskShortfall
      (P := P) (x0 := x0) hf (hq i) k)
    (fun i ↦ markovRiskShortfall_incrementAdapted P f (q i))
    (fun i j n ↦
      PACBayes.TimeUniformIID.integrable_subGammaExponentialProcess_of_bounded n
        (by norm_num) (by norm_num) (hlam j).le
        (by simpa using hlam_three j)
        (fun k ↦ measurable_markovRiskShortfall P f (q i) k)
        (fun k ↦ Filter.Eventually.of_forall fun x ↦
          abs_markovRiskShortfall_le_one P hf (hq i) k x))
    (fun i k ↦ Filter.Eventually.of_forall fun x ↦
      abs_markovRiskShortfall_le_one P hf (hq i) k x)
    (fun i k ↦ markovRiskShortfall_condExp_eq_zero P x0 hf (hq i) k)
    (fun i k ↦ markovRiskShortfall_condSecondMoment_le_one_fourth P x0 hf (hq i) k)

/-- Measurable hull of the posterior/tilt-existential Markov failure set. -/
def markovPACBayesTiltMixtureExceptionalEvent
    (prior : ι → ℝ) (weight : κ → ℝ)
    (P : Z → PMF Z) (x0 : Z) (f : Z → ℝ) (q : ι → Z → ℝ)
    (lam : κ → ℝ) (delta : ℝ) : Set (ℕ → Z) :=
  toMeasurable (markovPathMeasure P x0)
    (markovPACBayesTiltMixtureAnyPosteriorUpperFailure
      prior weight P f q lam delta)

omit [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] [Nonempty κ] in
theorem markovPACBayesTiltMixtureExceptionalEvent_measurable
    (prior : ι → ℝ) (weight : κ → ℝ)
    (P : Z → PMF Z) (x0 : Z) (f : Z → ℝ) (q : ι → Z → ℝ)
    (lam : κ → ℝ) (delta : ℝ) :
    MeasurableSet (markovPACBayesTiltMixtureExceptionalEvent
      prior weight P x0 f q lam delta) :=
  measurableSet_toMeasurable _ _

omit [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] [Nonempty κ] in
theorem markovPACBayesTiltMixtureRawFailure_subset_exceptionalEvent
    (prior : ι → ℝ) (weight : κ → ℝ)
    (P : Z → PMF Z) (x0 : Z) (f : Z → ℝ) (q : ι → Z → ℝ)
    (lam : κ → ℝ) (delta : ℝ) :
    markovPACBayesTiltMixtureAnyPosteriorUpperFailure
        prior weight P f q lam delta ⊆
      markovPACBayesTiltMixtureExceptionalEvent
        prior weight P x0 f q lam delta :=
  subset_toMeasurable _ _

omit [DecidableEq ι] [DecidableEq κ] [Nonempty κ] in
/-- The measurable master-mixture exceptional event has ordinary probability
at most `delta`. -/
theorem markovPACBayesTiltMixtureExceptionalEvent_mass_le_delta
    (P : Z → PMF Z) (x0 : Z) {f : Z → ℝ} {q : ι → Z → ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ i z, q i z ∈ Set.Icc (0 : ℝ) 1)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : κ → ℝ} {delta : ℝ}
    (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_three : ∀ j, lam j < 3) :
    (markovPathMeasure P x0).real
      (markovPACBayesTiltMixtureExceptionalEvent
        prior weight P x0 f q lam delta) ≤ delta := by
  rw [markovPACBayesTiltMixtureExceptionalEvent, Measure.real,
    measure_toMeasurable]
  exact markovPACBayes_tiltMixture_allPosteriors_bound
    P x0 hf hq hprior hweight hdelta hlam hlam_three

omit [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] [Nonempty κ] in
/-- Outside the common measurable event, every posterior, time, and declared
tilt obeys the Markov prequential upper-risk certificate. -/
theorem markovPosteriorAverageConditionalRisk_lt_tiltMixture_of_not_mem
    (prior : ι → ℝ) (weight : κ → ℝ)
    (P : Z → PMF Z) (x0 : Z) (f : Z → ℝ) (q : ι → Z → ℝ)
    {lam : κ → ℝ} {delta : ℝ} {x : ℕ → Z}
    (hx : x ∉ markovPACBayesTiltMixtureExceptionalEvent
      prior weight P x0 f q lam delta)
    (j : κ) (posterior : ι → ℝ) (hposterior : IsPMF posterior)
    (n : ℕ) (hn : 0 < n) :
    markovPosteriorAverageConditionalRisk P f q posterior n x <
      markovPosteriorEmpiricalPrequentialRisk f q posterior n x +
        subGammaCgf (1 / 4) 1 (lam j) / lam j +
        (klDiv posterior prior + Real.log (1 / (delta * weight j))) /
          ((n : ℝ) * lam j) := by
  have hxraw : x ∉ markovPACBayesTiltMixtureAnyPosteriorUpperFailure
      prior weight P f q lam delta :=
    fun hraw ↦ hx (markovPACBayesTiltMixtureRawFailure_subset_exceptionalEvent
      prior weight P x0 f q lam delta hraw)
  have hgap :
      markovPosteriorAverageConditionalRisk P f q posterior n x -
          markovPosteriorEmpiricalPrequentialRisk f q posterior n x <
        subGammaCgf (1 / 4) 1 (lam j) / lam j +
          (klDiv posterior prior + Real.log (1 / (delta * weight j))) /
            ((n : ℝ) * lam j) := by
    exact lt_of_not_ge fun hfailure ↦
      hxraw ⟨j, posterior, hposterior, n, hn, hfailure⟩
  linarith

omit [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ] [Nonempty κ] in
/--
A pointwise path- and posterior-dependent selector may choose one predeclared
finite tilt atom. No measurability or adaptedness condition is imposed on the
selector: this evaluates the common all-atom event and does not construct a
selected process or add an optional-stopping guarantee.
-/
theorem markovPosteriorAverageConditionalRisk_lt_tiltMixture_selected_of_not_mem
    (prior : ι → ℝ) (weight : κ → ℝ)
    (P : Z → PMF Z) (x0 : Z) (f : Z → ℝ) (q : ι → Z → ℝ)
    {lam : κ → ℝ} {delta : ℝ} {x : ℕ → Z}
    (hx : x ∉ markovPACBayesTiltMixtureExceptionalEvent
      prior weight P x0 f q lam delta)
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
  exact markovPosteriorAverageConditionalRisk_lt_tiltMixture_of_not_mem
    prior weight P x0 f q hx (select x posterior) posterior hposterior n hn

omit [DecidableEq ι] [DecidableEq κ] [Nonempty κ] in
/-- Publication-facing finite weighted-tilt Markov PAC-Bayes certificate with
the explicit universal `1/4` variance contribution. -/
theorem markovPACBayes_tiltMixture_prequentialRisk_certificate
    (P : Z → PMF Z) (x0 : Z) {f : Z → ℝ} {q : ι → Z → ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ i z, q i z ∈ Set.Icc (0 : ℝ) 1)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : κ → ℝ} {delta : ℝ}
    (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_three : ∀ j, lam j < 3) :
    ∃ E : Set (ℕ → Z),
      MeasurableSet E ∧
      (markovPathMeasure P x0).real E ≤ delta ∧
      ∀ x ∉ E, ∀ j : κ,
        ∀ posterior : ι → ℝ, IsPMF posterior →
          ∀ n : ℕ, 0 < n →
            markovPosteriorAverageConditionalRisk P f q posterior n x <
              markovPosteriorEmpiricalPrequentialRisk f q posterior n x +
                lam j / (8 * (1 - lam j / 3)) +
                (klDiv posterior prior +
                  Real.log (1 / (delta * weight j))) /
                    ((n : ℝ) * lam j) := by
  let E := markovPACBayesTiltMixtureExceptionalEvent
    prior weight P x0 f q lam delta
  refine ⟨E, markovPACBayesTiltMixtureExceptionalEvent_measurable
    prior weight P x0 f q lam delta, ?_, ?_⟩
  · exact markovPACBayesTiltMixtureExceptionalEvent_mass_le_delta
      P x0 hf hq hprior hweight hdelta hlam hlam_three
  · intro x hx j posterior hposterior n hn
    have hbound := markovPosteriorAverageConditionalRisk_lt_tiltMixture_of_not_mem
      prior weight P x0 f q hx j posterior hposterior n hn
    rw [subGammaCgf_oneFourth_one_div (hlam j) (hlam_three j)] at hbound
    exact hbound

end

end FormalSLT.StochasticDynamics
