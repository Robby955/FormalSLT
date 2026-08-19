/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.TrajectoryEmpiricalBernsteinPACBayes
import FormalSLT.PACBayes.ForwardBesselPACBayesCountable

/-!
# Countable-tilt empirical-Bernstein PAC-Bayes bounds for trajectories

This module combines the prefix-dependent trajectory empirical-Bernstein
endpoint with the explicit geometric tilt catalog.  For each natural-number
tilt atom, it instantiates the predictable-mean PAC-Bayes theorem with a
singleton tilt catalog and confidence budget
`delta * polynomialForwardTiltWeight j`.  The common exceptional event is the
countable union of those canonical process-crossing events.

Outside that one union, the bound is simultaneous over all times `n >= 2`, all
finite-hypothesis posterior PMFs, and every natural-number tilt atom.  Thus the
posterior may depend arbitrarily on the realized path and time, while the
explicit selector
`geometricForwardTiltIndex n = (Nat.log 4 n).pred` may be substituted at every
sample size.  The resulting exact observed hybrid-Bessel boundary converges to
zero along every path, even for an arbitrary time-varying posterior PMF,
because the finite full-support prior gives a uniform KL ceiling.

## Scope and non-claims

* The state and hypothesis spaces are finite, but kernels and scores may depend
  on the entire available trajectory prefix.
* The score catalog and countable tilt catalog are fixed before observing the
  path.  Posterior selection is substitution into a common event, not a
  selected e-process.
* The common event is obtained by countable confidence allocation across
  singleton predictable-mean e-process events.  This module does not claim
  that their countable sum is itself an e-process.
* The hybrid-Bessel score is only a pointwise lower envelope of each actual
  e-process, not an e-process itself.
* Event control is stated with `Measure.real` outer mass; no separate
  measurability certificate for the countable union is asserted.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardPredictableMeanBesselPACBayes
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open scoped BigOperators ENNReal

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {ι Z : Type*}
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-! ## Exact boundary and allocated exceptional events -/

/-- The exact countable-catalog trajectory boundary.  Its variance term is
computed from the observed score prefix separately for each hypothesis before
posterior averaging. -/
def trajectoryCountableEmpiricalBernsteinPACBayesBoundary
    (prior : ι → ℝ) (score : ι → TrajectoryScore Z)
    (posterior : ι → ℝ) (delta : ℝ) (j n : ℕ) (x : ℕ → Z) : ℝ :=
  countableForwardBesselPACBayesBoundary
    prior polynomialForwardTiltWeight geometricForwardTilt
      (fun i ↦ observedTrajectoryScore (score i))
      posterior delta j n x

omit [DecidableEq ι] [Nonempty ι]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The trajectory boundary exposes the polynomial confidence cost and the
observed trajectory hybrid-Bessel penalty exactly. -/
theorem trajectoryCountableEmpiricalBernsteinPACBayesBoundary_eq_explicit
    (prior : ι → ℝ) (score : ι → TrajectoryScore Z)
    (posterior : ι → ℝ) {delta : ℝ} (hdelta : delta ≠ 0)
    (j n : ℕ) (x : ℕ → Z) :
    trajectoryCountableEmpiricalBernsteinPACBayesBoundary
        prior score posterior delta j n x =
      (klDiv posterior prior +
          Real.log ((((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta) +
          forwardEmpiricalBernsteinPsi (geometricForwardTilt j) *
            trajectoryPosteriorHybridBesselPenalty posterior score n x) /
        ((n : ℝ) * geometricForwardTilt j) := by
  unfold trajectoryCountableEmpiricalBernsteinPACBayesBoundary
    countableForwardBesselPACBayesBoundary
    trajectoryPosteriorHybridBesselPenalty
    FormalSLT.PACBayes.ForwardBesselPACBayes.forwardPosteriorHybridBesselPenalty
  rw [polynomialForwardTiltWeight_log_cost hdelta j]

/-- The singleton tilt weight used for one allocated atom event. -/
private def trajectorySingletonTiltWeight (_u : Unit) : ℝ := 1

private theorem trajectorySingletonTiltWeight_isFullSupportPMF :
    IsFullSupportPMF trajectorySingletonTiltWeight := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro u
    cases u
    norm_num [trajectorySingletonTiltWeight]
  · simp [trajectorySingletonTiltWeight]
  · intro u
    cases u
    norm_num [trajectorySingletonTiltWeight]

/-- Canonical predictable-mean process-crossing event for countable atom `j`,
charged confidence `delta * polynomialForwardTiltWeight j`. -/
def trajectoryCountableEmpiricalBernsteinPACBayesAtomExceptionalEvent
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    (prior : ι → ℝ) (score : ι → TrajectoryScore Z)
    (delta : ℝ) (j : ℕ) : Set (ℕ → Z) :=
  forwardPredictableMeanBesselPACBayesExceptionalEvent
    prior trajectorySingletonTiltWeight
    (fun i ↦ observedTrajectoryScore (score i))
    (fun i ↦ conditionalTrajectoryRisk K (score i))
    (fun _u : Unit ↦ geometricForwardTilt j)
    (delta * polynomialForwardTiltWeight j)

/-- One countable confidence-allocation event containing every atom's
canonical predictable-mean crossing event. -/
def trajectoryCountableEmpiricalBernsteinPACBayesExceptionalEvent
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    (prior : ι → ℝ) (score : ι → TrajectoryScore Z)
    (delta : ℝ) : Set (ℕ → Z) :=
  ⋃ j : ℕ,
    trajectoryCountableEmpiricalBernsteinPACBayesAtomExceptionalEvent
      K prior score delta j

omit [DecidableEq ι] [Nonempty ι]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- A countable trajectory boundary is the singleton predictable-mean
boundary at confidence `delta * weight j`. -/
theorem trajectoryCountableEmpiricalBernsteinPACBayesBoundary_eq_singleton
    (prior : ι → ℝ) (score : ι → TrajectoryScore Z)
    (posterior : ι → ℝ) (delta : ℝ) (j n : ℕ) (x : ℕ → Z) :
    trajectoryCountableEmpiricalBernsteinPACBayesBoundary
        prior score posterior delta j n x =
      forwardPredictableMeanBesselPACBayesBoundary
        prior trajectorySingletonTiltWeight
        (fun _u : Unit ↦ geometricForwardTilt j)
        (fun i ↦ observedTrajectoryScore (score i))
        posterior (delta * polynomialForwardTiltWeight j) () n x := by
  unfold trajectoryCountableEmpiricalBernsteinPACBayesBoundary
    countableForwardBesselPACBayesBoundary
    forwardPredictableMeanBesselPACBayesBoundary
    FormalSLT.PACBayes.ForwardBesselPACBayes.forwardPosteriorHybridBesselPenalty
    FormalSLT.PACBayes.ForwardPredictableMeanBesselPACBayes.forwardPosteriorHybridBesselPenalty
    trajectorySingletonTiltWeight
  simp

/-! ## Countable outer-mass allocation -/

omit [Nonempty ι] in
/-- Each atom's canonical crossing event costs at most its assigned confidence
budget. -/
theorem trajectoryCountableEmpiricalBernsteinPACBayesAtomExceptionalEvent_mass_le
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (K n)] (x0 : Z)
    {score : ι → TrajectoryScore Z}
    (hscore : ∀ i n u y, score i n u y ∈ Set.Icc (0 : ℝ) 1)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {delta : ℝ} (hdelta : 0 < delta) (j : ℕ) :
    (trajectoryMeasure K x0).real
        (trajectoryCountableEmpiricalBernsteinPACBayesAtomExceptionalEvent
          K prior score delta j) ≤
      delta * polynomialForwardTiltWeight j := by
  exact forwardPredictableMeanBesselPACBayesExceptionalEvent_mass_le_delta
    (μ := trajectoryMeasure K x0)
    (ℱ := Filtration.piLE (X := fun _ : ℕ ↦ Z))
    (κ := Unit) hprior trajectorySingletonTiltWeight_isFullSupportPMF
    (mul_pos hdelta (polynomialForwardTiltWeight_pos j))
    (fun _u ↦ geometricForwardTilt_pos j)
    (fun _u ↦ geometricForwardTilt_lt_one j)
    (fun i ↦ observedTrajectoryScore_incrementAdapted (score i))
    (fun i ↦ conditionalTrajectoryRisk_stronglyAdapted K (score i))
    (fun i k x ↦ observedTrajectoryScore_mem_Icc (hscore i) k x)
    (fun i k ↦ observedTrajectoryScore_condExp K x0 (score i) (hscore i) k)

omit [Nonempty ι] in
/-- Countable subadditivity and the telescoping polynomial weights give total
outer mass at most `delta`. -/
theorem trajectoryCountableEmpiricalBernsteinPACBayesExceptionalEvent_mass_le
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (K n)] (x0 : Z)
    {score : ι → TrajectoryScore Z}
    (hscore : ∀ i n u y, score i n u y ∈ Set.Icc (0 : ℝ) 1)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {delta : ℝ} (hdelta : 0 < delta) :
    (trajectoryMeasure K x0).real
        (trajectoryCountableEmpiricalBernsteinPACBayesExceptionalEvent
          K prior score delta) ≤ delta := by
  let μ := trajectoryMeasure K x0
  let event : ℕ → Set (ℕ → Z) := fun j ↦
    trajectoryCountableEmpiricalBernsteinPACBayesAtomExceptionalEvent
      K prior score delta j
  have hatomReal : ∀ j, μ.real (event j) ≤
      delta * polynomialForwardTiltWeight j := by
    intro j
    exact trajectoryCountableEmpiricalBernsteinPACBayesAtomExceptionalEvent_mass_le
      K x0 hscore hprior hdelta j
  have hatomENNReal : ∀ j, μ (event j) ≤
      ENNReal.ofReal (delta * polynomialForwardTiltWeight j) := by
    intro j
    calc
      μ (event j) = ENNReal.ofReal (μ.real (event j)) := by
        rw [ofReal_measureReal]
      _ ≤ ENNReal.ofReal (delta * polynomialForwardTiltWeight j) :=
        ENNReal.ofReal_le_ofReal (hatomReal j)
  have hallocated : HasSum
      (fun j ↦ delta * polynomialForwardTiltWeight j) delta := by
    simpa using polynomialForwardTiltWeight_hasSum.mul_left delta
  have hsummable : Summable
      (fun j ↦ delta * polynomialForwardTiltWeight j) :=
    hallocated.summable
  have hnonneg : ∀ j, 0 ≤ delta * polynomialForwardTiltWeight j :=
    fun j ↦ mul_nonneg hdelta.le (polynomialForwardTiltWeight_pos j).le
  have hunionENNReal : μ (⋃ j, event j) ≤ ENNReal.ofReal delta := by
    calc
      μ (⋃ j, event j) ≤ ∑' j, μ (event j) := measure_iUnion_le _
      _ ≤ ∑' j, ENNReal.ofReal
          (delta * polynomialForwardTiltWeight j) :=
        ENNReal.tsum_le_tsum hatomENNReal
      _ = ENNReal.ofReal delta := by
        rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable,
          hallocated.tsum_eq]
  change μ.real (⋃ j, event j) ≤ delta
  calc
    μ.real (⋃ j, event j) ≤ (ENNReal.ofReal delta).toReal := by
      exact ENNReal.toReal_mono (by simp) hunionENNReal
    _ = delta := ENNReal.toReal_ofReal hdelta.le

/-! ## Simultaneous countable-atom trajectory endpoint -/

omit [DecidableEq ι] [Fintype Z] [MeasurableSingletonClass Z] in
/-- Outside the allocated union, every posterior and countable atom satisfies
the exact empirical-Bernstein trajectory bound at every `n >= 2`. -/
theorem trajectoryCountableEmpiricalBernsteinPACBayes_allPosteriors_of_not_mem
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    {score : ι → TrajectoryScore Z}
    (hscore : ∀ i n u y, score i n u y ∈ Set.Icc (0 : ℝ) 1)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {delta : ℝ} (hdelta : 0 < delta)
    {x : ℕ → Z}
    (hx : x ∉ trajectoryCountableEmpiricalBernsteinPACBayesExceptionalEvent
      K prior score delta) :
    ∀ j : ℕ, ∀ posterior : ι → ℝ, IsPMF posterior →
      ∀ n : ℕ, 2 ≤ n →
        trajectoryPosteriorAverageConditionalRisk
            K score posterior n x <
          trajectoryPosteriorEmpiricalPrequentialRisk score posterior n x +
            trajectoryCountableEmpiricalBernsteinPACBayesBoundary
              prior score posterior delta j n x := by
  intro j posterior hposterior n hn
  have hxj : x ∉
      trajectoryCountableEmpiricalBernsteinPACBayesAtomExceptionalEvent
        K prior score delta j := by
    intro hxj
    apply hx
    exact Set.mem_iUnion.mpr ⟨j, hxj⟩
  have hbound :=
    forwardPredictableMeanBesselPACBayes_allPosteriors_of_not_mem
      (κ := Unit) hprior trajectorySingletonTiltWeight_isFullSupportPMF
      (mul_pos hdelta (polynomialForwardTiltWeight_pos j))
      (fun _u ↦ geometricForwardTilt_pos j)
      (fun _u ↦ geometricForwardTilt_lt_one j)
      (fun i k x ↦ observedTrajectoryScore_mem_Icc (hscore i) k x)
      hxj () posterior hposterior n hn
  rw [trajectoryCountableEmpiricalBernsteinPACBayesBoundary_eq_singleton]
  simpa only [forwardPrefixMean_observedTrajectoryScore,
    forwardPrefixMean_conditionalTrajectoryRisk,
    trajectoryPosteriorAverageConditionalRisk,
    trajectoryPosteriorEmpiricalPrequentialRisk,
    trajectoryAverageConditionalRisk,
    trajectoryEmpiricalPrequentialRisk]
    using hbound

/-- One countable-allocation event is simultaneous over time, posterior, and
every natural-number geometric tilt atom. -/
theorem exists_trajectoryCountableEmpiricalBernsteinPACBayes_event
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (K n)] (x0 : Z)
    {score : ι → TrajectoryScore Z}
    (hscore : ∀ i n u y, score i n u y ∈ Set.Icc (0 : ℝ) 1)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ goodEvent : Set (ℕ → Z),
      (trajectoryMeasure K x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : ℕ,
          ∀ posterior : ι → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              trajectoryPosteriorAverageConditionalRisk
                  K score posterior n x <
                trajectoryPosteriorEmpiricalPrequentialRisk
                    score posterior n x +
                  trajectoryCountableEmpiricalBernsteinPACBayesBoundary
                    prior score posterior delta j n x := by
  let badEvent :=
    trajectoryCountableEmpiricalBernsteinPACBayesExceptionalEvent
      K prior score delta
  refine ⟨badEventᶜ, ?_, ?_⟩
  · simpa [badEvent] using
      (trajectoryCountableEmpiricalBernsteinPACBayesExceptionalEvent_mass_le
        K x0 hscore hprior hdelta)
  · intro x hx
    exact trajectoryCountableEmpiricalBernsteinPACBayes_allPosteriors_of_not_mem
      K hscore hprior hdelta hx

/-! ## Every-sample-size selector and vanishing exact width -/

omit [DecidableEq ι] [Nonempty ι]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- At `n >= 4`, the explicitly selected exact trajectory boundary is bounded
by the audited deterministic all-time rate. -/
theorem trajectoryCountableEmpiricalBernsteinPACBayesBoundary_selected_le_rate
    {prior posterior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (hposterior : IsPMF posterior)
    {score : ι → TrajectoryScore Z}
    (hscore : ∀ i n u y, score i n u y ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {n : ℕ} (hn : 4 ≤ n) (x : ℕ → Z) :
    trajectoryCountableEmpiricalBernsteinPACBayesBoundary
        prior score posterior delta (geometricForwardTiltIndex n) n x ≤
      allTimeGeometricPolynomialForwardRate
        (fun _ ↦ klDiv posterior prior) delta n := by
  exact countableForwardBesselPACBayesBoundary_selected_le_allTimeRate
    hprior hposterior hdelta hdelta1
    (fun i k x ↦ observedTrajectoryScore_mem_Icc (hscore i) k x)
    hn x

omit [DecidableEq ι] [Nonempty ι]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- For every path and arbitrary time-varying finite posterior PMF, the exact
observed selected trajectory boundary converges to zero over all integer
sample sizes. -/
theorem trajectoryCountableEmpiricalBernsteinPACBayesBoundary_selected_tendsto_zero
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (posterior : ℕ → ι → ℝ) (hposterior : ∀ n, IsPMF (posterior n))
    {score : ι → TrajectoryScore Z}
    (hscore : ∀ i n u y, score i n u y ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (x : ℕ → Z) :
    Filter.Tendsto
      (fun n ↦ trajectoryCountableEmpiricalBernsteinPACBayesBoundary
        prior score (posterior n) delta
          (geometricForwardTiltIndex n) n x)
      Filter.atTop (nhds 0) := by
  exact countableForwardBesselPACBayesBoundary_selected_tendsto_zero
    hprior posterior hposterior hdelta hdelta1
    (fun i k x ↦ observedTrajectoryScore_mem_Icc (hscore i) k x) x

/-- Capstone: one outer-mass event supports arbitrary path- and time-dependent
posterior PMFs, the explicit every-sample-size geometric atom selector, and an
exact observed hybrid-Bessel trajectory boundary tending to zero on each
path. -/
theorem exists_trajectoryCountableEmpiricalBernsteinPACBayes_allTime_vanishing_event
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (K n)] (x0 : Z)
    {score : ι → TrajectoryScore Z}
    (hscore : ∀ i n u y, score i n u y ∈ Set.Icc (0 : ℝ) 1)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (posterior : (ℕ → Z) → ℕ → ι → ℝ)
    (hposterior : ∀ x n, IsPMF (posterior x n)) :
    ∃ goodEvent : Set (ℕ → Z),
      (trajectoryMeasure K x0).real goodEventᶜ ≤ delta ∧
        (∀ x ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
          trajectoryPosteriorAverageConditionalRisk
              K score (posterior x n) n x <
            trajectoryPosteriorEmpiricalPrequentialRisk
                score (posterior x n) n x +
              trajectoryCountableEmpiricalBernsteinPACBayesBoundary
                prior score (posterior x n) delta
                  (geometricForwardTiltIndex n) n x) ∧
        (∀ x ∈ goodEvent,
          Filter.Tendsto
            (fun n ↦
              trajectoryCountableEmpiricalBernsteinPACBayesBoundary
                prior score (posterior x n) delta
                  (geometricForwardTiltIndex n) n x)
            Filter.atTop (nhds 0)) := by
  obtain ⟨goodEvent, hmass, hgood⟩ :=
    exists_trajectoryCountableEmpiricalBernsteinPACBayes_event
      K x0 hscore hprior hdelta
  refine ⟨goodEvent, hmass, ?_, ?_⟩
  · intro x hx n hn
    exact hgood x hx (geometricForwardTiltIndex n)
      (posterior x n) (hposterior x n) n hn
  · intro x _hx
    exact
      trajectoryCountableEmpiricalBernsteinPACBayesBoundary_selected_tendsto_zero
        hprior (posterior x) (hposterior x) hscore hdelta hdelta1 x

end

end FormalSLT.StochasticDynamics
