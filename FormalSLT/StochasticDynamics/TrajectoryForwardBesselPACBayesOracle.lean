/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.ForwardBesselPACBayesOracle
import FormalSLT.StochasticDynamics.TrajectoryEmpiricalBernsteinPACBayesCountable

/-!
# Observable PAC-Bayes oracle for adaptive trajectories

This module specializes the growing geometric-tilt oracle to finite-state,
prefix-dependent trajectories.  The score catalog and the countable tilt
catalog are fixed before observing the path.  On one countable-allocation
event, the posterior and the finite-prefix tilt minimizer may both depend on
the observed path and reporting time.

The endpoint compares posterior-averaged conditional loss along the monitored
trajectory with posterior-averaged empirical prequential loss.  It does not
by itself assert stationary, population, future, or deployment risk.  Those
interpretations require separate assumptions and bridge theorems.

The selected exact boundary retains the observed hybrid-Bessel penalty and is
bounded by an explicit square-root, iterated-logarithm-order envelope.  The
selector is an exact finite-prefix minimizer, not an all-real optimizer or a
selected e-process.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open FormalSLT.PACBayes.ForwardBesselPACBayesOracle

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {ι Z : Type*}
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-! ## Observable trajectory selector and boundary -/

/-- Exact minimizer of the observable trajectory boundary over the geometric
prefix available at reporting time `n`. -/
def trajectoryGrowingPrefixForwardBesselPACBayesArgmin
    (prior : ι → ℝ) (score : ι → TrajectoryScore Z)
    (posterior : ι → ℝ) (delta : ℝ) (n : ℕ) (x : ℕ → Z) : ℕ :=
  growingPrefixForwardBesselPACBayesArgmin
    prior (fun i ↦ observedTrajectoryScore (score i)) posterior delta n x

/-- The exact observable trajectory boundary evaluated at its growing-prefix
minimizer. -/
def trajectoryGrowingPrefixForwardBesselPACBayesBoundary
    (prior : ι → ℝ) (score : ι → TrajectoryScore Z)
    (posterior : ι → ℝ) (delta : ℝ) (n : ℕ) (x : ℕ → Z) : ℝ :=
  trajectoryCountableEmpiricalBernsteinPACBayesBoundary
    prior score posterior delta
      (trajectoryGrowingPrefixForwardBesselPACBayesArgmin
        prior score posterior delta n x) n x

/-- Observable square-root envelope for the selected trajectory boundary. -/
def trajectoryGrowingPrefixForwardBesselPACBayesLILEnvelope
    (prior : ι → ℝ) (score : ι → TrajectoryScore Z)
    (posterior : ι → ℝ) (delta : ℝ) (n : ℕ) (x : ℕ → Z) : ℝ :=
  growingPrefixForwardBesselPACBayesLILEnvelope
    prior (fun i ↦ observedTrajectoryScore (score i)) posterior delta n x

omit [DecidableEq ι] [Nonempty ι]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The selected atom belongs to the declared reporting-time prefix. -/
theorem trajectoryGrowingPrefixForwardBesselPACBayesArgmin_mem
    (prior : ι → ℝ) (score : ι → TrajectoryScore Z)
    (posterior : ι → ℝ) (delta : ℝ) (n : ℕ) (x : ℕ → Z) :
    trajectoryGrowingPrefixForwardBesselPACBayesArgmin
        prior score posterior delta n x ∈
      Finset.range (growingPrefixForwardBesselPACBayesMaxIndex n + 1) := by
  exact growingPrefixForwardBesselPACBayesArgmin_mem
    prior (fun i ↦ observedTrajectoryScore (score i)) posterior delta n x

omit [DecidableEq ι] [Nonempty ι]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The selected trajectory boundary is no larger than any declared atom in
the reporting-time prefix. -/
theorem trajectoryGrowingPrefixForwardBesselPACBayesBoundary_le_atom
    (prior : ι → ℝ) (score : ι → TrajectoryScore Z)
    (posterior : ι → ℝ) (delta : ℝ) (n : ℕ) (x : ℕ → Z) {j : ℕ}
    (hj : j ∈ Finset.range
      (growingPrefixForwardBesselPACBayesMaxIndex n + 1)) :
    trajectoryGrowingPrefixForwardBesselPACBayesBoundary
        prior score posterior delta n x ≤
      trajectoryCountableEmpiricalBernsteinPACBayesBoundary
        prior score posterior delta j n x := by
  exact growingPrefixForwardBesselPACBayesArgmin_le
    prior (fun i ↦ observedTrajectoryScore (score i)) posterior delta n x hj

omit [DecidableEq ι] [Nonempty ι]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The selected exact trajectory boundary is controlled by its observable
variance-adaptive, iterated-logarithm-order envelope. -/
theorem trajectoryGrowingPrefixForwardBesselPACBayesBoundary_le_LILEnvelope
    {prior posterior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (hposterior : IsPMF posterior)
    {score : ι → TrajectoryScore Z}
    (hscore : ∀ i n u y, score i n u y ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {n : ℕ} (hn : 4 ≤ n) (x : ℕ → Z) :
    trajectoryGrowingPrefixForwardBesselPACBayesBoundary
        prior score posterior delta n x ≤
      trajectoryGrowingPrefixForwardBesselPACBayesLILEnvelope
        prior score posterior delta n x := by
  exact growingPrefixForwardBesselPACBayesBoundary_le_LILEnvelope
    hprior hposterior hdelta hdelta1
      (fun i k x ↦ observedTrajectoryScore_mem_Icc (hscore i) k x) hn x

omit [DecidableEq ι] [Nonempty ι]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The selected trajectory boundary also retains the existing deterministic
all-time rate as a worst-case fallback. -/
theorem trajectoryGrowingPrefixForwardBesselPACBayesBoundary_le_allTimeRate
    {prior posterior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (hposterior : IsPMF posterior)
    {score : ι → TrajectoryScore Z}
    (hscore : ∀ i n u y, score i n u y ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {n : ℕ} (hn : 4 ≤ n) (x : ℕ → Z) :
    trajectoryGrowingPrefixForwardBesselPACBayesBoundary
        prior score posterior delta n x ≤
      allTimeGeometricPolynomialForwardRate
        (fun _ ↦ klDiv posterior prior) delta n := by
  exact growingPrefixForwardBesselPACBayesBoundary_le_allTimeRate
    hprior hposterior hdelta hdelta1
      (fun i k x ↦ observedTrajectoryScore_mem_Icc (hscore i) k x) hn x

omit [DecidableEq ι] [Nonempty ι]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- Along every path, the exact selected trajectory width converges to zero
for arbitrary time-varying finite posterior PMFs. -/
theorem trajectoryGrowingPrefixForwardBesselPACBayesBoundary_tendsto_zero
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (posterior : ℕ → ι → ℝ) (hposterior : ∀ n, IsPMF (posterior n))
    {score : ι → TrajectoryScore Z}
    (hscore : ∀ i n u y, score i n u y ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (x : ℕ → Z) :
    Filter.Tendsto
      (fun n ↦ trajectoryGrowingPrefixForwardBesselPACBayesBoundary
        prior score (posterior n) delta n x)
      Filter.atTop (nhds 0) := by
  exact growingPrefixForwardBesselPACBayesBoundary_tendsto_zero
    hprior posterior hposterior hdelta hdelta1
      (fun i k x ↦ observedTrajectoryScore_mem_Icc (hscore i) k x) x

/-! ## One-event trajectory oracle -/

/-- One countable-allocation event supports simultaneous path- and time-
dependent posterior selection and exact post-data minimization over the
growing geometric prefix.  On the same event, the ordinary monitored
conditional trajectory risk is controlled by empirical prequential risk plus
the selected exact boundary; that boundary obeys the observable LIL-order
envelope and tends to zero along every path. -/
theorem exists_trajectoryGrowingPrefixForwardBesselPACBayesOracle_event
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
        (∀ x ∈ goodEvent, ∀ n : ℕ, 4 ≤ n →
          let selected := trajectoryGrowingPrefixForwardBesselPACBayesArgmin
            prior score (posterior x n) delta n x
          selected ∈ Finset.range
              (growingPrefixForwardBesselPACBayesMaxIndex n + 1) ∧
            trajectoryPosteriorAverageConditionalRisk
                K score (posterior x n) n x <
              trajectoryPosteriorEmpiricalPrequentialRisk
                  score (posterior x n) n x +
                trajectoryGrowingPrefixForwardBesselPACBayesBoundary
                  prior score (posterior x n) delta n x ∧
            trajectoryGrowingPrefixForwardBesselPACBayesBoundary
                prior score (posterior x n) delta n x ≤
              trajectoryGrowingPrefixForwardBesselPACBayesLILEnvelope
                prior score (posterior x n) delta n x ∧
            trajectoryGrowingPrefixForwardBesselPACBayesBoundary
                prior score (posterior x n) delta n x ≤
              allTimeGeometricPolynomialForwardRate
                (fun _ ↦ klDiv (posterior x n) prior) delta n) ∧
        (∀ x ∈ goodEvent,
          Filter.Tendsto
            (fun n ↦ trajectoryGrowingPrefixForwardBesselPACBayesBoundary
              prior score (posterior x n) delta n x)
            Filter.atTop (nhds 0)) := by
  obtain ⟨goodEvent, hmass, hgood⟩ :=
    exists_trajectoryCountableEmpiricalBernsteinPACBayes_event
      K x0 hscore hprior hdelta
  refine ⟨goodEvent, hmass, ?_, ?_⟩
  · intro x hx n hn
    let selected := trajectoryGrowingPrefixForwardBesselPACBayesArgmin
      prior score (posterior x n) delta n x
    have hselected_mem : selected ∈
        Finset.range
          (growingPrefixForwardBesselPACBayesMaxIndex n + 1) := by
      exact trajectoryGrowingPrefixForwardBesselPACBayesArgmin_mem
        prior score (posterior x n) delta n x
    have hrisk := hgood x hx selected (posterior x n)
      (hposterior x n) n (by omega)
    have hLIL :=
      trajectoryGrowingPrefixForwardBesselPACBayesBoundary_le_LILEnvelope
        hprior (hposterior x n) hscore hdelta hdelta1 hn x
    have hrate :=
      trajectoryGrowingPrefixForwardBesselPACBayesBoundary_le_allTimeRate
        hprior (hposterior x n) hscore hdelta hdelta1 hn x
    exact ⟨hselected_mem, hrisk, hLIL, hrate⟩
  · intro x _hx
    exact trajectoryGrowingPrefixForwardBesselPACBayesBoundary_tendsto_zero
      hprior (posterior x) (hposterior x) hscore hdelta hdelta1 x

end

end FormalSLT.StochasticDynamics
