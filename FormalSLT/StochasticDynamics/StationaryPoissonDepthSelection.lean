/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.StationaryPoissonContraction
import FormalSLT.StochasticDynamics.TrajectoryEmpiricalBernsteinPACBayesCountable

/-!
# Confidence-allocated selection of a finite Poisson depth

This module confidence-allocates over the truncation depth in the finite-depth
Poisson construction.  Depth `m` receives the predeclared mass
`1 / ((m + 1) * (m + 2))`; within that depth, the existing countable
trajectory theorem allocates over the geometric tilt catalog.  One outer
event is therefore simultaneous over every depth, tilt, time, and finite-class
posterior.

The resulting certificate may be instantiated with a path- and time-dependent
depth and tilt.  This is substitution into a common event.  It is not a
selected process, and the countable depth union is not asserted to be a
single master e-process.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open scoped BigOperators ENNReal

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {ι Z : Type*}
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype Z] [Nonempty Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-! ## Depth-indexed scores and exact boundary -/

/-- The finite-depth Poisson potential catalog at depth `m`. -/
def finiteDepthPoissonPotentialCatalog
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : ι → MarkovTransitionScore Z) (m : ℕ) : ι → Z → ℝ :=
  fun i ↦ finiteDepthPoissonPotential P stationary (score i) m

/-- The normalized corrected trajectory-score catalog at depth `m`. -/
def finiteDepthPoissonCorrectedTrajectoryScoreCatalog
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : ι → MarkovTransitionScore Z) (alpha D : ℝ) (m : ℕ) :
    ι → TrajectoryScore Z :=
  fun i ↦ poissonCorrectedTrajectoryScore
    (finiteDepthPoissonSpanBound alpha D m) (score i)
    (finiteDepthPoissonPotential P stationary (score i) m)

/-- Exact selected-depth stationary-risk width.  Its confidence argument is
`delta * q_m`, where `q_m = 1 / ((m+1)(m+2))`; the inner trajectory boundary
then charges the geometric tilt atom `j`. -/
def stationaryPoissonDepthSelectionBoundary
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : ι → MarkovTransitionScore Z) (alpha D : ℝ)
    (prior posterior : ι → ℝ) (delta : ℝ)
    (m j n : ℕ) (x : ℕ → Z) : ℝ :=
  finiteDepthPoissonScaleBound alpha D m *
      trajectoryCountableEmpiricalBernsteinPACBayesBoundary
        prior
        (finiteDepthPoissonCorrectedTrajectoryScoreCatalog
          P stationary score alpha D m)
        posterior (delta * polynomialForwardTiltWeight m) j n x +
    finiteDepthPoissonSpanBound alpha D m / (n : ℝ) +
      finiteDepthPoissonResidualBound alpha D m

omit [DecidableEq ι] [Nonempty ι]
  [Fintype Z] [Nonempty Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
/-- The nested depth--tilt allocation has the exact logarithmic price
`log (((m+1)(m+2)(j+1)(j+2))/delta)`. -/
theorem depthTiltPolynomial_log_cost
    {delta : ℝ} (hdelta : delta ≠ 0) (m j : ℕ) :
    Real.log
        ((((j : ℝ) + 1) * ((j : ℝ) + 2)) /
          (delta * polynomialForwardTiltWeight m)) =
      Real.log
        ((((m : ℝ) + 1) * ((m : ℝ) + 2) *
          ((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta) := by
  congr 1
  unfold polynomialForwardTiltWeight
    FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch.reverseDyadicEpochWeight
  field_simp [hdelta]

omit [DecidableEq ι] [Nonempty ι]
  [Fintype Z] [Nonempty Z] [MeasurableSingletonClass Z] in
/-- Fully expanded selected-depth boundary, including the joint depth--tilt
confidence cost and the observed corrected-score hybrid-Bessel penalty. -/
theorem stationaryPoissonDepthSelectionBoundary_eq_explicit
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : ι → MarkovTransitionScore Z) (alpha D : ℝ)
    (prior posterior : ι → ℝ) {delta : ℝ} (hdelta : delta ≠ 0)
    (m j n : ℕ) (x : ℕ → Z) :
    stationaryPoissonDepthSelectionBoundary P stationary score alpha D
        prior posterior delta m j n x =
      finiteDepthPoissonScaleBound alpha D m *
        ((klDiv posterior prior +
            Real.log
              ((((m : ℝ) + 1) * ((m : ℝ) + 2) *
                ((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta) +
            forwardEmpiricalBernsteinPsi (geometricForwardTilt j) *
              trajectoryPosteriorHybridBesselPenalty posterior
                (finiteDepthPoissonCorrectedTrajectoryScoreCatalog
                  P stationary score alpha D m) n x) /
          ((n : ℝ) * geometricForwardTilt j)) +
        finiteDepthPoissonSpanBound alpha D m / (n : ℝ) +
          finiteDepthPoissonResidualBound alpha D m := by
  unfold stationaryPoissonDepthSelectionBoundary
  rw [trajectoryCountableEmpiricalBernsteinPACBayesBoundary_eq_explicit
    (hdelta := mul_ne_zero hdelta
      (ne_of_gt (polynomialForwardTiltWeight_pos m)))]
  rw [depthTiltPolynomial_log_cost hdelta m j]

/-! ## Countable confidence allocation over depth -/

/-- The already-countable geometric-tilt exceptional event for one fixed
Poisson depth, charged confidence `delta * q_m`. -/
def stationaryPoissonDepthAtomExceptionalEvent
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : ι → MarkovTransitionScore Z) (alpha D : ℝ)
    (prior : ι → ℝ) (delta : ℝ) (m : ℕ) : Set (ℕ → Z) :=
  trajectoryCountableEmpiricalBernsteinPACBayesExceptionalEvent
    (prefixKernel P) prior
    (finiteDepthPoissonCorrectedTrajectoryScoreCatalog
      P stationary score alpha D m)
    (delta * polynomialForwardTiltWeight m)

/-- The countable union of the depth-specific trajectory crossing events. -/
def stationaryPoissonDepthSelectionExceptionalEvent
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : ι → MarkovTransitionScore Z) (alpha D : ℝ)
    (prior : ι → ℝ) (delta : ℝ) : Set (ℕ → Z) :=
  ⋃ m : ℕ,
    stationaryPoissonDepthAtomExceptionalEvent
      P stationary score alpha D prior delta m

omit [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSingletonClass Z] in
/-- Every corrected score catalog is unit-valued under the contraction-derived
potential span. -/
theorem finiteDepthPoissonCorrectedTrajectoryScoreCatalog_mem_Icc
    (P : Z → PMF Z) (stationary : PMF Z)
    {score : ι → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {alpha D : ℝ} (halpha : 0 ≤ alpha) (hDnonneg : 0 ≤ D)
    (hcontract : IsOscillationContraction P alpha)
    (hD : ∀ i,
      finiteOscillation (centeredMarkovRowRisk P stationary (score i)) ≤ D)
    (m : ℕ) :
    ∀ i n u y,
      finiteDepthPoissonCorrectedTrajectoryScoreCatalog
          P stationary score alpha D m i n u y ∈ Set.Icc (0 : ℝ) 1 := by
  intro i n u y
  apply poissonCorrectedTransitionScore_mem_Icc
    (finiteDepthPoissonSpanBound_nonneg halpha hDnonneg m)
    (hscore i)
  intro x z
  exact finiteDepthPoissonPotential_span P stationary (score i) m
    halpha hcontract (hD i) x z

omit [Nonempty ι] in
/-- One depth-specific, already-countable tilt event costs at most its assigned
depth budget. -/
theorem stationaryPoissonDepthAtomExceptionalEvent_mass_le
    (P : Z → PMF Z) (stationary : PMF Z) (x0 : Z)
    {score : ι → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {alpha D : ℝ} (halpha : 0 ≤ alpha) (hDnonneg : 0 ≤ D)
    (hcontract : IsOscillationContraction P alpha)
    (hD : ∀ i,
      finiteOscillation (centeredMarkovRowRisk P stationary (score i)) ≤ D)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {delta : ℝ} (hdelta : 0 < delta) (m : ℕ) :
    (markovPathMeasure P x0).real
        (stationaryPoissonDepthAtomExceptionalEvent
          P stationary score alpha D prior delta m) ≤
      delta * polynomialForwardTiltWeight m := by
  have hcorrected :=
    finiteDepthPoissonCorrectedTrajectoryScoreCatalog_mem_Icc
      P stationary hscore halpha hDnonneg hcontract hD m
  have hmass :=
    trajectoryCountableEmpiricalBernsteinPACBayesExceptionalEvent_mass_le
      (prefixKernel P) x0 hcorrected hprior
      (mul_pos hdelta (polynomialForwardTiltWeight_pos m))
  simpa [stationaryPoissonDepthAtomExceptionalEvent,
    trajectoryMeasure_prefixKernel_eq_markovPathMeasure] using hmass

omit [Nonempty ι] in
/-- Countable subadditivity and the telescoping depth weights bound the full
depth-selection exceptional event by `delta`. -/
theorem stationaryPoissonDepthSelectionExceptionalEvent_mass_le
    (P : Z → PMF Z) (stationary : PMF Z) (x0 : Z)
    {score : ι → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {alpha D : ℝ} (halpha : 0 ≤ alpha) (hDnonneg : 0 ≤ D)
    (hcontract : IsOscillationContraction P alpha)
    (hD : ∀ i,
      finiteOscillation (centeredMarkovRowRisk P stationary (score i)) ≤ D)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {delta : ℝ} (hdelta : 0 < delta) :
    (markovPathMeasure P x0).real
        (stationaryPoissonDepthSelectionExceptionalEvent
          P stationary score alpha D prior delta) ≤ delta := by
  let μ := markovPathMeasure P x0
  let event : ℕ → Set (ℕ → Z) := fun m ↦
    stationaryPoissonDepthAtomExceptionalEvent
      P stationary score alpha D prior delta m
  have hatomReal : ∀ m, μ.real (event m) ≤
      delta * polynomialForwardTiltWeight m := by
    intro m
    exact stationaryPoissonDepthAtomExceptionalEvent_mass_le
      P stationary x0 hscore halpha hDnonneg hcontract hD hprior hdelta m
  have hatomENNReal : ∀ m, μ (event m) ≤
      ENNReal.ofReal (delta * polynomialForwardTiltWeight m) := by
    intro m
    calc
      μ (event m) = ENNReal.ofReal (μ.real (event m)) := by
        rw [ofReal_measureReal]
      _ ≤ ENNReal.ofReal (delta * polynomialForwardTiltWeight m) :=
        ENNReal.ofReal_le_ofReal (hatomReal m)
  have hallocated : HasSum
      (fun m ↦ delta * polynomialForwardTiltWeight m) delta := by
    simpa using polynomialForwardTiltWeight_hasSum.mul_left delta
  have hsummable : Summable
      (fun m ↦ delta * polynomialForwardTiltWeight m) :=
    hallocated.summable
  have hnonneg : ∀ m, 0 ≤ delta * polynomialForwardTiltWeight m :=
    fun m ↦ mul_nonneg hdelta.le (polynomialForwardTiltWeight_pos m).le
  have hunionENNReal : μ (⋃ m, event m) ≤ ENNReal.ofReal delta := by
    calc
      μ (⋃ m, event m) ≤ ∑' m, μ (event m) := measure_iUnion_le _
      _ ≤ ∑' m, ENNReal.ofReal
          (delta * polynomialForwardTiltWeight m) :=
        ENNReal.tsum_le_tsum hatomENNReal
      _ = ENNReal.ofReal delta := by
        rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable,
          hallocated.tsum_eq]
  change μ.real (⋃ m, event m) ≤ delta
  calc
    μ.real (⋃ m, event m) ≤ (ENNReal.ofReal delta).toReal := by
      exact ENNReal.toReal_mono (by simp) hunionENNReal
    _ = delta := ENNReal.toReal_ofReal hdelta.le

/-! ## Simultaneous selected-depth stationary-risk endpoint -/

omit [DecidableEq ι] in
/-- Outside the common depth union, every depth, geometric tilt, time, and
finite-class posterior satisfies the stationary-risk certificate. -/
theorem stationaryPoissonDepthSelection_allPosteriors_of_not_mem
    (P : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary)
    {score : ι → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {alpha D : ℝ} (halpha : 0 ≤ alpha) (hDnonneg : 0 ≤ D)
    (hcontract : IsOscillationContraction P alpha)
    (hD : ∀ i,
      finiteOscillation (centeredMarkovRowRisk P stationary (score i)) ≤ D)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {delta : ℝ} (hdelta : 0 < delta)
    {x : ℕ → Z}
    (hx : x ∉ stationaryPoissonDepthSelectionExceptionalEvent
      P stationary score alpha D prior delta) :
    ∀ m j : ℕ, ∀ posterior : ι → ℝ, IsPMF posterior →
      ∀ n : ℕ, 2 ≤ n →
        stationaryPosteriorMarkovRisk P stationary score posterior <
          empiricalTransitionPosteriorRisk score posterior n x +
            stationaryPoissonDepthSelectionBoundary
              P stationary score alpha D prior posterior delta m j n x := by
  intro m j posterior hposterior n hn
  let B := finiteDepthPoissonSpanBound alpha D m
  let R := finiteDepthPoissonResidualBound alpha D m
  let potential := finiteDepthPoissonPotentialCatalog P stationary score m
  have hB : 0 ≤ B :=
    finiteDepthPoissonSpanBound_nonneg halpha hDnonneg m
  have hR : 0 ≤ R :=
    finiteDepthPoissonResidualBound_nonneg halpha hDnonneg m
  have hspan : ∀ i y z, |potential i z - potential i y| ≤ B := by
    intro i y z
    exact finiteDepthPoissonPotential_span P stationary (score i) m
      halpha hcontract (hD i) y z
  have hresidual : ∀ i z,
      |approximatePoissonResidual P stationary (score i) (potential i) z| ≤ R := by
    intro i z
    exact finiteDepthPoissonResidual_le P stationary hstationary (score i) m
      halpha hcontract (hD i) z
  have hxDepth : x ∉ stationaryPoissonDepthAtomExceptionalEvent
      P stationary score alpha D prior delta m := by
    intro hxm
    apply hx
    exact Set.mem_iUnion.mpr ⟨m, hxm⟩
  have hcorrected :=
    finiteDepthPoissonCorrectedTrajectoryScoreCatalog_mem_Icc
      P stationary hscore halpha hDnonneg hcontract hD m
  have hbase :=
    trajectoryCountableEmpiricalBernsteinPACBayes_allPosteriors_of_not_mem
      (prefixKernel P) hcorrected hprior
      (mul_pos hdelta (polynomialForwardTiltWeight_pos m))
      hxDepth j posterior hposterior n hn
  have hnpos : 0 < n := by omega
  have hden : 0 < 1 + 2 * B := by linarith
  change
    trajectoryPosteriorAverageConditionalRisk (prefixKernel P)
        (fun i ↦ poissonCorrectedTrajectoryScore B (score i) (potential i))
        posterior n x <
      trajectoryPosteriorEmpiricalPrequentialRisk
          (fun i ↦ poissonCorrectedTrajectoryScore B (score i) (potential i))
          posterior n x +
        trajectoryCountableEmpiricalBernsteinPACBayesBoundary prior
          (fun i ↦ poissonCorrectedTrajectoryScore B (score i) (potential i))
          posterior (delta * polynomialForwardTiltWeight m) j n x at hbase
  rw [trajectoryPosteriorAverageConditionalRisk_poissonCorrected
      hB P stationary score potential posterior hposterior n hnpos x,
    trajectoryPosteriorEmpiricalPrequentialRisk_poissonCorrected
      hB score potential posterior hposterior n hnpos x] at hbase
  have hscaled := mul_lt_mul_of_pos_right hbase hden
  field_simp [ne_of_gt hden] at hscaled
  have hendpoint := posteriorPoissonEndpointCorrection_le
    hB hspan hposterior n hnpos x
  have hres := neg_posteriorPoissonResidualAverage_le
    P stationary score potential
    (residualEnvelope := fun _i : ι ↦ R)
    (fun _i ↦ hR) hresidual hposterior n hnpos x
  have hposteriorResidual :
      posteriorAverage posterior (fun _i : ι ↦ R) = R := by
    unfold posteriorAverage
    rw [← Finset.sum_mul, hposterior.sum_one, one_mul]
  rw [hposteriorResidual] at hres
  change
    stationaryPosteriorMarkovRisk P stationary score posterior <
      empiricalTransitionPosteriorRisk score posterior n x +
        ((1 + 2 * B) *
            trajectoryCountableEmpiricalBernsteinPACBayesBoundary prior
              (fun i ↦ poissonCorrectedTrajectoryScore
                B (score i) (potential i))
              posterior (delta * polynomialForwardTiltWeight m) j n x +
          B / (n : ℝ) + R)
  linarith

/-- One outer event is simultaneous over depth, geometric tilt, time, and
posterior.  The depth and tilt can therefore be selected after seeing the path
and time, without asserting that the selected object is an e-process. -/
theorem exists_stationaryPoissonDepthSelection_event
    (P : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary) (x0 : Z)
    {score : ι → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {alpha D : ℝ} (halpha : 0 ≤ alpha) (hDnonneg : 0 ≤ D)
    (hcontract : IsOscillationContraction P alpha)
    (hD : ∀ i,
      finiteOscillation (centeredMarkovRowRisk P stationary (score i)) ≤ D)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ goodEvent : Set (ℕ → Z),
      (markovPathMeasure P x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ m j : ℕ,
          ∀ posterior : ι → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              stationaryPosteriorMarkovRisk P stationary score posterior <
                empiricalTransitionPosteriorRisk score posterior n x +
                  stationaryPoissonDepthSelectionBoundary
                    P stationary score alpha D prior posterior delta m j n x := by
  let badEvent := stationaryPoissonDepthSelectionExceptionalEvent
    P stationary score alpha D prior delta
  refine ⟨badEventᶜ, ?_, ?_⟩
  · simpa [badEvent] using
      (stationaryPoissonDepthSelectionExceptionalEvent_mass_le
        P stationary x0 hscore halpha hDnonneg hcontract hD hprior hdelta)
  · intro x hx
    exact stationaryPoissonDepthSelection_allPosteriors_of_not_mem
      P stationary hstationary hscore halpha hDnonneg hcontract hD
      hprior hdelta hx

/-- Explicit substitution form for path- and time-dependent depth, tilt, and
posterior selectors. -/
theorem exists_stationaryPoissonDepthSelection_selected_event
    (P : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary) (x0 : Z)
    {score : ι → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {alpha D : ℝ} (halpha : 0 ≤ alpha) (hDnonneg : 0 ≤ D)
    (hcontract : IsOscillationContraction P alpha)
    (hD : ∀ i,
      finiteOscillation (centeredMarkovRowRisk P stationary (score i)) ≤ D)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {delta : ℝ} (hdelta : 0 < delta)
    (depth tilt : (ℕ → Z) → ℕ → ℕ)
    (posterior : (ℕ → Z) → ℕ → ι → ℝ)
    (hposterior : ∀ x n, IsPMF (posterior x n)) :
    ∃ goodEvent : Set (ℕ → Z),
      (markovPathMeasure P x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
          stationaryPosteriorMarkovRisk
              P stationary score (posterior x n) <
            empiricalTransitionPosteriorRisk score (posterior x n) n x +
              stationaryPoissonDepthSelectionBoundary
                P stationary score alpha D prior (posterior x n) delta
                  (depth x n) (tilt x n) n x := by
  obtain ⟨goodEvent, hmass, hgood⟩ :=
    exists_stationaryPoissonDepthSelection_event
      P stationary hstationary x0 hscore halpha hDnonneg hcontract hD
      hprior hdelta
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx n hn
  exact hgood x hx (depth x n) (tilt x n)
    (posterior x n) (hposterior x n) n hn

/-! ## Finite depth minimization -/

omit [DecidableEq ι] [Nonempty ι] [Fintype Z] [Nonempty Z]
  [MeasurableSingletonClass Z] in
private theorem stationaryPoissonFiniteDepth_exists_argmin
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : ι → MarkovTransitionScore Z) (alpha D : ℝ)
    (prior posterior : ι → ℝ) (delta : ℝ)
    (maxDepth j n : ℕ) (x : ℕ → Z) :
    ∃ m ∈ Finset.range (maxDepth + 1),
      ∀ m' ∈ Finset.range (maxDepth + 1),
        stationaryPoissonDepthSelectionBoundary
            P stationary score alpha D prior posterior delta m j n x ≤
          stationaryPoissonDepthSelectionBoundary
            P stationary score alpha D prior posterior delta m' j n x := by
  exact (Finset.range (maxDepth + 1)).exists_min_image
    (fun m ↦ stationaryPoissonDepthSelectionBoundary
      P stationary score alpha D prior posterior delta m j n x)
    (by simp)

/-- A concrete finite argmin over depths `0, ..., maxDepth`.  It may depend on
the path, posterior, time, and selected tilt because the common event is
already uniform over every depth. -/
def stationaryPoissonFiniteDepthArgmin
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : ι → MarkovTransitionScore Z) (alpha D : ℝ)
    (prior posterior : ι → ℝ) (delta : ℝ)
    (maxDepth j n : ℕ) (x : ℕ → Z) : ℕ :=
  Classical.choose (stationaryPoissonFiniteDepth_exists_argmin
    P stationary score alpha D prior posterior delta maxDepth j n x)

omit [DecidableEq ι] [Nonempty ι] [Fintype Z] [Nonempty Z]
  [MeasurableSingletonClass Z] in
/-- The finite argmin lies in the declared depth range. -/
theorem stationaryPoissonFiniteDepthArgmin_lt_succ
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : ι → MarkovTransitionScore Z) (alpha D : ℝ)
    (prior posterior : ι → ℝ) (delta : ℝ)
    (maxDepth j n : ℕ) (x : ℕ → Z) :
    stationaryPoissonFiniteDepthArgmin P stationary score alpha D
        prior posterior delta maxDepth j n x < maxDepth + 1 := by
  exact Finset.mem_range.mp
    (Classical.choose_spec (stationaryPoissonFiniteDepth_exists_argmin
      P stationary score alpha D prior posterior delta maxDepth j n x)).1

omit [DecidableEq ι] [Nonempty ι] [Fintype Z] [Nonempty Z]
  [MeasurableSingletonClass Z] in
/-- Minimality of the finite depth selector against every declared candidate. -/
theorem stationaryPoissonFiniteDepthArgmin_le
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : ι → MarkovTransitionScore Z) (alpha D : ℝ)
    (prior posterior : ι → ℝ) (delta : ℝ)
    (maxDepth j n : ℕ) (x : ℕ → Z)
    {m : ℕ} (hm : m < maxDepth + 1) :
    stationaryPoissonDepthSelectionBoundary P stationary score alpha D
        prior posterior delta
          (stationaryPoissonFiniteDepthArgmin P stationary score alpha D
            prior posterior delta maxDepth j n x) j n x ≤
      stationaryPoissonDepthSelectionBoundary P stationary score alpha D
        prior posterior delta m j n x := by
  exact (Classical.choose_spec (stationaryPoissonFiniteDepth_exists_argmin
    P stationary score alpha D prior posterior delta maxDepth j n x)).2
      m (Finset.mem_range.mpr hm)

/-! ## Deterministic logarithmic depth selector -/

/-- The deterministic truncation depth `floor(log_2 n)`. -/
def logarithmicPoissonDepth (n : ℕ) : ℕ := Nat.log 2 n

/-- The logarithmic depth diverges over the integer sample sizes. -/
theorem logarithmicPoissonDepth_tendsto_atTop :
    Filter.Tendsto logarithmicPoissonDepth Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨2 ^ b, ?_⟩
  intro n hn
  exact Nat.le_log_of_pow_le (by norm_num) hn

/-- Base four is the square of base two, so its integer logarithm is the
base-two integer logarithm divided by two. -/
theorem logarithmicPoissonDepth_div_two (n : ℕ) :
    Nat.log 4 n = logarithmicPoissonDepth n / 2 := by
  simpa [logarithmicPoissonDepth] using Nat.log_pow_left 2 2 n

/-- The depth selected at `n >= 4` is at most twice the geometric-tilt scale,
up to the unavoidable parity remainder. -/
theorem logarithmicPoissonDepth_le_two_geometricIndex_add_one
    {n : ℕ} (hn : 4 ≤ n) :
    logarithmicPoissonDepth n ≤
      2 * (geometricForwardTiltIndex n + 1) + 1 := by
  have hindex := geometricForwardTiltIndex_add_one hn
  have hbase := logarithmicPoissonDepth_div_two n
  omega

/-- Every polynomial allocation weight is at most one. -/
theorem polynomialForwardTiltWeight_le_one (m : ℕ) :
    polynomialForwardTiltWeight m ≤ 1 := by
  unfold polynomialForwardTiltWeight
    FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch.reverseDyadicEpochWeight
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  apply (div_le_one (by positivity)).2
  nlinarith

/-- The depth part of the joint logarithmic selection price, normalized by
the effective sample size of the all-time geometric tilt. -/
def logarithmicDepthTiltLogRate (delta : ℝ) (n : ℕ) : ℝ :=
  Real.log
      ((((logarithmicPoissonDepth n : ℝ) + 1) *
        ((logarithmicPoissonDepth n : ℝ) + 2) *
        ((geometricForwardTiltIndex n : ℝ) + 1) *
        ((geometricForwardTiltIndex n : ℝ) + 2)) / delta) /
    (2 : ℝ) ^ (geometricForwardTiltIndex n + 1)

/-- The extra confidence price for selecting `floor(log_2 n)` vanishes at the
geometric tilt's effective sample-size scale. -/
theorem logarithmicDepthTiltLogRate_tendsto_zero
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    Filter.Tendsto (logarithmicDepthTiltLogRate delta)
      Filter.atTop (nhds 0) := by
  let q : ℕ → ℕ := fun n ↦ geometricForwardTiltIndex n + 1
  have hq : Filter.Tendsto q Filter.atTop Filter.atTop := by
    simpa only [q, Function.comp_def] using
      (Filter.tendsto_add_atTop_nat 1).comp
        geometricForwardTiltIndex_tendsto_atTop
  have h4 := tendsto_pow_const_div_const_pow_of_one_lt 4
    (by norm_num : (1 : ℝ) < 2)
  have h3 := tendsto_pow_const_div_const_pow_of_one_lt 3
    (by norm_num : (1 : ℝ) < 2)
  have h2 := tendsto_pow_const_div_const_pow_of_one_lt 2
    (by norm_num : (1 : ℝ) < 2)
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1
    (by norm_num : (1 : ℝ) < 2)
  have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0
    (by norm_num : (1 : ℝ) < 2)
  have hpolyBase : Filter.Tendsto
      (fun r : ℕ ↦ ((r : ℝ) + 1) ^ 4 / (2 : ℝ) ^ r)
      Filter.atTop (nhds 0) := by
    have hsum :=
      (((h4.add (h3.const_mul 4)).add (h2.const_mul 6)).add
        (h1.const_mul 4)).add h0
    convert hsum using 1
    · funext r
      ring
    · norm_num
  let g : ℕ → ℝ := fun n ↦
    (6 / delta) * (((q n : ℝ) + 1) ^ 4 / (2 : ℝ) ^ (q n))
  have hg : Filter.Tendsto g Filter.atTop (nhds 0) := by
    simpa [g, Function.comp_def] using
      (hpolyBase.comp hq).const_mul (6 / delta)
  apply squeeze_zero'
  · filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    let m := logarithmicPoissonDepth n
    let r := q n
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hr1 : (1 : ℝ) ≤ r := by
      dsimp [r, q]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hprodOne :
        (1 : ℝ) ≤ ((m : ℝ) + 1) * ((m : ℝ) + 2) *
            (r : ℝ) * ((r : ℝ) + 1) := by
      have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith
      have hm2 : (1 : ℝ) ≤ (m : ℝ) + 2 := by linarith
      have hr2 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith
      exact one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le hm1 hm2) hr1) hr2
    have hratio : 1 ≤
        (((m : ℝ) + 1) * ((m : ℝ) + 2) *
          (r : ℝ) * ((r : ℝ) + 1)) / delta := by
      apply (le_div_iff₀ hdelta).2
      simpa only [one_mul] using hdelta1.trans hprodOne
    have hratio' : 1 ≤
        (((logarithmicPoissonDepth n : ℝ) + 1) *
          ((logarithmicPoissonDepth n : ℝ) + 2) *
          ((geometricForwardTiltIndex n : ℝ) + 1) *
          ((geometricForwardTiltIndex n : ℝ) + 2)) / delta := by
      dsimp [m, r, q] at hratio
      push_cast at hratio
      convert hratio using 1
      ring
    exact div_nonneg (Real.log_nonneg hratio') (by positivity)
  · filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    let m := logarithmicPoissonDepth n
    let r := q n
    have hmNat : m ≤ 2 * r + 1 := by
      dsimp [m, r, q]
      exact logarithmicPoissonDepth_le_two_geometricIndex_add_one hn
    have hm : (m : ℝ) ≤ 2 * (r : ℝ) + 1 := by exact_mod_cast hmNat
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hm1 : (m : ℝ) + 1 ≤ 2 * ((r : ℝ) + 1) := by linarith
    have hm2 : (m : ℝ) + 2 ≤ 3 * ((r : ℝ) + 1) := by linarith
    have hr1 : (r : ℝ) ≤ (r : ℝ) + 1 := by linarith
    have hAB :
        ((m : ℝ) + 1) * ((m : ℝ) + 2) ≤
          (2 * ((r : ℝ) + 1)) * (3 * ((r : ℝ) + 1)) :=
      mul_le_mul hm1 hm2 (by positivity) (by positivity)
    have hABr :
        ((m : ℝ) + 1) * ((m : ℝ) + 2) * (r : ℝ) ≤
          ((2 * ((r : ℝ) + 1)) * (3 * ((r : ℝ) + 1))) *
            ((r : ℝ) + 1) :=
      mul_le_mul hAB hr1 (by positivity) (by positivity)
    have hprod :
        ((m : ℝ) + 1) * ((m : ℝ) + 2) *
            (r : ℝ) * ((r : ℝ) + 1) ≤
          6 * ((r : ℝ) + 1) ^ 4 := by
      calc
        _ ≤ (((2 * ((r : ℝ) + 1)) * (3 * ((r : ℝ) + 1))) *
              ((r : ℝ) + 1)) * ((r : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hABr (by positivity)
        _ = 6 * ((r : ℝ) + 1) ^ 4 := by ring
    have hratioPos : 0 <
        (((m : ℝ) + 1) * ((m : ℝ) + 2) *
          (r : ℝ) * ((r : ℝ) + 1)) / delta := by
      positivity
    have hratioBound :
        (((m : ℝ) + 1) * ((m : ℝ) + 2) *
          (r : ℝ) * ((r : ℝ) + 1)) / delta ≤
            (6 * ((r : ℝ) + 1) ^ 4) / delta :=
      (div_le_div_iff_of_pos_right hdelta).2 hprod
    dsimp [m, r, q] at hratioPos hratioBound
    push_cast at hratioPos hratioBound
    have hratioPos' : 0 <
        (((logarithmicPoissonDepth n : ℝ) + 1) *
          ((logarithmicPoissonDepth n : ℝ) + 2) *
          ((geometricForwardTiltIndex n : ℝ) + 1) *
          ((geometricForwardTiltIndex n : ℝ) + 2)) / delta := by
      convert hratioPos using 1
      ring
    have hratioBound' :
        (((logarithmicPoissonDepth n : ℝ) + 1) *
          ((logarithmicPoissonDepth n : ℝ) + 2) *
          ((geometricForwardTiltIndex n : ℝ) + 1) *
          ((geometricForwardTiltIndex n : ℝ) + 2)) / delta ≤
            (6 * ((geometricForwardTiltIndex n : ℝ) + 2) ^ 4) / delta := by
      convert hratioBound using 1
      all_goals ring
    dsimp [logarithmicDepthTiltLogRate, g, m, r, q]
    calc
      Real.log
          ((((logarithmicPoissonDepth n : ℝ) + 1) *
            ((logarithmicPoissonDepth n : ℝ) + 2) *
            ((geometricForwardTiltIndex n : ℝ) + 1) *
            ((geometricForwardTiltIndex n : ℝ) + 2)) / delta) /
          (2 : ℝ) ^ (geometricForwardTiltIndex n + 1) ≤
        ((((logarithmicPoissonDepth n : ℝ) + 1) *
            ((logarithmicPoissonDepth n : ℝ) + 2) *
            ((geometricForwardTiltIndex n : ℝ) + 1) *
            ((geometricForwardTiltIndex n : ℝ) + 2)) / delta) /
          (2 : ℝ) ^ (geometricForwardTiltIndex n + 1) :=
        div_le_div_of_nonneg_right (Real.log_le_self hratioPos'.le)
          (by positivity)
      _ ≤ ((6 *
          ((geometricForwardTiltIndex n : ℝ) + 2) ^ 4) / delta) /
            (2 : ℝ) ^ (geometricForwardTiltIndex n + 1) :=
        div_le_div_of_nonneg_right hratioBound' (by positivity)
      _ = (6 / delta) *
          (((geometricForwardTiltIndex n : ℝ) + 2) ^ 4 /
            (2 : ℝ) ^ (geometricForwardTiltIndex n + 1)) := by ring
  · have hg' : Filter.Tendsto
        (fun n ↦ (6 / delta) *
          (((geometricForwardTiltIndex n : ℝ) + 2) ^ 4 /
            (2 : ℝ) ^ (geometricForwardTiltIndex n + 1)))
        Filter.atTop (nhds 0) := by
      convert hg using 1
      funext n
      dsimp [g, q]
      push_cast
      ring
    exact hg'

/-- Deterministic trajectory-width envelope after selecting both
`m(n) = floor(log_2 n)` and the all-time geometric tilt atom. -/
def logarithmicPoissonDepthTrajectoryRate
    (complexity : ℕ → ℝ) (delta : ℝ) (n : ℕ) : ℝ :=
  2 * geometricForwardTilt (geometricForwardTiltIndex n) +
    (complexity n / (2 : ℝ) ^ (geometricForwardTiltIndex n + 1) +
      logarithmicDepthTiltLogRate delta n)

omit [DecidableEq ι] [Nonempty ι] in
/-- The selected trajectory-width envelope vanishes for arbitrary posterior
sequences on a finite full-support prior. -/
theorem logarithmicPoissonDepthTrajectoryRate_tendsto_zero
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (posterior : ℕ → ι → ℝ) (hposterior : ∀ n, IsPMF (posterior n))
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    Filter.Tendsto
      (logarithmicPoissonDepthTrajectoryRate
        (fun n ↦ klDiv (posterior n) prior) delta)
      Filter.atTop (nhds 0) := by
  have htiltBase : Filter.Tendsto geometricForwardTilt
      Filter.atTop (nhds 0) := by
    have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0
      (by norm_num : (1 : ℝ) < 2)
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
  have hcomplexity :=
    klDiv_div_geometricForwardTiltIndex_tendsto_zero
      hprior posterior hposterior
  have hlog := logarithmicDepthTiltLogRate_tendsto_zero hdelta hdelta1
  have hsum := htilt.const_mul 2 |>.add (hcomplexity.add hlog)
  change Filter.Tendsto
    (fun n ↦ 2 * geometricForwardTilt (geometricForwardTiltIndex n) +
      (klDiv (posterior n) prior /
          (2 : ℝ) ^ (geometricForwardTiltIndex n + 1) +
        logarithmicDepthTiltLogRate delta n))
    Filter.atTop (nhds 0)
  simpa using hsum

/-- Full deterministic stationary-risk width envelope for the logarithmic
depth and all-time geometric tilt selectors. -/
def logarithmicPoissonDepthStationaryRate
    (alpha D : ℝ) (complexity : ℕ → ℝ) (delta : ℝ) (n : ℕ) : ℝ :=
  finiteDepthPoissonScaleBound alpha D (logarithmicPoissonDepth n) *
      logarithmicPoissonDepthTrajectoryRate complexity delta n +
    finiteDepthPoissonSpanBound alpha D (logarithmicPoissonDepth n) / (n : ℝ) +
      finiteDepthPoissonResidualBound alpha D (logarithmicPoissonDepth n)

omit [DecidableEq ι] [Nonempty ι] [MeasurableSingletonClass Z] in
/-- The exact selected boundary is bounded pointwise by the deterministic
logarithmic-depth stationary rate for every `n >= 4`. -/
theorem stationaryPoissonDepthSelectionBoundary_logarithmic_le_rate
    (P : Z → PMF Z) (stationary : PMF Z)
    {score : ι → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {alpha D : ℝ} (halpha : 0 ≤ alpha) (hDnonneg : 0 ≤ D)
    (hcontract : IsOscillationContraction P alpha)
    (hD : ∀ i,
      finiteOscillation (centeredMarkovRowRisk P stationary (score i)) ≤ D)
    {prior posterior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (hposterior : IsPMF posterior)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {n : ℕ} (hn : 4 ≤ n) (x : ℕ → Z) :
    stationaryPoissonDepthSelectionBoundary
        P stationary score alpha D prior posterior delta
          (logarithmicPoissonDepth n) (geometricForwardTiltIndex n) n x ≤
      logarithmicPoissonDepthStationaryRate alpha D
        (fun _ ↦ klDiv posterior prior) delta n := by
  let m := logarithmicPoissonDepth n
  have hcorrected :=
    finiteDepthPoissonCorrectedTrajectoryScoreCatalog_mem_Icc
      P stationary hscore halpha hDnonneg hcontract hD m
  have hconfPos : 0 < delta * polynomialForwardTiltWeight m :=
    mul_pos hdelta (polynomialForwardTiltWeight_pos m)
  have hconfOne : delta * polynomialForwardTiltWeight m ≤ 1 :=
    calc
      delta * polynomialForwardTiltWeight m ≤
          1 * polynomialForwardTiltWeight m :=
        mul_le_mul_of_nonneg_right hdelta1
          (polynomialForwardTiltWeight_pos m).le
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left
        (polynomialForwardTiltWeight_le_one m) (by norm_num)
      _ = 1 := one_mul 1
  have htrajectory :=
    trajectoryCountableEmpiricalBernsteinPACBayesBoundary_selected_le_rate
      hprior hposterior hcorrected hconfPos hconfOne hn x
  have hrateEq :
      allTimeGeometricPolynomialForwardRate
          (fun _ ↦ klDiv posterior prior)
          (delta * polynomialForwardTiltWeight m) n =
        logarithmicPoissonDepthTrajectoryRate
          (fun _ ↦ klDiv posterior prior) delta n := by
    unfold allTimeGeometricPolynomialForwardRate
      logarithmicPoissonDepthTrajectoryRate
      logarithmicDepthTiltLogRate
    dsimp only
    dsimp [m]
    rw [depthTiltPolynomial_log_cost hdelta.ne' (logarithmicPoissonDepth n)
      (geometricForwardTiltIndex n)]
    rw [add_div]
  rw [hrateEq] at htrajectory
  have hscale : 0 ≤ finiteDepthPoissonScaleBound alpha D m := by
    have hB := finiteDepthPoissonSpanBound_nonneg halpha hDnonneg m
    unfold finiteDepthPoissonScaleBound
    linarith
  unfold stationaryPoissonDepthSelectionBoundary
    logarithmicPoissonDepthStationaryRate
  exact add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left htrajectory hscale) le_rfl)
    le_rfl

omit [DecidableEq ι] [Nonempty ι] [MeasurableSingletonClass Z] in
/-- The exact logarithmic-depth boundary is nonnegative. -/
theorem stationaryPoissonDepthSelectionBoundary_logarithmic_nonneg
    (P : Z → PMF Z) (stationary : PMF Z)
    {score : ι → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {alpha D : ℝ} (halpha : 0 ≤ alpha) (hDnonneg : 0 ≤ D)
    (hcontract : IsOscillationContraction P alpha)
    (hD : ∀ i,
      finiteOscillation (centeredMarkovRowRisk P stationary (score i)) ≤ D)
    {prior posterior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (hposterior : IsPMF posterior)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) (x : ℕ → Z) :
    0 ≤ stationaryPoissonDepthSelectionBoundary
        P stationary score alpha D prior posterior delta
          (logarithmicPoissonDepth n) (geometricForwardTiltIndex n) n x := by
  let m := logarithmicPoissonDepth n
  have hcorrected :=
    finiteDepthPoissonCorrectedTrajectoryScoreCatalog_mem_Icc
      P stationary hscore halpha hDnonneg hcontract hD m
  have hconfPos : 0 < delta * polynomialForwardTiltWeight m :=
    mul_pos hdelta (polynomialForwardTiltWeight_pos m)
  have hconfOne : delta * polynomialForwardTiltWeight m ≤ 1 :=
    calc
      delta * polynomialForwardTiltWeight m ≤
          1 * polynomialForwardTiltWeight m :=
        mul_le_mul_of_nonneg_right hdelta1
          (polynomialForwardTiltWeight_pos m).le
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left
        (polynomialForwardTiltWeight_le_one m) (by norm_num)
      _ = 1 := one_mul 1
  have htrajectory := countableForwardBesselPACBayesBoundary_nonneg
    hprior hposterior hconfPos hconfOne
    (fun i k x ↦ observedTrajectoryScore_mem_Icc (hcorrected i) k x)
    (geometricForwardTiltIndex n) n hn x
  have htrajectory' : 0 ≤
      trajectoryCountableEmpiricalBernsteinPACBayesBoundary prior
        (finiteDepthPoissonCorrectedTrajectoryScoreCatalog
          P stationary score alpha D m)
        posterior (delta * polynomialForwardTiltWeight m)
          (geometricForwardTiltIndex n) n x := by
    exact htrajectory
  have hB := finiteDepthPoissonSpanBound_nonneg halpha hDnonneg m
  have hR := finiteDepthPoissonResidualBound_nonneg halpha hDnonneg m
  unfold stationaryPoissonDepthSelectionBoundary
    finiteDepthPoissonScaleBound
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (by linarith) htrajectory')
      (div_nonneg hB (Nat.cast_nonneg n))) hR

omit [DecidableEq ι] [Nonempty ι] in
/-- For every fixed `0 <= alpha < 1`, the complete deterministic stationary
rate vanishes with the logarithmic depth selector. -/
theorem logarithmicPoissonDepthStationaryRate_tendsto_zero
    {alpha D : ℝ} (halpha : 0 ≤ alpha) (halpha1 : alpha < 1)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (posterior : ℕ → ι → ℝ) (hposterior : ∀ n, IsPMF (posterior n))
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    Filter.Tendsto
      (logarithmicPoissonDepthStationaryRate alpha D
        (fun n ↦ klDiv (posterior n) prior) delta)
      Filter.atTop (nhds 0) := by
  have hdepth := logarithmicPoissonDepth_tendsto_atTop
  have hpowBase : Filter.Tendsto (fun m : ℕ ↦ alpha ^ m)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one halpha halpha1
  have hpow : Filter.Tendsto
      (fun n ↦ alpha ^ logarithmicPoissonDepth n)
      Filter.atTop (nhds 0) := hpowBase.comp hdepth
  have hBclosed : Filter.Tendsto
      (fun n ↦ ((1 - alpha ^ logarithmicPoissonDepth n) /
        (1 - alpha)) * D)
      Filter.atTop (nhds (((1 - 0) / (1 - alpha)) * D)) :=
    ((tendsto_const_nhds.sub hpow).div_const (1 - alpha)).mul_const D
  have hB : Filter.Tendsto
      (fun n ↦ finiteDepthPoissonSpanBound alpha D
        (logarithmicPoissonDepth n))
      Filter.atTop (nhds (((1 - 0) / (1 - alpha)) * D)) := by
    convert hBclosed using 1
    funext n
    rw [finiteDepthPoissonSpanBound_closed halpha1]
    rfl
  have hscale : Filter.Tendsto
      (fun n ↦ finiteDepthPoissonScaleBound alpha D
        (logarithmicPoissonDepth n))
      Filter.atTop
        (nhds (1 + 2 * (((1 - 0) / (1 - alpha)) * D))) := by
    unfold finiteDepthPoissonScaleBound
    exact tendsto_const_nhds.add (hB.const_mul 2)
  have htrajectory :=
    logarithmicPoissonDepthTrajectoryRate_tendsto_zero
      hprior posterior hposterior hdelta hdelta1
  have hscaled : Filter.Tendsto
      (fun n ↦ finiteDepthPoissonScaleBound alpha D
          (logarithmicPoissonDepth n) *
        logarithmicPoissonDepthTrajectoryRate
          (fun n ↦ klDiv (posterior n) prior) delta n)
      Filter.atTop (nhds 0) := by
    simpa using hscale.mul htrajectory
  have hendpoint : Filter.Tendsto
      (fun n ↦ finiteDepthPoissonSpanBound alpha D
          (logarithmicPoissonDepth n) / (n : ℝ))
      Filter.atTop (nhds 0) :=
    hB.div_atTop tendsto_natCast_atTop_atTop
  have hresidual : Filter.Tendsto
      (fun n ↦ finiteDepthPoissonResidualBound alpha D
        (logarithmicPoissonDepth n))
      Filter.atTop (nhds 0) := by
    unfold finiteDepthPoissonResidualBound
    simpa using hpow.mul_const D
  have hsum := (hscaled.add hendpoint).add hresidual
  change Filter.Tendsto
    (fun n ↦ finiteDepthPoissonScaleBound alpha D
        (logarithmicPoissonDepth n) *
          logarithmicPoissonDepthTrajectoryRate
            (fun n ↦ klDiv (posterior n) prior) delta n +
        finiteDepthPoissonSpanBound alpha D
            (logarithmicPoissonDepth n) / (n : ℝ) +
          finiteDepthPoissonResidualBound alpha D
            (logarithmicPoissonDepth n))
    Filter.atTop (nhds 0)
  simpa only [zero_add] using hsum

omit [DecidableEq ι] [Nonempty ι] [MeasurableSingletonClass Z] in
/-- For every path and arbitrary time-varying posterior PMF, the full exact
selected stationary boundary tends to zero. -/
theorem stationaryPoissonDepthSelectionBoundary_logarithmic_tendsto_zero
    (P : Z → PMF Z) (stationary : PMF Z)
    {score : ι → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {alpha D : ℝ} (halpha : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hDnonneg : 0 ≤ D) (hcontract : IsOscillationContraction P alpha)
    (hD : ∀ i,
      finiteOscillation (centeredMarkovRowRisk P stationary (score i)) ≤ D)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (posterior : ℕ → ι → ℝ) (hposterior : ∀ n, IsPMF (posterior n))
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (x : ℕ → Z) :
    Filter.Tendsto
      (fun n ↦ stationaryPoissonDepthSelectionBoundary
        P stationary score alpha D prior (posterior n) delta
          (logarithmicPoissonDepth n) (geometricForwardTiltIndex n) n x)
      Filter.atTop (nhds 0) := by
  have hrate := logarithmicPoissonDepthStationaryRate_tendsto_zero
    (D := D) halpha halpha1 hprior posterior hposterior hdelta hdelta1
  apply squeeze_zero'
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    exact stationaryPoissonDepthSelectionBoundary_logarithmic_nonneg
      P stationary hscore halpha hDnonneg hcontract hD hprior
      (hposterior n) hdelta hdelta1 hn x
  · filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    exact stationaryPoissonDepthSelectionBoundary_logarithmic_le_rate
      P stationary hscore halpha hDnonneg hcontract hD hprior
      (hposterior n) hdelta hdelta1 hn x
  · exact hrate

/-- Capstone: one outer event supports the deterministic
`m(n) = floor(log_2 n)` depth, the all-time geometric tilt, arbitrary
path- and time-dependent finite posteriors, and a full exact stationary width
that converges to zero on every path. -/
theorem exists_stationaryPoissonDepthSelection_allTime_vanishing_event
    (P : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary) (x0 : Z)
    {score : ι → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {alpha D : ℝ} (halpha : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hDnonneg : 0 ≤ D) (hcontract : IsOscillationContraction P alpha)
    (hD : ∀ i,
      finiteOscillation (centeredMarkovRowRisk P stationary (score i)) ≤ D)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (posterior : (ℕ → Z) → ℕ → ι → ℝ)
    (hposterior : ∀ x n, IsPMF (posterior x n)) :
    ∃ goodEvent : Set (ℕ → Z),
      (markovPathMeasure P x0).real goodEventᶜ ≤ delta ∧
        (∀ x ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
          stationaryPosteriorMarkovRisk
              P stationary score (posterior x n) <
            empiricalTransitionPosteriorRisk score (posterior x n) n x +
              stationaryPoissonDepthSelectionBoundary
                P stationary score alpha D prior (posterior x n) delta
                  (logarithmicPoissonDepth n)
                  (geometricForwardTiltIndex n) n x) ∧
        (∀ x ∈ goodEvent,
          Filter.Tendsto
            (fun n ↦ stationaryPoissonDepthSelectionBoundary
              P stationary score alpha D prior (posterior x n) delta
                (logarithmicPoissonDepth n)
                (geometricForwardTiltIndex n) n x)
            Filter.atTop (nhds 0)) := by
  obtain ⟨goodEvent, hmass, hgood⟩ :=
    exists_stationaryPoissonDepthSelection_event
      P stationary hstationary x0 hscore halpha hDnonneg hcontract hD
      hprior hdelta
  refine ⟨goodEvent, hmass, ?_, ?_⟩
  · intro x hx n hn
    exact hgood x hx (logarithmicPoissonDepth n)
      (geometricForwardTiltIndex n) (posterior x n)
      (hposterior x n) n hn
  · intro x _hx
    exact stationaryPoissonDepthSelectionBoundary_logarithmic_tendsto_zero
      P stationary hscore halpha halpha1 hDnonneg hcontract hD
      hprior (posterior x) (hposterior x) hdelta hdelta1 x

end

end FormalSLT.StochasticDynamics
