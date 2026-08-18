/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.StationaryPoissonDepthSelection
import FormalSLT.StochasticDynamics.StationaryPoissonRobustCandidate
import FormalSLT.StochasticDynamics.StationaryPoissonRobustInvariant
import FormalSLT.StochasticDynamics.EmpiricalTransitionConfidence

/-!
# Same-trajectory empirical stationary certificates from a declared catalog

This module closes the same-data selection loop for a finite, predeclared
catalog of candidate kernels.  Candidate `c` and truncation depth `m` receive
the declared risk confidence

`deltaRisk * candidateWeight c * (1 / ((m+1)(m+2)))`.

Inside each atom the existing countable geometric-tilt allocation is used.
The resulting risk event is therefore simultaneous over candidate, depth,
tilt, time, and finite-class posterior.  A separate transition-coordinate
event estimates a uniform row-total-variation budget from the same path.
Intersecting the two events costs `deltaRisk + deltaTransition`; no
independence or sample splitting is used.

The candidate kernels, reference PMFs, and their finite-depth potentials are
fixed before the risk event.  The theorem permits selection only by
substitution into this common catalog event.  It does not authorize an
arbitrary path-generated kernel or assert that the selected score is an
e-process.  The true invariant PMF remains a supplied assumption.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open scoped BigOperators ENNReal

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {C I Z Tau : Type*}
  [Fintype C] [DecidableEq C] [Nonempty C]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype Z] [Nonempty Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z]
  [Fintype Tau] [DecidableEq Tau]

/-! ## Declared candidate--depth score catalog -/

/-- Closed geometric span of candidate `c` at depth `m`. -/
def empiricalStationaryCatalogSpan
    (Q : C → Z → PMF Z) (D : C → ℝ) (c : C) (m : ℕ) : ℝ :=
  finiteDepthPoissonClosedSpanBound
    (finiteDobrushinCoefficient (Q c)) (D c) m

/-- Automatic depth-`m` potential constructed from declared candidate `c`. -/
def empiricalStationaryCatalogPotential
    (Q : C → Z → PMF Z) (reference : C → PMF Z)
    (score : I → MarkovTransitionScore Z)
    (c : C) (m : ℕ) : I → Z → ℝ :=
  fun i ↦ finiteDepthPoissonPotential (Q c) (reference c) (score i) m

/-- Unit-normalized corrected score fixed by candidate `c` and depth `m`. -/
def empiricalStationaryCatalogCorrectedScore
    (Q : C → Z → PMF Z) (reference : C → PMF Z)
    (score : I → MarkovTransitionScore Z) (D : C → ℝ)
    (c : C) (m : ℕ) : I → TrajectoryScore Z :=
  fun i ↦ poissonCorrectedTrajectoryScore
    (empiricalStationaryCatalogSpan Q D c m) (score i)
    (empiricalStationaryCatalogPotential Q reference score c m i)

/-- Exact misspecification-aware selected-candidate boundary.  The first line
is the observed
hybrid-Bessel/KL term at the jointly allocated candidate--depth--tilt atom;
the remaining lines are the endpoint, candidate contraction residual, and
empirical row-TV transfer terms. -/
def empiricalStationaryCatalogBoundary
    (Q : C → Z → PMF Z) (reference : C → PMF Z)
    (score : I → MarkovTransitionScore Z) (D : C → ℝ)
    (candidateWeight : C → ℝ) (prior posterior : I → ℝ)
    (deltaRisk eta : ℝ) (c : C) (m j n : ℕ) (x : ℕ → Z) : ℝ :=
  let alpha := finiteDobrushinCoefficient (Q c)
  let B := empiricalStationaryCatalogSpan Q D c m
  (1 + 2 * B) *
      trajectoryCountableEmpiricalBernsteinPACBayesBoundary
        prior
        (empiricalStationaryCatalogCorrectedScore
          Q reference score D c m)
        posterior
        (deltaRisk * candidateWeight c * polynomialForwardTiltWeight m)
        j n x +
    B / (n : ℝ) +
      alpha ^ m * D c + 2 * ((1 + B) * eta)

omit [Fintype C] [DecidableEq C] [Nonempty C]
  [DecidableEq I] [Nonempty I] [MeasurableSingletonClass Z] in
/-- The exact boundary exposes the candidate, depth, and countable-tilt
confidence allocation in its logarithmic term. -/
theorem empiricalStationaryCatalogBoundary_eq_explicit
    (Q : C → Z → PMF Z) (reference : C → PMF Z)
    (score : I → MarkovTransitionScore Z) (D : C → ℝ)
    (candidateWeight : C → ℝ) (prior posterior : I → ℝ)
    {deltaRisk eta : ℝ} (c : C) (m j n : ℕ) (x : ℕ → Z)
    (hallocated : deltaRisk * candidateWeight c *
        polynomialForwardTiltWeight m ≠ 0) :
    empiricalStationaryCatalogBoundary Q reference score D candidateWeight
        prior posterior deltaRisk eta c m j n x =
      let alpha := finiteDobrushinCoefficient (Q c)
      let B := empiricalStationaryCatalogSpan Q D c m
      (1 + 2 * B) *
          ((klDiv posterior prior +
              Real.log
                ((((j : ℝ) + 1) * ((j : ℝ) + 2)) /
                  (deltaRisk * candidateWeight c *
                    polynomialForwardTiltWeight m)) +
              forwardEmpiricalBernsteinPsi (geometricForwardTilt j) *
                trajectoryPosteriorHybridBesselPenalty posterior
                  (empiricalStationaryCatalogCorrectedScore
                    Q reference score D c m) n x) /
            ((n : ℝ) * geometricForwardTilt j)) +
        B / (n : ℝ) +
          alpha ^ m * D c + 2 * ((1 + B) * eta) := by
  unfold empiricalStationaryCatalogBoundary
  rw [trajectoryCountableEmpiricalBernsteinPACBayesBoundary_eq_explicit
    _ _ _ hallocated]

/-! ## Candidate and depth confidence allocation -/

/-- The already-countable geometric-tilt crossing event for candidate `c`
and depth `m`. -/
def empiricalStationaryCatalogDepthAtomExceptionalEvent
    (P : Z → PMF Z)
    (Q : C → Z → PMF Z) (reference : C → PMF Z)
    (score : I → MarkovTransitionScore Z) (D : C → ℝ)
    (candidateWeight : C → ℝ) (prior : I → ℝ)
    (deltaRisk : ℝ) (c : C) (m : ℕ) : Set (ℕ → Z) :=
  trajectoryCountableEmpiricalBernsteinPACBayesExceptionalEvent
    (prefixKernel P) prior
    (empiricalStationaryCatalogCorrectedScore Q reference score D c m)
    (deltaRisk * candidateWeight c * polynomialForwardTiltWeight m)

/-- Countable union over depths for one declared candidate. -/
def empiricalStationaryCatalogCandidateExceptionalEvent
    (P : Z → PMF Z)
    (Q : C → Z → PMF Z) (reference : C → PMF Z)
    (score : I → MarkovTransitionScore Z) (D : C → ℝ)
    (candidateWeight : C → ℝ) (prior : I → ℝ)
    (deltaRisk : ℝ) (c : C) : Set (ℕ → Z) :=
  ⋃ m : ℕ, empiricalStationaryCatalogDepthAtomExceptionalEvent
    P Q reference score D candidateWeight prior deltaRisk c m

/-- Finite candidate union around the countable depth and tilt allocations. -/
def empiricalStationaryCatalogExceptionalEvent
    (P : Z → PMF Z)
    (Q : C → Z → PMF Z) (reference : C → PMF Z)
    (score : I → MarkovTransitionScore Z) (D : C → ℝ)
    (candidateWeight : C → ℝ) (prior : I → ℝ)
    (deltaRisk : ℝ) : Set (ℕ → Z) :=
  ⋃ c : C, empiricalStationaryCatalogCandidateExceptionalEvent
    P Q reference score D candidateWeight prior deltaRisk c

omit [Fintype C] [DecidableEq C] [Nonempty C]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype Tau] [DecidableEq Tau] in
/-- Every predeclared candidate--depth corrected score is unit-valued. -/
theorem empiricalStationaryCatalogCorrectedScore_mem_Icc
    (Q : C → Z → PMF Z) (reference : C → PMF Z)
    {score : I → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {D : C → ℝ} (hDnonneg : ∀ c, 0 ≤ D c)
    (hcoefficient : ∀ c, finiteDobrushinCoefficient (Q c) < 1)
    (hD : ∀ c i, finiteOscillation
      (centeredMarkovRowRisk (Q c) (reference c) (score i)) ≤ D c)
    (c : C) (m : ℕ) :
    ∀ i n u y,
      empiricalStationaryCatalogCorrectedScore
        Q reference score D c m i n u y ∈ Set.Icc (0 : ℝ) 1 := by
  intro i n u y
  let alpha := finiteDobrushinCoefficient (Q c)
  let B := empiricalStationaryCatalogSpan Q D c m
  have halpha : 0 ≤ alpha := finiteDobrushinCoefficient_nonneg (Q c)
  have hcontract : IsOscillationContraction (Q c) alpha :=
    finiteDobrushinCoefficient_isOscillationContraction (Q c)
  have hB : 0 ≤ B := by
    rw [show B = finiteDepthPoissonSpanBound alpha (D c) m by
      dsimp [B, empiricalStationaryCatalogSpan, alpha]
      exact (finiteDepthPoissonSpanBound_closed (hcoefficient c) m).symm]
    exact finiteDepthPoissonSpanBound_nonneg halpha (hDnonneg c) m
  apply poissonCorrectedTransitionScore_mem_Icc hB (hscore i)
  intro x z
  change
    |finiteDepthPoissonPotential (Q c) (reference c) (score i) m z -
      finiteDepthPoissonPotential (Q c) (reference c) (score i) m x| ≤ B
  rw [show B = finiteDepthPoissonSpanBound alpha (D c) m by
    dsimp [B, empiricalStationaryCatalogSpan, alpha]
    exact (finiteDepthPoissonSpanBound_closed (hcoefficient c) m).symm]
  exact finiteDepthPoissonPotential_span
    (Q c) (reference c) (score i) m halpha hcontract (hD c i) x z

omit [DecidableEq C] [Nonempty C] [Nonempty I]
  [Fintype Tau] [DecidableEq Tau] in
/-- One candidate--depth atom costs exactly its declared outer budget. -/
theorem empiricalStationaryCatalogDepthAtomExceptionalEvent_mass_le
    (P : Z → PMF Z) (x0 : Z)
    (Q : C → Z → PMF Z) (reference : C → PMF Z)
    {score : I → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {D : C → ℝ} (hDnonneg : ∀ c, 0 ≤ D c)
    (hcoefficient : ∀ c, finiteDobrushinCoefficient (Q c) < 1)
    (hD : ∀ c i, finiteOscillation
      (centeredMarkovRowRisk (Q c) (reference c) (score i)) ≤ D c)
    {candidateWeight : C → ℝ}
    (hcandidateWeight : IsFullSupportPMF candidateWeight)
    {prior : I → ℝ} (hprior : IsFullSupportPMF prior)
    {deltaRisk : ℝ} (hdeltaRisk : 0 < deltaRisk)
    (c : C) (m : ℕ) :
    (markovPathMeasure P x0).real
        (empiricalStationaryCatalogDepthAtomExceptionalEvent
          P Q reference score D candidateWeight prior deltaRisk c m) ≤
      deltaRisk * candidateWeight c * polynomialForwardTiltWeight m := by
  have hcorrected := empiricalStationaryCatalogCorrectedScore_mem_Icc
    Q reference hscore hDnonneg hcoefficient hD c m
  have hmass :=
    trajectoryCountableEmpiricalBernsteinPACBayesExceptionalEvent_mass_le
      (prefixKernel P) x0 hcorrected hprior
      (mul_pos (mul_pos hdeltaRisk (hcandidateWeight.pos c))
        (polynomialForwardTiltWeight_pos m))
  simpa [empiricalStationaryCatalogDepthAtomExceptionalEvent,
    trajectoryMeasure_prefixKernel_eq_markovPathMeasure] using hmass

omit [DecidableEq C] [Nonempty C] [Nonempty I]
  [Fintype Tau] [DecidableEq Tau] in
/-- Countable depth allocation for one candidate costs
`deltaRisk * candidateWeight c`. -/
theorem empiricalStationaryCatalogCandidateExceptionalEvent_mass_le
    (P : Z → PMF Z) (x0 : Z)
    (Q : C → Z → PMF Z) (reference : C → PMF Z)
    {score : I → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {D : C → ℝ} (hDnonneg : ∀ c, 0 ≤ D c)
    (hcoefficient : ∀ c, finiteDobrushinCoefficient (Q c) < 1)
    (hD : ∀ c i, finiteOscillation
      (centeredMarkovRowRisk (Q c) (reference c) (score i)) ≤ D c)
    {candidateWeight : C → ℝ}
    (hcandidateWeight : IsFullSupportPMF candidateWeight)
    {prior : I → ℝ} (hprior : IsFullSupportPMF prior)
    {deltaRisk : ℝ} (hdeltaRisk : 0 < deltaRisk) (c : C) :
    (markovPathMeasure P x0).real
        (empiricalStationaryCatalogCandidateExceptionalEvent
          P Q reference score D candidateWeight prior deltaRisk c) ≤
      deltaRisk * candidateWeight c := by
  let mu := markovPathMeasure P x0
  let event : ℕ → Set (ℕ → Z) := fun m ↦
    empiricalStationaryCatalogDepthAtomExceptionalEvent
      P Q reference score D candidateWeight prior deltaRisk c m
  have hatomReal : ∀ m, mu.real (event m) ≤
      (deltaRisk * candidateWeight c) * polynomialForwardTiltWeight m := by
    intro m
    simpa [mul_assoc] using
      (empiricalStationaryCatalogDepthAtomExceptionalEvent_mass_le
        P x0 Q reference hscore hDnonneg hcoefficient hD
        hcandidateWeight hprior hdeltaRisk c m)
  have hatomENNReal : ∀ m, mu (event m) ≤
      ENNReal.ofReal
        ((deltaRisk * candidateWeight c) * polynomialForwardTiltWeight m) := by
    intro m
    calc
      mu (event m) = ENNReal.ofReal (mu.real (event m)) := by
        rw [ofReal_measureReal]
      _ ≤ ENNReal.ofReal
          ((deltaRisk * candidateWeight c) * polynomialForwardTiltWeight m) :=
        ENNReal.ofReal_le_ofReal (hatomReal m)
  have hallocated : HasSum
      (fun m ↦ (deltaRisk * candidateWeight c) *
        polynomialForwardTiltWeight m)
      (deltaRisk * candidateWeight c) := by
    simpa using polynomialForwardTiltWeight_hasSum.mul_left
      (deltaRisk * candidateWeight c)
  have hsummable := hallocated.summable
  have hnonneg : ∀ m, 0 ≤ (deltaRisk * candidateWeight c) *
      polynomialForwardTiltWeight m := fun m ↦
    mul_nonneg (mul_nonneg hdeltaRisk.le (hcandidateWeight.nonneg c))
      (polynomialForwardTiltWeight_pos m).le
  have hunionENNReal : mu (⋃ m, event m) ≤
      ENNReal.ofReal (deltaRisk * candidateWeight c) := by
    calc
      mu (⋃ m, event m) ≤ ∑' m, mu (event m) := measure_iUnion_le _
      _ ≤ ∑' m, ENNReal.ofReal
          ((deltaRisk * candidateWeight c) *
            polynomialForwardTiltWeight m) :=
        ENNReal.tsum_le_tsum hatomENNReal
      _ = ENNReal.ofReal (deltaRisk * candidateWeight c) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable,
          hallocated.tsum_eq]
  change mu.real (⋃ m, event m) ≤ deltaRisk * candidateWeight c
  calc
    mu.real (⋃ m, event m) ≤
        (ENNReal.ofReal (deltaRisk * candidateWeight c)).toReal := by
      exact ENNReal.toReal_mono (by simp) hunionENNReal
    _ = deltaRisk * candidateWeight c :=
      ENNReal.toReal_ofReal
        (mul_nonneg hdeltaRisk.le (hcandidateWeight.nonneg c))

omit [DecidableEq C] [Nonempty C] [Nonempty I]
  [Fintype Tau] [DecidableEq Tau] in
/-- The complete finite-candidate/countable-depth risk event costs at most
`deltaRisk`. -/
theorem empiricalStationaryCatalogExceptionalEvent_mass_le
    (P : Z → PMF Z) (x0 : Z)
    (Q : C → Z → PMF Z) (reference : C → PMF Z)
    {score : I → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {D : C → ℝ} (hDnonneg : ∀ c, 0 ≤ D c)
    (hcoefficient : ∀ c, finiteDobrushinCoefficient (Q c) < 1)
    (hD : ∀ c i, finiteOscillation
      (centeredMarkovRowRisk (Q c) (reference c) (score i)) ≤ D c)
    {candidateWeight : C → ℝ}
    (hcandidateWeight : IsFullSupportPMF candidateWeight)
    {prior : I → ℝ} (hprior : IsFullSupportPMF prior)
    {deltaRisk : ℝ} (hdeltaRisk : 0 < deltaRisk) :
    (markovPathMeasure P x0).real
        (empiricalStationaryCatalogExceptionalEvent
          P Q reference score D candidateWeight prior deltaRisk) ≤
      deltaRisk := by
  let mu := markovPathMeasure P x0
  let event : C → Set (ℕ → Z) := fun c ↦
    empiricalStationaryCatalogCandidateExceptionalEvent
      P Q reference score D candidateWeight prior deltaRisk c
  have hentryReal : ∀ c, mu.real (event c) ≤
      deltaRisk * candidateWeight c := by
    intro c
    exact empiricalStationaryCatalogCandidateExceptionalEvent_mass_le
      P x0 Q reference hscore hDnonneg hcoefficient hD
      hcandidateWeight hprior hdeltaRisk c
  have hentryENNReal : ∀ c, mu (event c) ≤
      ENNReal.ofReal (deltaRisk * candidateWeight c) := by
    intro c
    calc
      mu (event c) = ENNReal.ofReal (mu.real (event c)) := by
        rw [ofReal_measureReal]
      _ ≤ ENNReal.ofReal (deltaRisk * candidateWeight c) :=
        ENNReal.ofReal_le_ofReal (hentryReal c)
  have hunionENNReal : mu (⋃ c, event c) ≤ ENNReal.ofReal deltaRisk := by
    calc
      mu (⋃ c, event c) ≤ ∑' c, mu (event c) := measure_iUnion_le _
      _ ≤ ∑' c, ENNReal.ofReal (deltaRisk * candidateWeight c) :=
        ENNReal.tsum_le_tsum hentryENNReal
      _ = ∑ c, ENNReal.ofReal (deltaRisk * candidateWeight c) := by
        rw [tsum_fintype]
      _ = ENNReal.ofReal (∑ c, deltaRisk * candidateWeight c) := by
        symm
        exact ENNReal.ofReal_sum_of_nonneg
          (fun c _ ↦ mul_nonneg hdeltaRisk.le
            (hcandidateWeight.nonneg c))
      _ = ENNReal.ofReal deltaRisk := by
        congr 1
        rw [← Finset.mul_sum, hcandidateWeight.sum_one, mul_one]
  change mu.real (⋃ c, event c) ≤ deltaRisk
  calc
    mu.real (⋃ c, event c) ≤ (ENNReal.ofReal deltaRisk).toReal := by
      exact ENNReal.toReal_mono (by simp) hunionENNReal
    _ = deltaRisk := ENNReal.toReal_ofReal hdeltaRisk.le

/-! ## Candidate transfer outside the declared catalog event -/

omit [DecidableEq C] [Nonempty C] [DecidableEq I]
  [Fintype Tau] [DecidableEq Tau] in
/-- Outside the catalog event, any declared candidate and depth can be
combined with any certified row-TV budget `eta`. -/
theorem empiricalStationaryCatalog_allPosteriors_of_not_mem
    (P : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary)
    (Q : C → Z → PMF Z) (reference : C → PMF Z)
    {score : I → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {D : C → ℝ} (hDnonneg : ∀ c, 0 ≤ D c)
    (hcoefficient : ∀ c, finiteDobrushinCoefficient (Q c) < 1)
    (hD : ∀ c i, finiteOscillation
      (centeredMarkovRowRisk (Q c) (reference c) (score i)) ≤ D c)
    {candidateWeight : C → ℝ}
    (hcandidateWeight : IsFullSupportPMF candidateWeight)
    {prior : I → ℝ} (hprior : IsFullSupportPMF prior)
    {deltaRisk : ℝ} (hdeltaRisk : 0 < deltaRisk)
    {x : ℕ → Z}
    (hx : x ∉ empiricalStationaryCatalogExceptionalEvent
      P Q reference score D candidateWeight prior deltaRisk)
    (c : C) (m j : ℕ) {eta : ℝ} (heta : 0 ≤ eta)
    (hrowTV : ∀ z, finitePMFTotalVariation (P z) (Q c z) ≤ eta)
    (posterior : I → ℝ) (hposterior : IsPMF posterior)
    (n : ℕ) (hn : 2 ≤ n) :
    stationaryPosteriorMarkovRisk P stationary score posterior <
      empiricalTransitionPosteriorRisk score posterior n x +
        empiricalStationaryCatalogBoundary
          Q reference score D candidateWeight prior posterior
          deltaRisk eta c m j n x := by
  let alpha := finiteDobrushinCoefficient (Q c)
  let B := empiricalStationaryCatalogSpan Q D c m
  let potential := empiricalStationaryCatalogPotential
    Q reference score c m
  let residual := alpha ^ m * D c + 2 * ((1 + B) * eta)
  have halpha : 0 ≤ alpha := finiteDobrushinCoefficient_nonneg (Q c)
  have hcontract : IsOscillationContraction (Q c) alpha :=
    finiteDobrushinCoefficient_isOscillationContraction (Q c)
  have hB : 0 ≤ B := by
    rw [show B = finiteDepthPoissonSpanBound alpha (D c) m by
      dsimp [B, empiricalStationaryCatalogSpan, alpha]
      exact (finiteDepthPoissonSpanBound_closed (hcoefficient c) m).symm]
    exact finiteDepthPoissonSpanBound_nonneg halpha (hDnonneg c) m
  have hspan : ∀ i y z, |potential i z - potential i y| ≤ B := by
    intro i y z
    rw [show B = finiteDepthPoissonSpanBound alpha (D c) m by
      dsimp [B, empiricalStationaryCatalogSpan, alpha]
      exact (finiteDepthPoissonSpanBound_closed (hcoefficient c) m).symm]
    exact finiteDepthPoissonPotential_span
      (Q c) (reference c) (score i) m halpha hcontract (hD c i) y z
  have hresidual_nonneg : 0 ≤ residual := by
    dsimp [residual]
    exact add_nonneg (mul_nonneg (pow_nonneg halpha m) (hDnonneg c))
      (mul_nonneg (by norm_num) (mul_nonneg (by linarith) heta))
  have hresidual : ∀ i z,
      |approximatePoissonResidual P stationary (score i) (potential i) z| ≤
        residual := by
    intro i z
    have hrobust := abs_stationaryPoissonResidual_le_candidateOscillation
      P (Q c) stationary hstationary heta (hscore i) (hspan i) hrowTV z
    have hosc := finiteOscillation_markovPoissonDrift_finiteDepth_le
      (Q c) (reference c) (score i) m halpha hcontract (hD c i)
    exact hrobust.trans (add_le_add hosc (le_refl _))
  have hxCandidate : x ∉ empiricalStationaryCatalogCandidateExceptionalEvent
      P Q reference score D candidateWeight prior deltaRisk c := by
    intro hxc
    apply hx
    exact Set.mem_iUnion.mpr ⟨c, hxc⟩
  have hxDepth : x ∉ empiricalStationaryCatalogDepthAtomExceptionalEvent
      P Q reference score D candidateWeight prior deltaRisk c m := by
    intro hxm
    apply hxCandidate
    exact Set.mem_iUnion.mpr ⟨m, hxm⟩
  have hcorrected := empiricalStationaryCatalogCorrectedScore_mem_Icc
    Q reference hscore hDnonneg hcoefficient hD c m
  have hbase :=
    trajectoryCountableEmpiricalBernsteinPACBayes_allPosteriors_of_not_mem
      (prefixKernel P) hcorrected hprior
      (mul_pos (mul_pos hdeltaRisk (hcandidateWeight.pos c))
        (polynomialForwardTiltWeight_pos m))
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
          posterior
          (deltaRisk * candidateWeight c * polynomialForwardTiltWeight m)
          j n x at hbase
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
    (residualEnvelope := fun _i : I ↦ residual)
    (fun _i ↦ hresidual_nonneg) hresidual hposterior n hnpos x
  have hposteriorResidual :
      posteriorAverage posterior (fun _i : I ↦ residual) = residual := by
    unfold posteriorAverage
    rw [← Finset.sum_mul, hposterior.sum_one, one_mul]
  rw [hposteriorResidual] at hres
  dsimp only [empiricalStationaryCatalogBoundary,
    empiricalStationaryCatalogCorrectedScore,
    empiricalStationaryCatalogPotential, B, alpha, potential, residual]
    at hscaled hendpoint hres ⊢
  unfold empiricalStationaryCatalogCorrectedScore
    empiricalStationaryCatalogPotential
  linarith

/-! ## Same-data composition with empirical transition confidence -/

omit [DecidableEq C] [Nonempty C] in
/-- One event simultaneously supports the declared candidate--depth risk
catalog and the empirical all-row transition certificate.  Every displayed
candidate is predeclared; the row-coverage premise is explicit. -/
theorem exists_empiricalStationaryCatalog_event
    (P : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary) (x0 : Z)
    (Q : C → Z → PMF Z) (reference : C → PMF Z)
    {score : I → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {D : C → ℝ} (hDnonneg : ∀ c, 0 ≤ D c)
    (hcoefficient : ∀ c, finiteDobrushinCoefficient (Q c) < 1)
    (hD : ∀ c i, finiteOscillation
      (centeredMarkovRowRisk (Q c) (reference c) (score i)) ≤ D c)
    {candidateWeight : C → ℝ}
    (hcandidateWeight : IsFullSupportPMF candidateWeight)
    {prior : I → ℝ} (hprior : IsFullSupportPMF prior)
    {transitionPrior : TransitionCoordinate Z → ℝ}
    (htransitionPrior : IsFullSupportPMF transitionPrior)
    {transitionWeight : Tau → ℝ}
    (htransitionWeight : IsFullSupportPMF transitionWeight)
    {transitionLam : Tau → ℝ}
    (htransitionLam : ∀ k, 0 < transitionLam k)
    (htransitionLam_one : ∀ k, transitionLam k < 1)
    {deltaRisk deltaTransition : ℝ}
    (hdeltaRisk : 0 < deltaRisk)
    (hdeltaTransition : 0 < deltaTransition) :
    ∃ goodEvent : Set (ℕ → Z),
      (markovPathMeasure P x0).real goodEventᶜ ≤
          deltaRisk + deltaTransition ∧
        ∀ x ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
          (∀ z : Z, 0 < transitionVisitMass z n x) →
            ∀ c : C, ∀ m j : ℕ, ∀ k : Tau,
              ∀ posterior : I → ℝ, IsPMF posterior →
                let eta := empiricalCandidateKernelTVBudget
                  (Q c) transitionPrior transitionWeight transitionLam
                  deltaTransition k n x
                stationaryPosteriorMarkovRisk
                    P stationary score posterior <
                  empiricalTransitionPosteriorRisk score posterior n x +
                    empiricalStationaryCatalogBoundary
                      Q reference score D candidateWeight prior posterior
                      deltaRisk eta c m j n x ∧
                finiteDobrushinCoefficient P ≤
                  finiteDobrushinCoefficient (Q c) + 2 * eta ∧
                IsOscillationContraction P
                  (finiteDobrushinCoefficient (Q c) + 2 * eta) ∧
                (finiteDobrushinCoefficient (Q c) + 2 * eta < 1 →
                  ∀ stationaryOne stationaryTwo : PMF Z,
                    IsInvariantPMF P stationaryOne →
                    IsInvariantPMF P stationaryTwo →
                    stationaryOne = stationaryTwo) := by
  let riskBad := empiricalStationaryCatalogExceptionalEvent
    P Q reference score D candidateWeight prior deltaRisk
  have hriskMass : (markovPathMeasure P x0).real riskBad ≤ deltaRisk := by
    simpa [riskBad] using empiricalStationaryCatalogExceptionalEvent_mass_le
      P x0 Q reference hscore hDnonneg hcoefficient hD
      hcandidateWeight hprior hdeltaRisk
  rcases exists_empiricalCandidateKernelTV_event
      P x0 htransitionPrior htransitionWeight hdeltaTransition
      htransitionLam htransitionLam_one with
    ⟨transitionGood, htransitionMass, htransitionGood⟩
  let goodEvent := riskBadᶜ ∩ transitionGood
  refine ⟨goodEvent, ?_, ?_⟩
  · have hunion := measureReal_union_le
      (μ := markovPathMeasure P x0) riskBad transitionGoodᶜ
    calc
      (markovPathMeasure P x0).real goodEventᶜ =
          (markovPathMeasure P x0).real (riskBad ∪ transitionGoodᶜ) := by
        congr 1
        ext y
        by_cases hyrisk : y ∈ riskBad <;>
          by_cases hytransition : y ∈ transitionGood <;>
            simp [goodEvent, hyrisk, hytransition]
      _ ≤ (markovPathMeasure P x0).real riskBad +
          (markovPathMeasure P x0).real transitionGoodᶜ := hunion
      _ ≤ deltaRisk + deltaTransition :=
        add_le_add hriskMass htransitionMass
  · intro x hx n hn hvisit c m j k posterior hposterior
    have hxRisk : x ∉ riskBad := hx.1
    have hxTransition : x ∈ transitionGood := hx.2
    let eta := empiricalCandidateKernelTVBudget
      (Q c) transitionPrior transitionWeight transitionLam
      deltaTransition k n x
    have hrow : ∀ z,
        finitePMFTotalVariation (P z) (Q c z) ≤ eta :=
      htransitionGood x hxTransition k n hn hvisit (Q c)
    let z0 : Z := Classical.choice inferInstance
    have heta : 0 ≤ eta :=
      (finitePMFTotalVariation_nonneg (P z0) (Q c z0)).trans (hrow z0)
    have hrisk := empiricalStationaryCatalog_allPosteriors_of_not_mem
      P stationary hstationary Q reference hscore hDnonneg hcoefficient hD
      hcandidateWeight hprior hdeltaRisk hxRisk c m j heta hrow
      posterior hposterior n hn
    have hcoefficientP :=
      finiteDobrushinCoefficient_le_candidate_add_two_mul_rowTV
        P (Q c) hrow
    have hcontractionP :=
      candidateDobrushin_add_two_mul_rowTV_isOscillationContraction
        P (Q c) hrow
    refine ⟨hrisk, hcoefficientP, hcontractionP, ?_⟩
    intro hstrict stationaryOne stationaryTwo
      hstationaryOne hstationaryTwo
    exact invariantPMF_unique_of_candidate_rowTV
      P (Q c) hrow hstrict stationaryOne stationaryTwo
      hstationaryOne hstationaryTwo

omit [DecidableEq C] [Nonempty C] in
/-- Explicit substitution form.  Candidate, depth, both tilts, and posterior
may depend on the observed path and time because the preceding common event
already controls every catalog entry. -/
theorem exists_selectedEmpiricalStationaryCatalog_event
    (P : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary) (x0 : Z)
    (Q : C → Z → PMF Z) (reference : C → PMF Z)
    {score : I → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {D : C → ℝ} (hDnonneg : ∀ c, 0 ≤ D c)
    (hcoefficient : ∀ c, finiteDobrushinCoefficient (Q c) < 1)
    (hD : ∀ c i, finiteOscillation
      (centeredMarkovRowRisk (Q c) (reference c) (score i)) ≤ D c)
    {candidateWeight : C → ℝ}
    (hcandidateWeight : IsFullSupportPMF candidateWeight)
    {prior : I → ℝ} (hprior : IsFullSupportPMF prior)
    {transitionPrior : TransitionCoordinate Z → ℝ}
    (htransitionPrior : IsFullSupportPMF transitionPrior)
    {transitionWeight : Tau → ℝ}
    (htransitionWeight : IsFullSupportPMF transitionWeight)
    {transitionLam : Tau → ℝ}
    (htransitionLam : ∀ k, 0 < transitionLam k)
    (htransitionLam_one : ∀ k, transitionLam k < 1)
    {deltaRisk deltaTransition : ℝ}
    (hdeltaRisk : 0 < deltaRisk)
    (hdeltaTransition : 0 < deltaTransition)
    (selectCandidate : (ℕ → Z) → ℕ → C)
    (selectDepth selectRiskTilt : (ℕ → Z) → ℕ → ℕ)
    (selectTransitionTilt : (ℕ → Z) → ℕ → Tau)
    (selectPosterior : (ℕ → Z) → ℕ → I → ℝ)
    (hselectPosterior : ∀ x n, IsPMF (selectPosterior x n)) :
    ∃ goodEvent : Set (ℕ → Z),
      (markovPathMeasure P x0).real goodEventᶜ ≤
          deltaRisk + deltaTransition ∧
        ∀ x ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
          (∀ z : Z, 0 < transitionVisitMass z n x) →
            let c := selectCandidate x n
            let m := selectDepth x n
            let j := selectRiskTilt x n
            let k := selectTransitionTilt x n
            let posterior := selectPosterior x n
            let eta := empiricalCandidateKernelTVBudget
              (Q c) transitionPrior transitionWeight transitionLam
              deltaTransition k n x
            stationaryPosteriorMarkovRisk P stationary score posterior <
                empiricalTransitionPosteriorRisk score posterior n x +
                  empiricalStationaryCatalogBoundary
                    Q reference score D candidateWeight prior posterior
                    deltaRisk eta c m j n x ∧
              finiteDobrushinCoefficient P ≤
                finiteDobrushinCoefficient (Q c) + 2 * eta ∧
              IsOscillationContraction P
                (finiteDobrushinCoefficient (Q c) + 2 * eta) ∧
              (finiteDobrushinCoefficient (Q c) + 2 * eta < 1 →
                ∀ stationaryOne stationaryTwo : PMF Z,
                  IsInvariantPMF P stationaryOne →
                  IsInvariantPMF P stationaryTwo →
                  stationaryOne = stationaryTwo) := by
  rcases exists_empiricalStationaryCatalog_event
      P stationary hstationary x0 Q reference hscore hDnonneg
      hcoefficient hD hcandidateWeight hprior htransitionPrior
      htransitionWeight htransitionLam htransitionLam_one
      hdeltaRisk hdeltaTransition with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx n hn hvisit
  dsimp only
  have h := hgood x hx n hn hvisit
    (selectCandidate x n) (selectDepth x n) (selectRiskTilt x n)
    (selectTransitionTilt x n) (selectPosterior x n)
    (hselectPosterior x n)
  exact h

end

end FormalSLT.StochasticDynamics
