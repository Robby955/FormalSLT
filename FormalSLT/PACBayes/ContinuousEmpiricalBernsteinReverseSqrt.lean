/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.ContinuousJointMeanVarianceReverseCatalog
import FormalSLT.PACBayes.FiniteEmpiricalBernsteinReverseSqrt

/-!
# Closed-form continuous-posterior reverse empirical-Bernstein bounds

This module puts the existing dyadic empirical-Bernstein tilt catalog over a
general measurable hypothesis space.  One posterior-independent finite-horizon
event controls every prefix in the reverse epoch and every posterior that is
absolutely continuous with respect to the prior and has an integrable
log-likelihood ratio.  The endpoint has one measure-theoretic KL term and the
explicit constants `5/4` and `5/2`.

The observation space remains finite, the denominator is the fixed epoch floor
`m`, and the result is offline and finite-horizon.  This is not an all-time
confidence sequence, optional-stopping theorem, or continuous-observation
result.
-/

namespace FormalSLT.PACBayes.ContinuousEmpiricalBernsteinReverseSqrt

open Finset BigOperators MeasureTheory
open scoped ENNReal
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse
open FormalSLT.PACBayes.FiniteJointMeanVarianceMGF
open FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt
open FormalSLT.PACBayes.FiniteEmpiricalBernsteinReverseSqrt
open FormalSLT.PACBayes.ContinuousJointMeanVarianceReverse

noncomputable section

variable {Θ Z : Type*} [MeasurableSpace Θ] [MeasurableSpace Z]

/-- One posterior-independent bad event for the `J+1` dyadic tilts over a
continuous prior. -/
def continuousEmpiricalBernsteinReverseDyadicFailure
    [Fintype Z]
    (J N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (prior : Measure Θ) (ell : Θ → Z → ℝ)
    (delta : ℝ) : Set (Fin N → Z) :=
  continuousReverseJointMeanVarianceEpochCatalogBadPaths
    (finiteEmpiricalBernsteinDyadicWeight J) prior N hN m p ell
    (fun j : Fin (J + 1) ↦ finiteEmpiricalBernsteinTiltOfScale
      (finiteEmpiricalBernsteinDyadicScale j.1))
    (fun j : Fin (J + 1) ↦ finiteEmpiricalBernsteinEtaOfScale
      (finiteEmpiricalBernsteinDyadicScale j.1)) delta

/-- The continuous-prior dyadic catalog event has mass at most `delta`. -/
theorem continuousEmpiricalBernsteinReverseDyadicFailure_mass_le_delta
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    (J N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) :
    Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        (continuousEmpiricalBernsteinReverseDyadicFailure
          J N hN m p prior ell delta) ≤ ENNReal.ofReal delta := by
  apply continuousReverseJointMeanVarianceEpochCatalogBadPaths_mass_le_delta
    (finiteEmpiricalBernsteinDyadicWeight J)
    (finiteEmpiricalBernsteinDyadicWeight_isFullSupportPMF J)
    prior N m hN hm p hp ell hell_meas hell
  · intro j
    exact finiteEmpiricalBernsteinTiltOfScale_nonneg
      (finiteEmpiricalBernsteinDyadicScale_pos j.1).le
  · intro j
    exact finiteEmpiricalBernsteinEtaOfScale_nonneg
      (finiteEmpiricalBernsteinDyadicScale_pos j.1).le
  · intro j
    exact finiteJointMeanVarianceKappa_scale_nonneg hm.1
      (finiteEmpiricalBernsteinDyadicScale_pos j.1)
      (finiteEmpiricalBernsteinDyadicScale_le_two j.1)
  · exact hdelta

omit [MeasurableSpace Z] in
/-- The posterior integral of per-hypothesis Bessel empirical variance lies in
`[0, 1/2]`.  This is the posterior mean of the within-hypothesis variances, not
the empirical variance of a posterior-averaged loss. -/
theorem continuousPosterior_finiteEmpiricalVariance_mem_Icc
    [Fintype Z] {n : ℕ} (hn : 2 ≤ n)
    (ell : Θ → Z → ℝ) (S : Fin n → Z)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    (posterior : Measure Θ) [IsProbabilityMeasure posterior] :
    (∫ θ, finiteEmpiricalVariance ell θ S ∂posterior) ∈
      Set.Icc (0 : ℝ) (1 / 2 : ℝ) := by
  let V : Θ → ℝ := fun θ ↦ finiteEmpiricalVariance ell θ S
  have hVsm : StronglyMeasurable V :=
    stronglyMeasurable_finiteEmpiricalVariance_parameter ell S hell_meas
  have hV_nonneg (θ : Θ) : 0 ≤ V θ :=
    finiteEmpiricalVariance_nonneg hn ell θ S
  have hV_half (θ : Θ) : V θ ≤ (1 : ℝ) / 2 :=
    finiteEmpiricalVariance_le_half hn ell θ S (fun k ↦ hell θ (S k))
  have hVint : Integrable V posterior := by
    refine Integrable.of_bound hVsm.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun θ ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hV_nonneg θ)]
      linarith [hV_half θ]
  constructor
  · exact integral_nonneg hV_nonneg
  · calc
      (∫ θ, V θ ∂posterior) ≤ ∫ _θ, (1 : ℝ) / 2 ∂posterior :=
        integral_mono hVint (integrable_const ((1 : ℝ) / 2)) hV_half
      _ = (1 : ℝ) / 2 := by simp

omit [MeasurableSpace Z] in
/-- Square-root-plus-linear continuous-posterior bound for a finite dyadic
reverse-epoch catalog, assuming its final atom reaches the variance optimizer.
The same event works for every posterior satisfying the displayed absolute
continuity and finite-KL hypotheses. -/
theorem continuousEmpiricalBernsteinReverseDyadic_posteriorRisk_prefix_lt_sqrt_of_not_mem
    [Fintype Z]
    (J N m s : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m)
    (hms : m ≤ s) (hsN : s ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (prior posterior : Measure Θ)
    [IsProbabilityMeasure prior] [IsProbabilityMeasure posterior]
    (hposteriorPrior : posterior ≪ prior)
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta < 1)
    (x : Fin N → Z)
    (hx : x ∉ continuousEmpiricalBernsteinReverseDyadicFailure
      J N hN m p prior ell delta)
    (hllr : Integrable (llr posterior prior) posterior)
    (hcover :
      finiteEmpiricalBernsteinDyadicScale J ^ (2 : Nat) *
          (∫ θ, finiteEmpiricalVariance ell θ (samplePrefix hsN x)
            ∂posterior) ≤
        2 * (((InformationTheory.klDiv posterior prior).toReal +
          Real.log (((J : ℝ) + 1) / delta)) / (m : ℝ))) :
    (∫ θ, finitePopulationRisk p ell θ ∂posterior) <
      (∫ θ, finiteEmpiricalRisk ell θ (samplePrefix hsN x) ∂posterior) +
        (5 / 4 : ℝ) * Real.sqrt
          (2 * (∫ θ, finiteEmpiricalVariance ell θ (samplePrefix hsN x)
            ∂posterior) *
            ((InformationTheory.klDiv posterior prior).toReal +
              Real.log (((J : ℝ) + 1) / delta)) / (m : ℝ)) +
        (5 / 2 : ℝ) *
          ((InformationTheory.klDiv posterior prior).toReal +
            Real.log (((J : ℝ) + 1) / delta)) / (m : ℝ) := by
  let L := (InformationTheory.klDiv posterior prior).toReal +
    Real.log (((J : ℝ) + 1) / delta)
  let A := L / (m : ℝ)
  let V := ∫ θ, finiteEmpiricalVariance ell θ (samplePrefix hsN x) ∂posterior
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
  have hratio : 1 < ((J : ℝ) + 1) / delta := by
    rw [lt_div_iff₀ hdelta]
    have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
    have hJ : (1 : ℝ) ≤ (J : ℝ) + 1 := by linarith
    linarith
  have hL_pos : 0 < L := by
    dsimp [L]
    have hKL : 0 ≤ (InformationTheory.klDiv posterior prior).toReal :=
      ENNReal.toReal_nonneg
    have hlog := Real.log_pos hratio
    linarith
  have hA_pos : 0 < A := div_pos hL_pos hmR
  have hV_nonneg : 0 ≤ V := by
    dsimp [V]
    exact integral_nonneg fun θ ↦
      finiteEmpiricalVariance_nonneg (hm.trans hms) ell θ (samplePrefix hsN x)
  have hcover' : finiteEmpiricalBernsteinDyadicScale J ^ (2 : Nat) * V ≤
      2 * A := by simpa [A, V, L] using hcover
  obtain ⟨j, hj⟩ :=
    exists_dyadicScale_optimizer_bound J hA_pos hV_nonneg hcover'
  let scale : Fin (J + 1) → ℝ := fun c ↦
    finiteEmpiricalBernsteinDyadicScale c.1
  let tilt : Fin (J + 1) → ℝ := fun c ↦
    finiteEmpiricalBernsteinTiltOfScale (scale c)
  let varianceTilt : Fin (J + 1) → ℝ := fun c ↦
    finiteEmpiricalBernsteinEtaOfScale (scale c)
  have hlogweight :
      Real.log (1 / (delta * finiteEmpiricalBernsteinDyadicWeight J j)) =
        Real.log (((J : ℝ) + 1) / delta) := by
    congr 1
    unfold finiteEmpiricalBernsteinDyadicWeight
    field_simp [hdelta.ne']
  have hbase :=
    continuousReverseJointMeanVarianceEpochCatalog_posteriorRisk_prefix_lt_of_not_mem
      (finiteEmpiricalBernsteinDyadicWeight J)
      (finiteEmpiricalBernsteinDyadicWeight_isFullSupportPMF J)
      prior posterior hposteriorPrior N m s hN hm hms hsN p hp ell
      hell_meas hell tilt varianceTilt hdelta x
      (by simpa [continuousEmpiricalBernsteinReverseDyadicFailure, tilt,
        varianceTilt, scale] using hx)
      j
      (finiteEmpiricalBernsteinTiltOfScale_pos
        (finiteEmpiricalBernsteinDyadicScale_pos j.1))
      (finiteEmpiricalBernsteinEtaOfScale_nonneg
        (finiteEmpiricalBernsteinDyadicScale_pos j.1).le)
      (finiteJointMeanVarianceKappa_scale_nonneg hm
        (finiteEmpiricalBernsteinDyadicScale_pos j.1)
        (finiteEmpiricalBernsteinDyadicScale_le_two j.1))
      (finiteJointMeanVariance_balance_of_scale hm
        (finiteEmpiricalBernsteinDyadicScale_pos j.1)
        (finiteEmpiricalBernsteinDyadicScale_le_two j.1)) hllr
  rw [hlogweight] at hbase
  have hcomplexity :
      L / (finiteEmpiricalBernsteinTiltOfScale
          (finiteEmpiricalBernsteinDyadicScale j.1) * (m : ℝ)) =
        L / (finiteEmpiricalBernsteinDyadicScale j.1 * (m : ℝ)) +
          2 * L / (m : ℝ) := by
    unfold finiteEmpiricalBernsteinTiltOfScale
    field_simp [hmR.ne',
      (finiteEmpiricalBernsteinDyadicScale_pos j.1).ne']
  have hvariance :
      (finiteEmpiricalBernsteinEtaOfScale
          (finiteEmpiricalBernsteinDyadicScale j.1) /
        finiteEmpiricalBernsteinTiltOfScale
          (finiteEmpiricalBernsteinDyadicScale j.1)) * V =
        (finiteEmpiricalBernsteinDyadicScale j.1 / 2) * V := by
    rw [finiteEmpiricalBernsteinEta_div_tilt
      (finiteEmpiricalBernsteinDyadicScale_pos j.1)]
  change (∫ θ, finitePopulationRisk p ell θ ∂posterior) <
      (∫ θ, finiteEmpiricalRisk ell θ (samplePrefix hsN x) ∂posterior) +
        L / (finiteEmpiricalBernsteinTiltOfScale
          (finiteEmpiricalBernsteinDyadicScale j.1) * (m : ℝ)) +
        (finiteEmpiricalBernsteinEtaOfScale
          (finiteEmpiricalBernsteinDyadicScale j.1) /
          finiteEmpiricalBernsteinTiltOfScale
            (finiteEmpiricalBernsteinDyadicScale j.1)) * V at hbase
  rw [hcomplexity, hvariance] at hbase
  have hterm1 :
      L / (finiteEmpiricalBernsteinDyadicScale j.1 * (m : ℝ)) =
        A / finiteEmpiricalBernsteinDyadicScale j.1 := by
    dsimp [A]
    field_simp [hmR.ne',
      (finiteEmpiricalBernsteinDyadicScale_pos j.1).ne']
  have hterm2 : 2 * L / (m : ℝ) = 2 * A := by
    dsimp [A]
    ring
  rw [hterm1, hterm2] at hbase
  change (∫ θ, finitePopulationRisk p ell θ ∂posterior) <
      (∫ θ, finiteEmpiricalRisk ell θ (samplePrefix hsN x) ∂posterior) +
        (5 / 4 : ℝ) * Real.sqrt (2 * V * L / (m : ℝ)) +
        (5 / 2 : ℝ) * L / (m : ℝ)
  have hsimplify :
      A / finiteEmpiricalBernsteinDyadicScale j.1 + 2 * A +
          (finiteEmpiricalBernsteinDyadicScale j.1 / 2) * V ≤
        (5 / 4 : ℝ) * Real.sqrt (2 * V * L / (m : ℝ)) +
          (5 / 2 : ℝ) * L / (m : ℝ) := by
    have hsqrt : Real.sqrt (2 * A * V) =
        Real.sqrt (2 * V * L / (m : ℝ)) := by
      congr 1
      dsimp [A]
      ring
    calc
      A / finiteEmpiricalBernsteinDyadicScale j.1 + 2 * A +
            (finiteEmpiricalBernsteinDyadicScale j.1 / 2) * V ≤
          (5 / 4 : ℝ) * Real.sqrt (2 * A * V) + A / 2 + 2 * A := by
        nlinarith [hj]
      _ = (5 / 4 : ℝ) * Real.sqrt (2 * V * L / (m : ℝ)) +
            (5 / 2 : ℝ) * L / (m : ℝ) := by
        rw [hsqrt]
        dsimp [A]
        ring
  linarith

/-! ## Canonical logarithmic grid -/

/-- The canonical dyadic reverse-epoch event over a continuous prior. -/
def continuousEmpiricalBernsteinReverseSqrtFailure
    [Fintype Z]
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (prior : Measure Θ) (ell : Θ → Z → ℝ)
    (delta : ℝ) : Set (Fin N → Z) :=
  continuousEmpiricalBernsteinReverseDyadicFailure
    (finiteEmpiricalBernsteinGridDepth m) N hN m p prior ell delta

/-- The canonical continuous-prior reverse empirical-Bernstein event has mass
at most `delta`. -/
theorem continuousEmpiricalBernsteinReverseSqrtFailure_mass_le_delta
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) :
    Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        (continuousEmpiricalBernsteinReverseSqrtFailure
          N hN m p prior ell delta) ≤ ENNReal.ofReal delta := by
  simpa [continuousEmpiricalBernsteinReverseSqrtFailure] using
    (continuousEmpiricalBernsteinReverseDyadicFailure_mass_le_delta
      (finiteEmpiricalBernsteinGridDepth m) N m hN hm p hp prior ell
      hell_meas hell hdelta)

omit [MeasurableSpace Z] in
/-- The canonical epoch-floor grid reaches the variance optimizer for every
measurable posterior. -/
theorem continuousEmpiricalBernsteinReverseGridDepth_coverage
    [Fintype Z]
    {N m s : ℕ} (hm : 2 ≤ m) (hms : m ≤ s) (hsN : s ≤ N)
    (prior posterior : Measure Θ) [IsProbabilityMeasure posterior]
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta < 1)
    (x : Fin N → Z) :
    finiteEmpiricalBernsteinDyadicScale
          (finiteEmpiricalBernsteinGridDepth m) ^ (2 : Nat) *
        (∫ θ, finiteEmpiricalVariance ell θ (samplePrefix hsN x)
          ∂posterior) ≤
      2 * (((InformationTheory.klDiv posterior prior).toReal +
          Real.log
            ((((finiteEmpiricalBernsteinGridDepth m : ℕ) : ℝ) + 1) /
              delta)) / (m : ℝ)) := by
  let J := finiteEmpiricalBernsteinGridDepth m
  let V := ∫ θ, finiteEmpiricalVariance ell θ (samplePrefix hsN x) ∂posterior
  let L := (InformationTheory.klDiv posterior prior).toReal +
    Real.log (((J : ℝ) + 1) / delta)
  have hJpos : 0 < J := finiteEmpiricalBernsteinGridDepth_pos hm
  have hJoneR : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJpos
  have hratio : (2 : ℝ) ≤ ((J : ℝ) + 1) / delta := by
    rw [le_div_iff₀ hdelta]
    nlinarith
  have hloghalf : (1 : ℝ) / 2 ≤ Real.log (((J : ℝ) + 1) / delta) := by
    calc
      (1 : ℝ) / 2 = 1 - (2 : ℝ)⁻¹ := by norm_num
      _ ≤ Real.log 2 := Real.one_sub_inv_le_log_of_pos (by norm_num)
      _ ≤ Real.log (((J : ℝ) + 1) / delta) :=
        Real.log_le_log (by norm_num) hratio
  have hLhalf : (1 : ℝ) / 2 ≤ L := by
    dsimp [L]
    have hKL : 0 ≤ (InformationTheory.klDiv posterior prior).toReal :=
      ENNReal.toReal_nonneg
    linarith
  have hVmem := continuousPosterior_finiteEmpiricalVariance_mem_Icc
    (hm.trans hms) ell (samplePrefix hsN x) hell_meas hell posterior
  have hcover := finiteEmpiricalBernsteinGridDepth_coverage_of_half_le_complexity
    hm hVmem.1 hVmem.2 hLhalf
  simpa [J, V, L] using hcover

omit [MeasurableSpace Z] in
/-- Closed-form finite-horizon empirical-Bernstein PAC-Bayes bound on an
arbitrary measurable hypothesis space.  One prior-dependent event supports
every prefix in `[m,N]` and every finite-KL posterior selected after observing
the horizon path. -/
theorem continuousEmpiricalBernsteinReverseSqrt_posteriorRisk_prefix_lt_of_not_mem
    [Fintype Z]
    (N m s : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m)
    (hms : m ≤ s) (hsN : s ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (prior posterior : Measure Θ)
    [IsProbabilityMeasure prior] [IsProbabilityMeasure posterior]
    (hposteriorPrior : posterior ≪ prior)
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta < 1)
    (x : Fin N → Z)
    (hx : x ∉ continuousEmpiricalBernsteinReverseSqrtFailure
      N hN m p prior ell delta)
    (hllr : Integrable (llr posterior prior) posterior) :
    (∫ θ, finitePopulationRisk p ell θ ∂posterior) <
      (∫ θ, finiteEmpiricalRisk ell θ (samplePrefix hsN x) ∂posterior) +
        (5 / 4 : ℝ) * Real.sqrt
          (2 * (∫ θ, finiteEmpiricalVariance ell θ (samplePrefix hsN x)
            ∂posterior) *
            ((InformationTheory.klDiv posterior prior).toReal +
              Real.log
                ((((finiteEmpiricalBernsteinGridDepth m : ℕ) : ℝ) + 1) /
                  delta)) / (m : ℝ)) +
        (5 / 2 : ℝ) *
          ((InformationTheory.klDiv posterior prior).toReal +
            Real.log
              ((((finiteEmpiricalBernsteinGridDepth m : ℕ) : ℝ) + 1) /
                delta)) / (m : ℝ) := by
  simpa [continuousEmpiricalBernsteinReverseSqrtFailure] using
    (continuousEmpiricalBernsteinReverseDyadic_posteriorRisk_prefix_lt_sqrt_of_not_mem
      (finiteEmpiricalBernsteinGridDepth m) N m s hN hm hms hsN p hp
      prior posterior hposteriorPrior ell hell_meas hell hdelta hdelta_one x
      (by simpa [continuousEmpiricalBernsteinReverseSqrtFailure] using hx)
      hllr
      (continuousEmpiricalBernsteinReverseGridDepth_coverage
        hm hms hsN prior posterior ell hell_meas hell hdelta hdelta_one x))

end

end FormalSLT.PACBayes.ContinuousEmpiricalBernsteinReverseSqrt
