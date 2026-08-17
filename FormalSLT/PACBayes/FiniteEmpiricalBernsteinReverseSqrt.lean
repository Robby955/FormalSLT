/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteJointMeanVarianceReverseCatalog
import FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt

/-!
# Closed-form finite-horizon empirical-Bernstein PAC-Bayes bounds

This module specializes the joint reverse-epoch catalog to the existing
dyadic empirical-Bernstein scale family.  A predeclared logarithmic grid is
mixed before Doob's inequality.  On one finite-horizon event, every prefix in
the epoch and every finite post-sample posterior obey a square-root-plus-linear
bound with one KL term.

The denominator is the fixed epoch floor `m`, not the moving prefix size.  The
result is offline and finite-horizon; it is not a forward e-process, optional-
stopping theorem, or infinite-time confidence sequence.
-/

namespace FormalSLT.PACBayes.FiniteEmpiricalBernsteinReverseSqrt

open Finset BigOperators MeasureTheory
open scoped ENNReal
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse
open FormalSLT.PACBayes.FiniteJointMeanVarianceMGF
open FormalSLT.PACBayes.FiniteJointMeanVarianceReverse
open FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt

noncomputable section

variable {ι Z : Type*} [MeasurableSpace Z]

/-- Uniform dyadic catalog weights form a full-support PMF. -/
theorem finiteEmpiricalBernsteinDyadicWeight_isFullSupportPMF (J : ℕ) :
    IsFullSupportPMF (finiteEmpiricalBernsteinDyadicWeight J) := by
  constructor
  · constructor
    · intro j
      exact (finiteEmpiricalBernsteinDyadicWeight_pos J j).le
    · exact finiteEmpiricalBernsteinDyadicWeight_sum_eq_one J
  · exact finiteEmpiricalBernsteinDyadicWeight_pos J

/-- One exact all-prefix/all-posterior failure event for a `J+1` atom dyadic
reverse-epoch catalog. -/
def finiteEmpiricalBernsteinReverseDyadicFailure
    [Fintype Z] [Fintype ι]
    (J N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (delta : ℝ) : Set (Fin N → Z) :=
  reverseJointMeanVarianceEpochCatalogAnyPosteriorFailure
    (finiteEmpiricalBernsteinDyadicWeight J) prior N hN m p ell
    (fun j : Fin (J + 1) ↦ finiteEmpiricalBernsteinTiltOfScale
      (finiteEmpiricalBernsteinDyadicScale j.1))
    (fun j : Fin (J + 1) ↦ finiteEmpiricalBernsteinEtaOfScale
      (finiteEmpiricalBernsteinDyadicScale j.1)) delta

/-- The dyadic reverse-epoch failure event has mass at most `delta`. -/
theorem finiteEmpiricalBernsteinReverseDyadicFailure_mass_le_delta
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι]
    (J N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) :
    Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        (finiteEmpiricalBernsteinReverseDyadicFailure
          J N hN m p prior ell delta) ≤ ENNReal.ofReal delta := by
  apply reverseJointMeanVarianceEpochCatalogAnyPosteriorFailure_mass_le_delta
    N m hN hm p hp (finiteEmpiricalBernsteinDyadicWeight_isFullSupportPMF J)
      hprior ell hell
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

/-- Grid-depth coverage stated only through deterministic variance and
complexity bounds.  This separates the fixed endpoint denominator `m` from
the moving prefix sample size. -/
theorem finiteEmpiricalBernsteinGridDepth_coverage_of_half_le_complexity
    {m : ℕ} (hm : 2 ≤ m) {V L : ℝ}
    (hV0 : 0 ≤ V) (hVhalf : V ≤ (1 : ℝ) / 2)
    (hLhalf : (1 : ℝ) / 2 ≤ L) :
    finiteEmpiricalBernsteinDyadicScale
          (finiteEmpiricalBernsteinGridDepth m) ^ (2 : Nat) * V ≤
      2 * (L / (m : ℝ)) := by
  let J := finiteEmpiricalBernsteinGridDepth m
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hm)
  have hmR_two : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsle : finiteEmpiricalBernsteinDyadicScale J ≤ 2 / (m : ℝ) :=
    finiteEmpiricalBernsteinDyadicScale_gridDepth_le hm
  let y : ℝ := 2 / (m : ℝ)
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hy1 : y ≤ 1 := by
    dsimp [y]
    rw [div_le_one hmR]
    exact hmR_two
  have hscale_sq :
      finiteEmpiricalBernsteinDyadicScale J ^ (2 : Nat) ≤ y ^ (2 : Nat) :=
    (sq_le_sq₀ (finiteEmpiricalBernsteinDyadicScale_pos J).le hy0).mpr hsle
  have hleft :
      finiteEmpiricalBernsteinDyadicScale J ^ (2 : Nat) * V ≤
        y ^ (2 : Nat) * ((1 : ℝ) / 2) := by
    calc
      _ ≤ y ^ (2 : Nat) * V :=
        mul_le_mul_of_nonneg_right hscale_sq hV0
      _ ≤ y ^ (2 : Nat) * ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hVhalf (sq_nonneg y)
  have hysq : y ^ (2 : Nat) ≤ y := by
    nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1)]
  have hsmall : y ^ (2 : Nat) * ((1 : ℝ) / 2) ≤ 1 / (m : ℝ) := by
    calc
      _ ≤ y * ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hysq (by norm_num)
      _ = 1 / (m : ℝ) := by dsimp [y]; ring
  have hunit : 1 / (m : ℝ) ≤ 2 * (L / (m : ℝ)) := by
    calc
      _ ≤ (2 * L) / (m : ℝ) :=
        div_le_div_of_nonneg_right (by nlinarith) hmR.le
      _ = 2 * (L / (m : ℝ)) := by ring
  exact hleft.trans (hsmall.trans hunit)

omit [MeasurableSpace Z] in
/-- Square-root-plus-linear posterior bound for a finite dyadic reverse-epoch
catalog, assuming its final atom reaches the empirical-variance optimizer. -/
theorem finiteEmpiricalBernsteinReverseDyadic_posteriorRisk_prefix_lt_sqrt_of_not_mem
    [Fintype Z] [Fintype ι]
    (J N m s : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m)
    (hms : m ≤ s) (hsN : s ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (prior : ι → ℝ) (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta < 1)
    (x : Fin N → Z)
    (hx : x ∉ finiteEmpiricalBernsteinReverseDyadicFailure
      J N hN m p prior ell delta)
    {rho : ι → ℝ} (hrho : IsPMF rho)
    (hcover :
      finiteEmpiricalBernsteinDyadicScale J ^ (2 : Nat) *
          posteriorAverage rho (fun i ↦ finiteEmpiricalVariance ell i
            (samplePrefix hsN x)) ≤
        2 * ((klDiv rho prior + Real.log (((J : ℝ) + 1) / delta)) /
          (m : ℝ))) :
    posteriorAverage rho (finitePopulationRisk p ell) <
      posteriorAverage rho
          (fun i ↦ finiteEmpiricalRisk ell i (samplePrefix hsN x)) +
        (5 / 4 : ℝ) * Real.sqrt
          (2 * posteriorAverage rho
              (fun i ↦ finiteEmpiricalVariance ell i (samplePrefix hsN x)) *
            (klDiv rho prior + Real.log (((J : ℝ) + 1) / delta)) /
            (m : ℝ)) +
        (5 / 2 : ℝ) *
          (klDiv rho prior + Real.log (((J : ℝ) + 1) / delta)) /
            (m : ℝ) := by
  let L := klDiv rho prior + Real.log (((J : ℝ) + 1) / delta)
  let A := L / (m : ℝ)
  let V := posteriorAverage rho (fun i ↦ finiteEmpiricalVariance ell i
    (samplePrefix hsN x))
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
  have hratio : 1 < ((J : ℝ) + 1) / delta := by
    rw [lt_div_iff₀ hdelta]
    have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
    have hJ : (1 : ℝ) ≤ (J : ℝ) + 1 := by linarith
    linarith
  have hL_pos : 0 < L := by
    dsimp [L]
    have hKL : 0 ≤ klDiv rho prior := klDiv_nonneg hrho hprior
    have hlog := Real.log_pos hratio
    linarith
  have hA_pos : 0 < A := div_pos hL_pos hmR
  have hV_nonneg : 0 ≤ V := by
    unfold V posteriorAverage
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hrho.nonneg i)
      (finiteEmpiricalVariance_nonneg (hm.trans hms) ell i (samplePrefix hsN x))
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
    reverseJointMeanVarianceEpochCatalog_posteriorRisk_prefix_lt_of_not_mem
      N m s hN hm hms hsN p hp
      (finiteEmpiricalBernsteinDyadicWeight J) prior ell tilt varianceTilt x
      (by simpa [finiteEmpiricalBernsteinReverseDyadicFailure, tilt,
        varianceTilt, scale] using hx)
      j
      (finiteEmpiricalBernsteinTiltOfScale_pos
        (finiteEmpiricalBernsteinDyadicScale_pos j.1))
      (finiteJointMeanVariance_balance_of_scale hm
        (finiteEmpiricalBernsteinDyadicScale_pos j.1)
        (finiteEmpiricalBernsteinDyadicScale_le_two j.1)) hrho
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
  change posteriorAverage rho (finitePopulationRisk p ell) <
      posteriorAverage rho
          (fun i ↦ finiteEmpiricalRisk ell i (samplePrefix hsN x)) +
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
  change posteriorAverage rho (finitePopulationRisk p ell) <
      posteriorAverage rho
          (fun i ↦ finiteEmpiricalRisk ell i (samplePrefix hsN x)) +
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

/-- The single all-prefix/all-posterior failure event used by the canonical
reverse empirical-Bernstein theorem.  Its grid depth is fixed by the epoch
floor `m`, not by the moving prefix size. -/
def finiteEmpiricalBernsteinReverseSqrtFailure
    [Fintype Z] [Fintype ι]
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (delta : ℝ) : Set (Fin N → Z) :=
  finiteEmpiricalBernsteinReverseDyadicFailure
    (finiteEmpiricalBernsteinGridDepth m) N hN m p prior ell delta

/-- The canonical reverse empirical-Bernstein failure event has mass at most
`delta`. -/
theorem finiteEmpiricalBernsteinReverseSqrtFailure_mass_le_delta
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) :
    Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        (finiteEmpiricalBernsteinReverseSqrtFailure
          N hN m p prior ell delta) ≤ ENNReal.ofReal delta := by
  simpa [finiteEmpiricalBernsteinReverseSqrtFailure] using
    (finiteEmpiricalBernsteinReverseDyadicFailure_mass_le_delta
      (finiteEmpiricalBernsteinGridDepth m)
      N m hN hm p hp hprior ell hell hdelta)

omit [MeasurableSpace Z] in
/-- The canonical epoch-floor grid reaches the continuous optimizer for every
moving prefix and every posterior. -/
theorem finiteEmpiricalBernsteinReverseGridDepth_coverage
    [Fintype ι]
    {N m s : ℕ} (hm : 2 ≤ m) (hms : m ≤ s) (hsN : s ≤ N)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta < 1)
    (x : Fin N → Z)
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    finiteEmpiricalBernsteinDyadicScale
          (finiteEmpiricalBernsteinGridDepth m) ^ (2 : Nat) *
        posteriorAverage rho
          (fun i ↦ finiteEmpiricalVariance ell i (samplePrefix hsN x)) ≤
      2 *
        ((klDiv rho prior +
            Real.log
              ((((finiteEmpiricalBernsteinGridDepth m : ℕ) : ℝ) + 1) /
                delta)) /
          (m : ℝ)) := by
  let J := finiteEmpiricalBernsteinGridDepth m
  let V := posteriorAverage rho
    (fun i ↦ finiteEmpiricalVariance ell i (samplePrefix hsN x))
  let L := klDiv rho prior + Real.log (((J : ℝ) + 1) / delta)
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
    nlinarith [klDiv_nonneg hrho hprior]
  have hVmem := posteriorAverage_finiteEmpiricalVariance_mem_Icc
    (hm.trans hms) ell (samplePrefix hsN x) hell hrho
  have hcover := finiteEmpiricalBernsteinGridDepth_coverage_of_half_le_complexity
    hm hVmem.1 hVmem.2 hLhalf
  simpa [J, V, L] using hcover

omit [MeasurableSpace Z] in
/-- Closed-form finite-horizon empirical-Bernstein PAC-Bayes bound on the
canonical logarithmic grid.  One common event supports every prefix in
`[m, N]` and every finite posterior chosen after the full path is observed. -/
theorem finiteEmpiricalBernsteinReverseSqrt_posteriorRisk_prefix_lt_of_not_mem
    [Fintype Z] [Fintype ι]
    (N m s : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m)
    (hms : m ≤ s) (hsN : s ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta < 1)
    (x : Fin N → Z)
    (hx : x ∉ finiteEmpiricalBernsteinReverseSqrtFailure
      N hN m p prior ell delta)
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationRisk p ell) <
      posteriorAverage rho
          (fun i ↦ finiteEmpiricalRisk ell i (samplePrefix hsN x)) +
        (5 / 4 : ℝ) * Real.sqrt
          (2 * posteriorAverage rho
              (fun i ↦ finiteEmpiricalVariance ell i (samplePrefix hsN x)) *
            (klDiv rho prior +
              Real.log
                ((((finiteEmpiricalBernsteinGridDepth m : ℕ) : ℝ) + 1) /
                  delta)) /
            (m : ℝ)) +
        (5 / 2 : ℝ) *
          (klDiv rho prior +
            Real.log
              ((((finiteEmpiricalBernsteinGridDepth m : ℕ) : ℝ) + 1) /
                delta)) /
          (m : ℝ) := by
  simpa [finiteEmpiricalBernsteinReverseSqrtFailure] using
    (finiteEmpiricalBernsteinReverseDyadic_posteriorRisk_prefix_lt_sqrt_of_not_mem
      (finiteEmpiricalBernsteinGridDepth m) N m s hN hm hms hsN p hp
      prior hprior ell hdelta hdelta_one x
      (by simpa [finiteEmpiricalBernsteinReverseSqrtFailure] using hx)
      hrho
      (finiteEmpiricalBernsteinReverseGridDepth_coverage
        hm hms hsN hprior ell hell hdelta hdelta_one x hrho))

/-- **End-to-end finite-horizon closed-form empirical-Bernstein event.**

There is one measurable exceptional set of iid horizon paths with mass at most
`delta`.  Off it, the square-root-plus-linear bound holds simultaneously for
every prefix in `[m, N]` and every finite posterior chosen after the horizon
path.  The result is offline and finite-horizon, not optional stopping or an
infinite-time confidence sequence. -/
theorem exists_finiteEmpiricalBernsteinReverseSqrt_event
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta < 1) :
    ∃ E : Set (Fin N → Z),
      MeasurableSet E ∧
      Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure) E ≤
        ENNReal.ofReal delta ∧
      ∀ x, x ∉ E → ∀ s : ℕ, (hms : m ≤ s) → (hsN : s ≤ N) →
        ∀ rho : ι → ℝ, IsPMF rho →
          posteriorAverage rho (finitePopulationRisk p ell) <
            posteriorAverage rho
                (fun i ↦ finiteEmpiricalRisk ell i (samplePrefix hsN x)) +
              (5 / 4 : ℝ) * Real.sqrt
                (2 * posteriorAverage rho
                    (fun i ↦ finiteEmpiricalVariance ell i
                      (samplePrefix hsN x)) *
                  (klDiv rho prior +
                    Real.log
                      ((((finiteEmpiricalBernsteinGridDepth m : ℕ) : ℝ) + 1) /
                        delta)) /
                  (m : ℝ)) +
              (5 / 2 : ℝ) *
                (klDiv rho prior +
                  Real.log
                    ((((finiteEmpiricalBernsteinGridDepth m : ℕ) : ℝ) + 1) /
                      delta)) /
                (m : ℝ) := by
  let E := finiteEmpiricalBernsteinReverseSqrtFailure
    N hN m p prior ell delta
  refine ⟨E, (Set.toFinite E).measurableSet, ?_, ?_⟩
  · exact finiteEmpiricalBernsteinReverseSqrtFailure_mass_le_delta
      N m hN hm p hp hprior ell hell hdelta
  · intro x hx s hms hsN rho hrho
    exact finiteEmpiricalBernsteinReverseSqrt_posteriorRisk_prefix_lt_of_not_mem
      N m s hN hm.1 hms hsN p hp hprior ell hell hdelta hdelta_one x hx hrho

end

end FormalSLT.PACBayes.FiniteEmpiricalBernsteinReverseSqrt
