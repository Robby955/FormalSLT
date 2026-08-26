/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.AnytimeValid.CountableEProcess
import FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes

/-!
# Countable forward empirical-Bernstein PAC-Bayes mixtures

This module replaces the finite outer tilt catalog in
`ContinuousForwardPredictableMeanBesselPACBayes` by a fixed `Nat`-indexed
catalog. The hypothesis space remains an arbitrary measurable space and the
posterior remains an arbitrary probability measure satisfying the continuous
Donsker--Varadhan hypotheses.

The outer series is a real `tsum`. Joint path--parameter measurability and the
`[0,1]` bounds give a common finite-time bound for every tilt component. That
bound discharges pointwise summability, adaptedness, integrability, and the
set-integral interchange needed by the countable e-process closure theorem.

The result permits post-path selection of one declared countable tilt atom and
one eligible posterior on a common event. It is not an all-real optimizer, a
posterior over strategies, or a computable selector.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayes.ContinuousChangeOfMeasure
open FormalSLT.PACBayes.TimeUniformContinuous
open scoped BigOperators ENNReal

namespace FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayesCountable

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

open FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes

variable {Theta Omega : Type*} [MeasurableSpace Theta]
  {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
  {F : Filtration Nat mOmega}

/-- The continuous hypothesis-prior component at one declared countable tilt. -/
def countableContinuousForwardPredictableMeanBesselTiltComponent
    (prior : Measure Theta) (X mean : Theta -> Nat -> Omega -> Real)
    (lam : Nat -> Real) (j : Nat) : Nat -> Omega -> Real :=
  continuousForwardPredictableMeanBesselPriorProcess
    prior X mean (lam j)

/-- Countable mixture of continuous hypothesis-prior tilt components. -/
def countableContinuousForwardPredictableMeanBesselMasterProcess
    (prior : Measure Theta) (weight : Nat -> Real)
    (X mean : Theta -> Nat -> Omega -> Real) (lam : Nat -> Real) :
    Nat -> Omega -> Real :=
  countableWeightedProcess weight
    (countableContinuousForwardPredictableMeanBesselTiltComponent
      prior X mean lam)

/-- Exact continuous-posterior boundary at one countable tilt atom. -/
def countableContinuousForwardPredictableMeanBesselBoundary
    (prior : Measure Theta) (weight lam : Nat -> Real)
    (X : Theta -> Nat -> Omega -> Real) (posterior : Measure Theta)
    (delta : Real) (j n : Nat) (omega : Omega) : Real :=
  ((InformationTheory.klDiv posterior prior).toReal +
      Real.log (1 / (delta * weight j)) +
      forwardEmpiricalBernsteinPsi (lam j) *
        continuousForwardPosteriorHybridBesselPenalty posterior X n omega) /
    ((n : Real) * lam j)

/-- One crossing event for every time, posterior, and countable tilt atom. -/
def countableContinuousForwardPredictableMeanBesselExceptionalEvent
    (prior : Measure Theta) (weight : Nat -> Real)
    (X mean : Theta -> Nat -> Omega -> Real) (lam : Nat -> Real)
    (delta : Real) : Set Omega :=
  atTopCrossingEvent
    (countableContinuousForwardPredictableMeanBesselMasterProcess
      prior weight X mean lam) (1 / delta)

/-- Every fixed countable tilt component is an e-process. -/
theorem countableContinuousForwardPredictableMeanBesselTiltComponent_eProcess
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X mean : Theta -> Nat -> Omega -> Real} {lam : Nat -> Real}
    (hlam : forall j, 0 <= lam j) (hlam_one : forall j, lam j < 1)
    (hX_adapted : forall theta, IncrementAdapted F (X theta))
    (hmean_adapted : forall theta, StronglyAdapted F (mean theta))
    (hX_unit : forall theta k omega, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean : forall theta k, mu[X theta k | F k] =ᵐ[mu] mean theta k)
    (hjoint_ambient : forall j n, StronglyMeasurable
      (fun q : Omega × Theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2) (mean q.2) (lam j) n q.1))
    (hjoint_filtered : forall j n,
      StronglyMeasurable[MeasurableSpace.prod (F n) inferInstance]
        (fun q : Omega × Theta =>
          forwardPredictableMeanEmpiricalBernsteinLowerProcess
            (X q.2) (mean q.2) (lam j) n q.1))
    (j : Nat) :
    EProcess mu F
      (countableContinuousForwardPredictableMeanBesselTiltComponent
        prior X mean lam j) := by
  unfold countableContinuousForwardPredictableMeanBesselTiltComponent
  exact continuousForwardPredictableMeanBesselPriorProcess_eProcess
    prior (hlam j) (hlam_one j) hX_adapted hmean_adapted
    hX_unit hmean_unit hmean (hjoint_ambient j) (hjoint_filtered j)

/-- Every continuous-prior component is nonnegative pointwise. -/
theorem countableContinuousForwardPredictableMeanBesselTiltComponent_nonneg
    (prior : Measure Theta)
    (X mean : Theta -> Nat -> Omega -> Real) (lam : Nat -> Real)
    (j n : Nat) (omega : Omega) :
    0 <= countableContinuousForwardPredictableMeanBesselTiltComponent
      prior X mean lam j n omega := by
  change 0 <= ∫ theta,
    forwardPredictableMeanEmpiricalBernsteinLowerProcess
      (X theta) (mean theta) (lam j) n omega ∂prior
  exact integral_nonneg fun theta => by
    rw [forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq]
    exact (Real.exp_pos _).le

set_option maxHeartbeats 1000000 in
/-- Every admissible continuous-prior component is bounded by `exp n`,
uniformly over the countable tilt catalog. -/
theorem countableContinuousForwardPredictableMeanBesselTiltComponent_le_exp_card
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X mean : Theta -> Nat -> Omega -> Real} {lam : Nat -> Real}
    (hlam : forall j, 0 <= lam j) (hlam_one : forall j, lam j < 1)
    (hX_unit : forall theta k omega, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hjoint_ambient : forall j n, StronglyMeasurable
      (fun q : Omega × Theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2) (mean q.2) (lam j) n q.1))
    (j n : Nat) (omega : Omega) :
    countableContinuousForwardPredictableMeanBesselTiltComponent
        prior X mean lam j n omega <=
      Real.exp (n : Real) := by
  have hsection : StronglyMeasurable (fun theta =>
      forwardPredictableMeanEmpiricalBernsteinLowerProcess
        (X theta) (mean theta) (lam j) n omega) :=
    (hjoint_ambient j n).comp_measurable
      (measurable_const.prodMk measurable_id)
  have hpoint : forall theta,
      forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X theta) (mean theta) (lam j) n omega <=
        Real.exp (n : Real) := by
    intro theta
    calc
      forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X theta) (mean theta) (lam j) n omega <=
          Real.exp (lam j * (n : Real)) :=
        forwardPredictableMeanEmpiricalBernsteinLowerProcess_le_exp_card
          (hlam j) (hlam_one j) (hX_unit theta) (hmean_unit theta) n omega
      _ <= Real.exp (n : Real) := by
        apply Real.exp_le_exp.mpr
        have hn : 0 <= (n : Real) := Nat.cast_nonneg n
        simpa using mul_le_mul_of_nonneg_right (hlam_one j).le hn
  have hint : Integrable (fun theta =>
      forwardPredictableMeanEmpiricalBernsteinLowerProcess
        (X theta) (mean theta) (lam j) n omega) prior := by
    refine Integrable.of_bound hsection.aestronglyMeasurable
      (Real.exp (n : Real)) ?_
    exact Filter.Eventually.of_forall fun theta => by
      rw [Real.norm_eq_abs, abs_of_pos (by
        rw [forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq]
        positivity)]
      exact hpoint theta
  unfold countableContinuousForwardPredictableMeanBesselTiltComponent
    continuousForwardPredictableMeanBesselPriorProcess
    continuousPriorMixtureProcess
  calc
    (∫ theta, forwardPredictableMeanEmpiricalBernsteinLowerProcess
        (X theta) (mean theta) (lam j) n omega ∂prior) <=
        ∫ _theta, Real.exp (n : Real) ∂prior :=
      integral_mono hint (integrable_const _) hpoint
    _ = Real.exp (n : Real) := by simp [integral_const]

/-- The countable outer series is summable at every time and path. -/
theorem countableContinuousForwardPredictableMeanBesselMasterProcess_pointwise_summable
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {weight : Nat -> Real} (hweight_nonneg : forall j, 0 <= weight j)
    (hweight_summable : Summable weight)
    {X mean : Theta -> Nat -> Omega -> Real} {lam : Nat -> Real}
    (hlam : forall j, 0 <= lam j) (hlam_one : forall j, lam j < 1)
    (hX_unit : forall theta k omega, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hjoint_ambient : forall j n, StronglyMeasurable
      (fun q : Omega × Theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2) (mean q.2) (lam j) n q.1))
    (n : Nat) (omega : Omega) :
    Summable fun j => weight j *
      countableContinuousForwardPredictableMeanBesselTiltComponent
        prior X mean lam j n omega := by
  have hbound : Summable fun j => weight j * Real.exp (n : Real) :=
    hweight_summable.mul_right _
  exact hbound.of_nonneg_of_le
    (fun j => mul_nonneg (hweight_nonneg j)
      (countableContinuousForwardPredictableMeanBesselTiltComponent_nonneg
        prior X mean lam j n omega))
    (fun j => mul_le_mul_of_nonneg_left
      (countableContinuousForwardPredictableMeanBesselTiltComponent_le_exp_card
        prior hlam hlam_one hX_unit hmean_unit hjoint_ambient j n omega)
      (hweight_nonneg j))

/-- Pointwise nonnegativity of the countable continuous master process. -/
theorem countableContinuousForwardPredictableMeanBesselMasterProcess_nonneg
    {weight : Nat -> Real} (hweight_nonneg : forall j, 0 <= weight j)
    (prior : Measure Theta) (X mean : Theta -> Nat -> Omega -> Real)
    (lam : Nat -> Real) :
    0 <= countableContinuousForwardPredictableMeanBesselMasterProcess
      prior weight X mean lam := by
  unfold countableContinuousForwardPredictableMeanBesselMasterProcess
  exact countableWeightedProcess_nonneg hweight_nonneg
    (countableContinuousForwardPredictableMeanBesselTiltComponent_nonneg
      prior X mean lam)

/-- The normalized countable master inherits the common `exp n` bound. -/
theorem countableContinuousForwardPredictableMeanBesselMasterProcess_le_exp_card
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {weight : Nat -> Real} (hweight_nonneg : forall j, 0 <= weight j)
    (hweight_sum_one : HasSum weight 1)
    {X mean : Theta -> Nat -> Omega -> Real} {lam : Nat -> Real}
    (hlam : forall j, 0 <= lam j) (hlam_one : forall j, lam j < 1)
    (hX_unit : forall theta k omega, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hjoint_ambient : forall j n, StronglyMeasurable
      (fun q : Omega × Theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2) (mean q.2) (lam j) n q.1))
    (n : Nat) (omega : Omega) :
    countableContinuousForwardPredictableMeanBesselMasterProcess
        prior weight X mean lam n omega <=
      Real.exp (n : Real) := by
  have hseries :=
    countableContinuousForwardPredictableMeanBesselMasterProcess_pointwise_summable
      prior hweight_nonneg hweight_sum_one.summable hlam hlam_one
      hX_unit hmean_unit hjoint_ambient n omega
  have hbound_series : Summable fun j => weight j * Real.exp (n : Real) :=
    hweight_sum_one.summable.mul_right _
  unfold countableContinuousForwardPredictableMeanBesselMasterProcess
    countableWeightedProcess
  calc
    (∑' j, weight j *
        countableContinuousForwardPredictableMeanBesselTiltComponent
          prior X mean lam j n omega) <=
        ∑' j, weight j * Real.exp (n : Real) :=
      hseries.tsum_le_tsum
        (fun j => mul_le_mul_of_nonneg_left
          (countableContinuousForwardPredictableMeanBesselTiltComponent_le_exp_card
            prior hlam hlam_one hX_unit hmean_unit hjoint_ambient j n omega)
          (hweight_nonneg j))
        hbound_series
    _ = Real.exp (n : Real) := by
      simpa using (hweight_sum_one.mul_right (Real.exp (n : Real))).tsum_eq

/-- The automatically summable countable master is strongly adapted. -/
theorem countableContinuousForwardPredictableMeanBesselMasterProcess_stronglyAdapted
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {weight : Nat -> Real} (hweight_nonneg : forall j, 0 <= weight j)
    (hweight_sum_one : HasSum weight 1)
    {X mean : Theta -> Nat -> Omega -> Real} {lam : Nat -> Real}
    (hlam : forall j, 0 <= lam j) (hlam_one : forall j, lam j < 1)
    (hX_adapted : forall theta, IncrementAdapted F (X theta))
    (hmean_adapted : forall theta, StronglyAdapted F (mean theta))
    (hX_unit : forall theta k omega, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean : forall theta k, mu[X theta k | F k] =ᵐ[mu] mean theta k)
    (hjoint_ambient : forall j n, StronglyMeasurable
      (fun q : Omega × Theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2) (mean q.2) (lam j) n q.1))
    (hjoint_filtered : forall j n,
      StronglyMeasurable[MeasurableSpace.prod (F n) inferInstance]
        (fun q : Omega × Theta =>
          forwardPredictableMeanEmpiricalBernsteinLowerProcess
            (X q.2) (mean q.2) (lam j) n q.1)) :
    StronglyAdapted F
      (countableContinuousForwardPredictableMeanBesselMasterProcess
        prior weight X mean lam) := by
  intro n
  unfold countableContinuousForwardPredictableMeanBesselMasterProcess
    countableWeightedProcess
  refine stronglyMeasurable_of_tendsto Filter.atTop
    (f := fun N omega => ∑ j ∈ Finset.range N,
      weight j *
        countableContinuousForwardPredictableMeanBesselTiltComponent
          prior X mean lam j n omega)
    (g := fun omega => ∑' j, weight j *
      countableContinuousForwardPredictableMeanBesselTiltComponent
        prior X mean lam j n omega) ?_ ?_
  · intro N
    have hsum := Finset.stronglyMeasurable_sum (Finset.range N)
      (fun j _ =>
        (((countableContinuousForwardPredictableMeanBesselTiltComponent_eProcess
          prior hlam hlam_one hX_adapted hmean_adapted hX_unit hmean_unit
          hmean hjoint_ambient hjoint_filtered j).supermartingale
            ).stronglyAdapted n).const_mul (weight j))
    convert hsum using 1
    ext omega
    simp only [Finset.sum_apply]
  · rw [tendsto_pi_nhds]
    intro omega
    exact
      (countableContinuousForwardPredictableMeanBesselMasterProcess_pointwise_summable
        prior hweight_nonneg hweight_sum_one.summable hlam hlam_one
        hX_unit hmean_unit hjoint_ambient n omega).hasSum.tendsto_sum_nat

/-- The bounded countable continuous master is integrable at every time. -/
theorem countableContinuousForwardPredictableMeanBesselMasterProcess_integrable
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {weight : Nat -> Real} (hweight_nonneg : forall j, 0 <= weight j)
    (hweight_sum_one : HasSum weight 1)
    {X mean : Theta -> Nat -> Omega -> Real} {lam : Nat -> Real}
    (hlam : forall j, 0 <= lam j) (hlam_one : forall j, lam j < 1)
    (hX_adapted : forall theta, IncrementAdapted F (X theta))
    (hmean_adapted : forall theta, StronglyAdapted F (mean theta))
    (hX_unit : forall theta k omega, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean : forall theta k, mu[X theta k | F k] =ᵐ[mu] mean theta k)
    (hjoint_ambient : forall j n, StronglyMeasurable
      (fun q : Omega × Theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2) (mean q.2) (lam j) n q.1))
    (hjoint_filtered : forall j n,
      StronglyMeasurable[MeasurableSpace.prod (F n) inferInstance]
        (fun q : Omega × Theta =>
          forwardPredictableMeanEmpiricalBernsteinLowerProcess
            (X q.2) (mean q.2) (lam j) n q.1))
    (n : Nat) :
    Integrable
      (countableContinuousForwardPredictableMeanBesselMasterProcess
        prior weight X mean lam n) mu := by
  have hadapted :=
    countableContinuousForwardPredictableMeanBesselMasterProcess_stronglyAdapted
      prior hweight_nonneg hweight_sum_one hlam hlam_one hX_adapted
      hmean_adapted hX_unit hmean_unit hmean hjoint_ambient hjoint_filtered
  refine Integrable.of_bound
    ((hadapted n).mono (F.le n)).aestronglyMeasurable
    (Real.exp (n : Real)) ?_
  exact Filter.Eventually.of_forall fun omega => by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (countableContinuousForwardPredictableMeanBesselMasterProcess_nonneg
        hweight_nonneg prior X mean lam n omega)]
    exact countableContinuousForwardPredictableMeanBesselMasterProcess_le_exp_card
      prior hweight_nonneg hweight_sum_one hlam hlam_one
      hX_unit hmean_unit hjoint_ambient n omega

/-- The component-wise set-integral norms are dominated by the normalized
weight sequence. -/
theorem countableContinuousForwardPredictableMeanBesselMasterProcess_integralNorm_summable
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {weight : Nat -> Real} (hweight_nonneg : forall j, 0 <= weight j)
    (hweight_sum_one : HasSum weight 1)
    {X mean : Theta -> Nat -> Omega -> Real} {lam : Nat -> Real}
    (hlam : forall j, 0 <= lam j) (hlam_one : forall j, lam j < 1)
    (hX_unit : forall theta k omega, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hjoint_ambient : forall j n, StronglyMeasurable
      (fun q : Omega × Theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2) (mean q.2) (lam j) n q.1))
    (n : Nat) (s : Set Omega) (_hs : MeasurableSet s) :
    Summable fun j => ∫ omega in s,
      ‖weight j *
        countableContinuousForwardPredictableMeanBesselTiltComponent
          prior X mean lam j n omega‖ ∂mu := by
  let C := Real.exp (n : Real)
  have hC : 0 <= C := (Real.exp_pos _).le
  have hdom : Summable fun j => weight j * C :=
    hweight_sum_one.summable.mul_right C
  refine hdom.of_nonneg_of_le
    (fun j => integral_nonneg fun _ => norm_nonneg _) ?_
  intro j
  have hconst_nonneg : 0 <= weight j * C :=
    mul_nonneg (hweight_nonneg j) hC
  have hnorm_bound : ∀ omega ∈ s,
      ‖weight j *
        countableContinuousForwardPredictableMeanBesselTiltComponent
          prior X mean lam j n omega‖ <= weight j * C := by
    intro omega _homega
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (hweight_nonneg j)
        (countableContinuousForwardPredictableMeanBesselTiltComponent_nonneg
          prior X mean lam j n omega))]
    exact mul_le_mul_of_nonneg_left
      (countableContinuousForwardPredictableMeanBesselTiltComponent_le_exp_card
        prior hlam hlam_one hX_unit hmean_unit hjoint_ambient j n omega)
      (hweight_nonneg j)
  have hset := norm_setIntegral_le_of_norm_le_const
    (μ := mu) (s := s)
    (f := fun omega => ‖weight j *
      countableContinuousForwardPredictableMeanBesselTiltComponent
        prior X mean lam j n omega‖)
    (measure_lt_top mu s) (fun omega homega => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hnorm_bound omega homega)
  have hint_nonneg : 0 <= ∫ omega in s,
      ‖weight j *
        countableContinuousForwardPredictableMeanBesselTiltComponent
          prior X mean lam j n omega‖ ∂mu :=
    integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hint_nonneg] at hset
  calc
    (∫ omega in s, ‖weight j *
        countableContinuousForwardPredictableMeanBesselTiltComponent
          prior X mean lam j n omega‖ ∂mu) <=
        (weight j * C) * mu.real s := hset
    _ <= (weight j * C) * 1 :=
      mul_le_mul_of_nonneg_left measureReal_le_one hconst_nonneg
    _ = weight j * C := mul_one _

/-- The nested countable prior--tilt series is one e-process. -/
theorem countableContinuousForwardPredictableMeanBesselMasterProcess_eProcess
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {weight : Nat -> Real} (hweight_nonneg : forall j, 0 <= weight j)
    (hweight_sum_one : HasSum weight 1)
    {X mean : Theta -> Nat -> Omega -> Real} {lam : Nat -> Real}
    (hlam : forall j, 0 <= lam j) (hlam_one : forall j, lam j < 1)
    (hX_adapted : forall theta, IncrementAdapted F (X theta))
    (hmean_adapted : forall theta, StronglyAdapted F (mean theta))
    (hX_unit : forall theta k omega, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean : forall theta k, mu[X theta k | F k] =ᵐ[mu] mean theta k)
    (hjoint_ambient : forall j n, StronglyMeasurable
      (fun q : Omega × Theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2) (mean q.2) (lam j) n q.1))
    (hjoint_filtered : forall j n,
      StronglyMeasurable[MeasurableSpace.prod (F n) inferInstance]
        (fun q : Omega × Theta =>
          forwardPredictableMeanEmpiricalBernsteinLowerProcess
            (X q.2) (mean q.2) (lam j) n q.1)) :
    EProcess mu F
      (countableContinuousForwardPredictableMeanBesselMasterProcess
        prior weight X mean lam) := by
  unfold countableContinuousForwardPredictableMeanBesselMasterProcess
  apply countableWeightedProcess_eProcess
    hweight_nonneg hweight_sum_one
  · intro j
    exact countableContinuousForwardPredictableMeanBesselTiltComponent_eProcess
      prior hlam hlam_one hX_adapted hmean_adapted hX_unit hmean_unit
      hmean hjoint_ambient hjoint_filtered j
  · exact
      countableContinuousForwardPredictableMeanBesselMasterProcess_stronglyAdapted
        prior hweight_nonneg hweight_sum_one hlam hlam_one hX_adapted
        hmean_adapted hX_unit hmean_unit hmean hjoint_ambient hjoint_filtered
  · exact
      countableContinuousForwardPredictableMeanBesselMasterProcess_integrable
        prior hweight_nonneg hweight_sum_one hlam hlam_one hX_adapted
        hmean_adapted hX_unit hmean_unit hmean hjoint_ambient hjoint_filtered
  · exact
      countableContinuousForwardPredictableMeanBesselMasterProcess_integralNorm_summable
        prior hweight_nonneg hweight_sum_one hlam hlam_one
        hX_unit hmean_unit hjoint_ambient

/-- Ville control for the single countable continuous-hypothesis master. -/
theorem countableContinuousForwardPredictableMeanBesselExceptionalEvent_mass_le_delta
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {weight : Nat -> Real} (hweight_nonneg : forall j, 0 <= weight j)
    (hweight_sum_one : HasSum weight 1)
    {X mean : Theta -> Nat -> Omega -> Real} {lam : Nat -> Real}
    {delta : Real} (hdelta : 0 < delta)
    (hlam : forall j, 0 <= lam j) (hlam_one : forall j, lam j < 1)
    (hX_adapted : forall theta, IncrementAdapted F (X theta))
    (hmean_adapted : forall theta, StronglyAdapted F (mean theta))
    (hX_unit : forall theta k omega, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean : forall theta k, mu[X theta k | F k] =ᵐ[mu] mean theta k)
    (hjoint_ambient : forall j n, StronglyMeasurable
      (fun q : Omega × Theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2) (mean q.2) (lam j) n q.1))
    (hjoint_filtered : forall j n,
      StronglyMeasurable[MeasurableSpace.prod (F n) inferInstance]
        (fun q : Omega × Theta =>
          forwardPredictableMeanEmpiricalBernsteinLowerProcess
            (X q.2) (mean q.2) (lam j) n q.1)) :
    mu.real
        (countableContinuousForwardPredictableMeanBesselExceptionalEvent
          prior weight X mean lam delta) <=
      delta := by
  have hE :=
    countableContinuousForwardPredictableMeanBesselMasterProcess_eProcess
      prior hweight_nonneg hweight_sum_one hlam hlam_one hX_adapted
      hmean_adapted hX_unit hmean_unit hmean hjoint_ambient hjoint_filtered
  have hville := ville_atTop_maximal_ineq
    (μ := mu) (𝒢 := F)
    (M := countableContinuousForwardPredictableMeanBesselMasterProcess
      prior weight X mean lam)
    hE.supermartingale hE.nonneg (one_div_pos.mpr hdelta)
  rw [hE.integral_start_eq_one] at hville
  unfold countableContinuousForwardPredictableMeanBesselExceptionalEvent
  calc
    mu.real
        (atTopCrossingEvent
          (countableContinuousForwardPredictableMeanBesselMasterProcess
            prior weight X mean lam)
          (1 / delta)) =
        delta * ((1 / delta) *
          mu.real
            (atTopCrossingEvent
              (countableContinuousForwardPredictableMeanBesselMasterProcess
                prior weight X mean lam)
              (1 / delta))) := by
      field_simp [hdelta.ne']
    _ <= delta * 1 := mul_le_mul_of_nonneg_left hville hdelta.le
    _ = delta := by ring

set_option maxHeartbeats 3000000 in
/-- A failure for one continuous posterior, time, and countable atom forces the
single countable master process into its crossing event. -/
theorem countableContinuousForwardPredictableMeanBessel_boundaryFailure_mem_exceptionalEvent
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {weight : Nat -> Real} (hweight_pos : forall j, 0 < weight j)
    (hweight_sum_one : HasSum weight 1)
    {X mean : Theta -> Nat -> Omega -> Real} {lam : Nat -> Real}
    {delta : Real} (hdelta : 0 < delta)
    (hlam : forall j, 0 < lam j) (hlam_one : forall j, lam j < 1)
    (hX_unit : forall theta k omega, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hX_parameter : forall k omega,
      StronglyMeasurable (fun theta => X theta k omega))
    (hmean_parameter : forall k omega,
      StronglyMeasurable (fun theta => mean theta k omega))
    (hjoint_ambient : forall j n, StronglyMeasurable
      (fun q : Omega × Theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2) (mean q.2) (lam j) n q.1))
    (posterior : Measure Theta) [IsProbabilityMeasure posterior]
    (hposterior_prior : posterior ≪ prior)
    (hllr : Integrable (llr posterior prior) posterior)
    {j n : Nat} {omega : Omega} (hn : 2 <= n)
    (hfail :
      countableContinuousForwardPredictableMeanBesselBoundary
          prior weight lam X posterior delta j n omega <=
        (∫ theta, forwardPrefixMean (fun k => mean theta k omega) n
          ∂posterior) -
        ∫ theta, forwardPrefixMean (fun k => X theta k omega) n
          ∂posterior) :
    omega ∈ countableContinuousForwardPredictableMeanBesselExceptionalEvent
      prior weight X mean lam delta := by
  have hnpos : 0 < n := by omega
  have hdenpos : 0 < (n : Real) * lam j :=
    mul_pos (Nat.cast_pos.mpr hnpos) (hlam j)
  unfold countableContinuousForwardPredictableMeanBesselBoundary at hfail
  have hfail_mul := (div_le_iff₀ hdenpos).mp hfail
  have hscore_identity :=
    integral_continuousForwardPredictableMeanBesselScore
      posterior X mean (lam j) hn omega
      (fun k => hX_parameter k omega)
      (fun k => hmean_parameter k omega)
      (fun theta k => hX_unit theta k omega)
      (fun theta k => hmean_unit theta k omega)
  have hbudget_le_score :
      (InformationTheory.klDiv posterior prior).toReal +
          Real.log (1 / (delta * weight j)) <=
        ∫ theta, continuousForwardPredictableMeanBesselScore
          X mean (lam j) theta n omega ∂posterior := by
    rw [hscore_identity]
    nlinarith
  have hscore_int := integrable_continuousForwardPredictableMeanBesselScore
    posterior X mean (lam j) hn omega
    (fun k => hX_parameter k omega)
    (fun k => hmean_parameter k omega)
    (fun theta k => hX_unit theta k omega)
    (fun theta k => hmean_unit theta k omega)
  have hexp_int :=
    integrable_exp_continuousForwardPredictableMeanBesselScore
      prior X mean (hlam j).le (hlam_one j) hn omega
      (fun k => hX_parameter k omega)
      (fun k => hmean_parameter k omega)
      (fun theta k => hX_unit theta k omega)
      (fun theta k => hmean_unit theta k omega)
  have hdv := continuous_donsker_varadhan
    posterior prior hposterior_prior
    (fun theta => continuousForwardPredictableMeanBesselScore
      X mean (lam j) theta n omega)
    hexp_int hscore_int hllr
  let moment : Real := ∫ theta, Real.exp
    (continuousForwardPredictableMeanBesselScore
      X mean (lam j) theta n omega) ∂prior
  have hmoment_pos : 0 < moment := by
    dsimp [moment]
    exact integral_exp_pos hexp_int
  have hlog_le : Real.log (1 / (delta * weight j)) <= Real.log moment := by
    change (∫ theta, continuousForwardPredictableMeanBesselScore
      X mean (lam j) theta n omega ∂posterior) <=
        (InformationTheory.klDiv posterior prior).toReal + Real.log moment at hdv
    linarith
  have hthreshold_pos : 0 < 1 / (delta * weight j) :=
    one_div_pos.mpr (mul_pos hdelta (hweight_pos j))
  have hthreshold_le_moment : 1 / (delta * weight j) <= moment :=
    (Real.log_le_log_iff hthreshold_pos hmoment_pos).mp hlog_le
  have hprocess_section : StronglyMeasurable (fun theta =>
      forwardPredictableMeanEmpiricalBernsteinLowerProcess
        (X theta) (mean theta) (lam j) n omega) :=
    (hjoint_ambient j n).comp_measurable
      (measurable_const.prodMk measurable_id)
  have hprocess_int : Integrable (fun theta =>
      forwardPredictableMeanEmpiricalBernsteinLowerProcess
        (X theta) (mean theta) (lam j) n omega) prior := by
    refine Integrable.of_bound hprocess_section.aestronglyMeasurable
      (Real.exp (lam j * (n : Real))) ?_
    exact Filter.Eventually.of_forall fun theta => by
      rw [Real.norm_eq_abs, abs_of_pos (by
        rw [forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq]
        positivity)]
      exact forwardPredictableMeanEmpiricalBernsteinLowerProcess_le_exp_card
        (hlam j).le (hlam_one j) (hX_unit theta) (hmean_unit theta) n omega
  have hmoment_le_inner : moment <=
      countableContinuousForwardPredictableMeanBesselTiltComponent
        prior X mean lam j n omega := by
    dsimp [moment, countableContinuousForwardPredictableMeanBesselTiltComponent,
      continuousForwardPredictableMeanBesselPriorProcess,
      continuousPriorMixtureProcess]
    apply integral_mono hexp_int hprocess_int
    intro theta
    change Real.exp (continuousForwardPredictableMeanBesselScore
        X mean (lam j) theta n omega) <=
      forwardPredictableMeanEmpiricalBernsteinLowerProcess
        (X theta) (mean theta) (lam j) n omega
    change forwardPredictableMeanEmpiricalBernsteinLowerBesselEnvelope
        (X theta) (mean theta) (lam j) n omega <=
      forwardPredictableMeanEmpiricalBernsteinLowerProcess
        (X theta) (mean theta) (lam j) n omega
    exact forwardPredictableMeanEmpiricalBernsteinLowerBesselEnvelope_le_process
      (hlam j).le (hlam_one j) hn omega
      (fun k hk => hX_unit theta k omega)
  have hinner : 1 / (delta * weight j) <=
      countableContinuousForwardPredictableMeanBesselTiltComponent
        prior X mean lam j n omega :=
    hthreshold_le_moment.trans hmoment_le_inner
  have hweighted :
      weight j * (1 / (delta * weight j)) <=
        weight j *
          countableContinuousForwardPredictableMeanBesselTiltComponent
            prior X mean lam j n omega :=
    mul_le_mul_of_nonneg_left hinner (hweight_pos j).le
  have hseries :=
    countableContinuousForwardPredictableMeanBesselMasterProcess_pointwise_summable
      prior (fun k => (hweight_pos k).le) hweight_sum_one.summable
      (fun k => (hlam k).le) hlam_one hX_unit hmean_unit
      hjoint_ambient n omega
  have hsingle :
      weight j *
          countableContinuousForwardPredictableMeanBesselTiltComponent
            prior X mean lam j n omega <=
        countableContinuousForwardPredictableMeanBesselMasterProcess
          prior weight X mean lam n omega := by
    unfold countableContinuousForwardPredictableMeanBesselMasterProcess
      countableWeightedProcess
    exact hseries.le_tsum j fun k _ =>
      mul_nonneg (hweight_pos k).le
        (countableContinuousForwardPredictableMeanBesselTiltComponent_nonneg
          prior X mean lam k n omega)
  rw [show weight j * (1 / (delta * weight j)) = 1 / delta by
    field_simp [hdelta.ne', (hweight_pos j).ne']] at hweighted
  unfold countableContinuousForwardPredictableMeanBesselExceptionalEvent
  exact ⟨n, hweighted.trans hsingle⟩

/-- Outside the common crossing event, the boundary holds simultaneously for
all countable atoms, all eligible continuous posteriors, and all `n >= 2`. -/
theorem countableContinuousForwardPredictableMeanBessel_allPosteriors_of_not_mem
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {weight : Nat -> Real} (hweight_pos : forall j, 0 < weight j)
    (hweight_sum_one : HasSum weight 1)
    {X mean : Theta -> Nat -> Omega -> Real} {lam : Nat -> Real}
    {delta : Real} (hdelta : 0 < delta)
    (hlam : forall j, 0 < lam j) (hlam_one : forall j, lam j < 1)
    (hX_unit : forall theta k omega, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hX_parameter : forall k omega,
      StronglyMeasurable (fun theta => X theta k omega))
    (hmean_parameter : forall k omega,
      StronglyMeasurable (fun theta => mean theta k omega))
    (hjoint_ambient : forall j n, StronglyMeasurable
      (fun q : Omega × Theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2) (mean q.2) (lam j) n q.1))
    {omega : Omega}
    (homega : omega ∉
      countableContinuousForwardPredictableMeanBesselExceptionalEvent
        prior weight X mean lam delta) :
    forall j : Nat, forall posterior : Measure Theta,
      IsProbabilityMeasure posterior -> posterior ≪ prior ->
      Integrable (llr posterior prior) posterior ->
      forall n : Nat, 2 <= n ->
        (∫ theta, forwardPrefixMean (fun k => mean theta k omega) n
          ∂posterior) <
        (∫ theta, forwardPrefixMean (fun k => X theta k omega) n
          ∂posterior) +
          countableContinuousForwardPredictableMeanBesselBoundary
            prior weight lam X posterior delta j n omega := by
  intro j posterior hposterior hposterior_prior hllr n hn
  letI : IsProbabilityMeasure posterior := hposterior
  apply lt_of_not_ge
  intro hfail
  apply homega
  exact
    countableContinuousForwardPredictableMeanBessel_boundaryFailure_mem_exceptionalEvent
      prior hweight_pos hweight_sum_one hdelta hlam hlam_one
      hX_unit hmean_unit hX_parameter hmean_parameter hjoint_ambient
      posterior hposterior_prior hllr hn (by linarith)

/-- A path- and time-dependent posterior and countable atom selector may be
substituted into the common event. Selector measurability is not required for
this pointwise statement. -/
theorem countableContinuousForwardPredictableMeanBessel_selected_of_not_mem
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {weight : Nat -> Real} (hweight_pos : forall j, 0 < weight j)
    (hweight_sum_one : HasSum weight 1)
    {X mean : Theta -> Nat -> Omega -> Real} {lam : Nat -> Real}
    {delta : Real} (hdelta : 0 < delta)
    (hlam : forall j, 0 < lam j) (hlam_one : forall j, lam j < 1)
    (hX_unit : forall theta k omega, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hX_parameter : forall k omega,
      StronglyMeasurable (fun theta => X theta k omega))
    (hmean_parameter : forall k omega,
      StronglyMeasurable (fun theta => mean theta k omega))
    (hjoint_ambient : forall j n, StronglyMeasurable
      (fun q : Omega × Theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2) (mean q.2) (lam j) n q.1))
    {omega : Omega}
    (homega : omega ∉
      countableContinuousForwardPredictableMeanBesselExceptionalEvent
        prior weight X mean lam delta)
    (posterior : Omega -> Nat -> Measure Theta)
    (hposterior : forall omega n,
      IsProbabilityMeasure (posterior omega n))
    (hposterior_prior : forall omega n, posterior omega n ≪ prior)
    (hllr : forall omega n,
      Integrable (llr (posterior omega n) prior) (posterior omega n))
    (select : Omega -> Nat -> Measure Theta -> Nat)
    (n : Nat) (hn : 2 <= n) :
    (∫ theta, forwardPrefixMean (fun k => mean theta k omega) n
      ∂posterior omega n) <
    (∫ theta, forwardPrefixMean (fun k => X theta k omega) n
      ∂posterior omega n) +
      countableContinuousForwardPredictableMeanBesselBoundary
        prior weight lam X (posterior omega n) delta
          (select omega n (posterior omega n)) n omega := by
  exact countableContinuousForwardPredictableMeanBessel_allPosteriors_of_not_mem
    prior hweight_pos hweight_sum_one hdelta hlam hlam_one
    hX_unit hmean_unit hX_parameter hmean_parameter hjoint_ambient homega
    (select omega n (posterior omega n)) (posterior omega n)
    (hposterior omega n) (hposterior_prior omega n) (hllr omega n) n hn

/-- One outer-probability event carries the countable-tilt,
continuous-hypothesis PAC-Bayes boundary simultaneously over time, eligible
posteriors, and declared atoms. -/
theorem exists_countableContinuousForwardPredictableMeanBesselPACBayes_event
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {weight : Nat -> Real} (hweight_pos : forall j, 0 < weight j)
    (hweight_sum_one : HasSum weight 1)
    {X mean : Theta -> Nat -> Omega -> Real} {lam : Nat -> Real}
    {delta : Real} (hdelta : 0 < delta)
    (hlam : forall j, 0 < lam j) (hlam_one : forall j, lam j < 1)
    (hX_adapted : forall theta, IncrementAdapted F (X theta))
    (hmean_adapted : forall theta, StronglyAdapted F (mean theta))
    (hX_unit : forall theta k omega, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean : forall theta k, mu[X theta k | F k] =ᵐ[mu] mean theta k)
    (hX_parameter : forall k omega,
      StronglyMeasurable (fun theta => X theta k omega))
    (hmean_parameter : forall k omega,
      StronglyMeasurable (fun theta => mean theta k omega))
    (hjoint_ambient : forall j n, StronglyMeasurable
      (fun q : Omega × Theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2) (mean q.2) (lam j) n q.1))
    (hjoint_filtered : forall j n,
      StronglyMeasurable[MeasurableSpace.prod (F n) inferInstance]
        (fun q : Omega × Theta =>
          forwardPredictableMeanEmpiricalBernsteinLowerProcess
            (X q.2) (mean q.2) (lam j) n q.1)) :
    ∃ goodEvent : Set Omega,
      mu.real goodEventᶜ <= delta ∧
        ∀ omega ∈ goodEvent, forall j : Nat,
          forall posterior : Measure Theta,
            IsProbabilityMeasure posterior -> posterior ≪ prior ->
            Integrable (llr posterior prior) posterior ->
            forall n : Nat, 2 <= n ->
              (∫ theta, forwardPrefixMean
                  (fun k => mean theta k omega) n ∂posterior) <
              (∫ theta, forwardPrefixMean
                  (fun k => X theta k omega) n ∂posterior) +
                countableContinuousForwardPredictableMeanBesselBoundary
                  prior weight lam X posterior delta j n omega := by
  let badEvent :=
    countableContinuousForwardPredictableMeanBesselExceptionalEvent
      prior weight X mean lam delta
  refine ⟨badEventᶜ, ?_, ?_⟩
  · simpa [badEvent] using
      (countableContinuousForwardPredictableMeanBesselExceptionalEvent_mass_le_delta
        prior (fun j => (hweight_pos j).le) hweight_sum_one hdelta
        (fun j => (hlam j).le) hlam_one hX_adapted hmean_adapted
        hX_unit hmean_unit hmean hjoint_ambient hjoint_filtered)
  · intro omega homega
    exact
      countableContinuousForwardPredictableMeanBessel_allPosteriors_of_not_mem
        prior hweight_pos hweight_sum_one hdelta hlam hlam_one
        hX_unit hmean_unit hX_parameter hmean_parameter hjoint_ambient homega

end

end FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayesCountable
