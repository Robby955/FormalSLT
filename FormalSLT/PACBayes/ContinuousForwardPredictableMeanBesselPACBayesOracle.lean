/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayesCountable
import FormalSLT.PACBayes.ForwardBesselPACBayesOracle

/-!
# Observable countable-tilt oracle for measurable hypotheses

This module lifts the growing geometric-prefix oracle from finite hypothesis
catalogs to arbitrary measurable hypothesis spaces. The exact selector may
depend on the observed path, reporting time, and an eligible posterior measure
because the underlying countable master event already controls every declared
tilt atom and posterior.

The selected exact boundary has an observable hybrid-Bessel LIL-order envelope.
For a time-varying posterior sequence, vanishing width is stated only when
`KL_n / 2^(geometricForwardTiltIndex n + 1)` tends to zero, asymptotically the
condition `KL_n = o(sqrt n)`. Arbitrary measurable-space posteriors do not have
the finite-prior KL ceiling used by the finite-hypothesis theorem.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open scoped BigOperators ENNReal Topology

namespace FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayesOracle

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

open FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes
open FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayesCountable
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open FormalSLT.PACBayes.ForwardBesselPACBayesOracle

variable {Theta Omega : Type*} [MeasurableSpace Theta]
  {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
  {F : Filtration Nat mOmega}

private theorem countableContinuousForwardPredictableMeanBesselFinitePrefix_exists_argmin
    (prior : Measure Theta) (weight lam : Nat -> Real)
    (X : Theta -> Nat -> Omega -> Real) (posterior : Measure Theta)
    (delta : Real) (maxIndex n : Nat) (omega : Omega) :
    ∃ j ∈ Finset.range (maxIndex + 1),
      ∀ j' ∈ Finset.range (maxIndex + 1),
        countableContinuousForwardPredictableMeanBesselBoundary
            prior weight lam X posterior delta j n omega <=
          countableContinuousForwardPredictableMeanBesselBoundary
            prior weight lam X posterior delta j' n omega := by
  exact (Finset.range (maxIndex + 1)).exists_min_image
    (fun j => countableContinuousForwardPredictableMeanBesselBoundary
      prior weight lam X posterior delta j n omega)
    (by simp)

/-- Exact minimizer of the continuous-posterior boundary over atoms
`0, ..., maxIndex`. -/
def countableContinuousForwardPredictableMeanBesselFinitePrefixArgmin
    (prior : Measure Theta) (weight lam : Nat -> Real)
    (X : Theta -> Nat -> Omega -> Real) (posterior : Measure Theta)
    (delta : Real) (maxIndex n : Nat) (omega : Omega) : Nat :=
  Classical.choose
    (countableContinuousForwardPredictableMeanBesselFinitePrefix_exists_argmin
      prior weight lam X posterior delta maxIndex n omega)

/-- The finite-prefix minimizer is one of the declared atoms. -/
theorem countableContinuousForwardPredictableMeanBesselFinitePrefixArgmin_mem
    (prior : Measure Theta) (weight lam : Nat -> Real)
    (X : Theta -> Nat -> Omega -> Real) (posterior : Measure Theta)
    (delta : Real) (maxIndex n : Nat) (omega : Omega) :
    countableContinuousForwardPredictableMeanBesselFinitePrefixArgmin
        prior weight lam X posterior delta maxIndex n omega ∈
      Finset.range (maxIndex + 1) := by
  exact
    (Classical.choose_spec
      (countableContinuousForwardPredictableMeanBesselFinitePrefix_exists_argmin
        prior weight lam X posterior delta maxIndex n omega)).1

/-- The selected boundary is no larger than any candidate in the prefix. -/
theorem countableContinuousForwardPredictableMeanBesselFinitePrefixArgmin_le
    (prior : Measure Theta) (weight lam : Nat -> Real)
    (X : Theta -> Nat -> Omega -> Real) (posterior : Measure Theta)
    (delta : Real) (maxIndex n : Nat) (omega : Omega) {j : Nat}
    (hj : j ∈ Finset.range (maxIndex + 1)) :
    countableContinuousForwardPredictableMeanBesselBoundary
        prior weight lam X posterior delta
          (countableContinuousForwardPredictableMeanBesselFinitePrefixArgmin
            prior weight lam X posterior delta maxIndex n omega)
          n omega <=
      countableContinuousForwardPredictableMeanBesselBoundary
        prior weight lam X posterior delta j n omega := by
  exact
    (Classical.choose_spec
      (countableContinuousForwardPredictableMeanBesselFinitePrefix_exists_argmin
        prior weight lam X posterior delta maxIndex n omega)).2 j hj

/-- KL plus confidence and polynomial atom-selection cost. -/
def continuousGeometricForwardBesselPACBayesComplexity
    (prior posterior : Measure Theta) (delta : Real) (j : Nat) : Real :=
  (InformationTheory.klDiv posterior prior).toReal +
    Real.log ((((j : Real) + 1) * ((j : Real) + 2)) / delta)

/-- Continuous-posterior geometric complexity is monotone in the atom index. -/
theorem continuousGeometricForwardBesselPACBayesComplexity_mono
    (prior posterior : Measure Theta) {delta : Real} (hdelta : 0 < delta)
    {j maxIndex : Nat} (hj : j <= maxIndex) :
    continuousGeometricForwardBesselPACBayesComplexity
        prior posterior delta j <=
      continuousGeometricForwardBesselPACBayesComplexity
        prior posterior delta maxIndex := by
  have hjR : (j : Real) <= (maxIndex : Real) := by exact_mod_cast hj
  have hprod :
      ((j : Real) + 1) * ((j : Real) + 2) <=
        ((maxIndex : Real) + 1) * ((maxIndex : Real) + 2) := by
    have hj0 : (0 : Real) <= j := Nat.cast_nonneg j
    nlinarith
  have hratioPos : 0 <
      (((j : Real) + 1) * ((j : Real) + 2)) / delta := by
    positivity
  have hratio :
      (((j : Real) + 1) * ((j : Real) + 2)) / delta <=
        (((maxIndex : Real) + 1) * ((maxIndex : Real) + 2)) / delta :=
    div_le_div_of_nonneg_right hprod hdelta.le
  unfold continuousGeometricForwardBesselPACBayesComplexity
  linarith [Real.log_le_log hratioPos hratio]

/-- Complexity at the largest atom in the reporting-time prefix. -/
def continuousGrowingPrefixForwardBesselPACBayesComplexity
    (prior posterior : Measure Theta) (delta : Real) (n : Nat) : Real :=
  continuousGeometricForwardBesselPACBayesComplexity prior posterior delta
    (growingPrefixForwardBesselPACBayesMaxIndex n)

/-- For `delta <= 1`, the largest-prefix continuous complexity is at least
one half. -/
theorem continuousGrowingPrefixForwardBesselPACBayesComplexity_half_le
    (prior posterior : Measure Theta) {delta : Real} (hdelta : 0 < delta)
    (hdelta1 : delta <= 1) (n : Nat) :
    1 / 2 <= continuousGrowingPrefixForwardBesselPACBayesComplexity
      prior posterior delta n := by
  let maxIndex := growingPrefixForwardBesselPACBayesMaxIndex n
  have hratio : (2 : Real) <=
      (((maxIndex : Real) + 1) * ((maxIndex : Real) + 2)) / delta := by
    apply (le_div_iff₀ hdelta).2
    have hindex0 : (0 : Real) <= maxIndex := Nat.cast_nonneg maxIndex
    nlinarith
  have hloghalf : (1 : Real) / 2 <=
      Real.log
        ((((maxIndex : Real) + 1) * ((maxIndex : Real) + 2)) / delta) := by
    calc
      (1 : Real) / 2 = 1 - (2 : Real)⁻¹ := by norm_num
      _ <= Real.log 2 := Real.one_sub_inv_le_log_of_pos (by norm_num)
      _ <= Real.log
          ((((maxIndex : Real) + 1) * ((maxIndex : Real) + 2)) / delta) :=
        Real.log_le_log (by norm_num) hratio
  unfold continuousGrowingPrefixForwardBesselPACBayesComplexity
    continuousGeometricForwardBesselPACBayesComplexity
  change 1 / 2 <= (InformationTheory.klDiv posterior prior).toReal +
    Real.log
      ((((maxIndex : Real) + 1) * ((maxIndex : Real) + 2)) / delta)
  nlinarith [(InformationTheory.klDiv posterior prior).toReal_nonneg]

/-- Exact iterated-logarithm form of the continuous growing-prefix
complexity. -/
theorem continuousGrowingPrefixForwardBesselPACBayesComplexity_eq_logLog
    (prior posterior : Measure Theta) (delta : Real)
    {n : Nat} (hn : 4 <= n) :
    continuousGrowingPrefixForwardBesselPACBayesComplexity
        prior posterior delta n =
      (InformationTheory.klDiv posterior prior).toReal +
        Real.log
          ((((Nat.log 4 n : Real) + 2) *
            ((Nat.log 4 n : Real) + 3)) / delta) := by
  have hbase := geometricForwardTiltIndex_add_one hn
  have hfirstNat :
      geometricForwardTiltIndex n + 2 + 1 = Nat.log 4 n + 2 := by
    omega
  have hsecondNat :
      geometricForwardTiltIndex n + 2 + 2 = Nat.log 4 n + 3 := by
    omega
  have hfirst :
      ((geometricForwardTiltIndex n + 2 : Nat) : Real) + 1 =
        (Nat.log 4 n : Real) + 2 := by
    exact_mod_cast hfirstNat
  have hsecond :
      ((geometricForwardTiltIndex n + 2 : Nat) : Real) + 2 =
        (Nat.log 4 n : Real) + 3 := by
    exact_mod_cast hsecondNat
  unfold continuousGrowingPrefixForwardBesselPACBayesComplexity
    continuousGeometricForwardBesselPACBayesComplexity
    growingPrefixForwardBesselPACBayesMaxIndex
  rw [hfirst, hsecond]

/-- Posterior-integrated hybrid-Bessel penalty lies in `[0,n]`. -/
theorem continuousForwardPosteriorHybridBesselPenalty_mem_Icc
    (posterior : Measure Theta) [IsProbabilityMeasure posterior]
    {X : Theta -> Nat -> Omega -> Real} {n : Nat} (hn : 2 <= n)
    (omega : Omega)
    (hX_parameter : forall k,
      StronglyMeasurable (fun theta => X theta k omega))
    (hX_unit : forall theta k, X theta k omega ∈ Set.Icc (0 : Real) 1) :
    continuousForwardPosteriorHybridBesselPenalty posterior X n omega ∈
      Set.Icc 0 (n : Real) := by
  have hint := integrable_forwardHybridBesselPenalty_parameter_of_unit
    posterior (fun theta k => X theta k omega) hn hX_parameter hX_unit
  have hpoint_nonneg : forall theta,
      0 <= forwardHybridBesselPenalty (fun k => X theta k omega) n :=
    fun theta =>
      ContinuousForwardPredictableMeanBesselPACBayes.forwardHybridBesselPenalty_nonneg_of_unit
        (fun k => X theta k omega) hn (fun k _hk => hX_unit theta k)
  have hpoint_le : forall theta,
      forwardHybridBesselPenalty (fun k => X theta k omega) n <=
        (n : Real) := by
    intro theta
    have hraw :=
      ContinuousForwardPredictableMeanBesselPACBayes.forwardHybridBesselPenalty_le_of_unit
        (fun k => X theta k omega) hn (fun k _hk => hX_unit theta k)
    have hnR : (2 : Real) <= (n : Real) := by exact_mod_cast hn
    nlinarith
  unfold continuousForwardPosteriorHybridBesselPenalty
  constructor
  · exact integral_nonneg hpoint_nonneg
  · calc
      (∫ theta, forwardHybridBesselPenalty
          (fun k => X theta k omega) n ∂posterior) <=
          ∫ _theta, (n : Real) ∂posterior :=
        integral_mono hint (integrable_const _) hpoint_le
      _ = (n : Real) := by simp [integral_const]

/-- Observable square-root envelope for the continuous posterior. -/
def continuousGrowingPrefixForwardBesselPACBayesLILEnvelope
    (prior : Measure Theta) (X : Theta -> Nat -> Omega -> Real)
    (posterior : Measure Theta) (delta : Real) (n : Nat)
    (omega : Omega) : Real :=
  let A := continuousGrowingPrefixForwardBesselPACBayesComplexity
    prior posterior delta n
  let Q := continuousForwardPosteriorHybridBesselPenalty posterior X n omega
  (2 * A + (5 / 2 : Real) * A * Real.sqrt (2 * Q / A)) / (n : Real)

/-- Observable selector over the growing geometric prefix. -/
def continuousGrowingPrefixForwardBesselPACBayesArgmin
    (prior : Measure Theta) (X : Theta -> Nat -> Omega -> Real)
    (posterior : Measure Theta) (delta : Real) (n : Nat)
    (omega : Omega) : Nat :=
  countableContinuousForwardPredictableMeanBesselFinitePrefixArgmin
    prior polynomialForwardTiltWeight geometricForwardTilt X posterior delta
      (growingPrefixForwardBesselPACBayesMaxIndex n) n omega

/-- The continuous growing-prefix selector belongs to its candidate prefix. -/
theorem continuousGrowingPrefixForwardBesselPACBayesArgmin_mem
    (prior : Measure Theta) (X : Theta -> Nat -> Omega -> Real)
    (posterior : Measure Theta) (delta : Real) (n : Nat)
    (omega : Omega) :
    continuousGrowingPrefixForwardBesselPACBayesArgmin
        prior X posterior delta n omega ∈
      Finset.range (growingPrefixForwardBesselPACBayesMaxIndex n + 1) := by
  exact countableContinuousForwardPredictableMeanBesselFinitePrefixArgmin_mem
    prior polynomialForwardTiltWeight geometricForwardTilt X posterior delta
      (growingPrefixForwardBesselPACBayesMaxIndex n) n omega

/-- The continuous selector improves on every atom in its prefix. -/
theorem continuousGrowingPrefixForwardBesselPACBayesArgmin_le
    (prior : Measure Theta) (X : Theta -> Nat -> Omega -> Real)
    (posterior : Measure Theta) (delta : Real) (n : Nat)
    (omega : Omega) {j : Nat}
    (hj : j ∈ Finset.range
      (growingPrefixForwardBesselPACBayesMaxIndex n + 1)) :
    countableContinuousForwardPredictableMeanBesselBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt X posterior
          delta (continuousGrowingPrefixForwardBesselPACBayesArgmin
            prior X posterior delta n omega) n omega <=
      countableContinuousForwardPredictableMeanBesselBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt X posterior
          delta j n omega := by
  exact countableContinuousForwardPredictableMeanBesselFinitePrefixArgmin_le
    prior polynomialForwardTiltWeight geometricForwardTilt X posterior delta
      (growingPrefixForwardBesselPACBayesMaxIndex n) n omega hj

/-- Quadratic observable rate for one continuous-posterior geometric atom. -/
theorem countableContinuousForwardPredictableMeanBesselBoundary_le_observableRate
    (prior : Measure Theta) (posterior : Measure Theta)
    [IsProbabilityMeasure posterior]
    {X : Theta -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta)
    (hX_parameter : forall k omega,
      StronglyMeasurable (fun theta => X theta k omega))
    (hX : forall theta k omega, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (j n : Nat) (hn : 2 <= n) (omega : Omega) :
    countableContinuousForwardPredictableMeanBesselBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt
          X posterior delta j n omega <=
      (continuousGeometricForwardBesselPACBayesComplexity
          prior posterior delta j * geometricForwardEffectiveScale j +
        2 * continuousForwardPosteriorHybridBesselPenalty posterior X n omega /
          geometricForwardEffectiveScale j) /
        (n : Real) := by
  have hnpos : 0 < n := by omega
  have hpenalty := continuousForwardPosteriorHybridBesselPenalty_mem_Icc
    posterior hn omega (fun k => hX_parameter k omega)
      (fun theta k => hX theta k omega)
  have hpsi := forwardEmpiricalBernsteinPsi_le_two_mul_sq
    (geometricForwardTilt_le_half j)
  have hvar :
      forwardEmpiricalBernsteinPsi (geometricForwardTilt j) *
          continuousForwardPosteriorHybridBesselPenalty posterior X n omega <=
        2 * (geometricForwardTilt j) ^ 2 *
          continuousForwardPosteriorHybridBesselPenalty posterior X n omega :=
    mul_le_mul_of_nonneg_right hpsi hpenalty.1
  have hdenpos : 0 < (n : Real) * geometricForwardTilt j :=
    mul_pos (Nat.cast_pos.mpr hnpos) (geometricForwardTilt_pos j)
  unfold countableContinuousForwardPredictableMeanBesselBoundary
    continuousGeometricForwardBesselPACBayesComplexity
    geometricForwardEffectiveScale
  rw [polynomialForwardTiltWeight_log_cost hdelta.ne' j]
  calc
    ((InformationTheory.klDiv posterior prior).toReal +
          Real.log ((((j : Real) + 1) * ((j : Real) + 2)) / delta) +
        forwardEmpiricalBernsteinPsi (geometricForwardTilt j) *
          continuousForwardPosteriorHybridBesselPenalty posterior X n omega) /
        ((n : Real) * geometricForwardTilt j) <=
      ((InformationTheory.klDiv posterior prior).toReal +
          Real.log ((((j : Real) + 1) * ((j : Real) + 2)) / delta) +
        2 * (geometricForwardTilt j) ^ 2 *
          continuousForwardPosteriorHybridBesselPenalty posterior X n omega) /
        ((n : Real) * geometricForwardTilt j) := by
      apply div_le_div_of_nonneg_right _ hdenpos.le
      linarith
    _ = (((InformationTheory.klDiv posterior prior).toReal +
            Real.log ((((j : Real) + 1) * ((j : Real) + 2)) / delta)) *
          (2 : Real) ^ (j + 1) +
        2 * continuousForwardPosteriorHybridBesselPenalty posterior X n omega /
          (2 : Real) ^ (j + 1)) /
        (n : Real) := by
      unfold geometricForwardTilt
      field_simp [show (n : Real) ≠ 0 by positivity]

/-- The exact continuous selector is bounded by the observable LIL-order
envelope. -/
theorem continuousGrowingPrefixForwardBesselPACBayesBoundary_le_LILEnvelope
    (prior : Measure Theta) (posterior : Measure Theta)
    [IsProbabilityMeasure posterior]
    {X : Theta -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta) (hdelta1 : delta <= 1)
    (hX_parameter : forall k omega,
      StronglyMeasurable (fun theta => X theta k omega))
    (hX : forall theta k omega, X theta k omega ∈ Set.Icc (0 : Real) 1)
    {n : Nat} (hn : 4 <= n) (omega : Omega) :
    countableContinuousForwardPredictableMeanBesselBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt X posterior
          delta (continuousGrowingPrefixForwardBesselPACBayesArgmin
            prior X posterior delta n omega) n omega <=
      continuousGrowingPrefixForwardBesselPACBayesLILEnvelope
        prior X posterior delta n omega := by
  let maxIndex := growingPrefixForwardBesselPACBayesMaxIndex n
  let A := continuousGrowingPrefixForwardBesselPACBayesComplexity
    prior posterior delta n
  let Q := continuousForwardPosteriorHybridBesselPenalty posterior X n omega
  have hAhalf : (1 : Real) / 2 <= A := by
    simpa [A] using
      continuousGrowingPrefixForwardBesselPACBayesComplexity_half_le
        prior posterior hdelta hdelta1 n
  have hQmem : Q ∈ Set.Icc 0 (n : Real) := by
    simpa [Q] using continuousForwardPosteriorHybridBesselPenalty_mem_Icc
      posterior (by omega) omega (fun k => hX_parameter k omega)
        (fun theta k => hX theta k omega)
  have hscale :
      4 * (n : Real) < geometricForwardEffectiveScale maxIndex ^ 2 := by
    simpa [maxIndex] using
      growingPrefixForwardBesselPACBayes_scale_sq_gt_four_mul hn
  have hcover :
      2 * Q < A * geometricForwardEffectiveScale maxIndex ^ 2 := by
    calc
      2 * Q <= 2 * (n : Real) :=
        mul_le_mul_of_nonneg_left hQmem.2 (by norm_num)
      _ < (1 / 2 : Real) *
          geometricForwardEffectiveScale maxIndex ^ 2 := by
        nlinarith
      _ <= A * geometricForwardEffectiveScale maxIndex ^ 2 :=
        mul_le_mul_of_nonneg_right hAhalf
          (sq_nonneg (geometricForwardEffectiveScale maxIndex))
  obtain ⟨j, hj, horacle⟩ :=
    exists_dyadic_quadratic_oracle hAhalf hQmem.1 hcover
  have hjle : j <= maxIndex := by
    have hjlt : j < maxIndex + 1 := by
      simpa only [Finset.mem_range] using hj
    omega
  have hAjA :
      continuousGeometricForwardBesselPACBayesComplexity
          prior posterior delta j <= A := by
    simpa [A, maxIndex, continuousGrowingPrefixForwardBesselPACBayesComplexity]
      using continuousGeometricForwardBesselPACBayesComplexity_mono
        prior posterior hdelta hjle
  have hselected :
      countableContinuousForwardPredictableMeanBesselBoundary
          prior polynomialForwardTiltWeight geometricForwardTilt X posterior
            delta (continuousGrowingPrefixForwardBesselPACBayesArgmin
              prior X posterior delta n omega) n omega <=
        (continuousGeometricForwardBesselPACBayesComplexity
              prior posterior delta j * geometricForwardEffectiveScale j +
            2 * Q / geometricForwardEffectiveScale j) /
          (n : Real) := by
    have hn2 : 2 <= n := le_trans (by norm_num) hn
    have hargmin := continuousGrowingPrefixForwardBesselPACBayesArgmin_le
      prior X posterior delta n omega (by simpa [maxIndex] using hj)
    have hobservable :=
      countableContinuousForwardPredictableMeanBesselBoundary_le_observableRate
        (Theta := Theta) (Omega := Omega) prior posterior hdelta
        hX_parameter hX j n hn2 omega
    exact hargmin.trans (by simpa [Q] using hobservable)
  have hscale0 : 0 <= geometricForwardEffectiveScale j :=
    (geometricForwardEffectiveScale_pos j).le
  have hcomplexityRate :
      (continuousGeometricForwardBesselPACBayesComplexity
            prior posterior delta j * geometricForwardEffectiveScale j +
          2 * Q / geometricForwardEffectiveScale j) /
        (n : Real) <=
      (A * geometricForwardEffectiveScale j +
          2 * Q / geometricForwardEffectiveScale j) /
        (n : Real) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    have hmul := mul_le_mul_of_nonneg_right hAjA hscale0
    linarith
  have horacleRate :
      (A * geometricForwardEffectiveScale j +
          2 * Q / geometricForwardEffectiveScale j) /
        (n : Real) <=
      (2 * A + (5 / 2 : Real) * A * Real.sqrt (2 * Q / A)) /
        (n : Real) :=
    div_le_div_of_nonneg_right horacle (Nat.cast_nonneg n)
  calc
    countableContinuousForwardPredictableMeanBesselBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt X posterior
          delta (continuousGrowingPrefixForwardBesselPACBayesArgmin
            prior X posterior delta n omega) n omega <=
      (continuousGeometricForwardBesselPACBayesComplexity
            prior posterior delta j * geometricForwardEffectiveScale j +
          2 * Q / geometricForwardEffectiveScale j) /
        (n : Real) := hselected
    _ <= (A * geometricForwardEffectiveScale j +
          2 * Q / geometricForwardEffectiveScale j) /
        (n : Real) := hcomplexityRate
    _ <= (2 * A + (5 / 2 : Real) * A * Real.sqrt (2 * Q / A)) /
        (n : Real) := horacleRate
    _ = continuousGrowingPrefixForwardBesselPACBayesLILEnvelope
        prior X posterior delta n omega := by
      simp [continuousGrowingPrefixForwardBesselPACBayesLILEnvelope, A, Q]

/-- At every horizon beyond atom `j`'s geometric scale, the exact continuous
boundary is controlled by the deterministic geometric rate. -/
theorem countableContinuousForwardPredictableMeanBesselBoundary_le_geometricRate
    (prior : Measure Theta) (posterior : Measure Theta)
    [IsProbabilityMeasure posterior]
    {X : Theta -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta) (hdelta1 : delta <= 1)
    (hX_parameter : forall k omega,
      StronglyMeasurable (fun theta => X theta k omega))
    (hX : forall theta k omega, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (j n : Nat) (hn : 2 <= n)
    (hfloor : geometricForwardTiltTime j <= n) (omega : Omega) :
    countableContinuousForwardPredictableMeanBesselBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt
          X posterior delta j n omega <=
      geometricPolynomialForwardRate
        (fun _ => (InformationTheory.klDiv posterior prior).toReal) delta j := by
  have hlam0 : 0 <= geometricForwardTilt j :=
    (geometricForwardTilt_pos j).le
  have hpenalty := continuousForwardPosteriorHybridBesselPenalty_mem_Icc
    posterior hn omega (fun k => hX_parameter k omega)
      (fun theta k => hX theta k omega)
  have hpsi := forwardEmpiricalBernsteinPsi_le_two_mul_sq
    (geometricForwardTilt_le_half j)
  have hvar :
      forwardEmpiricalBernsteinPsi (geometricForwardTilt j) *
          continuousForwardPosteriorHybridBesselPenalty posterior X n omega <=
        2 * (geometricForwardTilt j) ^ 2 * (n : Real) :=
    (mul_le_mul_of_nonneg_right hpsi hpenalty.1).trans
      (mul_le_mul_of_nonneg_left hpenalty.2 (by positivity))
  have hden : (2 : Real) ^ (j + 1) <=
      (n : Real) * geometricForwardTilt j := by
    have hcast : (geometricForwardTiltTime j : Real) <= (n : Real) := by
      exact_mod_cast hfloor
    calc
      (2 : Real) ^ (j + 1) =
          (geometricForwardTiltTime j : Real) * geometricForwardTilt j :=
        (geometricForwardTiltTime_mul_tilt j).symm
      _ <= (n : Real) * geometricForwardTilt j :=
        mul_le_mul_of_nonneg_right hcast hlam0
  have hcomplex0 : 0 <=
      (InformationTheory.klDiv posterior prior).toReal +
        Real.log ((((j : Real) + 1) * ((j : Real) + 2)) / delta) := by
    have hratio : 1 <=
        (((j : Real) + 1) * ((j : Real) + 2)) / delta := by
      apply (le_div_iff₀ hdelta).2
      have hj : (0 : Real) <= j := Nat.cast_nonneg j
      nlinarith
    exact add_nonneg (InformationTheory.klDiv posterior prior).toReal_nonneg
      (Real.log_nonneg hratio)
  have hnpos : 0 < n := by omega
  have hdenpos : 0 < (n : Real) * geometricForwardTilt j :=
    mul_pos (Nat.cast_pos.mpr hnpos) (geometricForwardTilt_pos j)
  have hpowpos : 0 < (2 : Real) ^ (j + 1) := by positivity
  unfold countableContinuousForwardPredictableMeanBesselBoundary
    geometricPolynomialForwardRate
  rw [polynomialForwardTiltWeight_log_cost hdelta.ne' j]
  have hcomplex :
      ((InformationTheory.klDiv posterior prior).toReal +
          Real.log ((((j : Real) + 1) * ((j : Real) + 2)) / delta)) /
          ((n : Real) * geometricForwardTilt j) <=
        ((InformationTheory.klDiv posterior prior).toReal +
          Real.log ((((j : Real) + 1) * ((j : Real) + 2)) / delta)) /
          (2 : Real) ^ (j + 1) :=
    div_le_div_of_nonneg_left hcomplex0 hpowpos hden
  calc
    ((InformationTheory.klDiv posterior prior).toReal +
        Real.log ((((j : Real) + 1) * ((j : Real) + 2)) / delta) +
        forwardEmpiricalBernsteinPsi (geometricForwardTilt j) *
          continuousForwardPosteriorHybridBesselPenalty posterior X n omega) /
        ((n : Real) * geometricForwardTilt j) =
      ((InformationTheory.klDiv posterior prior).toReal +
        Real.log ((((j : Real) + 1) * ((j : Real) + 2)) / delta)) /
          ((n : Real) * geometricForwardTilt j) +
        (forwardEmpiricalBernsteinPsi (geometricForwardTilt j) *
          continuousForwardPosteriorHybridBesselPenalty posterior X n omega) /
          ((n : Real) * geometricForwardTilt j) := by ring
    _ <= ((InformationTheory.klDiv posterior prior).toReal +
        Real.log ((((j : Real) + 1) * ((j : Real) + 2)) / delta)) /
          (2 : Real) ^ (j + 1) +
        (2 * (geometricForwardTilt j) ^ 2 * (n : Real)) /
          ((n : Real) * geometricForwardTilt j) :=
      add_le_add hcomplex (div_le_div_of_nonneg_right hvar hdenpos.le)
    _ = 2 * geometricForwardTilt j +
        ((InformationTheory.klDiv posterior prior).toReal +
          Real.log ((((j : Real) + 1) * ((j : Real) + 2)) / delta)) /
          (2 : Real) ^ (j + 1) := by
      field_simp [show (n : Real) ≠ 0 by positivity,
        (geometricForwardTilt_pos j).ne']
      ring

/-- The continuous exact boundary is nonnegative on unit-valued prefixes. -/
theorem countableContinuousForwardPredictableMeanBesselBoundary_nonneg
    (prior : Measure Theta) (posterior : Measure Theta)
    [IsProbabilityMeasure posterior]
    {X : Theta -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta) (hdelta1 : delta <= 1)
    (hX_parameter : forall k omega,
      StronglyMeasurable (fun theta => X theta k omega))
    (hX : forall theta k omega, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (j n : Nat) (hn : 2 <= n) (omega : Omega) :
    0 <= countableContinuousForwardPredictableMeanBesselBoundary
      prior polynomialForwardTiltWeight geometricForwardTilt
        X posterior delta j n omega := by
  have hpenalty := continuousForwardPosteriorHybridBesselPenalty_mem_Icc
    posterior hn omega (fun k => hX_parameter k omega)
      (fun theta k => hX theta k omega)
  have hpsi0 := forwardEmpiricalBernsteinPsi_nonneg
    (geometricForwardTilt_pos j).le (geometricForwardTilt_lt_one j)
  have hratio : 1 <=
      (((j : Real) + 1) * ((j : Real) + 2)) / delta := by
    apply (le_div_iff₀ hdelta).2
    have hj : (0 : Real) <= j := Nat.cast_nonneg j
    nlinarith
  unfold countableContinuousForwardPredictableMeanBesselBoundary
  rw [polynomialForwardTiltWeight_log_cost hdelta.ne' j]
  exact div_nonneg
    (add_nonneg
      (add_nonneg (InformationTheory.klDiv posterior prior).toReal_nonneg
        (Real.log_nonneg hratio))
      (mul_nonneg hpsi0 hpenalty.1))
    (mul_nonneg (Nat.cast_nonneg _) (geometricForwardTilt_pos j).le)

/-- The exact growing-prefix selector is bounded by the standard all-time
geometric rate because that atom remains in the candidate prefix. -/
theorem continuousGrowingPrefixForwardBesselPACBayesBoundary_le_allTimeRate
    (prior : Measure Theta) (posterior : Measure Theta)
    [IsProbabilityMeasure posterior]
    {X : Theta -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta) (hdelta1 : delta <= 1)
    (hX_parameter : forall k omega,
      StronglyMeasurable (fun theta => X theta k omega))
    (hX : forall theta k omega, X theta k omega ∈ Set.Icc (0 : Real) 1)
    {n : Nat} (hn : 4 <= n) (omega : Omega) :
    countableContinuousForwardPredictableMeanBesselBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt X posterior
          delta (continuousGrowingPrefixForwardBesselPACBayesArgmin
            prior X posterior delta n omega) n omega <=
      allTimeGeometricPolynomialForwardRate
        (fun _ => (InformationTheory.klDiv posterior prior).toReal) delta n := by
  have hcandidate : geometricForwardTiltIndex n ∈
      Finset.range (growingPrefixForwardBesselPACBayesMaxIndex n + 1) := by
    simp [growingPrefixForwardBesselPACBayesMaxIndex]
  have hn2 : 2 <= n := le_trans (by norm_num) hn
  have hgeom :=
    countableContinuousForwardPredictableMeanBesselBoundary_le_geometricRate
      (Theta := Theta) (Omega := Omega) prior posterior hdelta hdelta1
      hX_parameter hX (geometricForwardTiltIndex n) n hn2
      (geometricForwardTiltIndex_floor hn) omega
  have hrate :
      countableContinuousForwardPredictableMeanBesselBoundary
          prior polynomialForwardTiltWeight geometricForwardTilt X posterior
            delta (geometricForwardTiltIndex n) n omega <=
        allTimeGeometricPolynomialForwardRate
          (fun _ => (InformationTheory.klDiv posterior prior).toReal)
            delta n := by
    simpa [allTimeGeometricPolynomialForwardRate,
      geometricPolynomialForwardRate] using hgeom
  exact (continuousGrowingPrefixForwardBesselPACBayesArgmin_le
    prior X posterior delta n omega hcandidate).trans hrate

/-- Under explicit sublinear KL complexity at the selected geometric scale,
the continuous growing-prefix exact boundary tends to zero. Absolute
continuity and log-density integrability rule out treating infinite KL as zero
through `ENNReal.toReal`. -/
theorem continuousGrowingPrefixForwardBesselPACBayesBoundary_tendsto_zero
    (prior : Measure Theta)
    (posterior : Nat -> Measure Theta)
    (hposterior : forall n, IsProbabilityMeasure (posterior n))
    (hposterior_prior : forall n, posterior n ≪ prior)
    (hllr : forall n,
      Integrable (llr (posterior n) prior) (posterior n))
    {X : Theta -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta) (hdelta1 : delta <= 1)
    (hX_parameter : forall k omega,
      StronglyMeasurable (fun theta => X theta k omega))
    (hX : forall theta k omega, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hcomplexity : Filter.Tendsto
      (fun n => (InformationTheory.klDiv (posterior n) prior).toReal /
        (2 : Real) ^ (geometricForwardTiltIndex n + 1))
      Filter.atTop (nhds 0))
    (omega : Omega) :
    Filter.Tendsto
      (fun n => countableContinuousForwardPredictableMeanBesselBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt X
          (posterior n) delta
          (continuousGrowingPrefixForwardBesselPACBayesArgmin
            prior X (posterior n) delta n omega) n omega)
      Filter.atTop (nhds 0) := by
  have _hfinite : forall n,
      InformationTheory.klDiv (posterior n) prior ≠ ∞ := fun n =>
    InformationTheory.klDiv_ne_top (hposterior_prior n) (hllr n)
  have hrate := allTimeGeometricPolynomialForwardRate_tendsto_zero
    hdelta hdelta1 hcomplexity
  apply squeeze_zero'
  · filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    letI : IsProbabilityMeasure (posterior n) := hposterior n
    exact countableContinuousForwardPredictableMeanBesselBoundary_nonneg
      prior (posterior n) hdelta hdelta1 hX_parameter hX
      (continuousGrowingPrefixForwardBesselPACBayesArgmin
        prior X (posterior n) delta n omega) n (by omega) omega
  · filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    letI : IsProbabilityMeasure (posterior n) := hposterior n
    exact continuousGrowingPrefixForwardBesselPACBayesBoundary_le_allTimeRate
      prior (posterior n) hdelta hdelta1 hX_parameter hX hn omega
  · exact hrate

/-- One countable-master event supports path- and time-selected continuous
posteriors and exact minimization over every reporting-time geometric prefix.
The selected boundary has an observable LIL-order envelope. Its vanishing
conclusion is conditional on the displayed posterior-complexity rate rather
than on an unavailable finite-prior KL ceiling. -/
theorem exists_continuousGrowingPrefixForwardBesselPACBayesOracle_event
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X mean : Theta -> Nat -> Omega -> Real}
    {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
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
          (X q.2) (mean q.2) (geometricForwardTilt j) n q.1))
    (hjoint_filtered : forall j n,
      StronglyMeasurable[MeasurableSpace.prod (F n) inferInstance]
        (fun q : Omega × Theta =>
          forwardPredictableMeanEmpiricalBernsteinLowerProcess
            (X q.2) (mean q.2) (geometricForwardTilt j) n q.1))
    (posterior : Omega -> Nat -> Measure Theta)
    (hposterior : forall omega n,
      IsProbabilityMeasure (posterior omega n))
    (hposterior_prior : forall omega n, posterior omega n ≪ prior)
    (hllr : forall omega n,
      Integrable (llr (posterior omega n) prior) (posterior omega n)) :
    ∃ goodEvent : Set Omega,
      mu.real goodEventᶜ <= delta ∧
        (∀ omega ∈ goodEvent, forall n : Nat, 4 <= n ->
          let rho := posterior omega n
          let selected := continuousGrowingPrefixForwardBesselPACBayesArgmin
            prior X rho delta n omega
          selected ∈ Finset.range
              (growingPrefixForwardBesselPACBayesMaxIndex n + 1) ∧
            (∫ theta, forwardPrefixMean
                (fun k => mean theta k omega) n ∂rho) <
              (∫ theta, forwardPrefixMean
                (fun k => X theta k omega) n ∂rho) +
                countableContinuousForwardPredictableMeanBesselBoundary
                  prior polynomialForwardTiltWeight geometricForwardTilt X
                    rho delta selected n omega ∧
            countableContinuousForwardPredictableMeanBesselBoundary
                prior polynomialForwardTiltWeight geometricForwardTilt X
                  rho delta selected n omega <=
              continuousGrowingPrefixForwardBesselPACBayesLILEnvelope
                prior X rho delta n omega ∧
            countableContinuousForwardPredictableMeanBesselBoundary
                prior polynomialForwardTiltWeight geometricForwardTilt X
                  rho delta selected n omega <=
              allTimeGeometricPolynomialForwardRate
                (fun _ => (InformationTheory.klDiv rho prior).toReal)
                delta n) ∧
        (∀ omega ∈ goodEvent,
          Filter.Tendsto
              (fun n =>
                (InformationTheory.klDiv (posterior omega n) prior).toReal /
                  (2 : Real) ^ (geometricForwardTiltIndex n + 1))
              Filter.atTop (nhds 0) ->
            Filter.Tendsto
              (fun n =>
                countableContinuousForwardPredictableMeanBesselBoundary
                  prior polynomialForwardTiltWeight geometricForwardTilt X
                    (posterior omega n) delta
                    (continuousGrowingPrefixForwardBesselPACBayesArgmin
                      prior X (posterior omega n) delta n omega) n omega)
              Filter.atTop (nhds 0)) := by
  obtain ⟨goodEvent, hmass, hgood⟩ :=
    exists_countableContinuousForwardPredictableMeanBesselPACBayes_event
      prior polynomialForwardTiltWeight_pos polynomialForwardTiltWeight_hasSum
      hdelta geometricForwardTilt_pos geometricForwardTilt_lt_one
      hX_adapted hmean_adapted hX_unit hmean_unit hmean
      hX_parameter hmean_parameter hjoint_ambient hjoint_filtered
  refine ⟨goodEvent, hmass, ?_, ?_⟩
  · intro omega homega n hn
    let rho := posterior omega n
    let selected := continuousGrowingPrefixForwardBesselPACBayesArgmin
      prior X rho delta n omega
    letI : IsProbabilityMeasure rho := hposterior omega n
    have hselected_mem : selected ∈
        Finset.range
          (growingPrefixForwardBesselPACBayesMaxIndex n + 1) :=
      continuousGrowingPrefixForwardBesselPACBayesArgmin_mem
        prior X rho delta n omega
    have hrisk := hgood omega homega selected rho
      (hposterior omega n) (hposterior_prior omega n) (hllr omega n)
      n (by omega)
    have hLIL :=
      continuousGrowingPrefixForwardBesselPACBayesBoundary_le_LILEnvelope
        prior rho hdelta hdelta1 hX_parameter hX_unit hn omega
    have hrate :=
      continuousGrowingPrefixForwardBesselPACBayesBoundary_le_allTimeRate
        prior rho hdelta hdelta1 hX_parameter hX_unit hn omega
    exact ⟨hselected_mem, hrisk, hLIL, hrate⟩
  · intro omega _homega hcomplexity
    exact continuousGrowingPrefixForwardBesselPACBayesBoundary_tendsto_zero
      prior (posterior omega) (hposterior omega) (hposterior_prior omega)
      (hllr omega) hdelta hdelta1 hX_parameter hX_unit hcomplexity omega

end

end FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayesOracle
