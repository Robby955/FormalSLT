/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.ContinuousTrajectorySleepingCountableTiltPACBayes

/-!
# Suffix-length geometric oracle for sleeping trajectory PAC-Bayes bounds

The countable geometric-tilt event controls every declared atom. For a suffix
of length `n - w`, this module selects the explicit atom
`geometricForwardTiltIndex (n - w)`. Its observable excess width is bounded by
the established all-time geometric-polynomial rate at effective confidence
`delta * polynomialEpochWeight w`.

This is a predeclared catalog substitution, not an exact finite-prefix argmin,
parameter-free inference, coin betting, or a selected e-process. Only the
excess above observed suffix risk is shown to vanish. The controlled target is
ordinary conditional risk encountered along the monitored suffix, not future,
stationary, population, or deployment risk.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.AllocationLogLog
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open scoped BigOperators Topology

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Theta Z : Type*} [MeasurableSpace Theta]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- Catalog atom selected from the number of observations after wake time. -/
def continuousTrajectorySleepingSuffixGeometricTiltIndex
    (w n : Nat) : Nat :=
  geometricForwardTiltIndex (n - w)

/-- Wake selection consumes a polynomial share of the outer confidence. -/
def continuousTrajectorySleepingSuffixEffectiveConfidence
    (delta : Real) (w : Nat) : Real :=
  delta * polynomialEpochWeight w

/-- Excess width of the suffix-length-selected geometric atom. -/
def continuousTrajectorySleepingSuffixGeometricTiltExcess
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) : Real :=
  let a := continuousTrajectorySleepingSuffixGeometricTiltIndex w n
  ((InformationTheory.klDiv posterior prior).toReal +
      (Real.log (1 / (delta * polynomialEpochWeight a)) -
        Real.log (polynomialEpochWeight w)) +
      continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
        score posterior (fun _ => geometricForwardTilt a) w n x) /
    (((n - w : Nat) : Real) * geometricForwardTilt a)

/-- Observable selected upper endpoint for encountered conditional suffix
risk. -/
def continuousTrajectorySleepingSuffixGeometricTiltBoundary
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) : Real :=
  continuousTrajectorySleepingGeometricTiltSuffixBoundary prior posterior score
      delta (continuousTrajectorySleepingSuffixGeometricTiltIndex w n) w n x

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
@[simp]
theorem continuousTrajectorySleepingSuffixGeometricTiltBoundary_eq
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) :
    continuousTrajectorySleepingSuffixGeometricTiltBoundary
        prior posterior score delta w n x =
      continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
          score posterior w n x +
        continuousTrajectorySleepingSuffixGeometricTiltExcess
          prior posterior score delta w n x := by
  unfold continuousTrajectorySleepingSuffixGeometricTiltBoundary
    continuousTrajectorySleepingGeometricTiltSuffixBoundary
    continuousTrajectorySleepingCountableTiltSuffixBoundary
    continuousTrajectorySleepingSuffixGeometricTiltExcess
  ring

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
theorem continuousTrajectorySleeping_geometricTiltWake_log_cost
    {delta : Real} (hdelta : 0 < delta) (a w : Nat) :
    Real.log (1 / (delta * polynomialEpochWeight a)) -
        Real.log (polynomialEpochWeight w) =
      Real.log ((((a : Real) + 1) * ((a : Real) + 2)) /
        continuousTrajectorySleepingSuffixEffectiveConfidence delta w) := by
  have ha : 0 < polynomialEpochWeight a := polynomialEpochWeight_pos a
  have hw : 0 < polynomialEpochWeight w := polynomialEpochWeight_pos w
  have hnum : 1 / (delta * polynomialEpochWeight a) ≠ 0 := by positivity
  rw [← Real.log_div hnum hw.ne']
  congr 1
  unfold continuousTrajectorySleepingSuffixEffectiveConfidence
    polynomialEpochWeight
  field_simp [hdelta.ne']

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- Prefix means remain measurable in a parameter when every preceding
coordinate is measurable in that parameter. -/
private theorem stronglyMeasurable_suffixOracleForwardPredictor
    {Alpha : Type*} [MeasurableSpace Alpha]
    (X : Nat -> Alpha -> Real) {k : Nat}
    (hX : forall i, i < k -> StronglyMeasurable (X i)) :
    StronglyMeasurable (forwardPredictorProcess X k) := by
  unfold forwardPredictorProcess forwardPredictor
  split_ifs
  · exact stronglyMeasurable_const
  · unfold forwardPrefixMean
    have hsum : StronglyMeasurable (∑ i ∈ Finset.range k, X i) :=
      Finset.stronglyMeasurable_sum (Finset.range k) fun i hi =>
        hX i (Finset.mem_range.mp hi)
    simpa only [Finset.sum_apply, div_eq_mul_inv] using
      hsum.mul_const ((k : Real)⁻¹)

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The continuous posterior-integrated observable suffix penalty is bounded
by the suffix length and the quadratic geometric-tilt envelope. -/
theorem
    continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty_mem_Icc
    (score : Theta -> TrajectoryScore Z)
    (hscore : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    (posterior : Measure Theta) [IsProbabilityMeasure posterior]
    {lam : Real} (hlam0 : 0 <= lam) (hlamhalf : lam <= 1 / 2)
    {w n : Nat} (hwn : w <= n) (x : Nat -> Z) :
    continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
        score posterior (fun _ => lam) w n x ∈
      Set.Icc 0 (2 * lam ^ 2 * (n - w : Nat)) := by
  let X : Nat -> Theta -> Real := fun k theta =>
    observedTrajectoryScore (score theta) k x
  have hX_meas (k : Nat) : StronglyMeasurable (X k) := by
    change StronglyMeasurable
      (fun theta => score theta k (Preorder.frestrictLe k x) (x (k + 1)))
    exact hscore_parameter k _ _
  have hX_unit (theta : Theta) (k : Nat) : X k theta ∈ Set.Icc (0 : Real) 1 := by
    exact hscore theta k _ _
  have hsquare_meas (k : Nat) : StronglyMeasurable (fun theta =>
      (X k theta - forwardPredictorProcess X k theta) ^ 2) := by
    have hpredictor : StronglyMeasurable
        (forwardPredictorProcess X k) :=
      stronglyMeasurable_suffixOracleForwardPredictor
        X (fun i _hi => hX_meas i)
    exact ((hX_meas k).sub hpredictor).pow 2
  have hsquare_mem (theta : Theta) (k : Nat) :
      (X k theta - forwardPredictorProcess X k theta) ^ 2 ∈
        Set.Icc (0 : Real) 1 := by
    have hpred := forwardPredictorProcess_mem_Icc_of_mem_Icc
      (X := X) (fun i theta => hX_unit theta i) k theta
    constructor
    · positivity
    · rcases hX_unit theta k with ⟨hX0, hX1⟩
      rcases hpred with ⟨hP0, hP1⟩
      nlinarith
  have hintegrable : Integrable (fun theta =>
      ∑ k ∈ Finset.Ico w n,
        forwardEmpiricalBernsteinPsi lam *
          (X k theta - forwardPredictorProcess X k theta) ^ 2)
      posterior := by
    have hsum : Integrable
        (∑ k ∈ Finset.Ico w n, fun theta =>
          forwardEmpiricalBernsteinPsi lam *
            (X k theta - forwardPredictorProcess X k theta) ^ 2)
        posterior := by
      apply integrable_finsetSum'
      intro k _hk
      have hsq : Integrable (fun theta =>
          (X k theta - forwardPredictorProcess X k theta) ^ 2)
          posterior := by
        refine Integrable.of_bound (hsquare_meas k).aestronglyMeasurable 1 ?_
        exact Filter.Eventually.of_forall fun theta => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hsquare_mem theta k).1]
          exact (hsquare_mem theta k).2
      exact hsq.const_mul (forwardEmpiricalBernsteinPsi lam)
    convert hsum using 1
    funext theta
    simp only [Finset.sum_apply]
  have hpsi0 : 0 <= forwardEmpiricalBernsteinPsi lam :=
    forwardEmpiricalBernsteinPsi_nonneg hlam0 (by linarith)
  have hpsi : forwardEmpiricalBernsteinPsi lam <= 2 * lam ^ 2 :=
    forwardEmpiricalBernsteinPsi_le_two_mul_sq hlamhalf
  have hpoint_nonneg : forall theta,
      0 <= ∑ k ∈ Finset.Ico w n,
        forwardEmpiricalBernsteinPsi lam *
          (X k theta - forwardPredictorProcess X k theta) ^ 2 := by
    intro theta
    exact Finset.sum_nonneg fun k _hk =>
      mul_nonneg hpsi0 (hsquare_mem theta k).1
  have hpoint_upper : forall theta,
      (∑ k ∈ Finset.Ico w n,
        forwardEmpiricalBernsteinPsi lam *
          (X k theta - forwardPredictorProcess X k theta) ^ 2) <=
        2 * lam ^ 2 * (n - w : Nat) := by
    intro theta
    calc
      (∑ k ∈ Finset.Ico w n,
          forwardEmpiricalBernsteinPsi lam *
            (X k theta - forwardPredictorProcess X k theta) ^ 2) <=
          ∑ _k ∈ Finset.Ico w n, 2 * lam ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        calc
          forwardEmpiricalBernsteinPsi lam *
                (X k theta - forwardPredictorProcess X k theta) ^ 2 <=
              (2 * lam ^ 2) *
                (X k theta - forwardPredictorProcess X k theta) ^ 2 :=
            mul_le_mul_of_nonneg_right hpsi (hsquare_mem theta k).1
          _ <= (2 * lam ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left (hsquare_mem theta k).2 (by positivity)
          _ = 2 * lam ^ 2 := by ring
      _ = 2 * lam ^ 2 * (n - w : Nat) := by
        simp [Nat.card_Ico, hwn, nsmul_eq_mul]
        ring
  unfold continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
  change (∫ theta,
      ∑ k ∈ Finset.Ico w n,
        forwardEmpiricalBernsteinPsi lam *
          (X k theta - forwardPredictorProcess X k theta) ^ 2
      ∂posterior) ∈ Set.Icc 0 (2 * lam ^ 2 * (n - w : Nat))
  constructor
  · exact integral_nonneg hpoint_nonneg
  · calc
      (∫ theta,
          ∑ k ∈ Finset.Ico w n,
            forwardEmpiricalBernsteinPsi lam *
              (X k theta - forwardPredictorProcess X k theta) ^ 2
          ∂posterior) <=
          ∫ _theta, 2 * lam ^ 2 * (n - w : Nat) ∂posterior :=
        integral_mono hintegrable (integrable_const _) hpoint_upper
      _ = 2 * lam ^ 2 * (n - w : Nat) := by simp

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The selected excess width is controlled by the standard geometric rate
at the wake-adjusted confidence level. -/
theorem continuousTrajectorySleepingSuffixGeometricTiltExcess_le_allTimeRate
    (prior posterior : Measure Theta) [IsProbabilityMeasure posterior]
    (score : Theta -> TrajectoryScore Z)
    (hscore : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
    {w n : Nat} (hsuffix : 4 <= n - w) (x : Nat -> Z) :
    continuousTrajectorySleepingSuffixGeometricTiltExcess
        prior posterior score delta w n x <=
      allTimeGeometricPolynomialForwardRate
        (fun _ => (InformationTheory.klDiv posterior prior).toReal)
        (continuousTrajectorySleepingSuffixEffectiveConfidence delta w)
        (n - w) := by
  let m := n - w
  let a := geometricForwardTiltIndex m
  let lam := geometricForwardTilt a
  let effectiveDelta :=
    continuousTrajectorySleepingSuffixEffectiveConfidence delta w
  let complexity := (InformationTheory.klDiv posterior prior).toReal
  let penalty :=
    continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
      score posterior (fun _ => lam) w n x
  have hwn : w <= n := by omega
  have hmpos : 0 < m := by omega
  have hlampos : 0 < lam := geometricForwardTilt_pos a
  have hpenalty : penalty ∈ Set.Icc 0 (2 * lam ^ 2 * m) := by
    simpa [penalty, lam, a, m] using
      continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty_mem_Icc
        score hscore hscore_parameter posterior
        (geometricForwardTilt_pos a).le (geometricForwardTilt_le_half a)
        hwn x
  have heffective_pos : 0 < effectiveDelta := by
    exact mul_pos hdelta (polynomialEpochWeight_pos w)
  have hweight_le_one : polynomialEpochWeight w <= 1 := by
    unfold polynomialEpochWeight
    rw [div_le_one (by positivity :
      (0 : Real) < ((w : Real) + 1) * ((w : Real) + 2))]
    have hw0 : (0 : Real) <= w := Nat.cast_nonneg w
    nlinarith
  have heffective_one : effectiveDelta <= 1 := by
    dsimp [effectiveDelta,
      continuousTrajectorySleepingSuffixEffectiveConfidence]
    calc
      delta * polynomialEpochWeight w <= 1 * polynomialEpochWeight w :=
        mul_le_mul_of_nonneg_right hdelta1 (polynomialEpochWeight_pos w).le
      _ <= 1 := by simpa using hweight_le_one
  have hlog :
      Real.log (1 / (delta * polynomialEpochWeight a)) -
          Real.log (polynomialEpochWeight w) =
        Real.log ((((a : Real) + 1) * ((a : Real) + 2)) /
          effectiveDelta) := by
    simpa [effectiveDelta] using
      continuousTrajectorySleeping_geometricTiltWake_log_cost hdelta a w
  have hratio : 1 <=
      (((a : Real) + 1) * ((a : Real) + 2)) / effectiveDelta := by
    apply (le_div_iff₀ heffective_pos).2
    have ha0 : (0 : Real) <= a := Nat.cast_nonneg a
    nlinarith
  have hcomplexity0 : 0 <= complexity +
      Real.log ((((a : Real) + 1) * ((a : Real) + 2)) /
        effectiveDelta) :=
    add_nonneg (InformationTheory.klDiv posterior prior).toReal_nonneg
      (Real.log_nonneg hratio)
  have hfloor : geometricForwardTiltTime a <= m := by
    simpa [a] using geometricForwardTiltIndex_floor hsuffix
  have hden : (2 : Real) ^ (a + 1) <= (m : Real) * lam := by
    have hcast : (geometricForwardTiltTime a : Real) <= (m : Real) := by
      exact_mod_cast hfloor
    calc
      (2 : Real) ^ (a + 1) =
          (geometricForwardTiltTime a : Real) * lam := by
        simpa [lam] using (geometricForwardTiltTime_mul_tilt a).symm
      _ <= (m : Real) * lam :=
        mul_le_mul_of_nonneg_right hcast hlampos.le
  have hdenpos : 0 < (m : Real) * lam :=
    mul_pos (Nat.cast_pos.mpr hmpos) hlampos
  have hpowpos : 0 < (2 : Real) ^ (a + 1) := by positivity
  have hcomplexity :
      (complexity +
          Real.log ((((a : Real) + 1) * ((a : Real) + 2)) /
            effectiveDelta)) / ((m : Real) * lam) <=
        (complexity +
          Real.log ((((a : Real) + 1) * ((a : Real) + 2)) /
            effectiveDelta)) / (2 : Real) ^ (a + 1) :=
    div_le_div_of_nonneg_left hcomplexity0 hpowpos hden
  have hpenalty_rate : penalty / ((m : Real) * lam) <= 2 * lam := by
    calc
      penalty / ((m : Real) * lam) <=
          (2 * lam ^ 2 * m) / ((m : Real) * lam) :=
        div_le_div_of_nonneg_right hpenalty.2 hdenpos.le
      _ = 2 * lam := by
        field_simp [show (m : Real) ≠ 0 by positivity, hlampos.ne']
  unfold continuousTrajectorySleepingSuffixGeometricTiltExcess
  change
    (complexity +
        (Real.log (1 / (delta * polynomialEpochWeight a)) -
          Real.log (polynomialEpochWeight w)) + penalty) /
      ((m : Real) * lam) <= _
  rw [hlog]
  calc
    (complexity +
          Real.log ((((a : Real) + 1) * ((a : Real) + 2)) /
            effectiveDelta) + penalty) / ((m : Real) * lam) =
        (complexity +
          Real.log ((((a : Real) + 1) * ((a : Real) + 2)) /
            effectiveDelta)) / ((m : Real) * lam) +
          penalty / ((m : Real) * lam) := by ring
    _ <= (complexity +
          Real.log ((((a : Real) + 1) * ((a : Real) + 2)) /
            effectiveDelta)) / (2 : Real) ^ (a + 1) + 2 * lam :=
      add_le_add hcomplexity hpenalty_rate
    _ = allTimeGeometricPolynomialForwardRate
        (fun _ => (InformationTheory.klDiv posterior prior).toReal)
        (continuousTrajectorySleepingSuffixEffectiveConfidence delta w)
        (n - w) := by
      simp [allTimeGeometricPolynomialForwardRate, complexity, effectiveDelta,
        lam, a, m]
      ring

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The selected excess is nonnegative on every suffix of length at least
four at confidence at most one. -/
theorem continuousTrajectorySleepingSuffixGeometricTiltExcess_nonneg
    (prior posterior : Measure Theta) [IsProbabilityMeasure posterior]
    (score : Theta -> TrajectoryScore Z)
    (hscore : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
    {w n : Nat} (hsuffix : 4 <= n - w) (x : Nat -> Z) :
    0 <= continuousTrajectorySleepingSuffixGeometricTiltExcess
      prior posterior score delta w n x := by
  let a := continuousTrajectorySleepingSuffixGeometricTiltIndex w n
  have hwn : w <= n := by omega
  have hpenalty :=
    continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty_mem_Icc
      score hscore hscore_parameter posterior
      (geometricForwardTilt_pos a).le (geometricForwardTilt_le_half a)
      hwn x
  have hlog := continuousTrajectorySleeping_geometricTiltWake_log_cost
    hdelta a w
  have heffective_pos :
      0 < continuousTrajectorySleepingSuffixEffectiveConfidence delta w :=
    mul_pos hdelta (polynomialEpochWeight_pos w)
  have hweight_le_one : polynomialEpochWeight w <= 1 := by
    unfold polynomialEpochWeight
    rw [div_le_one (by positivity :
      (0 : Real) < ((w : Real) + 1) * ((w : Real) + 2))]
    have hw0 : (0 : Real) <= w := Nat.cast_nonneg w
    nlinarith
  have heffective_one :
      continuousTrajectorySleepingSuffixEffectiveConfidence delta w <= 1 := by
    unfold continuousTrajectorySleepingSuffixEffectiveConfidence
    calc
      delta * polynomialEpochWeight w <= 1 * polynomialEpochWeight w :=
        mul_le_mul_of_nonneg_right hdelta1 (polynomialEpochWeight_pos w).le
      _ <= 1 := by simpa using hweight_le_one
  have hratio : 1 <=
      (((a : Real) + 1) * ((a : Real) + 2)) /
        continuousTrajectorySleepingSuffixEffectiveConfidence delta w := by
    apply (le_div_iff₀ heffective_pos).2
    have ha0 : (0 : Real) <= a := Nat.cast_nonneg a
    nlinarith
  unfold continuousTrajectorySleepingSuffixGeometricTiltExcess
  change 0 <=
    ((InformationTheory.klDiv posterior prior).toReal +
        (Real.log (1 / (delta * polynomialEpochWeight a)) -
          Real.log (polynomialEpochWeight w)) +
        continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
          score posterior (fun _ => geometricForwardTilt a) w n x) /
      (((n - w : Nat) : Real) * geometricForwardTilt a)
  rw [hlog]
  exact div_nonneg
    (add_nonneg
      (add_nonneg (InformationTheory.klDiv posterior prior).toReal_nonneg
        (Real.log_nonneg hratio))
      hpenalty.1)
    (mul_nonneg (Nat.cast_nonneg _)
      (geometricForwardTilt_pos a).le)

/-- On the common countable event, the suffix-length geometric atom controls
ordinary encountered conditional suffix risk. Posterior, wake, and reporting
time may be selected from the observed path. -/
theorem
    exists_continuousTrajectorySleepingSuffixGeometricTiltPACBayes_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {delta : Real} (hdelta : 0 < delta)
    (posterior : (Nat -> Z) -> Nat -> Measure Theta)
    (hposterior : forall x n,
      IsProbabilityMeasure (posterior x n))
    (hposterior_prior : forall x n, posterior x n ≪ prior)
    (hllr : forall x n,
      Integrable (llr (posterior x n) prior) (posterior x n))
    (wake : (Nat -> Z) -> Nat -> Nat) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta ∧
        forall x, x ∈ goodEvent ->
          forall n : Nat, wake x n < n ->
            continuousTrajectoryPosteriorAverageConditionalSuffixRisk
                K score (posterior x n) (wake x n) n x <
              continuousTrajectorySleepingSuffixGeometricTiltBoundary
                prior (posterior x n) score delta (wake x n) n x := by
  obtain ⟨goodEvent, hmass, hgood⟩ :=
    exists_continuousTrajectorySleepingGeometricTiltPACBayes_suffixRisk_event_of_parameterMeasurable
      K x0 score hscore hscore_parameter prior hdelta
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx n hwn
  let rho := posterior x n
  let w := wake x n
  let a := continuousTrajectorySleepingSuffixGeometricTiltIndex w n
  have hbound := hgood x hx rho (hposterior x n)
    (hposterior_prior x n) (hllr x n) a w n hwn
  simpa [continuousTrajectorySleepingSuffixGeometricTiltBoundary, a, w, rho]
    using hbound

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- For a fixed wake time, the selected excess width vanishes as the suffix
length grows, provided posterior KL is negligible at the selected geometric
scale. Absolute continuity and log-density integrability enforce that every
posterior is eligible for the PAC-Bayes event and prevent `ENNReal.toReal`
from silently mapping infinite KL to zero. -/
theorem continuousTrajectorySleepingSuffixGeometricTiltExcess_tendsto_zero_fixedWake
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    (posterior : Nat -> Measure Theta)
    (hposterior : forall m, IsProbabilityMeasure (posterior m))
    (hposterior_prior : forall m, posterior m ≪ prior)
    (hllr : forall m,
      Integrable (llr (posterior m) prior) (posterior m))
    (score : Theta -> TrajectoryScore Z)
    (hscore : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
    (w : Nat) (x : Nat -> Z)
    (hcomplexity : Filter.Tendsto
      (fun m => (InformationTheory.klDiv (posterior m) prior).toReal /
        (2 : Real) ^ (geometricForwardTiltIndex m + 1))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun m => continuousTrajectorySleepingSuffixGeometricTiltExcess
        prior (posterior m) score delta w (m + w) x)
      Filter.atTop (nhds 0) := by
  let complexity : Nat -> Real := fun m =>
    (InformationTheory.klDiv (posterior m) prior).toReal
  let effectiveDelta :=
    continuousTrajectorySleepingSuffixEffectiveConfidence delta w
  have heffective_pos : 0 < effectiveDelta :=
    mul_pos hdelta (polynomialEpochWeight_pos w)
  have hweight_le_one : polynomialEpochWeight w <= 1 := by
    unfold polynomialEpochWeight
    rw [div_le_one (by positivity :
      (0 : Real) < ((w : Real) + 1) * ((w : Real) + 2))]
    have hw0 : (0 : Real) <= w := Nat.cast_nonneg w
    nlinarith
  have heffective_one : effectiveDelta <= 1 := by
    dsimp [effectiveDelta,
      continuousTrajectorySleepingSuffixEffectiveConfidence]
    calc
      delta * polynomialEpochWeight w <= 1 * polynomialEpochWeight w :=
        mul_le_mul_of_nonneg_right hdelta1 (polynomialEpochWeight_pos w).le
      _ <= 1 := by simpa using hweight_le_one
  have hrate : Filter.Tendsto
      (allTimeGeometricPolynomialForwardRate complexity effectiveDelta)
      Filter.atTop (nhds 0) :=
    allTimeGeometricPolynomialForwardRate_tendsto_zero
      heffective_pos heffective_one (by simpa [complexity] using hcomplexity)
  have _hfinite : forall m,
      InformationTheory.klDiv (posterior m) prior ≠ ⊤ := fun m =>
    InformationTheory.klDiv_ne_top (hposterior_prior m) (hllr m)
  apply squeeze_zero'
  · filter_upwards [Filter.eventually_ge_atTop 4] with m hm
    letI : IsProbabilityMeasure (posterior m) := hposterior m
    simpa using
      (continuousTrajectorySleepingSuffixGeometricTiltExcess_nonneg
        prior (posterior m) score hscore hscore_parameter hdelta hdelta1
        (w := w) (n := m + w) (by omega) x)
  · filter_upwards [Filter.eventually_ge_atTop 4] with m hm
    letI : IsProbabilityMeasure (posterior m) := hposterior m
    have hupper :=
      continuousTrajectorySleepingSuffixGeometricTiltExcess_le_allTimeRate
        prior (posterior m) score hscore hscore_parameter hdelta hdelta1
        (w := w) (n := m + w) (by omega) x
    simpa [allTimeGeometricPolynomialForwardRate, complexity, effectiveDelta]
      using hupper
  · exact hrate

end

end FormalSLT.StochasticDynamics
