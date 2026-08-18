/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.ForwardPredictableMeanBesselPACBayes
import FormalSLT.PACBayes.TimeUniformContinuousPACBayes

/-!
# Continuous-hypothesis predictable-mean empirical-Bernstein PAC-Bayes

This module replaces the finite hypothesis sum in the forward predictable-mean
empirical-Bernstein theorem by an integral over an arbitrary measurable
hypothesis space.  The mixed objects are the actual predictable-residual
e-processes.  The observable hybrid-Bessel expression is used only later as a
pointwise lower envelope.

The joint strong-measurability hypothesis is an explicit analytic interface:
at time `n`, the parameterized actual process must be measurable for the
product of the path filtration `F n` and the hypothesis sigma algebra.  From
that interface and boundedness, this file derives every product-integrability
obligation required by Fubini, the continuous prior-mixture e-process, Ville's
crossing bound, and the continuous Donsker--Varadhan inversion.

The final event is common to every time `n >= 2`, every declared finite tilt,
and every probability posterior absolutely continuous with respect to the
prior whose log-likelihood ratio is integrable.  No topology, finite
hypothesis assumption, or selected-process claim is made.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayes.ContinuousChangeOfMeasure
open FormalSLT.PACBayes.TimeUniformContinuous
open scoped BigOperators ENNReal

namespace FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {Theta Tau Omega : Type*} [MeasurableSpace Theta]
  [Fintype Tau] [DecidableEq Tau] [Nonempty Tau]
  {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
  {F : Filtration Nat mOmega}

/-- Continuous prior mixture of the actual lower-tail predictable-mean
empirical-Bernstein e-process at one declared tilt. -/
def continuousForwardPredictableMeanBesselPriorProcess
    (prior : Measure Theta) (X mean : Theta -> Nat -> Omega -> Real)
    (lam : Real) : Nat -> Omega -> Real :=
  continuousPriorMixtureProcess prior fun theta =>
    forwardPredictableMeanEmpiricalBernsteinLowerProcess
      (X theta) (mean theta) lam

/-- Finite declared-tilt mixture of continuous hypothesis-prior mixtures. -/
def continuousForwardPredictableMeanBesselMasterProcess
    (prior : Measure Theta) (weight : Tau -> Real)
    (X mean : Theta -> Nat -> Omega -> Real) (lam : Tau -> Real) :
    Nat -> Omega -> Real :=
  finiteWeightedProcess weight fun j =>
    continuousForwardPredictableMeanBesselPriorProcess
      prior X mean (lam j)

/-- Posterior integral of the per-hypothesis hybrid Bessel penalty. -/
def continuousForwardPosteriorHybridBesselPenalty
    (posterior : Measure Theta) (X : Theta -> Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) : Real :=
  ∫ theta, forwardHybridBesselPenalty (fun k => X theta k omega) n ∂posterior

/-- Exact continuous-posterior empirical-Bernstein boundary at one declared
tilt atom. -/
def continuousForwardPredictableMeanBesselBoundary
    (prior : Measure Theta) (weight : Tau -> Real) (lam : Tau -> Real)
    (X : Theta -> Nat -> Omega -> Real) (posterior : Measure Theta)
    (delta : Real) (j : Tau) (n : Nat) (omega : Omega) : Real :=
  ((InformationTheory.klDiv posterior prior).toReal +
      Real.log (1 / (delta * weight j)) +
      forwardEmpiricalBernsteinPsi (lam j) *
        continuousForwardPosteriorHybridBesselPenalty posterior X n omega) /
    ((n : Real) * lam j)

/-- Per-hypothesis hybrid-Bessel score used in the continuous
Donsker--Varadhan inversion. -/
def continuousForwardPredictableMeanBesselScore
    (X mean : Theta -> Nat -> Omega -> Real) (lam : Real)
    (theta : Theta) (n : Nat) (omega : Omega) : Real :=
  lam * (∑ k ∈ Finset.range n, (mean theta k omega - X theta k omega)) -
    forwardEmpiricalBernsteinPsi lam *
      forwardHybridBesselPenalty (fun k => X theta k omega) n

/-- Canonical crossing event of the actual continuous-prior, finite-tilt
master e-process. -/
def continuousForwardPredictableMeanBesselExceptionalEvent
    (prior : Measure Theta) (weight : Tau -> Real)
    (X mean : Theta -> Nat -> Omega -> Real) (lam : Tau -> Real)
    (delta : Real) : Set Omega :=
  atTopCrossingEvent
    (continuousForwardPredictableMeanBesselMasterProcess
      prior weight X mean lam) (1 / delta)

omit [MeasurableSpace Theta] [Fintype Tau] [DecidableEq Tau]
  [Nonempty Tau] in
/-- The actual predictable-mean lower process has a deterministic finite-time
upper bound under pointwise `[0,1]` bounds on both observations and means. -/
theorem forwardPredictableMeanEmpiricalBernsteinLowerProcess_le_exp_card
    {X mean : Nat -> Omega -> Real} {lam : Real}
    (hlam : 0 <= lam) (hlam_one : lam < 1)
    (hX : forall k omega, X k omega ∈ Set.Icc (0 : Real) 1)
    (hmean : forall k omega, mean k omega ∈ Set.Icc (0 : Real) 1)
    (n : Nat) (omega : Omega) :
    forwardPredictableMeanEmpiricalBernsteinLowerProcess X mean lam n omega <=
      Real.exp (lam * (n : Real)) := by
  rw [forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq]
  apply Real.exp_le_exp.mpr
  have hsum :
      (∑ k ∈ Finset.range n, (mean k omega - X k omega)) <= (n : Real) := by
    calc
      (∑ k ∈ Finset.range n, (mean k omega - X k omega)) <=
          ∑ _k ∈ Finset.range n, (1 : Real) := by
            apply Finset.sum_le_sum
            intro k hk
            linarith [(hmean k omega).2, (hX k omega).1]
      _ = (n : Real) := by simp
  have hquad : 0 <= forwardPredictableQuadratic (fun k => X k omega) n := by
    unfold forwardPredictableQuadratic
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpsi : 0 <= forwardEmpiricalBernsteinPsi lam :=
    forwardEmpiricalBernsteinPsi_nonneg hlam hlam_one
  nlinarith [mul_le_mul_of_nonneg_left hsum hlam,
    mul_nonneg hpsi hquad]

omit [Fintype Tau] [DecidableEq Tau]
  [Nonempty Tau] in
/-- Prefix means are strongly measurable in the parameter when every
coordinate section is. -/
theorem stronglyMeasurable_forwardPrefixMean_parameter
    (x : Theta -> Nat -> Real) (n : Nat)
    (hx : forall k, StronglyMeasurable (fun theta => x theta k)) :
    StronglyMeasurable (fun theta =>
      forwardPrefixMean (fun k => x theta k) n) := by
  unfold forwardPrefixMean
  have hsum : StronglyMeasurable
      (∑ k ∈ Finset.range n, fun theta => x theta k) :=
    Finset.stronglyMeasurable_sum (Finset.range n) fun k _ => hx k
  have heq : (fun theta => (∑ k ∈ Finset.range n, x theta k) / (n : Real)) =
      fun theta => (∑ k ∈ Finset.range n, fun theta => x theta k) theta *
        (n : Real)⁻¹ := by
    funext theta
    simp [div_eq_mul_inv]
  rw [heq]
  exact hsum.mul_const (n : Real)⁻¹

omit [Fintype Tau] [DecidableEq Tau]
  [Nonempty Tau] in
/-- The centered sum of squares is strongly measurable in the parameter. -/
theorem stronglyMeasurable_forwardBesselQ_parameter
    (x : Theta -> Nat -> Real) (n : Nat)
    (hx : forall k, StronglyMeasurable (fun theta => x theta k)) :
    StronglyMeasurable (fun theta =>
      forwardBesselQ (fun k => x theta k) n) := by
  have hmean := stronglyMeasurable_forwardPrefixMean_parameter x n hx
  unfold forwardBesselQ
  have hsum := Finset.stronglyMeasurable_sum (Finset.range n) fun k _ =>
    ((hx k).sub hmean).pow 2
  have heq : (fun theta => ∑ k ∈ Finset.range n,
      (x theta k - forwardPrefixMean (fun j => x theta j) n) ^ 2) =
      ∑ k ∈ Finset.range n, fun theta =>
        (x theta k - forwardPrefixMean (fun j => x theta j) n) ^ 2 := by
    funext theta
    simp
  rw [heq]
  exact hsum

omit [Fintype Tau] [DecidableEq Tau]
  [Nonempty Tau] in
/-- The hybrid Bessel penalty is strongly measurable in the parameter. -/
theorem stronglyMeasurable_forwardHybridBesselPenalty_parameter
    (x : Theta -> Nat -> Real) (n : Nat)
    (hx : forall k, StronglyMeasurable (fun theta => x theta k)) :
    StronglyMeasurable (fun theta =>
      forwardHybridBesselPenalty (fun k => x theta k) n) := by
  have hq := stronglyMeasurable_forwardBesselQ_parameter x n hx
  unfold forwardHybridBesselPenalty
  have hleft : StronglyMeasurable (fun theta =>
      (1 : Real) / 2 + (3 : Real) / 2 *
        forwardBesselQ (fun k => x theta k) n) :=
    stronglyMeasurable_const.add (hq.const_mul ((3 : Real) / 2))
  have hright : StronglyMeasurable (fun theta =>
      (n : Real) / ((n : Real) - 1) *
          forwardBesselQ (fun k => x theta k) n +
        (1 : Real) / 4 *
          (1 + ((harmonic (n - 2) : Rat) : Real))) :=
    (hq.const_mul ((n : Real) / ((n : Real) - 1))).add
      stronglyMeasurable_const
  exact (hleft.measurable.min hright.measurable).stronglyMeasurable

omit [MeasurableSpace Theta] [Fintype Tau] [DecidableEq Tau]
  [Nonempty Tau] in
/-- A nonempty prefix mean of `[0,1]` values remains in `[0,1]`. -/
theorem forwardPrefixMean_mem_Icc_of_unit
    (x : Nat -> Real) {n : Nat} (hn : 0 < n)
    (hx : ∀ k < n, x k ∈ Set.Icc (0 : Real) 1) :
    forwardPrefixMean x n ∈ Set.Icc (0 : Real) 1 := by
  have hnR : 0 < (n : Real) := Nat.cast_pos.mpr hn
  have hlo : 0 <= ∑ k ∈ Finset.range n, x k :=
    Finset.sum_nonneg fun k hk => (hx k (Finset.mem_range.mp hk)).1
  have hhi : (∑ k ∈ Finset.range n, x k) <= (n : Real) := by
    calc
      (∑ k ∈ Finset.range n, x k) <=
          ∑ _k ∈ Finset.range n, (1 : Real) := by
            apply Finset.sum_le_sum
            intro k hk
            exact (hx k (Finset.mem_range.mp hk)).2
      _ = (n : Real) := by simp
  unfold forwardPrefixMean
  constructor
  · exact div_nonneg hlo hnR.le
  · exact (div_le_one hnR).mpr hhi

omit [MeasurableSpace Theta] [Fintype Tau] [DecidableEq Tau]
  [Nonempty Tau] in
/-- The hybrid Bessel penalty is nonnegative on a `[0,1]` prefix. -/
theorem forwardHybridBesselPenalty_nonneg_of_unit
    (x : Nat -> Real) {n : Nat} (hn : 2 <= n)
    (_hx : ∀ k < n, x k ∈ Set.Icc (0 : Real) 1) :
    0 <= forwardHybridBesselPenalty x n := by
  have hq : 0 <= forwardBesselQ x n := forwardBesselQ_nonneg x n
  unfold forwardHybridBesselPenalty
  apply le_min
  · nlinarith
  · have hden : 0 < (n : Real) - 1 := by
      have : (1 : Real) < (n : Real) := by exact_mod_cast (show 1 < n by omega)
      linarith
    have hratio : 0 <= (n : Real) / ((n : Real) - 1) :=
      div_nonneg (Nat.cast_nonneg n) hden.le
    have hharm : 0 <= ((harmonic (n - 2) : Rat) : Real) := by
      unfold harmonic
      positivity
    positivity

omit [MeasurableSpace Theta] [Fintype Tau] [DecidableEq Tau]
  [Nonempty Tau] in
/-- A simple uniform upper bound on the hybrid penalty. -/
theorem forwardHybridBesselPenalty_le_of_unit
    (x : Nat -> Real) {n : Nat} (hn : 2 <= n)
    (hx : ∀ k < n, x k ∈ Set.Icc (0 : Real) 1) :
    forwardHybridBesselPenalty x n <=
      (1 : Real) / 2 + (3 : Real) / 2 * ((n : Real) / 4) := by
  have hq := forwardBesselQ_le_quarter_card x (by omega) hx
  exact (min_le_left _ _).trans (by nlinarith)

omit [Fintype Tau] [DecidableEq Tau] [Nonempty Tau] in
/-- Joint filtered measurability and pointwise boundedness are sufficient to
mix the actual forward e-processes over an arbitrary probability prior.  All
Fubini integrability obligations are derived here. -/
theorem continuousForwardPredictableMeanBesselPriorProcess_eProcess
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X mean : Theta -> Nat -> Omega -> Real} {lam : Real}
    (hlam : 0 <= lam) (hlam_one : lam < 1)
    (hX_adapted : forall theta, IncrementAdapted F (X theta))
    (hmean_adapted : forall theta, StronglyAdapted F (mean theta))
    (hX_unit : forall theta k omega, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean : forall theta k, mu[X theta k | F k] =ᵐ[mu] mean theta k)
    (hjoint_ambient : forall n, StronglyMeasurable
        (fun q : Omega × Theta =>
          forwardPredictableMeanEmpiricalBernsteinLowerProcess
            (X q.2) (mean q.2) lam n q.1))
    (hjoint : forall n,
      StronglyMeasurable[MeasurableSpace.prod (F n) inferInstance]
        (fun q : Omega × Theta =>
          forwardPredictableMeanEmpiricalBernsteinLowerProcess
            (X q.2) (mean q.2) lam n q.1)) :
    EProcess mu F
      (continuousForwardPredictableMeanBesselPriorProcess
        prior X mean lam) := by
  let M : Theta -> Nat -> Omega -> Real := fun theta =>
    forwardPredictableMeanEmpiricalBernsteinLowerProcess
      (X theta) (mean theta) lam
  have hprod_current (n : Nat) : Integrable
      (fun q : Omega × Theta => M q.2 n q.1) (mu.prod prior) := by
    refine Integrable.of_bound (hjoint_ambient n).aestronglyMeasurable
      (Real.exp (lam * (n : Real))) ?_
    exact Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs, abs_of_pos (by
        dsimp [M]
        rw [forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq]
        positivity)]
      exact forwardPredictableMeanEmpiricalBernsteinLowerProcess_le_exp_card
        hlam hlam_one (hX_unit q.2) (hmean_unit q.2) n q.1
  have hprod_prior (n : Nat) : Integrable
      (fun q : Theta × Omega => M q.1 n q.2) (prior.prod mu) := by
    simpa [Function.comp_def] using (hprod_current n).swap
  have hmix_adapted : StronglyAdapted F
      (continuousForwardPredictableMeanBesselPriorProcess
        prior X mean lam) := by
    intro n
    change StronglyMeasurable[F n]
      (fun omega => ∫ theta, M theta n omega ∂prior)
    letI : MeasurableSpace Omega := F n
    exact StronglyMeasurable.integral_prod_right' (ν := prior) (hjoint n)
  have hmix_integrable (n : Nat) : Integrable
      (continuousForwardPredictableMeanBesselPriorProcess
        prior X mean lam n) mu := by
    exact (hprod_current n).integral_prod_left
  have hrestrict (n : Nat) {s : Set Omega} : Integrable
      (fun q : Omega × Theta => M q.2 n q.1)
      ((mu.restrict s).prod prior) :=
    (hprod_current n).mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hfixed : ∀ᵐ theta ∂prior,
      Supermartingale (M theta) F mu := by
    exact Filter.Eventually.of_forall fun theta =>
      (forwardPredictableMeanEmpiricalBernsteinLowerProcess_eProcess_of_bounded
        hlam hlam_one (hX_adapted theta) (hmean_adapted theta)
        (hX_unit theta) (hmean theta)).supermartingale
  have hsup : Supermartingale
      (continuousForwardPredictableMeanBesselPriorProcess
        prior X mean lam) F mu := by
    change Supermartingale (continuousPriorMixtureProcess prior M) F mu
    exact (continuousPriorMixture_supermartingale
      hmix_adapted hmix_integrable
      (fun n => hprod_prior (n + 1))
      (fun n _s _hs _hfinite => hrestrict (n + 1))
      hprod_current
      (fun n _s _hs _hfinite => hrestrict n)
      hfixed (fun theta n omega => by
        rw [forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq]
        exact (Real.exp_pos _).le)).1
  refine
    { nonneg := ?_
      start_one := ?_
      supermartingale := hsup }
  · intro n omega
    exact integral_nonneg fun theta => by
      dsimp [continuousForwardPredictableMeanBesselPriorProcess,
        continuousPriorMixtureProcess]
      rw [forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq]
      exact (Real.exp_pos _).le
  · intro omega
    simp [continuousForwardPredictableMeanBesselPriorProcess,
      continuousPriorMixtureProcess,
      forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq,
      forwardPredictableQuadratic]

omit [Nonempty Tau] in
/-- The continuous hypothesis-prior mixture followed by a finite declared-tilt
mixture is one actual e-process. -/
theorem continuousForwardPredictableMeanBesselMasterProcess_eProcess
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {weight : Tau -> Real}
    (hweight_nonneg : forall j, 0 <= weight j)
    (hweight_sum : ∑ j, weight j = 1)
    {X mean : Theta -> Nat -> Omega -> Real} {lam : Tau -> Real}
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
    (hjoint : forall j n,
      StronglyMeasurable[MeasurableSpace.prod (F n) inferInstance]
        (fun q : Omega × Theta =>
          forwardPredictableMeanEmpiricalBernsteinLowerProcess
            (X q.2) (mean q.2) (lam j) n q.1)) :
    EProcess mu F
      (continuousForwardPredictableMeanBesselMasterProcess
        prior weight X mean lam) := by
  unfold continuousForwardPredictableMeanBesselMasterProcess
  apply finiteWeightedProcess_eProcess hweight_nonneg hweight_sum
  intro j
  exact continuousForwardPredictableMeanBesselPriorProcess_eProcess
    prior (hlam j) (hlam_one j) hX_adapted hmean_adapted hX_unit
    hmean_unit hmean (hjoint_ambient j) (hjoint j)

omit [Nonempty Tau] in
/-- Ville control for the single continuous-hypothesis, finite-tilt master
process. -/
theorem continuousForwardPredictableMeanBesselExceptionalEvent_mass_le_delta
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {weight : Tau -> Real}
    (hweight_nonneg : forall j, 0 <= weight j)
    (hweight_sum : ∑ j, weight j = 1)
    {X mean : Theta -> Nat -> Omega -> Real} {lam : Tau -> Real}
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
    (hjoint : forall j n,
      StronglyMeasurable[MeasurableSpace.prod (F n) inferInstance]
        (fun q : Omega × Theta =>
          forwardPredictableMeanEmpiricalBernsteinLowerProcess
            (X q.2) (mean q.2) (lam j) n q.1)) :
    mu.real (continuousForwardPredictableMeanBesselExceptionalEvent
      prior weight X mean lam delta) <= delta := by
  have hE := continuousForwardPredictableMeanBesselMasterProcess_eProcess
    prior hweight_nonneg hweight_sum hlam hlam_one hX_adapted
    hmean_adapted hX_unit hmean_unit hmean hjoint_ambient hjoint
  have hville := ville_atTop_maximal_ineq
    (μ := mu) (𝒢 := F)
    (M := continuousForwardPredictableMeanBesselMasterProcess
      prior weight X mean lam)
    hE.supermartingale hE.nonneg (one_div_pos.mpr hdelta)
  rw [hE.integral_start_eq_one] at hville
  unfold continuousForwardPredictableMeanBesselExceptionalEvent
  calc
    mu.real (atTopCrossingEvent
        (continuousForwardPredictableMeanBesselMasterProcess
          prior weight X mean lam) (1 / delta)) =
      delta * ((1 / delta) * mu.real (atTopCrossingEvent
        (continuousForwardPredictableMeanBesselMasterProcess
          prior weight X mean lam) (1 / delta))) := by
        field_simp [hdelta.ne']
    _ <= delta * 1 := mul_le_mul_of_nonneg_left hville hdelta.le
    _ = delta := by ring

omit [Fintype Tau] [DecidableEq Tau] [Nonempty Tau] in
/-- The hybrid-Bessel score is strongly measurable in an arbitrary hypothesis
parameter when all observation and predictable-mean coordinate sections are. -/
theorem stronglyMeasurable_continuousForwardPredictableMeanBesselScore
    (X mean : Theta -> Nat -> Omega -> Real) (lam : Real)
    (n : Nat) (omega : Omega)
    (hX_parameter : forall k,
      StronglyMeasurable (fun theta => X theta k omega))
    (hmean_parameter : forall k,
      StronglyMeasurable (fun theta => mean theta k omega)) :
    StronglyMeasurable (fun theta =>
      continuousForwardPredictableMeanBesselScore
        X mean lam theta n omega) := by
  have hsum : StronglyMeasurable
      (∑ k ∈ Finset.range n, fun theta =>
        mean theta k omega - X theta k omega) :=
    Finset.stronglyMeasurable_sum (Finset.range n) fun k _ =>
      (hmean_parameter k).sub (hX_parameter k)
  have hpen := stronglyMeasurable_forwardHybridBesselPenalty_parameter
    (fun theta k => X theta k omega) n hX_parameter
  have hmeas := (hsum.const_mul lam).sub
    (hpen.const_mul (forwardEmpiricalBernsteinPsi lam))
  convert hmeas using 1
  funext theta
  simp [continuousForwardPredictableMeanBesselScore]

omit [MeasurableSpace Theta] [Fintype Tau] [DecidableEq Tau]
  [Nonempty Tau] in
/-- Pointwise score identity in terms of the two prefix means and the hybrid
Bessel penalty. -/
theorem continuousForwardPredictableMeanBesselScore_eq_prefixMeans
    (X mean : Theta -> Nat -> Omega -> Real) (lam : Real)
    (theta : Theta) {n : Nat} (hn : 0 < n) (omega : Omega) :
    continuousForwardPredictableMeanBesselScore X mean lam theta n omega =
      (n : Real) * lam *
        (forwardPrefixMean (fun k => mean theta k omega) n -
          forwardPrefixMean (fun k => X theta k omega) n) -
      forwardEmpiricalBernsteinPsi lam *
        forwardHybridBesselPenalty (fun k => X theta k omega) n := by
  unfold continuousForwardPredictableMeanBesselScore
  rw [sum_predictableMean_sub_eq_mul_sub_forwardPrefixMean
    (fun k => mean theta k omega) (fun k => X theta k omega) hn]
  ring

omit [Fintype Tau] [DecidableEq Tau] [Nonempty Tau] in
/-- A measurable `[0,1]` parameter family has an integrable prefix mean under
every probability posterior. -/
theorem integrable_forwardPrefixMean_parameter_of_unit
    (posterior : Measure Theta) [IsProbabilityMeasure posterior]
    (x : Theta -> Nat -> Real) {n : Nat} (hn : 0 < n)
    (hx_meas : forall k, StronglyMeasurable (fun theta => x theta k))
    (hx_unit : forall theta k, x theta k ∈ Set.Icc (0 : Real) 1) :
    Integrable (fun theta => forwardPrefixMean (fun k => x theta k) n)
      posterior := by
  refine Integrable.of_bound
    (stronglyMeasurable_forwardPrefixMean_parameter x n hx_meas).aestronglyMeasurable
    1 ?_
  exact Filter.Eventually.of_forall fun theta => by
    have hprefix := forwardPrefixMean_mem_Icc_of_unit
      (fun k => x theta k) hn (fun k hk => hx_unit theta k)
    rw [Real.norm_eq_abs, abs_of_nonneg hprefix.1]
    exact hprefix.2

omit [Fintype Tau] [DecidableEq Tau] [Nonempty Tau] in
/-- The measurable hybrid Bessel penalty is integrable under every
probability posterior. -/
theorem integrable_forwardHybridBesselPenalty_parameter_of_unit
    (posterior : Measure Theta) [IsProbabilityMeasure posterior]
    (x : Theta -> Nat -> Real) {n : Nat} (hn : 2 <= n)
    (hx_meas : forall k, StronglyMeasurable (fun theta => x theta k))
    (hx_unit : forall theta k, x theta k ∈ Set.Icc (0 : Real) 1) :
    Integrable (fun theta =>
      forwardHybridBesselPenalty (fun k => x theta k) n) posterior := by
  let C : Real := (1 : Real) / 2 + (3 : Real) / 2 * ((n : Real) / 4)
  refine Integrable.of_bound
    (stronglyMeasurable_forwardHybridBesselPenalty_parameter
      x n hx_meas).aestronglyMeasurable C ?_
  exact Filter.Eventually.of_forall fun theta => by
    have hnonneg := forwardHybridBesselPenalty_nonneg_of_unit
      (fun k => x theta k) hn (fun k hk => hx_unit theta k)
    have hupper := forwardHybridBesselPenalty_le_of_unit
      (fun k => x theta k) hn (fun k hk => hx_unit theta k)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hupper

omit [Fintype Tau] [DecidableEq Tau] [Nonempty Tau] in
/-- The continuous hybrid-Bessel score is integrable under every probability
posterior from section measurability and pointwise boundedness alone. -/
theorem integrable_continuousForwardPredictableMeanBesselScore
    (posterior : Measure Theta) [IsProbabilityMeasure posterior]
    (X mean : Theta -> Nat -> Omega -> Real) (lam : Real)
    {n : Nat} (hn : 2 <= n) (omega : Omega)
    (hX_parameter : forall k,
      StronglyMeasurable (fun theta => X theta k omega))
    (hmean_parameter : forall k,
      StronglyMeasurable (fun theta => mean theta k omega))
    (hX_unit : forall theta k, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k,
      mean theta k omega ∈ Set.Icc (0 : Real) 1) :
    Integrable (fun theta =>
      continuousForwardPredictableMeanBesselScore
        X mean lam theta n omega) posterior := by
  have hnpos : 0 < n := by omega
  have hmean_int := integrable_forwardPrefixMean_parameter_of_unit
    posterior (fun theta k => mean theta k omega) hnpos
    hmean_parameter hmean_unit
  have hX_int := integrable_forwardPrefixMean_parameter_of_unit
    posterior (fun theta k => X theta k omega) hnpos
    hX_parameter hX_unit
  have hpen_int := integrable_forwardHybridBesselPenalty_parameter_of_unit
    posterior (fun theta k => X theta k omega) hn hX_parameter hX_unit
  have hcombined :=
    ((hmean_int.sub hX_int).const_mul ((n : Real) * lam)).sub
      (hpen_int.const_mul (forwardEmpiricalBernsteinPsi lam))
  refine hcombined.congr ?_
  exact Filter.Eventually.of_forall fun theta => by
    change ((n : Real) * lam *
        (forwardPrefixMean (fun k => mean theta k omega) n -
          forwardPrefixMean (fun k => X theta k omega) n) -
      forwardEmpiricalBernsteinPsi lam *
        forwardHybridBesselPenalty (fun k => X theta k omega) n) =
      continuousForwardPredictableMeanBesselScore
        X mean lam theta n omega
    exact (continuousForwardPredictableMeanBesselScore_eq_prefixMeans
      X mean lam theta hnpos omega).symm

omit [Fintype Tau] [DecidableEq Tau] [Nonempty Tau] in
/-- The prior exponential hybrid score is integrable.  This is derived from
boundedness; it is not an assumed MGF certificate. -/
theorem integrable_exp_continuousForwardPredictableMeanBesselScore
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    (X mean : Theta -> Nat -> Omega -> Real) {lam : Real}
    (hlam : 0 <= lam) (hlam_one : lam < 1)
    {n : Nat} (hn : 2 <= n) (omega : Omega)
    (hX_parameter : forall k,
      StronglyMeasurable (fun theta => X theta k omega))
    (hmean_parameter : forall k,
      StronglyMeasurable (fun theta => mean theta k omega))
    (hX_unit : forall theta k, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k,
      mean theta k omega ∈ Set.Icc (0 : Real) 1) :
    Integrable (fun theta => Real.exp
      (continuousForwardPredictableMeanBesselScore
        X mean lam theta n omega)) prior := by
  have hscore_meas :=
    stronglyMeasurable_continuousForwardPredictableMeanBesselScore
      X mean lam n omega hX_parameter hmean_parameter
  refine Integrable.of_bound
    (Real.continuous_exp.comp_stronglyMeasurable hscore_meas).aestronglyMeasurable
    (Real.exp (lam * (n : Real))) ?_
  exact Filter.Eventually.of_forall fun theta => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hnpos : 0 < n := by omega
    rw [continuousForwardPredictableMeanBesselScore_eq_prefixMeans
      X mean lam theta hnpos omega]
    have hmean_prefix := forwardPrefixMean_mem_Icc_of_unit
      (fun k => mean theta k omega) hnpos
      (fun k hk => hmean_unit theta k)
    have hX_prefix := forwardPrefixMean_mem_Icc_of_unit
      (fun k => X theta k omega) hnpos
      (fun k hk => hX_unit theta k)
    have hpen := forwardHybridBesselPenalty_nonneg_of_unit
      (fun k => X theta k omega) hn (fun k hk => hX_unit theta k)
    have hpsi := forwardEmpiricalBernsteinPsi_nonneg hlam hlam_one
    have hgap :
        forwardPrefixMean (fun k => mean theta k omega) n -
          forwardPrefixMean (fun k => X theta k omega) n <= 1 := by
      linarith [hmean_prefix.2, hX_prefix.1]
    nlinarith [mul_le_mul_of_nonneg_left hgap
      (mul_nonneg (Nat.cast_nonneg n) hlam), mul_nonneg hpsi hpen]

omit [Fintype Tau] [DecidableEq Tau] [Nonempty Tau] in
/-- Exact posterior integral identity for the continuous hybrid-Bessel score. -/
theorem integral_continuousForwardPredictableMeanBesselScore
    (posterior : Measure Theta) [IsProbabilityMeasure posterior]
    (X mean : Theta -> Nat -> Omega -> Real) (lam : Real)
    {n : Nat} (hn : 2 <= n) (omega : Omega)
    (hX_parameter : forall k,
      StronglyMeasurable (fun theta => X theta k omega))
    (hmean_parameter : forall k,
      StronglyMeasurable (fun theta => mean theta k omega))
    (hX_unit : forall theta k, X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k,
      mean theta k omega ∈ Set.Icc (0 : Real) 1) :
    (∫ theta, continuousForwardPredictableMeanBesselScore
        X mean lam theta n omega ∂posterior) =
      (n : Real) * lam *
        ((∫ theta, forwardPrefixMean (fun k => mean theta k omega) n ∂posterior) -
          (∫ theta, forwardPrefixMean (fun k => X theta k omega) n ∂posterior)) -
      forwardEmpiricalBernsteinPsi lam *
        continuousForwardPosteriorHybridBesselPenalty posterior X n omega := by
  have hnpos : 0 < n := by omega
  have hmean_int := integrable_forwardPrefixMean_parameter_of_unit
    posterior (fun theta k => mean theta k omega) hnpos
    hmean_parameter hmean_unit
  have hX_int := integrable_forwardPrefixMean_parameter_of_unit
    posterior (fun theta k => X theta k omega) hnpos
    hX_parameter hX_unit
  have hpen_int := integrable_forwardHybridBesselPenalty_parameter_of_unit
    posterior (fun theta k => X theta k omega) hn hX_parameter hX_unit
  let a : Theta -> Real := fun theta =>
    forwardPrefixMean (fun k => mean theta k omega) n
  let b : Theta -> Real := fun theta =>
    forwardPrefixMean (fun k => X theta k omega) n
  let p : Theta -> Real := fun theta =>
    forwardHybridBesselPenalty (fun k => X theta k omega) n
  have ha : Integrable a posterior := by simpa [a] using hmean_int
  have hb : Integrable b posterior := by simpa [b] using hX_int
  have hp : Integrable p posterior := by simpa [p] using hpen_int
  have hleft : Integrable (fun theta =>
      (n : Real) * lam * (a theta - b theta)) posterior :=
    (ha.sub hb).const_mul ((n : Real) * lam)
  have hright : Integrable (fun theta =>
      forwardEmpiricalBernsteinPsi lam * p theta) posterior :=
    hp.const_mul (forwardEmpiricalBernsteinPsi lam)
  calc
    (∫ theta, continuousForwardPredictableMeanBesselScore
        X mean lam theta n omega ∂posterior) =
      ∫ theta,
        ((n : Real) * lam *
          (forwardPrefixMean (fun k => mean theta k omega) n -
            forwardPrefixMean (fun k => X theta k omega) n) -
          forwardEmpiricalBernsteinPsi lam *
            forwardHybridBesselPenalty (fun k => X theta k omega) n)
        ∂posterior := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun theta =>
            continuousForwardPredictableMeanBesselScore_eq_prefixMeans
              X mean lam theta hnpos omega
    _ = (n : Real) * lam *
        ((∫ theta, forwardPrefixMean (fun k => mean theta k omega) n ∂posterior) -
          (∫ theta, forwardPrefixMean (fun k => X theta k omega) n ∂posterior)) -
        forwardEmpiricalBernsteinPsi lam *
          continuousForwardPosteriorHybridBesselPenalty posterior X n omega := by
      change (∫ theta, (n : Real) * lam * (a theta - b theta) -
          forwardEmpiricalBernsteinPsi lam * p theta ∂posterior) = _
      have hsplit :
          (∫ theta, (n : Real) * lam * (a theta - b theta) -
              forwardEmpiricalBernsteinPsi lam * p theta ∂posterior) =
            (∫ theta, (n : Real) * lam * (a theta - b theta) ∂posterior) -
              ∫ theta, forwardEmpiricalBernsteinPsi lam * p theta ∂posterior := by
        exact integral_sub hleft hright
      rw [hsplit, integral_const_mul, integral_sub ha hb,
        integral_const_mul]
      rfl

omit [Nonempty Tau] [DecidableEq Tau] in
set_option maxHeartbeats 3000000 in
/-- Continuous Donsker--Varadhan inversion for one posterior, time, and
declared tilt.  A boundary failure forces the single actual master e-process
into its canonical crossing event. -/
theorem continuousForwardPredictableMeanBessel_boundaryFailure_mem_exceptionalEvent
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {weight : Tau -> Real} (hweight_pos : forall j, 0 < weight j)
    {X mean : Theta -> Nat -> Omega -> Real} {lam : Tau -> Real}
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
    {j : Tau} {n : Nat} {omega : Omega} (hn : 2 <= n)
    (hfail :
      continuousForwardPredictableMeanBesselBoundary
          prior weight lam X posterior delta j n omega <=
        (∫ theta, forwardPrefixMean (fun k => mean theta k omega) n
          ∂posterior) -
        ∫ theta, forwardPrefixMean (fun k => X theta k omega) n
          ∂posterior) :
    omega ∈ continuousForwardPredictableMeanBesselExceptionalEvent
      prior weight X mean lam delta := by
  have hnpos : 0 < n := by omega
  have hdenpos : 0 < (n : Real) * lam j :=
    mul_pos (Nat.cast_pos.mpr hnpos) (hlam j)
  unfold continuousForwardPredictableMeanBesselBoundary at hfail
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
      continuousForwardPredictableMeanBesselPriorProcess
        prior X mean (lam j) n omega := by
    dsimp [moment, continuousForwardPredictableMeanBesselPriorProcess,
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
      continuousForwardPredictableMeanBesselPriorProcess
        prior X mean (lam j) n omega :=
    hthreshold_le_moment.trans hmoment_le_inner
  have hweighted :
      weight j * (1 / (delta * weight j)) <=
        weight j * continuousForwardPredictableMeanBesselPriorProcess
          prior X mean (lam j) n omega :=
    mul_le_mul_of_nonneg_left hinner (hweight_pos j).le
  have hsingle :
      weight j * continuousForwardPredictableMeanBesselPriorProcess
          prior X mean (lam j) n omega <=
        continuousForwardPredictableMeanBesselMasterProcess
          prior weight X mean lam n omega := by
    unfold continuousForwardPredictableMeanBesselMasterProcess
      finiteWeightedProcess
    exact Finset.single_le_sum
      (f := fun k => weight k *
        continuousForwardPredictableMeanBesselPriorProcess
          prior X mean (lam k) n omega)
      (fun k _ => mul_nonneg (hweight_pos k).le
        (integral_nonneg fun theta => by
          change 0 <= forwardPredictableMeanEmpiricalBernsteinLowerProcess
            (X theta) (mean theta) (lam k) n omega
          rw [forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq]
          exact (Real.exp_pos _).le))
      (Finset.mem_univ j)
  rw [show weight j * (1 / (delta * weight j)) = 1 / delta by
    field_simp [hdelta.ne', (hweight_pos j).ne']] at hweighted
  unfold continuousForwardPredictableMeanBesselExceptionalEvent
  exact ⟨n, hweighted.trans hsingle⟩

omit [Nonempty Tau] [DecidableEq Tau] in
/-- Outside the canonical crossing event, every eligible continuous posterior
satisfies every declared tilt boundary at every time `n >= 2`. -/
theorem continuousForwardPredictableMeanBessel_allPosteriors_of_not_mem
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {weight : Tau -> Real} (hweight_pos : forall j, 0 < weight j)
    {X mean : Theta -> Nat -> Omega -> Real} {lam : Tau -> Real}
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
    (homega : omega ∉ continuousForwardPredictableMeanBesselExceptionalEvent
      prior weight X mean lam delta) :
    forall j : Tau, forall posterior : Measure Theta,
      IsProbabilityMeasure posterior -> posterior ≪ prior ->
      Integrable (llr posterior prior) posterior ->
      forall n : Nat, 2 <= n ->
        (∫ theta, forwardPrefixMean (fun k => mean theta k omega) n
          ∂posterior) <
        (∫ theta, forwardPrefixMean (fun k => X theta k omega) n
          ∂posterior) +
          continuousForwardPredictableMeanBesselBoundary
            prior weight lam X posterior delta j n omega := by
  intro j posterior hposterior hposterior_prior hllr n hn
  letI : IsProbabilityMeasure posterior := hposterior
  apply lt_of_not_ge
  intro hfail
  apply homega
  exact continuousForwardPredictableMeanBessel_boundaryFailure_mem_exceptionalEvent
    prior hweight_pos hdelta hlam hlam_one hX_unit hmean_unit
    hX_parameter hmean_parameter hjoint_ambient posterior
    hposterior_prior hllr hn (by linarith)

omit [Nonempty Tau] in
/-- One outer-probability event carries the continuous-hypothesis
empirical-Bernstein PAC-Bayes boundary simultaneously for all eligible times,
posteriors, and declared finite tilt atoms. -/
theorem exists_continuousForwardPredictableMeanBesselPACBayes_event
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {weight : Tau -> Real} (hweight_pos : forall j, 0 < weight j)
    (hweight_sum : ∑ j, weight j = 1)
    {X mean : Theta -> Nat -> Omega -> Real} {lam : Tau -> Real}
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
        ∀ omega ∈ goodEvent, forall j : Tau,
          forall posterior : Measure Theta,
            IsProbabilityMeasure posterior -> posterior ≪ prior ->
            Integrable (llr posterior prior) posterior ->
            forall n : Nat, 2 <= n ->
              (∫ theta, forwardPrefixMean
                  (fun k => mean theta k omega) n ∂posterior) <
              (∫ theta, forwardPrefixMean
                  (fun k => X theta k omega) n ∂posterior) +
                continuousForwardPredictableMeanBesselBoundary
                  prior weight lam X posterior delta j n omega := by
  let badEvent := continuousForwardPredictableMeanBesselExceptionalEvent
    prior weight X mean lam delta
  refine ⟨badEventᶜ, ?_, ?_⟩
  · simpa [badEvent] using
      (continuousForwardPredictableMeanBesselExceptionalEvent_mass_le_delta
        prior (fun j => (hweight_pos j).le) hweight_sum hdelta
        (fun j => (hlam j).le) hlam_one hX_adapted hmean_adapted
        hX_unit hmean_unit hmean hjoint_ambient hjoint_filtered)
  · intro omega homega
    exact continuousForwardPredictableMeanBessel_allPosteriors_of_not_mem
      prior hweight_pos hdelta hlam hlam_one hX_unit hmean_unit
      hX_parameter hmean_parameter hjoint_ambient homega

end

end FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes
