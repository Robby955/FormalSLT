/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.AnytimeValid.SingularFractionObservableLIL
import FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes

/-!
# Continuous-posterior singular-fraction PAC-Bayes bounds

This module mixes the actual lower-tail predictable-mean empirical-Bernstein
processes jointly over an arbitrary measurable hypothesis prior and the
singular fraction family `u ↦ exp (-1 / u)`.  One Ville event then controls
every reporting time, every eligible posterior chosen after observing the
path, and every admissible target fraction.

The final corollary is an observable one-sided LIL-order bound for the
posterior-averaged conditional prefix mean encountered along the monitored
stream.  It is not a population, future, deployment, or stationary-risk
statement.  The scalar fraction mixture is not a posterior over arbitrary
predictable betting strategies, and no such strategy-uniform claim is made.

The two joint-measurability arguments are a deliberate caller interface.
`hjoint_ambient n` must establish strong measurability of the actual process
on the ambient product sigma algebra of paths, fractions, and hypotheses;
`hjoint_filtered n` must establish the corresponding fact using `F n` on the
path coordinate.  Per-hypothesis adaptedness does not imply either joint fact
for an arbitrary measurable hypothesis space.  Concrete callers are
responsible for deriving them from their jointly measurable observation and
conditional-mean families.  The measurable singular-fraction map is already
composed into the exact function displayed in both hypotheses.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayes.ContinuousChangeOfMeasure
open FormalSLT.PACBayes.TimeUniformContinuous
open FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes
open scoped BigOperators ENNReal

namespace FormalSLT.PACBayes.ContinuousSingularFractionBesselPACBayes

noncomputable section

variable {Theta Omega : Type*} [MeasurableSpace Theta]
  {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
  {F : Filtration Nat mOmega}

/-- Joint hypothesis--fraction prior mixture of the actual lower-tail
predictable-mean empirical-Bernstein processes. -/
def continuousSingularFractionBesselMasterProcess
    (prior : Measure Theta) (X mean : Theta -> Nat -> Omega -> Real) :
    Nat -> Omega -> Real :=
  continuousPriorMixtureProcess ((uniformTiltPrior 0 1).prod prior) fun p =>
    forwardPredictableMeanEmpiricalBernsteinLowerProcess
      (X p.2) (mean p.2) (singularFraction p.1)

/-- The one Ville crossing event for the joint hypothesis--fraction mixture. -/
def continuousSingularFractionBesselExceptionalEvent
    (prior : Measure Theta) (X mean : Theta -> Nat -> Omega -> Real)
    (delta : Real) : Set Omega :=
  {omega | exists n : Nat, 0 < n ∧
    1 / delta <=
      continuousSingularFractionBesselMasterProcess
        prior X mean n omega}

/-- Explicit posterior deviation boundary at one target fraction.  The
hypothesis KL cost and the log price of the positive-mass singular window are
both paid inside the continuous mixture. -/
def continuousSingularFractionBesselBoundary
    (prior : Measure Theta) (X : Theta -> Nat -> Omega -> Real)
    (posterior : Measure Theta) (delta lam : Real)
    (n : Nat) (omega : Omega) : Real :=
  (lam * continuousForwardPosteriorHybridBesselPenalty
      posterior X n omega +
    Real.exp 1 / lam *
      ((InformationTheory.klDiv posterior prior).toReal +
        Real.log
          (singularFractionLogScale lam *
            (singularFractionLogScale lam + 1) / delta))) /
    (n : Real)

/-- Confidence level obtained by absorbing the posterior KL cost into the
confidence parameter of the scalar singular-fraction boundary. -/
def continuousSingularFractionBesselEffectiveConfidence
    (prior posterior : Measure Theta) (delta : Real) : Real :=
  delta * Real.exp (-(InformationTheory.klDiv posterior prior).toReal)

/-- The KL-adjusted confidence level remains positive. -/
theorem continuousSingularFractionBesselEffectiveConfidence_pos
    (prior posterior : Measure Theta) {delta : Real} (hdelta : 0 < delta) :
    0 < continuousSingularFractionBesselEffectiveConfidence
      prior posterior delta := by
  exact mul_pos hdelta (Real.exp_pos _)

/-- A probability-level confidence budget remains at most one after the KL
adjustment. -/
theorem continuousSingularFractionBesselEffectiveConfidence_le_one
    (prior posterior : Measure Theta) {delta : Real}
    (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    continuousSingularFractionBesselEffectiveConfidence
        prior posterior delta <= 1 := by
  have hK : 0 <= (InformationTheory.klDiv posterior prior).toReal :=
    (InformationTheory.klDiv posterior prior).toReal_nonneg
  calc
    continuousSingularFractionBesselEffectiveConfidence
        prior posterior delta <= delta * 1 := by
      unfold continuousSingularFractionBesselEffectiveConfidence
      exact mul_le_mul_of_nonneg_left
        ((Real.exp_le_one_iff).2 (by linarith)) hdelta.le
    _ <= 1 := by simpa using hdelta_one

/-- Absorbing KL into the confidence level exactly reproduces the PAC-Bayes
logarithmic price. -/
theorem continuousSingularFractionBessel_log_effectiveConfidence
    (prior posterior : Measure Theta) {delta A : Real}
    (hdelta : 0 < delta) (hA : 0 < A) :
    Real.log
        (A / continuousSingularFractionBesselEffectiveConfidence
          prior posterior delta) =
      (InformationTheory.klDiv posterior prior).toReal +
        Real.log (A / delta) := by
  unfold continuousSingularFractionBesselEffectiveConfidence
  rw [Real.log_div hA.ne' (mul_ne_zero hdelta.ne' (Real.exp_ne_zero _)),
    Real.log_mul hdelta.ne' (Real.exp_ne_zero _), Real.log_exp,
    Real.log_div hA.ne' hdelta.ne']
  ring

private theorem integrable_continuousSingularFractionBessel_parameter
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X mean : Theta -> Nat -> Omega -> Real}
    (hX_unit : forall theta k omega,
      X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hjoint_ambient : forall n, StronglyMeasurable
      (fun q : Omega × (Real × Theta) =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2.2) (mean q.2.2) (singularFraction q.2.1) n q.1))
    (n : Nat) (omega : Omega) :
    Integrable
      (fun p : Real × Theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X p.2) (mean p.2) (singularFraction p.1) n omega)
      ((uniformTiltPrior 0 1).prod prior) := by
  letI : IsProbabilityMeasure (uniformTiltPrior 0 1) :=
    uniformTiltPrior_isProbabilityMeasure (by norm_num)
  have hsection : StronglyMeasurable (fun p : Real × Theta =>
      forwardPredictableMeanEmpiricalBernsteinLowerProcess
        (X p.2) (mean p.2) (singularFraction p.1) n omega) :=
    (hjoint_ambient n).comp_measurable
      (measurable_const.prodMk measurable_id)
  refine Integrable.of_bound hsection.aestronglyMeasurable
    (Real.exp (n : Real)) ?_
  have hsupp : ∀ᵐ p : Real × Theta ∂((uniformTiltPrior 0 1).prod prior),
      p.1 ∈ Set.Icc (0 : Real) 1 := by
    exact (Measure.quasiMeasurePreserving_fst).ae
      (uniformTiltPrior_ae_mem_Icc
        (lam0 := (0 : Real)) (lam1 := 1))
  filter_upwards [hsupp] with p hp
  rw [Real.norm_eq_abs, abs_of_pos (by
    rw [forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq]
    positivity)]
  calc
    forwardPredictableMeanEmpiricalBernsteinLowerProcess
        (X p.2) (mean p.2) (singularFraction p.1) n omega <=
        Real.exp (singularFraction p.1 * (n : Real)) :=
      forwardPredictableMeanEmpiricalBernsteinLowerProcess_le_exp_card
        (singularFraction_nonneg p.1)
        (singularFraction_lt_one_of_mem_unit hp)
        (hX_unit p.2) (hmean_unit p.2) n omega
    _ <= Real.exp (n : Real) := by
      apply Real.exp_le_exp.mpr
      have htheta_le : singularFraction p.1 <= 1 :=
        (singularFraction_lt_one_of_mem_unit hp).le
      have hn : 0 <= (n : Real) := Nat.cast_nonneg n
      nlinarith [mul_le_mul_of_nonneg_right htheta_le hn]

/-- Bounded adapted observations and explicit joint measurability make the
joint hypothesis--fraction prior mixture an actual e-process.

The caller supplies both product-space obligations: `hjoint_ambient` for the
ambient path sigma algebra and `hjoint_filtered` for `F n`.  These assumptions
refer to the actual process after composition with `singularFraction`; they
are not inferred from separate per-hypothesis measurability claims. -/
theorem continuousSingularFractionBesselMasterProcess_eProcess
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X mean : Theta -> Nat -> Omega -> Real}
    (hX_adapted : forall theta, IncrementAdapted F (X theta))
    (hmean_adapted : forall theta, StronglyAdapted F (mean theta))
    (hX_unit : forall theta k omega,
      X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean : forall theta k,
      mu[X theta k | F k] =ᵐ[mu] mean theta k)
    (hjoint_ambient : forall n, StronglyMeasurable
      (fun q : Omega × (Real × Theta) =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2.2) (mean q.2.2) (singularFraction q.2.1) n q.1))
    (hjoint_filtered : forall n,
      StronglyMeasurable[MeasurableSpace.prod (F n) inferInstance]
        (fun q : Omega × (Real × Theta) =>
          forwardPredictableMeanEmpiricalBernsteinLowerProcess
            (X q.2.2) (mean q.2.2)
              (singularFraction q.2.1) n q.1)) :
    EProcess mu F
      (continuousSingularFractionBesselMasterProcess prior X mean) := by
  let tiltPrior : Measure Real := uniformTiltPrior 0 1
  let parameterPrior : Measure (Real × Theta) := tiltPrior.prod prior
  let M : (Real × Theta) -> Nat -> Omega -> Real := fun p =>
    forwardPredictableMeanEmpiricalBernsteinLowerProcess
      (X p.2) (mean p.2) (singularFraction p.1)
  letI : IsProbabilityMeasure tiltPrior := by
    dsimp [tiltPrior]
    exact uniformTiltPrior_isProbabilityMeasure (by norm_num)
  letI : IsProbabilityMeasure parameterPrior := by
    dsimp [parameterPrior]
    infer_instance
  have hprod_current (n : Nat) : Integrable
      (fun q : Omega × (Real × Theta) => M q.2 n q.1)
      (mu.prod parameterPrior) := by
    refine Integrable.of_bound (hjoint_ambient n).aestronglyMeasurable
      (Real.exp (n : Real)) ?_
    have hsupp : ∀ᵐ q : Omega × (Real × Theta) ∂(mu.prod parameterPrior),
        q.2.1 ∈ Set.Icc (0 : Real) 1 := by
      have hsupp_parameter : ∀ᵐ p : Real × Theta ∂parameterPrior,
          p.1 ∈ Set.Icc (0 : Real) 1 := by
        exact (Measure.quasiMeasurePreserving_fst).ae
          (by simpa [tiltPrior] using
            (uniformTiltPrior_ae_mem_Icc
              (lam0 := (0 : Real)) (lam1 := 1)))
      exact (Measure.quasiMeasurePreserving_snd).ae hsupp_parameter
    filter_upwards [hsupp] with q hq
    rw [Real.norm_eq_abs, abs_of_pos (by
      dsimp [M]
      rw [forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq]
      positivity)]
    calc
      M q.2 n q.1 <=
          Real.exp (singularFraction q.2.1 * (n : Real)) := by
        dsimp [M]
        exact forwardPredictableMeanEmpiricalBernsteinLowerProcess_le_exp_card
          (singularFraction_nonneg q.2.1)
          (singularFraction_lt_one_of_mem_unit hq)
          (hX_unit q.2.2) (hmean_unit q.2.2) n q.1
      _ <= Real.exp (n : Real) := by
        apply Real.exp_le_exp.mpr
        have htheta_le : singularFraction q.2.1 <= 1 :=
          (singularFraction_lt_one_of_mem_unit hq).le
        have hn : 0 <= (n : Real) := Nat.cast_nonneg n
        nlinarith [mul_le_mul_of_nonneg_right htheta_le hn]
  have hprod_parameter (n : Nat) : Integrable
      (fun q : (Real × Theta) × Omega => M q.1 n q.2)
      (parameterPrior.prod mu) := by
    simpa [Function.comp_def] using (hprod_current n).swap
  have hmix_adapted : StronglyAdapted F
      (continuousSingularFractionBesselMasterProcess prior X mean) := by
    intro n
    change StronglyMeasurable[F n]
      (fun omega => ∫ p, M p n omega ∂parameterPrior)
    letI : MeasurableSpace Omega := F n
    exact StronglyMeasurable.integral_prod_right'
      (ν := parameterPrior) (hjoint_filtered n)
  have hmix_integrable (n : Nat) : Integrable
      (continuousSingularFractionBesselMasterProcess
        prior X mean n) mu := by
    exact (hprod_current n).integral_prod_left
  have hrestrict (n : Nat) {s : Set Omega} : Integrable
      (fun q : Omega × (Real × Theta) => M q.2 n q.1)
      ((mu.restrict s).prod parameterPrior) :=
    (hprod_current n).mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hfixed : ∀ᵐ p ∂parameterPrior, Supermartingale (M p) F mu := by
    have hsupp : ∀ᵐ p : Real × Theta ∂parameterPrior,
        p.1 ∈ Set.Icc (0 : Real) 1 := by
      exact (Measure.quasiMeasurePreserving_fst).ae
        (by simpa [tiltPrior] using
          (uniformTiltPrior_ae_mem_Icc
            (lam0 := (0 : Real)) (lam1 := 1)))
    filter_upwards [hsupp] with p hp
    exact
      (forwardPredictableMeanEmpiricalBernsteinLowerProcess_eProcess_of_bounded
        (singularFraction_nonneg p.1)
        (singularFraction_lt_one_of_mem_unit hp)
        (hX_adapted p.2) (hmean_adapted p.2)
        (hX_unit p.2) (hmean p.2)).supermartingale
  have hsup : Supermartingale
      (continuousSingularFractionBesselMasterProcess prior X mean) F mu := by
    change Supermartingale
      (continuousPriorMixtureProcess parameterPrior M) F mu
    exact (continuousPriorMixture_supermartingale
      hmix_adapted hmix_integrable
      (fun n => hprod_parameter (n + 1))
      (fun n _s _hs _hfinite => hrestrict (n + 1))
      hprod_current
      (fun n _s _hs _hfinite => hrestrict n)
      hfixed (fun p n omega => by
        rw [forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq]
        exact (Real.exp_pos _).le)).1
  refine
    { nonneg := ?_
      start_one := ?_
      supermartingale := hsup }
  · intro n omega
    change 0 <= ∫ p, M p n omega ∂parameterPrior
    exact integral_nonneg fun p => by
      dsimp [M]
      rw [forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq]
      exact (Real.exp_pos _).le
  · intro omega
    simp [continuousSingularFractionBesselMasterProcess,
      continuousPriorMixtureProcess,
      forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq,
      forwardPredictableQuadratic]

/-- The joint hypothesis--fraction mixture has one exceptional event of outer
mass at most `delta`.  Its joint-measurability arguments are exactly the two
caller-supplied obligations consumed by
`continuousSingularFractionBesselMasterProcess_eProcess`. -/
theorem continuousSingularFractionBesselExceptionalEvent_mass_le_delta
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X mean : Theta -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta)
    (hX_adapted : forall theta, IncrementAdapted F (X theta))
    (hmean_adapted : forall theta, StronglyAdapted F (mean theta))
    (hX_unit : forall theta k omega,
      X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean : forall theta k,
      mu[X theta k | F k] =ᵐ[mu] mean theta k)
    (hjoint_ambient : forall n, StronglyMeasurable
      (fun q : Omega × (Real × Theta) =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2.2) (mean q.2.2) (singularFraction q.2.1) n q.1))
    (hjoint_filtered : forall n,
      StronglyMeasurable[MeasurableSpace.prod (F n) inferInstance]
        (fun q : Omega × (Real × Theta) =>
          forwardPredictableMeanEmpiricalBernsteinLowerProcess
            (X q.2.2) (mean q.2.2)
              (singularFraction q.2.1) n q.1)) :
    mu.real (continuousSingularFractionBesselExceptionalEvent
      prior X mean delta) <= delta := by
  letI : IsProbabilityMeasure (uniformTiltPrior 0 1) :=
    uniformTiltPrior_isProbabilityMeasure (by norm_num)
  letI : IsProbabilityMeasure ((uniformTiltPrior 0 1).prod prior) := by
    infer_instance
  have hE := continuousSingularFractionBesselMasterProcess_eProcess
    prior hX_adapted hmean_adapted hX_unit hmean_unit hmean
      hjoint_ambient hjoint_filtered
  change mu.real {omega | exists n : Nat, 0 < n ∧
    1 / delta <=
      continuousSingularFractionBesselMasterProcess
        prior X mean n omega} <= delta
  exact continuousPriorMixture_crossing_bound hdelta
    hE.supermartingale hE.nonneg (fun _p omega => by
      simp [forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq,
        forwardPredictableQuadratic])

set_option maxHeartbeats 3000000 in
/-- A failure of one posterior boundary forces the single joint
hypothesis--fraction mixture across its Ville threshold. -/
theorem continuousSingularFractionBessel_boundaryFailure_mem_exceptionalEvent
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X mean : Theta -> Nat -> Omega -> Real} {delta lam : Real}
    (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (hlam : 0 < lam) (hlam_exp : lam <= Real.exp (-1))
    (hX_unit : forall theta k omega,
      X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hX_parameter : forall k omega,
      StronglyMeasurable (fun theta => X theta k omega))
    (hmean_parameter : forall k omega,
      StronglyMeasurable (fun theta => mean theta k omega))
    (hjoint_ambient : forall n, StronglyMeasurable
      (fun q : Omega × (Real × Theta) =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2.2) (mean q.2.2) (singularFraction q.2.1) n q.1))
    (posterior : Measure Theta) [IsProbabilityMeasure posterior]
    (hposterior_prior : posterior ≪ prior)
    (hllr : Integrable (llr posterior prior) posterior)
    {n : Nat} {omega : Omega} (hn : 2 <= n)
    (hfail :
      continuousSingularFractionBesselBoundary
          prior X posterior delta lam n omega <=
        (∫ theta, forwardPrefixMean
            (fun k => mean theta k omega) n ∂posterior) -
          ∫ theta, forwardPrefixMean
            (fun k => X theta k omega) n ∂posterior) :
    omega ∈ continuousSingularFractionBesselExceptionalEvent
      prior X mean delta := by
  let tiltPrior : Measure Real := uniformTiltPrior 0 1
  let K : Real := (InformationTheory.klDiv posterior prior).toReal
  let Q : Real := continuousForwardPosteriorHybridBesselPenalty
    posterior X n omega
  let gap : Real :=
    (∫ theta, forwardPrefixMean
        (fun k => mean theta k omega) n ∂posterior) -
      ∫ theta, forwardPrefixMean
        (fun k => X theta k omega) n ∂posterior
  let G : Real := (n : Real) * gap
  let L : Real := singularFractionLogScale lam
  let A : Real := L * (L + 1)
  let budget : Real := K + Real.log (A / delta)
  letI : IsProbabilityMeasure tiltPrior := by
    dsimp [tiltPrior]
    exact uniformTiltPrior_isProbabilityMeasure (by norm_num)
  have hnpos : 0 < n := by omega
  have hnRpos : 0 < (n : Real) := Nat.cast_pos.mpr hnpos
  have hL : 1 <= L := by
    simpa [L] using one_le_singularFractionLogScale hlam hlam_exp
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos (zero_lt_one.trans_le hL) (by linarith)
  have hratio : 1 < A / delta := by
    apply (lt_div_iff₀ hdelta).2
    have hAtwo : 2 <= A := by
      dsimp [A]
      nlinarith
    linarith
  have hlog : 0 < Real.log (A / delta) := Real.log_pos hratio
  have hK : 0 <= K := by
    dsimp [K]
    exact (InformationTheory.klDiv posterior prior).toReal_nonneg
  have hbudget : 0 < budget := by
    dsimp [budget]
    linarith
  have hQ : 0 <= Q := by
    dsimp [Q, continuousForwardPosteriorHybridBesselPenalty]
    exact integral_nonneg fun theta =>
      forwardHybridBesselPenalty_nonneg_of_unit
        (fun k => X theta k omega) hn
        (fun k _hk => hX_unit theta k omega)
  have hmain :
      lam * Q + Real.exp 1 / lam * budget <= G := by
    unfold continuousSingularFractionBesselBoundary at hfail
    have hmul := (div_le_iff₀ hnRpos).mp hfail
    have hmul' : lam * Q + Real.exp 1 / lam * budget <=
        (n : Real) * gap := by
      simpa [K, Q, gap, L, A, budget, mul_comm] using hmul
    simpa [G] using hmul'
  have hgap : Real.exp 1 / lam * budget <= G - lam * Q := by
    linarith
  have hgap_nonneg : 0 <= G - lam * Q := by
    have : 0 < Real.exp 1 / lam * budget := by positivity
    linarith
  have hscaled : budget <= lam / Real.exp 1 * (G - lam * Q) := by
    calc
      budget = lam / Real.exp 1 * (Real.exp 1 / lam * budget) := by
        field_simp [hlam.ne', Real.exp_ne_zero]
      _ <= lam / Real.exp 1 * (G - lam * Q) :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
  have hparameter_int :=
    integrable_continuousSingularFractionBessel_parameter
      prior hX_unit hmean_unit hjoint_ambient n omega
  have houter_int : Integrable
      (fun u => continuousForwardPredictableMeanBesselPriorProcess
        prior X mean (singularFraction u) n omega) tiltPrior := by
    simpa [tiltPrior, continuousForwardPredictableMeanBesselPriorProcess,
      continuousPriorMixtureProcess] using hparameter_int.integral_prod_left
  have hlower (u : Real) (hu : u ∈ singularFractionWindow lam) :
      A / delta <=
        continuousForwardPredictableMeanBesselPriorProcess
          prior X mean (singularFraction u) n omega := by
    let t : Real := singularFraction u
    have hmap := singularFractionWindow_maps hlam hlam_exp hu
    have ht0 : 0 <= t := by
      simpa [t] using singularFraction_nonneg u
    have htlam : t <= lam := by simpa [t] using hmap.2
    have htexp : t <= Real.exp (-1) := htlam.trans hlam_exp
    have ht1 : t < 1 :=
      htexp.trans_lt (Real.exp_lt_one_iff.mpr (by norm_num))
    have ht_lower : lam / Real.exp 1 <= t := by simpa [t] using hmap.1
    have hpsi := forwardEmpiricalBernsteinPsi_le_sq_of_le_exp_neg_one
      ht0 htexp
    have ht_sq : t ^ 2 <= lam * t := by nlinarith
    have hlinear : lam / Real.exp 1 * (G - lam * Q) <=
        t * (G - lam * Q) :=
      mul_le_mul_of_nonneg_right ht_lower hgap_nonneg
    have hpenalty : forwardEmpiricalBernsteinPsi t * Q <=
        (lam * t) * Q :=
      (mul_le_mul_of_nonneg_right hpsi hQ).trans
        (mul_le_mul_of_nonneg_right ht_sq hQ)
    have hscore_lower : budget <=
        ∫ theta, continuousForwardPredictableMeanBesselScore
          X mean t theta n omega ∂posterior := by
      have hidentity := integral_continuousForwardPredictableMeanBesselScore
        posterior X mean t hn omega
        (fun k => hX_parameter k omega)
        (fun k => hmean_parameter k omega)
        (fun theta k => hX_unit theta k omega)
        (fun theta k => hmean_unit theta k omega)
      rw [hidentity]
      calc
        budget <= lam / Real.exp 1 * (G - lam * Q) := hscaled
        _ <= t * (G - lam * Q) := hlinear
        _ <= (n : Real) * t * gap -
            forwardEmpiricalBernsteinPsi t * Q := by
          dsimp [G]
          nlinarith
    have hscore_int := integrable_continuousForwardPredictableMeanBesselScore
      posterior X mean t hn omega
      (fun k => hX_parameter k omega)
      (fun k => hmean_parameter k omega)
      (fun theta k => hX_unit theta k omega)
      (fun theta k => hmean_unit theta k omega)
    have hexp_int :=
      integrable_exp_continuousForwardPredictableMeanBesselScore
        prior X mean ht0 ht1 hn omega
        (fun k => hX_parameter k omega)
        (fun k => hmean_parameter k omega)
        (fun theta k => hX_unit theta k omega)
        (fun theta k => hmean_unit theta k omega)
    have hdv := continuous_donsker_varadhan
      posterior prior hposterior_prior
      (fun theta => continuousForwardPredictableMeanBesselScore
        X mean t theta n omega)
      hexp_int hscore_int hllr
    let moment : Real := ∫ theta, Real.exp
      (continuousForwardPredictableMeanBesselScore
        X mean t theta n omega) ∂prior
    have hmoment_pos : 0 < moment := by
      dsimp [moment]
      exact integral_exp_pos hexp_int
    have hlog_moment : Real.log (A / delta) <= Real.log moment := by
      change (∫ theta, continuousForwardPredictableMeanBesselScore
        X mean t theta n omega ∂posterior) <=
          K + Real.log moment at hdv
      dsimp [budget] at hscore_lower
      linarith
    have hthreshold : A / delta <= moment :=
      (Real.log_le_log_iff (div_pos hA hdelta) hmoment_pos).mp hlog_moment
    have hprocess_section : StronglyMeasurable (fun theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X theta) (mean theta) t n omega) := by
      exact (hjoint_ambient n).comp_measurable
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hprocess_int : Integrable (fun theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X theta) (mean theta) t n omega) prior := by
      refine Integrable.of_bound hprocess_section.aestronglyMeasurable
        (Real.exp (n : Real)) ?_
      exact Filter.Eventually.of_forall fun theta => by
        rw [Real.norm_eq_abs, abs_of_pos (by
          rw [forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq]
          positivity)]
        calc
          forwardPredictableMeanEmpiricalBernsteinLowerProcess
              (X theta) (mean theta) t n omega <=
              Real.exp (t * (n : Real)) :=
            forwardPredictableMeanEmpiricalBernsteinLowerProcess_le_exp_card
              ht0 ht1 (hX_unit theta) (hmean_unit theta) n omega
          _ <= Real.exp (n : Real) := by
            apply Real.exp_le_exp.mpr
            nlinarith [mul_le_mul_of_nonneg_right ht1.le
              (Nat.cast_nonneg n)]
    have hmoment_le_inner : moment <=
        continuousForwardPredictableMeanBesselPriorProcess
          prior X mean t n omega := by
      dsimp [moment, continuousForwardPredictableMeanBesselPriorProcess,
        continuousPriorMixtureProcess]
      apply integral_mono hexp_int hprocess_int
      intro theta
      change forwardPredictableMeanEmpiricalBernsteinLowerBesselEnvelope
          (X theta) (mean theta) t n omega <=
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X theta) (mean theta) t n omega
      exact forwardPredictableMeanEmpiricalBernsteinLowerBesselEnvelope_le_process
        ht0 ht1 hn omega (fun k _hk => hX_unit theta k omega)
    exact hthreshold.trans (by simpa [t] using hmoment_le_inner)
  have hmix := continuousPriorMixtureProcess_competes_of_priorMass
    tiltPrior (measurableSet_singularFractionWindow lam)
    (M := fun u => continuousForwardPredictableMeanBesselPriorProcess
      prior X mean (singularFraction u))
    (c := A / delta) (n := n) (ω := omega)
    (fun u => by
      change 0 <= ∫ theta,
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X theta) (mean theta) (singularFraction u) n omega ∂prior
      exact integral_nonneg fun theta => by
        change 0 <= forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X theta) (mean theta) (singularFraction u) n omega
        rw [forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq]
        exact (Real.exp_pos _).le)
    houter_int hlower
  have hmass := singularFractionWindow_uniformTiltPrior_real hlam hlam_exp
  have hmaster_eq :
      continuousSingularFractionBesselMasterProcess
          prior X mean n omega =
        continuousPriorMixtureProcess tiltPrior
          (fun u => continuousForwardPredictableMeanBesselPriorProcess
            prior X mean (singularFraction u)) n omega := by
    unfold continuousSingularFractionBesselMasterProcess
      continuousForwardPredictableMeanBesselPriorProcess
      continuousPriorMixtureProcess
    simpa [tiltPrior] using integral_prod
      (fun p : Real × Theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X p.2) (mean p.2) (singularFraction p.1) n omega)
      hparameter_int
  have hcross : 1 / delta <=
      continuousSingularFractionBesselMasterProcess
        prior X mean n omega := by
    rw [hmass] at hmix
    have hA_def : singularFractionLogScale lam *
        (singularFractionLogScale lam + 1) = A := rfl
    rw [hA_def] at hmix
    have hid : (1 / A) * (A / delta) = 1 / delta := by
      field_simp [hA.ne', hdelta.ne']
    rw [hid, ← hmaster_eq] at hmix
    exact hmix
  exact ⟨n, hnpos, hcross⟩

/-- Outside the one joint crossing event, every eligible posterior satisfies
the explicit singular-fraction boundary at every time and every admissible
target fraction.  The posterior is quantified after the path is observed. -/
theorem continuousSingularFractionBessel_allPosteriors_allFractions_of_not_mem
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X mean : Theta -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (hX_unit : forall theta k omega,
      X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hX_parameter : forall k omega,
      StronglyMeasurable (fun theta => X theta k omega))
    (hmean_parameter : forall k omega,
      StronglyMeasurable (fun theta => mean theta k omega))
    (hjoint_ambient : forall n, StronglyMeasurable
      (fun q : Omega × (Real × Theta) =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2.2) (mean q.2.2) (singularFraction q.2.1) n q.1))
    {omega : Omega}
    (homega : omega ∉ continuousSingularFractionBesselExceptionalEvent
      prior X mean delta) :
    forall posterior : Measure Theta,
      IsProbabilityMeasure posterior -> posterior ≪ prior ->
      Integrable (llr posterior prior) posterior ->
      forall n : Nat, 2 <= n -> forall lam : Real,
        0 < lam -> lam <= Real.exp (-1) ->
        (∫ theta, forwardPrefixMean
            (fun k => mean theta k omega) n ∂posterior) <
          (∫ theta, forwardPrefixMean
              (fun k => X theta k omega) n ∂posterior) +
            continuousSingularFractionBesselBoundary
              prior X posterior delta lam n omega := by
  intro posterior hposterior hposterior_prior hllr n hn lam hlam hlam_exp
  letI : IsProbabilityMeasure posterior := hposterior
  apply lt_of_not_ge
  intro hfail
  apply homega
  exact continuousSingularFractionBessel_boundaryFailure_mem_exceptionalEvent
    prior hdelta hdelta_one hlam hlam_exp hX_unit hmean_unit
    hX_parameter hmean_parameter hjoint_ambient posterior
    hposterior_prior hllr hn (by linarith)

/-- Outside the joint crossing event, substituting the observable tuned
fraction gives a one-sided LIL-order bound for every posterior selected from
the observed path and every reporting time. -/
theorem continuousSingularFractionBessel_allPosteriors_observableLIL_of_not_mem
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X mean : Theta -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (hX_unit : forall theta k omega,
      X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hX_parameter : forall k omega,
      StronglyMeasurable (fun theta => X theta k omega))
    (hmean_parameter : forall k omega,
      StronglyMeasurable (fun theta => mean theta k omega))
    (hjoint_ambient : forall n, StronglyMeasurable
      (fun q : Omega × (Real × Theta) =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2.2) (mean q.2.2) (singularFraction q.2.1) n q.1))
    {omega : Omega}
    (homega : omega ∉ continuousSingularFractionBesselExceptionalEvent
      prior X mean delta) :
    forall posterior : Measure Theta,
      IsProbabilityMeasure posterior -> posterior ≪ prior ->
      Integrable (llr posterior prior) posterior ->
      forall n : Nat, 2 <= n ->
        (∫ theta, forwardPrefixMean
            (fun k => mean theta k omega) n ∂posterior) <
          (∫ theta, forwardPrefixMean
              (fun k => X theta k omega) n ∂posterior) +
            singularFractionObservableLILBoundary
                (continuousForwardPosteriorHybridBesselPenalty
                  posterior X n omega)
                (continuousSingularFractionBesselEffectiveConfidence
                  prior posterior delta) /
              (n : Real) := by
  intro posterior hposterior hposterior_prior hllr n hn
  letI : IsProbabilityMeasure posterior := hposterior
  let Q := continuousForwardPosteriorHybridBesselPenalty
    posterior X n omega
  let effectiveDelta := continuousSingularFractionBesselEffectiveConfidence
    prior posterior delta
  let lam := singularFractionObservableTunedLambda Q effectiveDelta
  have hQ : 0 <= Q := by
    dsimp [Q, continuousForwardPosteriorHybridBesselPenalty]
    exact integral_nonneg fun theta =>
      forwardHybridBesselPenalty_nonneg_of_unit
        (fun k => X theta k omega) hn
        (fun k _hk => hX_unit theta k omega)
  have heffective_pos : 0 < effectiveDelta := by
    simpa [effectiveDelta] using
      continuousSingularFractionBesselEffectiveConfidence_pos
        prior posterior hdelta
  have heffective_one : effectiveDelta <= 1 := by
    simpa [effectiveDelta] using
      continuousSingularFractionBesselEffectiveConfidence_le_one
        prior posterior hdelta hdelta_one
  have hlam : 0 < lam := by
    simpa [lam] using
      singularFractionObservableTunedLambda_pos Q effectiveDelta
  have hlam_exp : lam <= Real.exp (-1) := by
    simpa [lam] using
      singularFractionObservableTunedLambda_le_exp_neg_one Q effectiveDelta
  have hexact :=
    continuousSingularFractionBessel_allPosteriors_allFractions_of_not_mem
      prior hdelta hdelta_one hX_unit hmean_unit hX_parameter
      hmean_parameter hjoint_ambient homega posterior inferInstance
      hposterior_prior hllr n hn lam hlam hlam_exp
  let A := singularFractionLogScale lam *
    (singularFractionLogScale lam + 1)
  have hL : 1 <= singularFractionLogScale lam := by
    exact one_le_singularFractionLogScale hlam hlam_exp
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos (zero_lt_one.trans_le hL) (by linarith)
  have hlog :
      Real.log (A / effectiveDelta) =
        (InformationTheory.klDiv posterior prior).toReal +
          Real.log (A / delta) := by
    simpa [effectiveDelta] using
      continuousSingularFractionBessel_log_effectiveConfidence
        prior posterior hdelta hA
  have henvelope := singularFraction_tunedBoundary_le_observableLIL
    hQ heffective_pos heffective_one
  have henvelope' :
      lam * Q + Real.exp 1 / lam *
          ((InformationTheory.klDiv posterior prior).toReal +
            Real.log (A / delta)) <=
        singularFractionObservableLILBoundary Q effectiveDelta := by
    simpa [lam, A, hlog] using henvelope
  have hboundary :
      continuousSingularFractionBesselBoundary
          prior X posterior delta lam n omega <=
        singularFractionObservableLILBoundary Q effectiveDelta / (n : Real) := by
    unfold continuousSingularFractionBesselBoundary
    apply div_le_div_of_nonneg_right
    · simpa [Q, A] using henvelope'
    · exact Nat.cast_nonneg n
  have hboundary' :
      continuousSingularFractionBesselBoundary
          prior X posterior delta lam n omega <=
        singularFractionObservableLILBoundary
            (continuousForwardPosteriorHybridBesselPenalty posterior X n omega)
            (continuousSingularFractionBesselEffectiveConfidence
              prior posterior delta) /
          (n : Real) := by
    simpa [Q, effectiveDelta] using hboundary
  linarith

/-- One outer-probability event controls the monitored posterior-averaged
conditional prefix mean for every observed path in the event, every eligible
path-selected posterior, and every reporting time `n >= 2`.  The radius is
one-sided and LIL-order; the claim does not identify the conditional prefix
mean with population, future, deployment, or stationary risk.

The final two hypotheses remain explicit because arbitrary measurable
hypothesis spaces need not turn separate section measurability into joint
measurability.  They are propagated unchanged to the master e-process and its
exceptional-event bound. -/
theorem exists_continuousSingularFractionBesselPACBayesLIL_event
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X mean : Theta -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (hX_adapted : forall theta, IncrementAdapted F (X theta))
    (hmean_adapted : forall theta, StronglyAdapted F (mean theta))
    (hX_unit : forall theta k omega,
      X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : forall theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean : forall theta k,
      mu[X theta k | F k] =ᵐ[mu] mean theta k)
    (hX_parameter : forall k omega,
      StronglyMeasurable (fun theta => X theta k omega))
    (hmean_parameter : forall k omega,
      StronglyMeasurable (fun theta => mean theta k omega))
    (hjoint_ambient : forall n, StronglyMeasurable
      (fun q : Omega × (Real × Theta) =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2.2) (mean q.2.2) (singularFraction q.2.1) n q.1))
    (hjoint_filtered : forall n,
      StronglyMeasurable[MeasurableSpace.prod (F n) inferInstance]
        (fun q : Omega × (Real × Theta) =>
          forwardPredictableMeanEmpiricalBernsteinLowerProcess
            (X q.2.2) (mean q.2.2)
              (singularFraction q.2.1) n q.1)) :
    ∃ goodEvent : Set Omega,
      mu.real goodEventᶜ <= delta ∧
        ∀ omega ∈ goodEvent,
          forall posterior : Measure Theta,
            IsProbabilityMeasure posterior -> posterior ≪ prior ->
            Integrable (llr posterior prior) posterior ->
            forall n : Nat, 2 <= n ->
              (∫ theta, forwardPrefixMean
                  (fun k => mean theta k omega) n ∂posterior) <
                (∫ theta, forwardPrefixMean
                    (fun k => X theta k omega) n ∂posterior) +
                  singularFractionObservableLILBoundary
                      (continuousForwardPosteriorHybridBesselPenalty
                        posterior X n omega)
                      (continuousSingularFractionBesselEffectiveConfidence
                        prior posterior delta) /
                    (n : Real) := by
  let badEvent := continuousSingularFractionBesselExceptionalEvent
    prior X mean delta
  refine ⟨badEventᶜ, ?_, ?_⟩
  · simpa [badEvent] using
      (continuousSingularFractionBesselExceptionalEvent_mass_le_delta
        prior hdelta hX_adapted hmean_adapted hX_unit hmean_unit hmean
          hjoint_ambient hjoint_filtered)
  · intro omega homega
    have houtside : omega ∉ continuousSingularFractionBesselExceptionalEvent
        prior X mean delta := by
      simpa [badEvent] using homega
    exact
      continuousSingularFractionBessel_allPosteriors_observableLIL_of_not_mem
        prior hdelta hdelta_one hX_unit hmean_unit hX_parameter
          hmean_parameter hjoint_ambient houtside

end

end FormalSLT.PACBayes.ContinuousSingularFractionBesselPACBayes
