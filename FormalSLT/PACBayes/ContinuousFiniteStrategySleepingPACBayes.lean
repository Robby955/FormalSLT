/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.AnytimeValid.FiniteStrategySleepingEProcessMixture
import FormalSLT.PACBayes.ChangeOfMeasure
import FormalSLT.PACBayes.TimeUniformContinuousPACBayes

/-!
# Continuous-model PAC-Bayes for finite strategies and countable wakes

This module builds a genuine two-axis process master.  For every model
parameter `theta`, it mixes a finite predeclared strategy catalog and the
countable polynomial sleeping-wake prior:

`M(theta,n) = tail(n) + sum_{w<n} p(w) sum_a q(a) exp(S(theta,a,w,n))`.

The construction reuses `finiteStrategySleepingProcessMixture`, so each
finite-time value is a finite sum plus a closed-form tail despite the
countable wake axis.  A second mixture integrates `M(theta,n)` against an
arbitrary measurable model prior.
Under the explicit Fubini obligations below, Ville gives one crossing event
for that continuous prior mixture.

Outside the event, nested change of measure gives, simultaneously for every
eligible continuous model posterior, finite strategy posterior, active wake,
and time,

`E_rho E_sigma S < KL(rho || pi) + KL(sigma || q)
  - log p(w) + log(1 / delta)`.

The posterior is factorized: a continuous posterior over models and a finite
posterior over strategies.  The strategy catalog and wake prior are fixed
before observation, while both reporting posteriors and the wake may be
selected after observing the path.  This is a master-mixture result, not coin
betting or parameter-free inference, and it makes no claim about correlated
model--strategy posteriors or ordinary risk without a separate score-to-risk
bridge.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.AllocationLogLog
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ChangeOfMeasure
open FormalSLT.PACBayes.ContinuousChangeOfMeasure
open FormalSLT.PACBayes.TimeUniformContinuous
open scoped BigOperators ENNReal

namespace FormalSLT.PACBayes.ContinuousFiniteStrategySleepingPACBayes

noncomputable section

variable {A Theta Omega : Type*}
  [Fintype A] [DecidableEq A] [Nonempty A]
  [MeasurableSpace Theta]
  {mOmega : MeasurableSpace Omega}

/-- The exact finite-strategy, countable-wake master for one model parameter. -/
def parameterizedTwoAxisSleepingMaster
    (strategyPrior : A -> Real)
    (score : Theta -> A -> Nat -> Nat -> Omega -> Real) :
    Theta -> Nat -> Omega -> Real :=
  fun theta =>
    finiteStrategySleepingProcessMixture strategyPrior
      (fun a w n omega => Real.exp (score theta a w n omega))

/-- The continuous model-prior mixture of the exact two-axis masters. -/
def continuousTwoAxisSleepingMaster
    (modelPrior : Measure Theta) (strategyPrior : A -> Real)
    (score : Theta -> A -> Nat -> Nat -> Omega -> Real) :
    Nat -> Omega -> Real :=
  continuousPriorMixtureProcess modelPrior
    (parameterizedTwoAxisSleepingMaster strategyPrior score)

/-- The prior exponential moment of the finite strategy catalog at one wake. -/
def finiteStrategyPriorMoment
    (strategyPrior : A -> Real)
    (score : Theta -> A -> Nat -> Nat -> Omega -> Real)
    (theta : Theta) (w n : Nat) (omega : Omega) : Real :=
  ∑ a : A, strategyPrior a * Real.exp (score theta a w n omega)

/-- The soft strategy-posterior average of the selected-wake score. -/
def finiteStrategyPosteriorScore
    (strategyPosterior : A -> Real)
    (score : Theta -> A -> Nat -> Nat -> Omega -> Real)
    (theta : Theta) (w n : Nat) (omega : Omega) : Real :=
  ∑ a : A, strategyPosterior a * score theta a w n omega

omit [DecidableEq A] [Nonempty A] [MeasurableSpace Theta] in
/-- Expanded finite-time formula for the parameterized master.  The closed
form tail is shared across strategies because the strategy prior sums to one. -/
theorem parameterizedTwoAxisSleepingMaster_eq
    {strategyPrior : A -> Real} (hstrategyPrior : IsPMF strategyPrior)
    (score : Theta -> A -> Nat -> Nat -> Omega -> Real)
    (theta : Theta) (n : Nat) (omega : Omega) :
    parameterizedTwoAxisSleepingMaster strategyPrior score theta n omega =
      polynomialSleepingTail n +
        ∑ w ∈ Finset.range n, polynomialEpochWeight w *
          finiteStrategyPriorMoment
            strategyPrior score theta w n omega := by
  unfold parameterizedTwoAxisSleepingMaster
    finiteStrategySleepingProcessMixture finiteWeightedProcess
    countableSleepingProcessMixture finiteStrategyPriorMoment
  simp_rw [mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul,
    hstrategyPrior.sum_one, one_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _hw
  apply Finset.sum_congr rfl
  intro a _ha
  ring

omit [Nonempty A] [MeasurableSpace Theta] in
/-- The generic finite-strategy/countable-wake closure gives one e-process for
each fixed model parameter.  The atom scores must be zero while sleeping so
their exponentials remain exactly one. -/
theorem parameterizedTwoAxisSleepingMaster_eProcess
    {mu : @Measure Omega mOmega} [IsFiniteMeasure mu]
    {F : Filtration Nat mOmega}
    {strategyPrior : A -> Real}
    (hstrategyPrior : IsFullSupportPMF strategyPrior)
    {score : Theta -> A -> Nat -> Nat -> Omega -> Real}
    (hscore : forall a w,
      EProcess mu F (fun n omega => Real.exp (score theta a w n omega)))
    (hsleep : forall a w n omega, n <= w -> score theta a w n omega = 0) :
    EProcess mu F
      (parameterizedTwoAxisSleepingMaster strategyPrior score theta) := by
  unfold parameterizedTwoAxisSleepingMaster
  refine finiteStrategySleepingProcessMixture_eProcess
    hstrategyPrior.toIsPMF.nonneg hstrategyPrior.toIsPMF.sum_one hscore ?_
  intro a w n omega hn
  simp [hsleep a w n omega hn]

omit [DecidableEq A] [Nonempty A] [MeasurableSpace Theta] in
/-- The two-axis master is pointwise nonnegative without any stochastic
assumption on the score. -/
theorem parameterizedTwoAxisSleepingMaster_nonneg
    {strategyPrior : A -> Real}
    (hstrategyPrior : IsPMF strategyPrior)
    (score : Theta -> A -> Nat -> Nat -> Omega -> Real) :
    0 <= parameterizedTwoAxisSleepingMaster strategyPrior score := by
  intro theta n omega
  unfold parameterizedTwoAxisSleepingMaster
  exact (finiteStrategySleepingProcessMixture_nonneg
    hstrategyPrior.nonneg
      (fun _a _w _n _omega => (Real.exp_pos _).le)) n omega

omit [DecidableEq A] [MeasurableSpace Theta] in
/-- A full-support strategy prior makes every parameterized master strictly
positive; the unused sleeping-wake tail already has positive mass. -/
theorem parameterizedTwoAxisSleepingMaster_pos
    {strategyPrior : A -> Real}
    (hstrategyPrior : IsFullSupportPMF strategyPrior)
    (score : Theta -> A -> Nat -> Nat -> Omega -> Real)
    (theta : Theta) (n : Nat) (omega : Omega) :
    0 < parameterizedTwoAxisSleepingMaster
      strategyPrior score theta n omega := by
  unfold parameterizedTwoAxisSleepingMaster
    finiteStrategySleepingProcessMixture finiteWeightedProcess
  exact Finset.sum_pos
    (fun a _ha => mul_pos (hstrategyPrior.pos a)
      (countableSleepingProcessMixture_pos
        (fun _w _k _xi => (Real.exp_pos _).le) n omega))
    Finset.univ_nonempty

omit [DecidableEq A] [Nonempty A] [MeasurableSpace Theta] in
/-- Every parameterized master starts at one. -/
@[simp]
theorem parameterizedTwoAxisSleepingMaster_zero
    {strategyPrior : A -> Real} (hstrategyPrior : IsPMF strategyPrior)
    (score : Theta -> A -> Nat -> Nat -> Omega -> Real)
    (theta : Theta) (omega : Omega) :
    parameterizedTwoAxisSleepingMaster strategyPrior score theta 0 omega = 1 := by
  unfold parameterizedTwoAxisSleepingMaster
    finiteStrategySleepingProcessMixture finiteWeightedProcess
  simp [hstrategyPrior.sum_one]

omit [DecidableEq A] [Nonempty A] [MeasurableSpace Theta] in
/-- The selected wake's soft finite-strategy prior moment is dominated by the
single two-axis master after multiplication by its polynomial wake weight. -/
theorem finiteStrategyPriorMoment_mul_wakeWeight_le_master
    {strategyPrior : A -> Real}
    (hstrategyPrior : IsPMF strategyPrior)
    {score : Theta -> A -> Nat -> Nat -> Omega -> Real}
    {w n : Nat} (hwn : w < n) (theta : Theta) (omega : Omega) :
    polynomialEpochWeight w *
        finiteStrategyPriorMoment strategyPrior score theta w n omega <=
      parameterizedTwoAxisSleepingMaster strategyPrior score theta n omega := by
  have hcomponent : forall a : A,
      polynomialEpochWeight w * Real.exp (score theta a w n omega) <=
        countableSleepingProcessMixture
          (fun j k xi => Real.exp (score theta a j k xi)) n omega := by
    intro a
    exact countableSleepingProcessMixture_competes_of_lt
      (fun _j _k _xi => (Real.exp_pos _).le) hwn omega
  calc
    polynomialEpochWeight w *
          finiteStrategyPriorMoment strategyPrior score theta w n omega =
        ∑ a : A, strategyPrior a *
          (polynomialEpochWeight w * Real.exp (score theta a w n omega)) := by
            unfold finiteStrategyPriorMoment
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _ha
            ring
    _ <= ∑ a : A, strategyPrior a *
          countableSleepingProcessMixture
            (fun j k xi => Real.exp (score theta a j k xi)) n omega := by
            exact Finset.sum_le_sum fun a _ha =>
              mul_le_mul_of_nonneg_left (hcomponent a)
                (hstrategyPrior.nonneg a)
    _ = parameterizedTwoAxisSleepingMaster
          strategyPrior score theta n omega := by
            rfl

omit [DecidableEq A] [MeasurableSpace Theta] in
/-- The selected-wake finite strategy moment is strictly positive. -/
theorem finiteStrategyPriorMoment_pos
    {strategyPrior : A -> Real}
    (hstrategyPrior : IsFullSupportPMF strategyPrior)
    (score : Theta -> A -> Nat -> Nat -> Omega -> Real)
    (theta : Theta) (w n : Nat) (omega : Omega) :
    0 < finiteStrategyPriorMoment strategyPrior score theta w n omega := by
  unfold finiteStrategyPriorMoment
  exact Finset.sum_pos
    (fun a _ha => mul_pos (hstrategyPrior.pos a) (Real.exp_pos _))
    Finset.univ_nonempty

omit [DecidableEq A] [MeasurableSpace Theta] in
/-- A selected active wake and soft finite strategy posterior pay finite
strategy KL plus the exact wake log-prior cost against the one master. -/
theorem finiteStrategyPosteriorScore_le_logMaster
    {strategyPrior : A -> Real}
    (hstrategyPrior : IsFullSupportPMF strategyPrior)
    {strategyPosterior : A -> Real}
    (hstrategyPosterior : IsPMF strategyPosterior)
    {score : Theta -> A -> Nat -> Nat -> Omega -> Real}
    {w n : Nat} (hwn : w < n) (theta : Theta) (omega : Omega) :
    finiteStrategyPosteriorScore strategyPosterior score theta w n omega <=
      klDiv strategyPosterior strategyPrior +
        Real.log
          (parameterizedTwoAxisSleepingMaster
            strategyPrior score theta n omega) -
        Real.log (polynomialEpochWeight w) := by
  have hdv := dv_variational_step hstrategyPosterior hstrategyPrior
    (fun a => score theta a w n omega)
  have hmoment_pos := finiteStrategyPriorMoment_pos
    hstrategyPrior score theta w n omega
  have hwake_pos : 0 < polynomialEpochWeight w := polynomialEpochWeight_pos w
  have hdom := finiteStrategyPriorMoment_mul_wakeWeight_le_master
    (score := score) hstrategyPrior.toIsPMF hwn theta omega
  have hlogdom := Real.log_le_log
    (mul_pos hwake_pos hmoment_pos) hdom
  rw [Real.log_mul hwake_pos.ne' hmoment_pos.ne'] at hlogdom
  change finiteStrategyPosteriorScore strategyPosterior score theta w n omega <=
      klDiv strategyPosterior strategyPrior +
        Real.log (finiteStrategyPriorMoment
          strategyPrior score theta w n omega) at hdv
  linarith

/-- The crossing event of the single continuous-prior two-axis master. -/
def continuousTwoAxisSleepingExceptionalEvent
    (modelPrior : Measure Theta) (strategyPrior : A -> Real)
    (score : Theta -> A -> Nat -> Nat -> Omega -> Real)
    (delta : Real) : Set Omega :=
  {omega | exists n : Nat, 0 < n /\
    (1 / delta) <=
      continuousTwoAxisSleepingMaster
        modelPrior strategyPrior score n omega}

omit [DecidableEq A] [Nonempty A] in
/-- Under the explicit continuous-mixture Fubini obligations, the continuous
model-prior integral of the finite-strategy/countable-wake masters has one
Ville crossing event of mass at most `delta`. -/
theorem continuousTwoAxisSleepingExceptionalEvent_mass_le_delta
    {mu : @Measure Omega mOmega} [IsProbabilityMeasure mu]
    {F : Filtration Nat mOmega}
    (modelPrior : Measure Theta) [IsProbabilityMeasure modelPrior]
    {strategyPrior : A -> Real}
    (hstrategyPrior : IsFullSupportPMF strategyPrior)
    {score : Theta -> A -> Nat -> Nat -> Omega -> Real}
    {delta : Real} (hdelta : 0 < delta)
    (h_adapted_mix : StronglyAdapted F
      (continuousTwoAxisSleepingMaster modelPrior strategyPrior score))
    (h_integrable_mix : forall n, Integrable
      (continuousTwoAxisSleepingMaster modelPrior strategyPrior score n) mu)
    (hM_int_next : forall n, Integrable
      (fun p : Theta × Omega =>
        parameterizedTwoAxisSleepingMaster strategyPrior score
          p.1 (n + 1) p.2) (modelPrior.prod mu))
    (hM_int_next_restrict : forall n, forall {s : Set Omega},
      MeasurableSet s -> mu s < ⊤ ->
        Integrable
          (fun p : Omega × Theta =>
            parameterizedTwoAxisSleepingMaster strategyPrior score
              p.2 (n + 1) p.1)
          ((mu.restrict s).prod modelPrior))
    (hM_int_current : forall n, Integrable
      (fun p : Omega × Theta =>
        parameterizedTwoAxisSleepingMaster strategyPrior score
          p.2 n p.1) (mu.prod modelPrior))
    (hM_int_current_restrict : forall n, forall {s : Set Omega},
      MeasurableSet s -> mu s < ⊤ ->
        Integrable
          (fun p : Omega × Theta =>
            parameterizedTwoAxisSleepingMaster strategyPrior score
              p.2 n p.1)
          ((mu.restrict s).prod modelPrior))
    (hfixed : ∀ᵐ theta ∂modelPrior,
      EProcess mu F
        (parameterizedTwoAxisSleepingMaster strategyPrior score theta)) :
    mu.real (continuousTwoAxisSleepingExceptionalEvent
        modelPrior strategyPrior score delta) <= delta := by
  have hmix := continuousPriorMixture_supermartingale
    h_adapted_mix h_integrable_mix hM_int_next hM_int_next_restrict
    hM_int_current hM_int_current_restrict
    (hfixed.mono fun theta htheta => htheta.supermartingale)
    (fun theta n omega =>
      parameterizedTwoAxisSleepingMaster_nonneg
        hstrategyPrior.toIsPMF score theta n omega)
  have hcross := continuousPriorMixture_crossing_bound
    hdelta hmix.1 hmix.2
    (parameterizedTwoAxisSleepingMaster_zero
      hstrategyPrior.toIsPMF score)
  simpa [continuousTwoAxisSleepingExceptionalEvent,
    continuousTwoAxisSleepingMaster] using hcross

omit [DecidableEq A] in
/-- Outside the one master crossing event, continuous Donsker--Varadhan
controls the posterior mean log master for every eligible model posterior. -/
theorem continuousTwoAxisSleeping_allPosteriorsLogMaster_of_not_mem
    (modelPrior : Measure Theta) [IsProbabilityMeasure modelPrior]
    {strategyPrior : A -> Real}
    (hstrategyPrior : IsFullSupportPMF strategyPrior)
    {score : Theta -> A -> Nat -> Nat -> Omega -> Real}
    {delta : Real} (hdelta : 0 < delta)
    (hprior_integrable : forall n omega, Integrable
      (fun theta => parameterizedTwoAxisSleepingMaster
        strategyPrior score theta n omega) modelPrior)
    {omega : Omega}
    (homega : omega ∉ continuousTwoAxisSleepingExceptionalEvent
      modelPrior strategyPrior score delta) :
    forall modelPosterior : Measure Theta,
      IsProbabilityMeasure modelPosterior -> modelPosterior ≪ modelPrior ->
      Integrable (llr modelPosterior modelPrior) modelPosterior ->
      forall n : Nat, 0 < n ->
        Integrable
          (fun theta => Real.log
            (parameterizedTwoAxisSleepingMaster
              strategyPrior score theta n omega)) modelPosterior ->
        (∫ theta, Real.log
            (parameterizedTwoAxisSleepingMaster
              strategyPrior score theta n omega) ∂modelPosterior) <
          (InformationTheory.klDiv modelPosterior modelPrior).toReal +
            Real.log (1 / delta) := by
  intro modelPosterior hmodelPosterior hposterior_prior hllr n hn hlog_int
  letI : IsProbabilityMeasure modelPosterior := hmodelPosterior
  let M := parameterizedTwoAxisSleepingMaster strategyPrior score
  have hmix_lt :
      continuousPriorMixtureProcess modelPrior M n omega < 1 / delta := by
    apply lt_of_not_ge
    intro hcross
    apply homega
    exact ⟨n, hn, by
      simpa [continuousTwoAxisSleepingMaster, M] using hcross⟩
  have hM_pos : forall theta, 0 < M theta n omega := fun theta =>
    parameterizedTwoAxisSleepingMaster_pos
      hstrategyPrior score theta n omega
  have hexp_eq :
      (fun theta => Real.exp (Real.log (M theta n omega))) =
        fun theta => M theta n omega := by
    funext theta
    exact Real.exp_log (hM_pos theta)
  have hexp_int : Integrable
      (fun theta => Real.exp (Real.log (M theta n omega))) modelPrior := by
    rw [hexp_eq]
    simpa [M] using hprior_integrable n omega
  have hmix_pos : 0 < continuousPriorMixtureProcess
      modelPrior M n omega := by
    have hpos := integral_exp_pos hexp_int
    rw [hexp_eq] at hpos
    simpa [continuousPriorMixtureProcess] using hpos
  have hdv := continuous_donsker_varadhan
    modelPosterior modelPrior hposterior_prior
      (fun theta => Real.log (M theta n omega))
      hexp_int (by simpa [M] using hlog_int) hllr
  rw [hexp_eq] at hdv
  have hdv' :
      (∫ theta, Real.log (M theta n omega) ∂modelPosterior) <=
        (InformationTheory.klDiv modelPosterior modelPrior).toReal +
          Real.log (continuousPriorMixtureProcess
            modelPrior M n omega) := by
    simpa [continuousPriorMixtureProcess] using hdv
  have hthreshold_pos : 0 < 1 / delta := one_div_pos.mpr hdelta
  have hlog_lt :
      Real.log (continuousPriorMixtureProcess modelPrior M n omega) <
        Real.log (1 / delta) :=
    Real.strictMonoOn_log hmix_pos hthreshold_pos hmix_lt
  change
    (∫ theta, Real.log (M theta n omega) ∂modelPosterior) <
      (InformationTheory.klDiv modelPosterior modelPrior).toReal +
        Real.log (1 / delta)
  exact lt_of_le_of_lt hdv'
    (by simpa [add_comm] using
      (add_lt_add_left hlog_lt
        (InformationTheory.klDiv modelPosterior modelPrior).toReal))

omit [DecidableEq A] in
/-- Nested finite and continuous change of measure.  An active wake and a
soft strategy posterior may be selected after observing the path.  Model and
strategy selection are charged separately, and the wake pays the exact
polynomial-prior log cost. -/
theorem continuousTwoAxisSleeping_selectedWakeSoftPosteriorScore_of_not_mem
    (modelPrior : Measure Theta) [IsProbabilityMeasure modelPrior]
    {strategyPrior : A -> Real}
    (hstrategyPrior : IsFullSupportPMF strategyPrior)
    {score : Theta -> A -> Nat -> Nat -> Omega -> Real}
    {delta : Real} (hdelta : 0 < delta)
    (hprior_integrable : forall n omega, Integrable
      (fun theta => parameterizedTwoAxisSleepingMaster
        strategyPrior score theta n omega) modelPrior)
    {omega : Omega}
    (homega : omega ∉ continuousTwoAxisSleepingExceptionalEvent
      modelPrior strategyPrior score delta)
    (modelPosterior : Measure Theta)
    (hmodelPosterior : IsProbabilityMeasure modelPosterior)
    (hposterior_prior : modelPosterior ≪ modelPrior)
    (hllr : Integrable (llr modelPosterior modelPrior) modelPosterior)
    {strategyPosterior : A -> Real}
    (hstrategyPosterior : IsPMF strategyPosterior)
    {w n : Nat} (hwn : w < n)
    (hlog_integrable : Integrable
      (fun theta => Real.log
        (parameterizedTwoAxisSleepingMaster
          strategyPrior score theta n omega)) modelPosterior)
    (hscore_integrable : Integrable
      (fun theta => finiteStrategyPosteriorScore
        strategyPosterior score theta w n omega) modelPosterior) :
    (∫ theta, finiteStrategyPosteriorScore
        strategyPosterior score theta w n omega ∂modelPosterior) <
      (InformationTheory.klDiv modelPosterior modelPrior).toReal +
        klDiv strategyPosterior strategyPrior -
        Real.log (polynomialEpochWeight w) +
        Real.log (1 / delta) := by
  letI : IsProbabilityMeasure modelPosterior := hmodelPosterior
  have hpac := continuousTwoAxisSleeping_allPosteriorsLogMaster_of_not_mem
    modelPrior hstrategyPrior hdelta hprior_integrable homega
      modelPosterior hmodelPosterior hposterior_prior hllr n
      (Nat.zero_lt_of_lt hwn) hlog_integrable
  let strategyKL := klDiv strategyPosterior strategyPrior
  let wakeLog := Real.log (polynomialEpochWeight w)
  let logMaster : Theta -> Real := fun theta => Real.log
    (parameterizedTwoAxisSleepingMaster
      strategyPrior score theta n omega)
  have hlog_integrable' : Integrable logMaster modelPosterior := by
    simpa [logMaster] using hlog_integrable
  have hpac' :
      (∫ theta, logMaster theta ∂modelPosterior) <
        (InformationTheory.klDiv modelPosterior modelPrior).toReal +
          Real.log (1 / delta) := by
    simpa [logMaster] using hpac
  have hpoint : forall theta,
      finiteStrategyPosteriorScore
          strategyPosterior score theta w n omega <=
        strategyKL + logMaster theta - wakeLog := by
    intro theta
    simpa [strategyKL, logMaster, wakeLog] using
      (finiteStrategyPosteriorScore_le_logMaster
        (strategyPosterior := strategyPosterior) (score := score)
        hstrategyPrior hstrategyPosterior hwn theta omega)
  have hrhs_integrable : Integrable
      (fun theta => strategyKL + logMaster theta - wakeLog) modelPosterior :=
    ((integrable_const _).add hlog_integrable').sub (integrable_const _)
  have hintegral_le :=
    integral_mono hscore_integrable hrhs_integrable hpoint
  have hsum_integral :
      (∫ theta, strategyKL + logMaster theta ∂modelPosterior) =
        strategyKL + ∫ theta, logMaster theta ∂modelPosterior := by
    simpa only [integral_const, probReal_univ, one_smul] using
      (integral_add (integrable_const strategyKL) hlog_integrable')
  have hrhs_integral :
      (∫ theta, (strategyKL + logMaster theta - wakeLog) ∂modelPosterior) =
        strategyKL + (∫ theta, logMaster theta ∂modelPosterior) - wakeLog := by
    calc
      (∫ theta, strategyKL + logMaster theta - wakeLog ∂modelPosterior) =
          (∫ theta, strategyKL + logMaster theta ∂modelPosterior) -
            ∫ _theta : Theta, wakeLog ∂modelPosterior :=
        integral_sub ((integrable_const strategyKL).add hlog_integrable')
          (integrable_const wakeLog)
      _ = strategyKL + (∫ theta, logMaster theta ∂modelPosterior) -
            ∫ _theta : Theta, wakeLog ∂modelPosterior := by rw [hsum_integral]
      _ = strategyKL + (∫ theta, logMaster theta ∂modelPosterior) - wakeLog := by
        simp only [integral_const, probReal_univ, one_smul]
  have hintegral_le' :
      (∫ theta, finiteStrategyPosteriorScore
          strategyPosterior score theta w n omega ∂modelPosterior) <=
        strategyKL + (∫ theta, logMaster theta ∂modelPosterior) -
          wakeLog := by
    exact hintegral_le.trans_eq hrhs_integral
  dsimp [strategyKL, wakeLog] at hintegral_le'
  linarith

omit [DecidableEq A] in
/-- One event simultaneously supports path-selected continuous model
posteriors, soft finite strategy posteriors, active wakes, and report times.
All model-measure and integrability eligibility conditions remain explicit. -/
theorem exists_continuousTwoAxisSleepingPACBayes_factorized_event
    {mu : @Measure Omega mOmega} [IsProbabilityMeasure mu]
    {F : Filtration Nat mOmega}
    (modelPrior : Measure Theta) [IsProbabilityMeasure modelPrior]
    {strategyPrior : A -> Real}
    (hstrategyPrior : IsFullSupportPMF strategyPrior)
    {score : Theta -> A -> Nat -> Nat -> Omega -> Real}
    {delta : Real} (hdelta : 0 < delta)
    (h_adapted_mix : StronglyAdapted F
      (continuousTwoAxisSleepingMaster modelPrior strategyPrior score))
    (h_integrable_mix : forall n, Integrable
      (continuousTwoAxisSleepingMaster modelPrior strategyPrior score n) mu)
    (hM_int_next : forall n, Integrable
      (fun p : Theta × Omega =>
        parameterizedTwoAxisSleepingMaster strategyPrior score
          p.1 (n + 1) p.2) (modelPrior.prod mu))
    (hM_int_next_restrict : forall n, forall {s : Set Omega},
      MeasurableSet s -> mu s < ⊤ ->
        Integrable
          (fun p : Omega × Theta =>
            parameterizedTwoAxisSleepingMaster strategyPrior score
              p.2 (n + 1) p.1)
          ((mu.restrict s).prod modelPrior))
    (hM_int_current : forall n, Integrable
      (fun p : Omega × Theta =>
        parameterizedTwoAxisSleepingMaster strategyPrior score
          p.2 n p.1) (mu.prod modelPrior))
    (hM_int_current_restrict : forall n, forall {s : Set Omega},
      MeasurableSet s -> mu s < ⊤ ->
        Integrable
          (fun p : Omega × Theta =>
            parameterizedTwoAxisSleepingMaster strategyPrior score
              p.2 n p.1)
          ((mu.restrict s).prod modelPrior))
    (hfixed : ∀ᵐ theta ∂modelPrior,
      EProcess mu F
        (parameterizedTwoAxisSleepingMaster strategyPrior score theta))
    (hprior_integrable : forall n omega, Integrable
      (fun theta => parameterizedTwoAxisSleepingMaster
        strategyPrior score theta n omega) modelPrior) :
    exists goodEvent : Set Omega,
      mu.real goodEventᶜ <= delta /\
        forall omega, omega ∈ goodEvent ->
          forall modelPosterior : Measure Theta,
            IsProbabilityMeasure modelPosterior ->
            modelPosterior ≪ modelPrior ->
            Integrable (llr modelPosterior modelPrior) modelPosterior ->
            forall strategyPosterior : A -> Real,
              IsPMF strategyPosterior ->
              forall w n : Nat, w < n ->
                Integrable
                  (fun theta => Real.log
                    (parameterizedTwoAxisSleepingMaster
                      strategyPrior score theta n omega)) modelPosterior ->
                Integrable
                  (fun theta => finiteStrategyPosteriorScore
                    strategyPosterior score theta w n omega) modelPosterior ->
                (∫ theta, finiteStrategyPosteriorScore
                    strategyPosterior score theta w n omega ∂modelPosterior) <
                  (InformationTheory.klDiv
                      modelPosterior modelPrior).toReal +
                    klDiv strategyPosterior strategyPrior -
                    Real.log (polynomialEpochWeight w) +
                    Real.log (1 / delta) := by
  let badEvent := continuousTwoAxisSleepingExceptionalEvent
    modelPrior strategyPrior score delta
  have hmass : mu.real badEvent <= delta := by
    simpa [badEvent] using
      (continuousTwoAxisSleepingExceptionalEvent_mass_le_delta
        modelPrior hstrategyPrior hdelta h_adapted_mix h_integrable_mix
        hM_int_next hM_int_next_restrict hM_int_current
        hM_int_current_restrict hfixed)
  refine ⟨badEventᶜ, by simpa, ?_⟩
  · intro omega homega modelPosterior hmodelPosterior hposterior_prior
      hllr strategyPosterior hstrategyPosterior w n hwn
      hlog_integrable hscore_integrable
    exact continuousTwoAxisSleeping_selectedWakeSoftPosteriorScore_of_not_mem
      modelPrior hstrategyPrior hdelta hprior_integrable
      (by simpa [badEvent] using homega)
      modelPosterior hmodelPosterior hposterior_prior hllr
      hstrategyPosterior hwn hlog_integrable hscore_integrable

end

end FormalSLT.PACBayes.ContinuousFiniteStrategySleepingPACBayes
