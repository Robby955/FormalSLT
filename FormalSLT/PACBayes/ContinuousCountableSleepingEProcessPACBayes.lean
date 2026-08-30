/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteModelCountableSleepingEProcessPACBayes
import FormalSLT.PACBayes.TimeUniformContinuousPACBayes

/-!
# Continuous-model PAC-Bayes for countable sleeping e-process strategies

This module crosses an arbitrary measurable model space with the active prefix
of a fixed countable catalog of sleeping e-process strategies.  For each model
parameter `theta`, the exact finite-time master is

`tail(n) + sum_{j<n} p(j) E(theta,j,n)`.

The unused countable tail is represented in closed form.  A continuous model
prior is then integrated against these parameterized masters.  Under the
explicit product-integrability obligations below, Ville's inequality provides
one event before the sample path, reporting time, model posterior, and active
strategy posterior are chosen.

On that event the reporting posterior is factorized.  The continuous model
posterior pays `KL(modelPosterior || modelPrior)`, while the posterior on
`Fin n` pays the finite KL to the exact active-prefix-or-tail polynomial prior.
The two costs remain separate.

The strategy catalog and its sleeping schedule must be fixed before observing
the path.  This is confidence allocation over a predeclared countable catalog,
not coin betting or competition with an unrestricted data-dependent strategy.
The theorem controls posterior log e-process values; it does not yet state an
ordinary-risk bound.  Such a statement requires a separate score-to-risk
bridge for the chosen e-process family.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ContinuousChangeOfMeasure
open FormalSLT.PACBayes.TimeUniformContinuous
open FormalSLT.PACBayes.FiniteModelCountableSleepingEProcessPACBayes

namespace FormalSLT.PACBayes.ContinuousCountableSleepingEProcessPACBayes

noncomputable section

variable {Theta Omega : Type*} [MeasurableSpace Theta]
  {mOmega : MeasurableSpace Omega}

/-! ## Continuous model-prior master -/

/-- The exact polynomial sleeping master attached to one model parameter. -/
def parameterizedCountableSleepingEProcessMaster
    (E : Theta -> Nat -> Nat -> Omega -> Real) :
    Theta -> Nat -> Omega -> Real :=
  fun theta => countableSleepingProcessMixture (E theta)

/-- The continuous model-prior mixture of the parameterized countable
sleeping masters. -/
def continuousCountableSleepingEProcessMaster
    (modelPrior : Measure Theta)
    (E : Theta -> Nat -> Nat -> Omega -> Real) : Nat -> Omega -> Real :=
  continuousPriorMixtureProcess modelPrior
    (parameterizedCountableSleepingEProcessMaster E)

omit [MeasurableSpace Theta] in
/-- A predeclared sleeping catalog of e-processes gives an e-process for each
fixed model parameter. -/
theorem parameterizedCountableSleepingEProcessMaster_eProcess
    {mu : @Measure Omega mOmega} [IsFiniteMeasure mu]
    {F : Filtration Nat mOmega}
    (E : Theta -> Nat -> Nat -> Omega -> Real)
    (hE : forall theta j, EProcess mu F (E theta j))
    (hsleep : forall theta j n omega, n <= j -> E theta j n omega = 1)
    (theta : Theta) :
    EProcess mu F (parameterizedCountableSleepingEProcessMaster E theta) := by
  exact countableSleepingProcessMixture_eProcess (hE theta) (hsleep theta)

omit [MeasurableSpace Theta] in
/-- Pointwise nonnegativity of every parameterized master. -/
theorem parameterizedCountableSleepingEProcessMaster_nonneg
    (E : Theta -> Nat -> Nat -> Omega -> Real)
    (hEnonneg : forall theta j n omega, 0 <= E theta j n omega) :
    0 <= parameterizedCountableSleepingEProcessMaster E := by
  intro theta n omega
  exact countableSleepingProcessMixture_nonneg (hEnonneg theta) n omega

omit [MeasurableSpace Theta] in
/-- The compressed sleeping tail makes every parameterized master strictly
positive whenever the component processes are nonnegative. -/
theorem parameterizedCountableSleepingEProcessMaster_pos
    (E : Theta -> Nat -> Nat -> Omega -> Real)
    (hEnonneg : forall theta j n omega, 0 <= E theta j n omega)
    (theta : Theta) (n : Nat) (omega : Omega) :
    0 < parameterizedCountableSleepingEProcessMaster E theta n omega := by
  exact countableSleepingProcessMixture_pos (hEnonneg theta) n omega

omit [MeasurableSpace Theta] in
/-- Every parameterized master starts at one. -/
@[simp]
theorem parameterizedCountableSleepingEProcessMaster_zero
    (E : Theta -> Nat -> Nat -> Omega -> Real)
    (theta : Theta) (omega : Omega) :
    parameterizedCountableSleepingEProcessMaster E theta 0 omega = 1 := by
  exact countableSleepingProcessMixture_zero (E theta) omega

/-! ## Active-prefix strategy change of measure -/

/-- Posterior mean log value over the strategies active before time `n`. -/
def activeStrategyPosteriorLogValue
    (E : Theta -> Nat -> Nat -> Omega -> Real)
    (strategyPosterior : Fin n -> Real)
    (theta : Theta) (omega : Omega) : Real :=
  posteriorAverage strategyPosterior fun j =>
    Real.log (E theta j.1 n omega)

omit [MeasurableSpace Theta] in
/-- The active-prefix strategy posterior pays its finite KL to the compressed
polynomial active-or-tail prior, pointwise in the model parameter. -/
theorem activeStrategyPosteriorLogValue_le_logMaster
    (E : Theta -> Nat -> Nat -> Omega -> Real)
    (hEpos : forall theta j n omega, 0 < E theta j n omega)
    (n : Nat) (strategyPosterior : Fin n -> Real)
    (hstrategyPosterior : IsPMF strategyPosterior)
    (theta : Theta) (omega : Omega) :
    activeStrategyPosteriorLogValue
        E strategyPosterior theta omega <=
      klDiv (liftPolynomialActivePosterior strategyPosterior)
          (polynomialActiveTailPrior n) +
        Real.log
          (parameterizedCountableSleepingEProcessMaster E theta n omega) := by
  simpa [activeStrategyPosteriorLogValue,
    parameterizedCountableSleepingEProcessMaster] using
      (countableSleepingEProcessStrategyPosterior_logValue_le
        (E theta) (hEpos theta) n strategyPosterior
          hstrategyPosterior omega)

/-! ## One continuous-prior event -/

/-- Crossing event for the single continuous model-prior master.  Reporting
times are positive because only then can an active-prefix posterior exist. -/
def continuousCountableSleepingEProcessExceptionalEvent
    (modelPrior : Measure Theta)
    (E : Theta -> Nat -> Nat -> Omega -> Real)
    (delta : Real) : Set Omega :=
  {omega | exists n : Nat, 0 < n /\
    (1 / delta) <=
      continuousCountableSleepingEProcessMaster
        modelPrior E n omega}

/-- Under the explicit continuous-mixture Fubini obligations, the crossing
event of the continuous model-prior master has mass at most `delta`. -/
theorem continuousCountableSleepingEProcessExceptionalEvent_mass_le_delta
    {mu : @Measure Omega mOmega} [IsProbabilityMeasure mu]
    {F : Filtration Nat mOmega}
    (modelPrior : Measure Theta) [IsProbabilityMeasure modelPrior]
    (E : Theta -> Nat -> Nat -> Omega -> Real)
    (hE : forall theta j, EProcess mu F (E theta j))
    (hsleep : forall theta j n omega, n <= j -> E theta j n omega = 1)
    {delta : Real} (hdelta : 0 < delta)
    (h_adapted_mix : StronglyAdapted F
      (continuousCountableSleepingEProcessMaster modelPrior E))
    (h_integrable_mix : forall n, Integrable
      (continuousCountableSleepingEProcessMaster modelPrior E n) mu)
    (hM_int_next : forall n, Integrable
      (fun p : Theta × Omega =>
        parameterizedCountableSleepingEProcessMaster
          E p.1 (n + 1) p.2) (modelPrior.prod mu))
    (hM_int_next_restrict : forall n, forall {s : Set Omega},
      MeasurableSet s -> mu s < ⊤ -> Integrable
        (fun p : Omega × Theta =>
          parameterizedCountableSleepingEProcessMaster
            E p.2 (n + 1) p.1)
        ((mu.restrict s).prod modelPrior))
    (hM_int_current : forall n, Integrable
      (fun p : Omega × Theta =>
        parameterizedCountableSleepingEProcessMaster
          E p.2 n p.1) (mu.prod modelPrior))
    (hM_int_current_restrict : forall n, forall {s : Set Omega},
      MeasurableSet s -> mu s < ⊤ -> Integrable
        (fun p : Omega × Theta =>
          parameterizedCountableSleepingEProcessMaster E p.2 n p.1)
        ((mu.restrict s).prod modelPrior)) :
    mu.real (continuousCountableSleepingEProcessExceptionalEvent
      modelPrior E delta) <= delta := by
  let M := parameterizedCountableSleepingEProcessMaster E
  have hfixed : ∀ᵐ theta ∂modelPrior, Supermartingale (M theta) F mu :=
    Filter.Eventually.of_forall fun theta =>
      (parameterizedCountableSleepingEProcessMaster_eProcess
        E hE hsleep theta).supermartingale
  have hnonneg : forall theta n omega, 0 <= M theta n omega := by
    intro theta n omega
    exact (parameterizedCountableSleepingEProcessMaster_eProcess
      E hE hsleep theta).nonneg n omega
  have hmix := continuousPriorMixture_supermartingale
    (prior := modelPrior) (M := M) h_adapted_mix h_integrable_mix
      hM_int_next hM_int_next_restrict hM_int_current
      hM_int_current_restrict hfixed hnonneg
  have hcross := continuousPriorMixture_crossing_bound
    (prior := modelPrior) (M := M) hdelta hmix.1 hmix.2
      (fun theta omega =>
        (parameterizedCountableSleepingEProcessMaster_eProcess
          E hE hsleep theta).start_one omega)
  simpa [continuousCountableSleepingEProcessExceptionalEvent,
    continuousCountableSleepingEProcessMaster, M] using hcross

/-- Outside the one crossing event, continuous Donsker--Varadhan controls the
posterior mean log master for every eligible model posterior. -/
theorem continuousCountableSleeping_allPosteriorsLogMaster_of_not_mem
    (modelPrior : Measure Theta) [IsProbabilityMeasure modelPrior]
    (E : Theta -> Nat -> Nat -> Omega -> Real)
    (hEpos : forall theta j n omega, 0 < E theta j n omega)
    {delta : Real} (hdelta : 0 < delta)
    (hprior_integrable : forall n omega, Integrable
      (fun theta => parameterizedCountableSleepingEProcessMaster
        E theta n omega) modelPrior)
    {omega : Omega}
    (homega : omega ∉ continuousCountableSleepingEProcessExceptionalEvent
      modelPrior E delta) :
    forall modelPosterior : Measure Theta,
      IsProbabilityMeasure modelPosterior -> modelPosterior ≪ modelPrior ->
      Integrable (llr modelPosterior modelPrior) modelPosterior ->
      forall n : Nat, 0 < n ->
        Integrable
          (fun theta => Real.log
            (parameterizedCountableSleepingEProcessMaster
              E theta n omega)) modelPosterior ->
        (∫ theta, Real.log
            (parameterizedCountableSleepingEProcessMaster
              E theta n omega) ∂modelPosterior) <
          (InformationTheory.klDiv modelPosterior modelPrior).toReal +
            Real.log (1 / delta) := by
  intro modelPosterior hmodelPosterior hposterior_prior hllr n hn hlog_int
  letI : IsProbabilityMeasure modelPosterior := hmodelPosterior
  let M := parameterizedCountableSleepingEProcessMaster E
  have hM_pos : forall theta, 0 < M theta n omega := fun theta =>
    parameterizedCountableSleepingEProcessMaster_pos E
      (fun theta j k xi => (hEpos theta j k xi).le) theta n omega
  have hmix_lt :
      continuousPriorMixtureProcess modelPrior M n omega < 1 / delta := by
    apply lt_of_not_ge
    intro hcross
    apply homega
    exact ⟨n, hn, by
      simpa [continuousCountableSleepingEProcessMaster, M] using hcross⟩
  have hexp_eq :
      (fun theta => Real.exp (Real.log (M theta n omega))) =
        fun theta => M theta n omega := by
    funext theta
    exact Real.exp_log (hM_pos theta)
  have hexp_int : Integrable
      (fun theta => Real.exp (Real.log (M theta n omega))) modelPrior := by
    rw [hexp_eq]
    simpa [M] using hprior_integrable n omega
  have hmix_pos :
      0 < continuousPriorMixtureProcess modelPrior M n omega := by
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
          Real.log
            (continuousPriorMixtureProcess modelPrior M n omega) := by
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
    (add_lt_add_right hlog_lt
      (InformationTheory.klDiv modelPosterior modelPrior).toReal)

/-- Outside the common event, a path-selected continuous model posterior and
a path-selected posterior over the active countable strategy prefix pay
separate model and strategy KL costs. -/
theorem continuousCountableSleeping_factorizedPosteriorLogValue_of_not_mem
    (modelPrior : Measure Theta) [IsProbabilityMeasure modelPrior]
    (E : Theta -> Nat -> Nat -> Omega -> Real)
    (hEpos : forall theta j n omega, 0 < E theta j n omega)
    {delta : Real} (hdelta : 0 < delta)
    (hprior_integrable : forall n omega, Integrable
      (fun theta => parameterizedCountableSleepingEProcessMaster
        E theta n omega) modelPrior)
    {omega : Omega}
    (homega : omega ∉ continuousCountableSleepingEProcessExceptionalEvent
      modelPrior E delta)
    (modelPosterior : Measure Theta)
    (hmodelPosterior : IsProbabilityMeasure modelPosterior)
    (hposterior_prior : modelPosterior ≪ modelPrior)
    (hllr : Integrable (llr modelPosterior modelPrior) modelPosterior)
    {n : Nat} (hn : 0 < n)
    (strategyPosterior : Fin n -> Real)
    (hstrategyPosterior : IsPMF strategyPosterior)
    (hlog_integrable : Integrable
      (fun theta => Real.log
        (parameterizedCountableSleepingEProcessMaster
          E theta n omega)) modelPosterior)
    (hscore_integrable : Integrable
      (fun theta => activeStrategyPosteriorLogValue
        E strategyPosterior theta omega) modelPosterior) :
    (∫ theta, activeStrategyPosteriorLogValue
        E strategyPosterior theta omega ∂modelPosterior) <
      (InformationTheory.klDiv modelPosterior modelPrior).toReal +
        klDiv (liftPolynomialActivePosterior strategyPosterior)
          (polynomialActiveTailPrior n) +
        Real.log (1 / delta) := by
  letI : IsProbabilityMeasure modelPosterior := hmodelPosterior
  have hpac :=
    continuousCountableSleeping_allPosteriorsLogMaster_of_not_mem
      modelPrior E hEpos hdelta hprior_integrable homega
        modelPosterior hmodelPosterior hposterior_prior hllr n hn
          hlog_integrable
  let strategyKL :=
    klDiv (liftPolynomialActivePosterior strategyPosterior)
      (polynomialActiveTailPrior n)
  let logMaster : Theta -> Real := fun theta =>
    Real.log
      (parameterizedCountableSleepingEProcessMaster E theta n omega)
  have hlog_integrable' : Integrable logMaster modelPosterior := by
    simpa [logMaster] using hlog_integrable
  have hpac' :
      (∫ theta, logMaster theta ∂modelPosterior) <
        (InformationTheory.klDiv modelPosterior modelPrior).toReal +
          Real.log (1 / delta) := by
    simpa [logMaster] using hpac
  have hpoint : forall theta,
      activeStrategyPosteriorLogValue
          E strategyPosterior theta omega <=
        strategyKL + logMaster theta := by
    intro theta
    simpa [strategyKL, logMaster] using
      (activeStrategyPosteriorLogValue_le_logMaster
        E hEpos n strategyPosterior hstrategyPosterior theta omega)
  have hrhs_integrable : Integrable
      (fun theta => strategyKL + logMaster theta) modelPosterior :=
    (integrable_const _).add hlog_integrable'
  have hintegral_le :=
    integral_mono hscore_integrable hrhs_integrable hpoint
  have hrhs_integral :
      (∫ theta, strategyKL + logMaster theta ∂modelPosterior) =
        strategyKL + ∫ theta, logMaster theta ∂modelPosterior := by
    simpa only [integral_const, probReal_univ, one_smul] using
      (integral_add (integrable_const strategyKL) hlog_integrable')
  have hintegral_le' :
      (∫ theta, activeStrategyPosteriorLogValue
          E strategyPosterior theta omega ∂modelPosterior) <=
        strategyKL + ∫ theta, logMaster theta ∂modelPosterior :=
    hintegral_le.trans_eq hrhs_integral
  dsimp [strategyKL] at hintegral_le'
  linarith

/-- One event simultaneously supports post-path selection of the continuous
model posterior, reporting time, and posterior over the active prefix of the
fixed countable sleeping-strategy catalog. -/
theorem exists_continuousCountableSleepingEProcessPACBayes_factorized_event
    {mu : @Measure Omega mOmega} [IsProbabilityMeasure mu]
    {F : Filtration Nat mOmega}
    (modelPrior : Measure Theta) [IsProbabilityMeasure modelPrior]
    (E : Theta -> Nat -> Nat -> Omega -> Real)
    (hE : forall theta j, EProcess mu F (E theta j))
    (hsleep : forall theta j n omega, n <= j -> E theta j n omega = 1)
    (hEpos : forall theta j n omega, 0 < E theta j n omega)
    {delta : Real} (hdelta : 0 < delta)
    (h_adapted_mix : StronglyAdapted F
      (continuousCountableSleepingEProcessMaster modelPrior E))
    (h_integrable_mix : forall n, Integrable
      (continuousCountableSleepingEProcessMaster modelPrior E n) mu)
    (hM_int_next : forall n, Integrable
      (fun p : Theta × Omega =>
        parameterizedCountableSleepingEProcessMaster
          E p.1 (n + 1) p.2) (modelPrior.prod mu))
    (hM_int_next_restrict : forall n, forall {s : Set Omega},
      MeasurableSet s -> mu s < ⊤ -> Integrable
        (fun p : Omega × Theta =>
          parameterizedCountableSleepingEProcessMaster
            E p.2 (n + 1) p.1)
        ((mu.restrict s).prod modelPrior))
    (hM_int_current : forall n, Integrable
      (fun p : Omega × Theta =>
        parameterizedCountableSleepingEProcessMaster
          E p.2 n p.1) (mu.prod modelPrior))
    (hM_int_current_restrict : forall n, forall {s : Set Omega},
      MeasurableSet s -> mu s < ⊤ -> Integrable
        (fun p : Omega × Theta =>
          parameterizedCountableSleepingEProcessMaster E p.2 n p.1)
        ((mu.restrict s).prod modelPrior))
    (hprior_integrable : forall n omega, Integrable
      (fun theta => parameterizedCountableSleepingEProcessMaster
        E theta n omega) modelPrior) :
    exists goodEvent : Set Omega,
      mu.real goodEventᶜ <= delta /\
        forall omega, omega ∈ goodEvent ->
          forall modelPosterior : Measure Theta,
            IsProbabilityMeasure modelPosterior ->
            modelPosterior ≪ modelPrior ->
            Integrable (llr modelPosterior modelPrior) modelPosterior ->
            forall n : Nat, 0 < n ->
              forall strategyPosterior : Fin n -> Real,
                IsPMF strategyPosterior ->
                Integrable
                  (fun theta => Real.log
                    (parameterizedCountableSleepingEProcessMaster
                      E theta n omega)) modelPosterior ->
                Integrable
                  (fun theta => activeStrategyPosteriorLogValue
                    E strategyPosterior theta omega) modelPosterior ->
                (∫ theta, activeStrategyPosteriorLogValue
                    E strategyPosterior theta omega ∂modelPosterior) <
                  (InformationTheory.klDiv
                      modelPosterior modelPrior).toReal +
                    klDiv
                      (liftPolynomialActivePosterior strategyPosterior)
                      (polynomialActiveTailPrior n) +
                    Real.log (1 / delta) := by
  let badEvent := continuousCountableSleepingEProcessExceptionalEvent
    modelPrior E delta
  have hmass : mu.real badEvent <= delta := by
    simpa [badEvent] using
      (continuousCountableSleepingEProcessExceptionalEvent_mass_le_delta
        modelPrior E hE hsleep hdelta h_adapted_mix h_integrable_mix
          hM_int_next hM_int_next_restrict hM_int_current
          hM_int_current_restrict)
  refine ⟨badEventᶜ, by simpa, ?_⟩
  intro omega homega modelPosterior hmodelPosterior hposterior_prior hllr
    n hn strategyPosterior hstrategyPosterior hlog_integrable
    hscore_integrable
  exact
    continuousCountableSleeping_factorizedPosteriorLogValue_of_not_mem
      modelPrior E hEpos hdelta hprior_integrable
        (by simpa [badEvent] using homega)
        modelPosterior hmodelPosterior hposterior_prior hllr hn
        strategyPosterior hstrategyPosterior hlog_integrable
        hscore_integrable

end

end FormalSLT.PACBayes.ContinuousCountableSleepingEProcessPACBayes
