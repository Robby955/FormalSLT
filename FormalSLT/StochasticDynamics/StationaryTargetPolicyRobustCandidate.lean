/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.ControlledKernelTV
import FormalSLT.StochasticDynamics.StationaryPoissonRobustCandidate
import FormalSLT.StochasticDynamics.StationaryTargetPolicyOPE

/-!
# Robust candidate-kernel bridges for stationary target policies

This module supplies deterministic adapters between controlled target-policy
quantities and the reusable finite-state Poisson theory.  A target policy is
shared by the true environment `P` and candidate environment `Q` throughout.

The environment misspecification radius `etaEnv` bounds every
state--action-conditioned row `P state action` versus `Q state action`.  The
induced target-policy state kernels are then at total variation at most
`etaEnv`: mixing the rows with the same target policy adds no factor.  The
more precise weighted inequality is also exposed.  Equality is not claimed,
because marginalizing the action can cancel signed row differences.

For a transition score in `[0,1]` and a potential of span at most `B`, the
true and candidate target-policy Poisson drifts differ by at most
`(1 + B) * etaEnv`.  Centering at an invariant law of the true induced kernel
uses this perturbation twice and yields the residual envelope

`osc(candidate drift) + 2 * ((1 + B) * etaEnv)`.

These are deterministic robustness statements.  They do not construct a
confidence event, estimate an environment kernel, choose a candidate after
seeing data, construct an invariant law, or specialize a finite-depth
potential.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Z A : Type*}
  [Fintype Z] [Nonempty Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- Encode a target policy's controlled row risk as a state-transition score
that is constant in the next state.  This adapter preserves row risks and is
intended for deterministic composition with the ordinary Markov APIs. -/
def targetPolicyRowScore
    (P : Z → A → PMF Z) (π : MarkovTargetPolicy Z A)
    (score : TargetPolicyTransitionScore Z A) : MarkovTransitionScore Z :=
  fun state _nextState ↦ targetPolicyRowRisk P π score state

omit [Nonempty Z] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The row-score adapter has exactly the original target-policy row risk
under the induced state kernel. -/
@[simp] theorem markovRowRisk_targetPolicyRowScore
    (P : Z → A → PMF Z) (π : MarkovTargetPolicy Z A)
    (score : TargetPolicyTransitionScore Z A) (state : Z) :
    markovRowRisk (targetPolicyKernel P π)
        (targetPolicyRowScore P π score) state =
      targetPolicyRowRisk P π score state := by
  classical
  unfold markovRowRisk targetPolicyRowScore
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  rw [← Finset.sum_mul, finitePMF_real_mass_sum, one_mul]

omit [Nonempty Z] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The same adapter preserves stationary target-policy risk. -/
@[simp] theorem stationaryMarkovRisk_targetPolicyRowScore
    (P : Z → A → PMF Z) (π : MarkovTargetPolicy Z A)
    (stationary : PMF Z) (score : TargetPolicyTransitionScore Z A) :
    stationaryMarkovRisk (targetPolicyKernel P π) stationary
        (targetPolicyRowScore P π score) =
      stationaryTargetPolicyRisk P π stationary score := by
  classical
  unfold stationaryMarkovRisk stationaryTargetPolicyRisk
  simp only [PMF.integral_eq_sum, smul_eq_mul,
    markovRowRisk_targetPolicyRowScore]

/-- Target-policy Poisson drift before subtracting the stationary target. -/
def targetPolicyPoissonDrift
    (P : Z → A → PMF Z) (π : MarkovTargetPolicy Z A)
    (score : TargetPolicyTransitionScore Z A) (potential : Z → ℝ)
    (state : Z) : ℝ :=
  targetPolicyRowRisk P π score state +
    targetPolicyPotentialMean P π potential state - potential state

omit [Nonempty Z] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Target-policy drift is ordinary Markov drift for the induced kernel and
the constant-next-state row-score adapter. -/
@[simp] theorem targetPolicyPoissonDrift_eq_markovPoissonDrift
    (P : Z → A → PMF Z) (π : MarkovTargetPolicy Z A)
    (score : TargetPolicyTransitionScore Z A) (potential : Z → ℝ)
    (state : Z) :
    targetPolicyPoissonDrift P π score potential state =
      markovPoissonDrift (targetPolicyKernel P π)
        (targetPolicyRowScore P π score) potential state := by
  unfold targetPolicyPoissonDrift markovPoissonDrift
  rw [markovRowRisk_targetPolicyRowScore,
    targetPolicyPotentialMean_eq_inducedKernel]

/-- Target-policy residual relative to a supplied stationary law. -/
def approximateTargetPolicyPoissonResidual
    (P : Z → A → PMF Z) (π : MarkovTargetPolicy Z A)
    (stationary : PMF Z) (score : TargetPolicyTransitionScore Z A)
    (potential : Z → ℝ) (state : Z) : ℝ :=
  targetPolicyPoissonDrift P π score potential state -
    stationaryTargetPolicyRisk P π stationary score

omit [Nonempty Z] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The target-policy residual is the ordinary induced-kernel residual under
the row-score adapter. -/
@[simp] theorem approximateTargetPolicyPoissonResidual_eq_inducedKernel
    (P : Z → A → PMF Z) (π : MarkovTargetPolicy Z A)
    (stationary : PMF Z) (score : TargetPolicyTransitionScore Z A)
    (potential : Z → ℝ) (state : Z) :
    approximateTargetPolicyPoissonResidual
        P π stationary score potential state =
      approximatePoissonResidual (targetPolicyKernel P π) stationary
        (targetPolicyRowScore P π score) potential state := by
  unfold approximateTargetPolicyPoissonResidual approximatePoissonResidual
  rw [targetPolicyPoissonDrift_eq_markovPoissonDrift,
    stationaryMarkovRisk_targetPolicyRowScore]
  rfl

omit [Nonempty Z] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Invariance makes the stationary average of target-policy drift equal to
the stationary target-policy risk. -/
theorem targetPolicyPoissonDrift_stationary_mean
    (P : Z → A → PMF Z) (π : MarkovTargetPolicy Z A)
    (stationary : PMF Z)
    (hstationary : IsInvariantPMF (targetPolicyKernel P π) stationary)
    (score : TargetPolicyTransitionScore Z A) (potential : Z → ℝ) :
    (∫ state, targetPolicyPoissonDrift P π score potential state
        ∂stationary.toMeasure) =
      stationaryTargetPolicyRisk P π stationary score := by
  simp_rw [targetPolicyPoissonDrift_eq_markovPoissonDrift]
  rw [markovPoissonDrift_stationary_mean
    (targetPolicyKernel P π) stationary hstationary
      (targetPolicyRowScore P π score) potential]
  exact stationaryMarkovRisk_targetPolicyRowScore P π stationary score

omit [Nonempty Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Mixing environment rows with one shared target policy cannot increase
total variation beyond the target-policy-weighted row distances. -/
theorem finitePMFTotalVariation_targetPolicyKernel_le_weighted_environment
    (P Q : Z → A → PMF Z) (π : MarkovTargetPolicy Z A) (state : Z) :
    finitePMFTotalVariation
        (targetPolicyKernel P π state) (targetPolicyKernel Q π state) ≤
      ∑ action : A, (π state action).toReal *
        finitePMFTotalVariation (P state action) (Q state action) := by
  classical
  unfold finitePMFTotalVariation targetPolicyKernel
  simp only [PMF.bind_apply, tsum_fintype]
  have hrealP (nextState : Z) :
      (∑ action : A,
          π state action * P state action nextState).toReal =
        ∑ action : A, (π state action).toReal *
          (P state action nextState).toReal := by
    rw [ENNReal.toReal_sum (by
      intro action _ha
      exact ENNReal.mul_ne_top
        ((π state).apply_ne_top action)
        ((P state action).apply_ne_top nextState))]
    simp only [ENNReal.toReal_mul]
  have hrealQ (nextState : Z) :
      (∑ action : A,
          π state action * Q state action nextState).toReal =
        ∑ action : A, (π state action).toReal *
          (Q state action nextState).toReal := by
    rw [ENNReal.toReal_sum (by
      intro action _ha
      exact ENNReal.mul_ne_top
        ((π state).apply_ne_top action)
        ((Q state action).apply_ne_top nextState))]
    simp only [ENNReal.toReal_mul]
  simp_rw [hrealP, hrealQ]
  have hpointwise (nextState : Z) :
      |(∑ action : A, (π state action).toReal *
          (P state action nextState).toReal) -
        ∑ action : A, (π state action).toReal *
          (Q state action nextState).toReal| ≤
        ∑ action : A, (π state action).toReal *
          |(P state action nextState).toReal -
            (Q state action nextState).toReal| := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    calc
      |∑ action : A, (π state action).toReal *
          ((P state action nextState).toReal -
            (Q state action nextState).toReal)| ≤
        ∑ action : A,
          |(π state action).toReal *
            ((P state action nextState).toReal -
              (Q state action nextState).toReal)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ action : A, (π state action).toReal *
          |(P state action nextState).toReal -
            (Q state action nextState).toReal| := by
        apply Finset.sum_congr rfl
        intro action _ha
        rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  calc
    (1 / 2 : ℝ) * ∑ nextState : Z,
        |∑ action : A,
            (π state action).toReal * (P state action nextState).toReal -
          ∑ action : A,
            (π state action).toReal * (Q state action nextState).toReal| ≤
      (1 / 2 : ℝ) * ∑ nextState : Z, ∑ action : A,
        (π state action).toReal *
          |(P state action nextState).toReal -
            (Q state action nextState).toReal| := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun nextState _hnextState ↦
          hpointwise nextState)
        (by norm_num)
    _ = ∑ action : A, (1 / 2 : ℝ) *
        (∑ nextState : Z, (π state action).toReal *
          |(P state action nextState).toReal -
            (Q state action nextState).toReal|) := by
      rw [Finset.sum_comm, Finset.mul_sum]
    _ = ∑ action : A, (π state action).toReal *
        ((1 / 2 : ℝ) * ∑ nextState : Z,
          |(P state action nextState).toReal -
            (Q state action nextState).toReal|) := by
      apply Finset.sum_congr rfl
      intro action _ha
      rw [← Finset.mul_sum]
      ring

omit [Nonempty Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- A uniform action-conditioned environment radius transfers sharply to the
induced target-policy kernel.  `etaEnv` is the environment-row radius, not an
augmented action--state-kernel radius. -/
theorem finitePMFTotalVariation_targetPolicyKernel_le_environmentRadius
    (P Q : Z → A → PMF Z) (π : MarkovTargetPolicy Z A) {etaEnv : ℝ}
    (hrowTV : ∀ state action,
      finitePMFTotalVariation (P state action) (Q state action) ≤ etaEnv)
    (state : Z) :
    finitePMFTotalVariation
        (targetPolicyKernel P π state) (targetPolicyKernel Q π state) ≤
      etaEnv := by
  calc
    finitePMFTotalVariation
        (targetPolicyKernel P π state) (targetPolicyKernel Q π state) ≤
      ∑ action : A, (π state action).toReal *
        finitePMFTotalVariation (P state action) (Q state action) :=
      finitePMFTotalVariation_targetPolicyKernel_le_weighted_environment
        P Q π state
    _ ≤ ∑ action : A, (π state action).toReal * etaEnv := by
      apply Finset.sum_le_sum
      intro action _ha
      exact mul_le_mul_of_nonneg_left (hrowTV state action)
        ENNReal.toReal_nonneg
    _ = etaEnv := by
      rw [← Finset.sum_mul, finitePMF_real_mass_sum, one_mul]

/-- True and candidate target-policy drifts differ by at most
`(1 + B) * etaEnv`.  The factor `1` controls the controlled transition score,
and `B` controls the next-state potential. -/
theorem abs_targetPolicyPoissonDrift_sub_candidate_le
    (P Q : Z → A → PMF Z) (π : MarkovTargetPolicy Z A)
    {score : TargetPolicyTransitionScore Z A} {potential : Z → ℝ}
    {B etaEnv : ℝ} (hetaEnv : 0 ≤ etaEnv)
    (hscore : ∀ state action nextState,
      score state action nextState ∈ Set.Icc (0 : ℝ) 1)
    (hspan : ∀ x y, |potential y - potential x| ≤ B)
    (hrowTV : ∀ state action,
      finitePMFTotalVariation (P state action) (Q state action) ≤ etaEnv)
    (state : Z) :
    |targetPolicyPoissonDrift P π score potential state -
        targetPolicyPoissonDrift Q π score potential state| ≤
      (1 + B) * etaEnv := by
  have hscoreOsc : ∀ action : A,
      finiteOscillation (score state action) ≤ 1 := by
    intro action
    apply finiteOscillation_le
    intro x y
    rcases hscore state action x with ⟨hx0, hx1⟩
    rcases hscore state action y with ⟨hy0, hy1⟩
    rw [abs_le]
    constructor <;> linarith
  have hpotentialOsc : finiteOscillation potential ≤ B :=
    finiteOscillation_le potential hspan
  have haction : ∀ action : A,
      |∑ nextState : Z,
          (P state action nextState).toReal * score state action nextState -
        ∑ nextState : Z,
          (Q state action nextState).toReal * score state action nextState| ≤
        etaEnv := by
    intro action
    calc
      |∑ nextState : Z,
          (P state action nextState).toReal * score state action nextState -
        ∑ nextState : Z,
          (Q state action nextState).toReal * score state action nextState| ≤
        finitePMFTotalVariation (P state action) (Q state action) *
          finiteOscillation (score state action) :=
        abs_finitePMFExpectation_sub_le_totalVariation_mul_oscillation
          (P state action) (Q state action) (score state action)
      _ ≤ etaEnv * finiteOscillation (score state action) :=
        mul_le_mul_of_nonneg_right (hrowTV state action)
          (finiteOscillation_nonneg _)
      _ ≤ etaEnv * 1 :=
        mul_le_mul_of_nonneg_left (hscoreOsc action) hetaEnv
      _ = etaEnv := mul_one etaEnv
  have hrow :
      |targetPolicyRowRisk P π score state -
          targetPolicyRowRisk Q π score state| ≤ etaEnv := by
    unfold targetPolicyRowRisk
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    calc
      |∑ action : A, (π state action).toReal *
          ((∑ nextState : Z,
              (P state action nextState).toReal *
                score state action nextState) -
            ∑ nextState : Z,
              (Q state action nextState).toReal *
                score state action nextState)| ≤
        ∑ action : A, |(π state action).toReal *
          ((∑ nextState : Z,
              (P state action nextState).toReal *
                score state action nextState) -
            ∑ nextState : Z,
              (Q state action nextState).toReal *
                score state action nextState)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ action : A, (π state action).toReal *
          |(∑ nextState : Z,
              (P state action nextState).toReal *
                score state action nextState) -
            ∑ nextState : Z,
              (Q state action nextState).toReal *
                score state action nextState| := by
        apply Finset.sum_congr rfl
        intro action _ha
        rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      _ ≤ ∑ action : A, (π state action).toReal * etaEnv := by
        apply Finset.sum_le_sum
        intro action _ha
        exact mul_le_mul_of_nonneg_left (haction action)
          ENNReal.toReal_nonneg
      _ = etaEnv := by
        rw [← Finset.sum_mul, finitePMF_real_mass_sum, one_mul]
  have hpotential :
      |targetPolicyPotentialMean P π potential state -
          targetPolicyPotentialMean Q π potential state| ≤
        etaEnv * B := by
    rw [targetPolicyPotentialMean_eq_inducedKernel,
      targetPolicyPotentialMean_eq_inducedKernel]
    calc
      |markovPotentialMean (targetPolicyKernel P π) potential state -
          markovPotentialMean (targetPolicyKernel Q π) potential state| ≤
        finitePMFTotalVariation
            (targetPolicyKernel P π state) (targetPolicyKernel Q π state) *
          finiteOscillation potential := by
        simpa only [markovPotentialMean] using
          abs_pmfIntegral_sub_le_totalVariation_mul_oscillation
            (targetPolicyKernel P π state)
            (targetPolicyKernel Q π state) potential
      _ ≤ etaEnv * finiteOscillation potential :=
        mul_le_mul_of_nonneg_right
          (finitePMFTotalVariation_targetPolicyKernel_le_environmentRadius
            P Q π hrowTV state)
          (finiteOscillation_nonneg _)
      _ ≤ etaEnv * B :=
        mul_le_mul_of_nonneg_left hpotentialOsc hetaEnv
  unfold targetPolicyPoissonDrift
  rw [show
      targetPolicyRowRisk P π score state +
            targetPolicyPotentialMean P π potential state - potential state -
          (targetPolicyRowRisk Q π score state +
            targetPolicyPotentialMean Q π potential state - potential state) =
        (targetPolicyRowRisk P π score state -
            targetPolicyRowRisk Q π score state) +
          (targetPolicyPotentialMean P π potential state -
            targetPolicyPotentialMean Q π potential state) by ring]
  calc
    |(targetPolicyRowRisk P π score state -
          targetPolicyRowRisk Q π score state) +
        (targetPolicyPotentialMean P π potential state -
          targetPolicyPotentialMean Q π potential state)| ≤
      |targetPolicyRowRisk P π score state -
          targetPolicyRowRisk Q π score state| +
        |targetPolicyPotentialMean P π potential state -
          targetPolicyPotentialMean Q π potential state| := abs_add_le _ _
    _ ≤ etaEnv + etaEnv * B := add_le_add hrow hpotential
    _ = (1 + B) * etaEnv := by ring

/-- Stationary residual envelope for a target policy evaluated with a fixed
candidate environment.  The true target-policy kernel's invariant law is an
explicit premise, and `etaEnv` is the action-conditioned environment radius. -/
theorem abs_approximateTargetPolicyPoissonResidual_le_candidateOscillation
    (P Q : Z → A → PMF Z) (π : MarkovTargetPolicy Z A)
    (stationary : PMF Z)
    (hstationary : IsInvariantPMF (targetPolicyKernel P π) stationary)
    {score : TargetPolicyTransitionScore Z A} {potential : Z → ℝ}
    {B etaEnv : ℝ} (hetaEnv : 0 ≤ etaEnv)
    (hscore : ∀ state action nextState,
      score state action nextState ∈ Set.Icc (0 : ℝ) 1)
    (hspan : ∀ x y, |potential y - potential x| ≤ B)
    (hrowTV : ∀ state action,
      finitePMFTotalVariation (P state action) (Q state action) ≤ etaEnv)
    (state : Z) :
    |approximateTargetPolicyPoissonResidual
        P π stationary score potential state| ≤
      finiteOscillation (targetPolicyPoissonDrift Q π score potential) +
        2 * ((1 + B) * etaEnv) := by
  let epsilon : ℝ := (1 + B) * etaEnv
  have hdrift : ∀ nextState,
      |targetPolicyPoissonDrift P π score potential nextState -
          targetPolicyPoissonDrift Q π score potential nextState| ≤
        epsilon := by
    intro nextState
    exact abs_targetPolicyPoissonDrift_sub_candidate_le
      P Q π hetaEnv hscore hspan hrowTV nextState
  have hmeans :
      |(∫ nextState, targetPolicyPoissonDrift P π score potential nextState
          ∂stationary.toMeasure) -
        ∫ nextState, targetPolicyPoissonDrift Q π score potential nextState
          ∂stationary.toMeasure| ≤ epsilon :=
    abs_pmfIntegral_sub_le_of_abs_sub_le stationary _ _ hdrift
  have hcandidate :
      |targetPolicyPoissonDrift Q π score potential state -
          ∫ nextState, targetPolicyPoissonDrift Q π score potential nextState
            ∂stationary.toMeasure| ≤
        finiteOscillation (targetPolicyPoissonDrift Q π score potential) :=
    abs_sub_pmfIntegral_le_finiteOscillation stationary
      (targetPolicyPoissonDrift Q π score potential) state
  unfold approximateTargetPolicyPoissonResidual
  rw [← targetPolicyPoissonDrift_stationary_mean
    P π stationary hstationary score potential]
  rw [show
      targetPolicyPoissonDrift P π score potential state -
          ∫ nextState, targetPolicyPoissonDrift P π score potential nextState
            ∂stationary.toMeasure =
        (targetPolicyPoissonDrift P π score potential state -
          targetPolicyPoissonDrift Q π score potential state) +
        (targetPolicyPoissonDrift Q π score potential state -
          ∫ nextState, targetPolicyPoissonDrift Q π score potential nextState
            ∂stationary.toMeasure) +
        ((∫ nextState, targetPolicyPoissonDrift Q π score potential nextState
            ∂stationary.toMeasure) -
          ∫ nextState, targetPolicyPoissonDrift P π score potential nextState
            ∂stationary.toMeasure) by ring]
  calc
    |(targetPolicyPoissonDrift P π score potential state -
        targetPolicyPoissonDrift Q π score potential state) +
      (targetPolicyPoissonDrift Q π score potential state -
        ∫ nextState, targetPolicyPoissonDrift Q π score potential nextState
          ∂stationary.toMeasure) +
      ((∫ nextState, targetPolicyPoissonDrift Q π score potential nextState
          ∂stationary.toMeasure) -
        ∫ nextState, targetPolicyPoissonDrift P π score potential nextState
          ∂stationary.toMeasure)| ≤
      |targetPolicyPoissonDrift P π score potential state -
        targetPolicyPoissonDrift Q π score potential state| +
      |targetPolicyPoissonDrift Q π score potential state -
        ∫ nextState, targetPolicyPoissonDrift Q π score potential nextState
          ∂stationary.toMeasure| +
      |(∫ nextState, targetPolicyPoissonDrift Q π score potential nextState
          ∂stationary.toMeasure) -
        ∫ nextState, targetPolicyPoissonDrift P π score potential nextState
          ∂stationary.toMeasure| := by
        exact (abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ epsilon +
        finiteOscillation (targetPolicyPoissonDrift Q π score potential) +
          epsilon := by
      exact add_le_add (add_le_add (hdrift state) hcandidate)
        (by simpa [abs_sub_comm] using hmeans)
    _ = finiteOscillation (targetPolicyPoissonDrift Q π score potential) +
        2 * ((1 + B) * etaEnv) := by
      dsimp [epsilon]
      ring

end

end FormalSLT.StochasticDynamics
