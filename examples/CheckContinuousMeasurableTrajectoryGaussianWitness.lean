import FormalSLT.StochasticDynamics.ContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes
import FormalSLT.PACBayes.FinitePMFBridge
import FormalSLT.PACBayes.GaussianMeasureKL
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Distributions.Uniform

/-!
# Continuous-state, continuous-posterior trajectory receipt

The trajectory state space is `Real` and the hypothesis space is
`(Fin 1 -> Real) x Bool`.  The state kernel emits fair Rademacher values on
every step.  The prior has a standard-Gaussian coordinate and a fair Boolean
coordinate; the fixed posterior shifts the Gaussian mean by `1/4` and keeps
the Boolean coordinate fair.  It has no point masses and exact KL `1/32`.

The zero-one score compares the sign of the real next state with a Boolean
prediction that is itself flipped by the sign of the Gaussian parameter, so
the score genuinely uses both nonfinite coordinates and attains both endpoints.

At horizon `64`, confidence `1/8`, and tilt `1/2`, the complete continuous
trajectory boundary is at most `489/1024`, hence below `1/2`.  Each of two
opposite-sign two-step cylinders has exact path mass `1/4`, larger than the
common exceptional-event
budget.  Hence both cylinders contain a theorem-produced good path.  On those
paths every fixed hypothesis has positive observed Bessel variance, while the
posterior empirical risk is exactly `1/2`; the complete right-hand side is
therefore strictly below one.

This is a fixed continuous posterior and a fixed predeclared tilt.  It does
not claim data-dependent posterior selection, atomless state transitions, or
an observed-variance comparison against another boundary.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes
open FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes

namespace FormalSLT.Examples.CheckContinuousMeasurableTrajectoryGaussianWitness

open FormalSLT.StochasticDynamics

noncomputable section

abbrev GaussianCoordinate := GaussianParameterSpace 1
abbrev Hypothesis := GaussianCoordinate × Bool

def receiptPriorGaussianParams : SphericalGaussianParams 1 where
  mean := fun _ ↦ 0
  variance := 1
  variance_pos := by norm_num

def receiptPosteriorGaussianParams : SphericalGaussianParams 1 where
  mean := fun _ ↦ (1 : Real) / 4
  variance := 1
  variance_pos := by norm_num

def receiptPriorGaussian : Measure GaussianCoordinate :=
  sphericalGaussianMeasure receiptPriorGaussianParams

def receiptPosteriorGaussian : Measure GaussianCoordinate :=
  sphericalGaussianMeasure receiptPosteriorGaussianParams

def receiptBoolPMF : Bool → Real := fun _ ↦ 1 / 2

theorem receiptBoolPMF_isPMF : IsPMF receiptBoolPMF := by
  constructor
  · intro b
    norm_num [receiptBoolPMF]
  · simp [receiptBoolPMF]

def receiptBoolMeasure : Measure Bool := receiptBoolPMF_isPMF.toPMF.toMeasure

instance receiptPriorGaussian_probability :
    IsProbabilityMeasure receiptPriorGaussian := by
  dsimp [receiptPriorGaussian]
  infer_instance

instance receiptPosteriorGaussian_probability :
    IsProbabilityMeasure receiptPosteriorGaussian := by
  dsimp [receiptPosteriorGaussian]
  infer_instance

instance receiptBoolMeasure_probability :
    IsProbabilityMeasure receiptBoolMeasure := by
  dsimp [receiptBoolMeasure]
  infer_instance

def receiptBoolKernel : Kernel GaussianCoordinate Bool :=
  Kernel.const GaussianCoordinate receiptBoolMeasure

instance receiptBoolKernel_markov : IsMarkovKernel receiptBoolKernel := by
  dsimp [receiptBoolKernel]
  infer_instance

def receiptPrior : Measure Hypothesis :=
  receiptPriorGaussian ⊗ₘ receiptBoolKernel

def receiptPosterior : Measure Hypothesis :=
  receiptPosteriorGaussian ⊗ₘ receiptBoolKernel

instance receiptPrior_probability : IsProbabilityMeasure receiptPrior := by
  dsimp [receiptPrior, receiptPriorGaussian, receiptBoolKernel,
    receiptBoolMeasure]
  infer_instance

instance receiptPosterior_probability : IsProbabilityMeasure receiptPosterior := by
  dsimp [receiptPosterior, receiptPosteriorGaussian, receiptBoolKernel,
    receiptBoolMeasure]
  infer_instance

instance receiptPriorGaussian_nullSingleton :
    NullSingletonClass receiptPriorGaussian := by
  dsimp [receiptPriorGaussian, sphericalGaussianMeasure,
    diagonalGaussianMeasure]
  infer_instance

instance receiptPosteriorGaussian_nullSingleton :
    NullSingletonClass receiptPosteriorGaussian := by
  dsimp [receiptPosteriorGaussian, sphericalGaussianMeasure,
    diagonalGaussianMeasure]
  infer_instance

instance receiptPrior_nullSingleton : NullSingletonClass receiptPrior := by
  rw [receiptPrior, receiptBoolKernel, Measure.compProd_const]
  infer_instance

instance receiptPosterior_nullSingleton :
    NullSingletonClass receiptPosterior := by
  rw [receiptPosterior, receiptBoolKernel, Measure.compProd_const]
  infer_instance

theorem receiptPosterior_finite_set_mass_zero (s : Finset Hypothesis) :
    receiptPosterior s = 0 := by
  exact s.measure_zero receiptPosterior

theorem receiptPosterior_absolutelyContinuous :
    receiptPosterior ≪ receiptPrior := by
  exact (sphericalGaussianMeasure_absolutelyContinuous
    receiptPosteriorGaussianParams receiptPriorGaussianParams).compProd_left
      receiptBoolKernel

theorem receiptPosterior_llr_integrable :
    Integrable (llr receiptPosterior receiptPrior) receiptPosterior := by
  have hac := receiptPosterior_absolutelyContinuous
  apply (InformationTheory.integrable_llr_compProd_iff hac).2
  constructor
  · exact integrable_llr_diagonalGaussianMeasure
      receiptPosteriorGaussianParams.toDiagonal
      receiptPriorGaussianParams.toDiagonal
  · rw [integrable_congr (llr_self _)]
    exact integrable_zero _ _ _

theorem receiptPosterior_kl_eq :
    (InformationTheory.klDiv receiptPosterior receiptPrior).toReal =
      (1 : Real) / 32 := by
  rw [receiptPosterior, receiptPrior,
    InformationTheory.klDiv_compProd_left,
    receiptPosteriorGaussian, receiptPriorGaussian,
    sphericalGaussianMeasure_klDiv_toReal_eq,
    sphericalGaussianKL_eq_closedForm]
  norm_num [receiptPosteriorGaussianParams, receiptPriorGaussianParams,
    squaredMeanDistance, sphericalGaussianKLClosedForm]

def receiptPrediction (theta : Hypothesis) : Bool :=
  if 0 ≤ theta.1 0 then theta.2 else !theta.2

def receiptRealLabel (y : Real) : Bool :=
  if 0 ≤ y then true else false

def receiptScore (theta : Hypothesis) : TrajectoryScore Real :=
  fun _n _u y ↦ if receiptPrediction theta = receiptRealLabel y then 0 else 1

theorem receiptPrediction_measurable : Measurable receiptPrediction := by
  have hsign : MeasurableSet {theta : Hypothesis | 0 ≤ theta.1 0} :=
    measurableSet_le measurable_const
      ((measurable_pi_apply 0).comp measurable_fst)
  have hnot : Measurable (fun theta : Hypothesis ↦ !theta.2) :=
    (measurable_of_finite (fun b : Bool ↦ !b)).comp measurable_snd
  exact Measurable.ite hsign measurable_snd hnot

theorem receiptRealLabel_measurable : Measurable receiptRealLabel := by
  have hsign : MeasurableSet {y : Real | 0 ≤ y} :=
    measurableSet_le measurable_const measurable_id
  exact Measurable.ite hsign measurable_const measurable_const

theorem receiptScore_joint :
    JointlyStronglyMeasurableParameterizedTrajectoryScore receiptScore := by
  intro n
  have hp : Measurable
      (fun q : Hypothesis × (((i : Finset.Iic n) → Real) × Real) ↦
        receiptPrediction q.1) :=
    receiptPrediction_measurable.comp measurable_fst
  have hy : Measurable
      (fun q : Hypothesis × (((i : Finset.Iic n) → Real) × Real) ↦
        receiptRealLabel q.2.2) :=
    receiptRealLabel_measurable.comp (measurable_snd.comp measurable_snd)
  have hout : Measurable (fun q : Bool × Bool ↦
      if q.1 = q.2 then (0 : Real) else 1) := measurable_of_finite _
  exact (hout.comp (hp.prodMk hy)).stronglyMeasurable

theorem receiptScore_mem_Icc :
    ∀ theta n u y, receiptScore theta n u y ∈ Set.Icc (0 : Real) 1 := by
  intro theta n u y
  unfold receiptScore
  split <;> norm_num

theorem receiptScore_attains_endpoints
    (theta : Hypothesis) (n : Nat)
    (u : (i : Finset.Iic n) → Real) :
    receiptScore theta n u
        (if receiptPrediction theta then (1 : Real) else -1) = 0 ∧
      receiptScore theta n u
        (if receiptPrediction theta then (-1 : Real) else 1) = 1 := by
  cases h : receiptPrediction theta <;>
    norm_num [receiptScore, receiptRealLabel, h]

def receiptPositiveGaussian : GaussianCoordinate := fun _ ↦ 1

def receiptNegativeGaussian : GaussianCoordinate := fun _ ↦ -1

/-- At the same positive real state, changing either the Gaussian sign or the
Boolean coordinate changes the zero-one score. -/
theorem receiptScore_uses_gaussian_and_bool
    (n : Nat) (u : (i : Finset.Iic n) → Real) :
    receiptScore (receiptPositiveGaussian, true) n u 1 = 0 ∧
      receiptScore (receiptNegativeGaussian, true) n u 1 = 1 ∧
      receiptScore (receiptPositiveGaussian, false) n u 1 = 1 := by
  norm_num [receiptScore, receiptPrediction, receiptRealLabel,
    receiptPositiveGaussian, receiptNegativeGaussian]

def receiptRademacherValue (b : Bool) : Real := if b then 1 else -1

def receiptStatePMF : PMF Real :=
  (PMF.uniformOfFintype Bool).map receiptRademacherValue

def receiptStateKernel (n : Nat) :
    Kernel ((i : Finset.Iic n) → Real) Real :=
  Kernel.const _ receiptStatePMF.toMeasure

instance receiptStateKernel_markov (n : Nat) :
    IsMarkovKernel (receiptStateKernel n) := by
  unfold receiptStateKernel
  infer_instance

def receiptWeight (_j : Unit) : Real := 1

def receiptTilt (_j : Unit) : Real := 1 / 2

def receiptHorizon : Nat := 64

def receiptDelta : Real := 1 / 8

theorem receiptConditionalRisk_eq_half
    (theta : Hypothesis) (n : Nat) (x : Nat → Real) :
    conditionalTrajectoryRisk receiptStateKernel (receiptScore theta) n x =
      (1 : Real) / 2 := by
  let u := Preorder.frestrictLe n x
  have hintegrand : StronglyMeasurable
      (fun y : Real ↦ receiptScore theta n u y) := by
    have hmap : Measurable (fun y : Real ↦ (u, y)) :=
      measurable_const.prodMk measurable_id
    simpa only [Function.comp_def] using
      (jointlyStronglyMeasurableTrajectoryScore_section
        receiptScore_joint theta n).comp_measurable hmap
  unfold conditionalTrajectoryRisk receiptStateKernel receiptStatePMF
  change ∫ y, receiptScore theta n u y
      ∂((PMF.uniformOfFintype Bool).map receiptRademacherValue).toMeasure =
    (1 : Real) / 2
  rw [← PMF.toMeasure_map (p := PMF.uniformOfFintype Bool)
    (f := receiptRademacherValue) (by fun_prop)]
  rw [integral_map (by fun_prop) hintegrand.aestronglyMeasurable]
  rw [PMF.integral_eq_sum]
  cases h : receiptPrediction theta <;>
    norm_num [receiptScore, receiptRealLabel, receiptRademacherValue,
      PMF.uniformOfFintype_apply, h]

theorem receiptTrajectoryAverageConditionalRisk_eq_half
    (theta : Hypothesis) {n : Nat} (hn : 0 < n) (x : Nat → Real) :
    trajectoryAverageConditionalRisk receiptStateKernel
        (receiptScore theta) n x = (1 : Real) / 2 := by
  unfold trajectoryAverageConditionalRisk runningMean runningSum
  simp_rw [receiptConditionalRisk_eq_half]
  simp [hn.ne']

theorem receiptPosteriorAverageConditionalRisk_eq_half
    {n : Nat} (hn : 0 < n) (x : Nat → Real) :
    continuousTrajectoryPosteriorAverageConditionalRisk
        receiptStateKernel receiptScore receiptPosterior n x =
      (1 : Real) / 2 := by
  unfold continuousTrajectoryPosteriorAverageConditionalRisk
  simp_rw [receiptTrajectoryAverageConditionalRisk_eq_half _ hn x]
  simp

theorem receiptTwoBoolEmpiricalRisk_add_eq_one
    (g : GaussianCoordinate) {n : Nat} (hn : 0 < n) (x : Nat → Real) :
    trajectoryEmpiricalPrequentialRisk (receiptScore (g, false)) n x +
        trajectoryEmpiricalPrequentialRisk (receiptScore (g, true)) n x =
      1 := by
  unfold trajectoryEmpiricalPrequentialRisk runningMean runningSum
  rw [← add_div, ← Finset.sum_add_distrib]
  have hsum :
      (∑ k ∈ Finset.range n,
          (observedTrajectoryScore (receiptScore (g, false)) k x +
            observedTrajectoryScore (receiptScore (g, true)) k x)) = n := by
    calc
      _ = ∑ _k ∈ Finset.range n, (1 : Real) := by
        apply Finset.sum_congr rfl
        intro k _hk
        by_cases hg : 0 ≤ g 0 <;>
          cases hlabel : receiptRealLabel (x (k + 1)) <;>
          simp [observedTrajectoryScore, receiptScore, receiptPrediction,
            hg, hlabel]
      _ = n := by simp
  rw [hsum]
  norm_num [hn.ne']

theorem receiptBoolIntegralEmpiricalRisk_eq_half
    (g : GaussianCoordinate) {n : Nat} (hn : 0 < n) (x : Nat → Real) :
    (∫ b, trajectoryEmpiricalPrequentialRisk (receiptScore (g, b)) n x
        ∂receiptBoolMeasure) = (1 : Real) / 2 := by
  rw [receiptBoolMeasure, receiptBoolPMF_isPMF.integral_toPMF_eq_sum]
  simp only [Fintype.sum_bool, receiptBoolPMF]
  have hsum := receiptTwoBoolEmpiricalRisk_add_eq_one g hn x
  linarith

theorem receiptPosteriorEmpiricalRisk_eq_half
    {n : Nat} (hn : 0 < n) (x : Nat → Real) :
    continuousTrajectoryPosteriorEmpiricalPrequentialRisk
        receiptScore receiptPosterior n x = (1 : Real) / 2 := by
  let X : Hypothesis → Nat → Real := fun theta k ↦
    observedTrajectoryScore (receiptScore theta) k x
  have hX_meas : ∀ k, StronglyMeasurable (fun theta ↦ X theta k) := by
    intro k
    exact stronglyMeasurable_observedTrajectoryScore_parameter_of_joint
      receiptScore_joint k x
  have hX_unit : ∀ theta k, X theta k ∈ Set.Icc (0 : Real) 1 := by
    intro theta k
    exact observedTrajectoryScore_mem_Icc
      (receiptScore_mem_Icc theta) k x
  have hf_int : Integrable
      (fun theta ↦ trajectoryEmpiricalPrequentialRisk
        (receiptScore theta) n x) receiptPosterior := by
    have h := integrable_forwardPrefixMean_parameter_of_unit
      receiptPosterior X hn hX_meas hX_unit
    convert h using 1
    funext theta
    exact forwardPrefixMean_observedTrajectoryScore
      (receiptScore theta) n x
  unfold continuousTrajectoryPosteriorEmpiricalPrequentialRisk
  rw [receiptPosterior, Measure.integral_compProd hf_int]
  simp only [receiptBoolKernel, Kernel.const_apply]
  change
    (∫ g, ∫ b, trajectoryEmpiricalPrequentialRisk
        (receiptScore (g, b)) n x ∂receiptBoolMeasure
      ∂receiptPosteriorGaussian) = (1 : Real) / 2
  have hinner : ∀ g : GaussianCoordinate,
      (∫ b, trajectoryEmpiricalPrequentialRisk
        (receiptScore (g, b)) n x ∂receiptBoolMeasure) =
        (1 : Real) / 2 := fun g ↦
    receiptBoolIntegralEmpiricalRisk_eq_half g hn x
  simp_rw [hinner]
  simp

theorem receiptWeight_pos : ∀ j, 0 < receiptWeight j := by
  intro j
  norm_num [receiptWeight]

theorem receiptWeight_sum : ∑ j, receiptWeight j = 1 := by
  simp [receiptWeight]

theorem receiptTilt_pos : ∀ j, 0 < receiptTilt j := by
  intro j
  norm_num [receiptTilt]

theorem receiptTilt_lt_one : ∀ j, receiptTilt j < 1 := by
  intro j
  norm_num [receiptTilt]

theorem receiptPosteriorHybridPenalty_le
    (x : Nat → Real) :
    continuousTrajectoryPosteriorHybridBesselPenalty
        receiptScore receiptPosterior receiptHorizon x ≤ 49 / 2 := by
  let X : Hypothesis → Nat → Real := fun theta k ↦
    observedTrajectoryScore (receiptScore theta) k x
  have hX_meas : ∀ k, StronglyMeasurable (fun theta ↦ X theta k) := by
    intro k
    exact stronglyMeasurable_observedTrajectoryScore_parameter_of_joint
      receiptScore_joint k x
  have hX_unit : ∀ theta k, X theta k ∈ Set.Icc (0 : Real) 1 := by
    intro theta k
    exact observedTrajectoryScore_mem_Icc
      (receiptScore_mem_Icc theta) k x
  have hInt : Integrable
      (fun theta ↦ forwardHybridBesselPenalty
        (fun k ↦ X theta k) receiptHorizon) receiptPosterior :=
    integrable_forwardHybridBesselPenalty_parameter_of_unit
      receiptPosterior X (by norm_num [receiptHorizon]) hX_meas hX_unit
  unfold continuousTrajectoryPosteriorHybridBesselPenalty
  calc
    (∫ theta, forwardHybridBesselPenalty
        (fun k ↦ observedTrajectoryScore (receiptScore theta) k x)
        receiptHorizon ∂receiptPosterior) ≤
        ∫ _theta : Hypothesis, (49 / 2 : Real) ∂receiptPosterior := by
      apply integral_mono_ae hInt (integrable_const (49 / 2 : Real))
      exact Filter.Eventually.of_forall fun theta ↦ by
        change forwardHybridBesselPenalty
          (fun k ↦ observedTrajectoryScore (receiptScore theta) k x)
          receiptHorizon ≤ 49 / 2
        have hle := forwardHybridBesselPenalty_le_of_unit
          (n := receiptHorizon)
          (fun k ↦ observedTrajectoryScore (receiptScore theta) k x)
          (by norm_num [receiptHorizon])
          (fun k hk ↦ observedTrajectoryScore_mem_Icc
            (receiptScore_mem_Icc theta) k x)
        norm_num [receiptHorizon] at hle ⊢
        exact hle
    _ = 49 / 2 := by simp

theorem receiptLogEight_le_three : Real.log 8 ≤ 3 := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hpow : Real.log (8 : Real) = 3 * Real.log 2 := by
    convert Real.log_pow (2 : Real) 3 using 1 <;> norm_num
  rw [hpow]
  linarith

theorem receiptPsiHalf_le_half :
    forwardEmpiricalBernsteinPsi (1 / 2 : Real) ≤ 1 / 2 := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlogHalf : Real.log (1 / 2 : Real) = -Real.log 2 := by
    rw [show (1 / 2 : Real) = (2 : Real)⁻¹ by norm_num, Real.log_inv]
  unfold forwardEmpiricalBernsteinPsi
  rw [show (1 - (1 / 2 : Real)) = 1 / 2 by norm_num]
  rw [hlogHalf]
  linarith

theorem receiptBoundary_le (x : Nat → Real) :
    continuousTrajectoryEmpiricalBernsteinPACBayesBoundary
        receiptPrior receiptWeight receiptTilt receiptScore receiptPosterior
        receiptDelta () receiptHorizon x ≤ 489 / 1024 := by
  have hpen := receiptPosteriorHybridPenalty_le x
  have hpsiNonneg := forwardEmpiricalBernsteinPsi_nonneg
    (show (0 : Real) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : Real) < 1 by norm_num)
  have hpsi := receiptPsiHalf_le_half
  have hproduct :
      forwardEmpiricalBernsteinPsi (1 / 2 : Real) *
          continuousTrajectoryPosteriorHybridBesselPenalty
            receiptScore receiptPosterior receiptHorizon x ≤ 49 / 4 := by
    calc
      _ ≤ forwardEmpiricalBernsteinPsi (1 / 2 : Real) * (49 / 2) :=
        mul_le_mul_of_nonneg_left hpen hpsiNonneg
      _ ≤ (1 / 2 : Real) * (49 / 2) :=
        mul_le_mul_of_nonneg_right hpsi (by norm_num)
      _ = 49 / 4 := by norm_num
  unfold continuousTrajectoryEmpiricalBernsteinPACBayesBoundary
  rw [receiptPosterior_kl_eq]
  norm_num [receiptWeight, receiptTilt, receiptDelta, receiptHorizon]
  have hlog := receiptLogEight_le_three
  norm_num [receiptHorizon] at hproduct
  rw [div_le_iff₀ (show (0 : Real) < 32 by norm_num)]
  norm_num
  linarith

theorem receiptBoundary_lt_half (x : Nat → Real) :
    continuousTrajectoryEmpiricalBernsteinPACBayesBoundary
        receiptPrior receiptWeight receiptTilt receiptScore receiptPosterior
        receiptDelta () receiptHorizon x < 1 / 2 := by
  exact (receiptBoundary_le x).trans_lt (by norm_num)

/-! ## Positive-mass sign-flip branches -/

/-- A two-step cylinder whose two observed Rademacher states have opposite
signs.  Each branch has probability `1/4` under the trajectory law. -/
def receiptSignFlipBranch (b : Bool) : Set (Nat → Real) :=
  {x | x 1 = receiptRademacherValue b ∧
    x 2 = receiptRademacherValue (!b)}

theorem receiptSignFlipBranch_measurable (b : Bool) :
    MeasurableSet (receiptSignFlipBranch b) := by
  change MeasurableSet
    ({x : Nat → Real | x 1 = receiptRademacherValue b} ∩
      {x : Nat → Real | x 2 = receiptRademacherValue (!b)})
  have hone : MeasurableSet
      {x : Nat → Real | x 1 = receiptRademacherValue b} := by
    change MeasurableSet ((fun x : Nat → Real ↦ x 1) ⁻¹'
      ({receiptRademacherValue b} : Set Real))
    exact (measurable_pi_apply 1)
      (MeasurableSet.singleton (receiptRademacherValue b))
  have htwo : MeasurableSet
      {x : Nat → Real | x 2 = receiptRademacherValue (!b)} := by
    change MeasurableSet ((fun x : Nat → Real ↦ x 2) ⁻¹'
      ({receiptRademacherValue (!b)} : Set Real))
    exact (measurable_pi_apply 2)
      (MeasurableSet.singleton (receiptRademacherValue (!b)))
  exact hone.inter htwo

theorem receiptState_singleton_mass (b : Bool) :
    receiptStatePMF.toMeasure {receiptRademacherValue b} = 1 / 2 := by
  unfold receiptStatePMF
  rw [(PMF.map receiptRademacherValue
      (PMF.uniformOfFintype Bool)).toMeasure_apply_singleton
        (receiptRademacherValue b)
        (MeasurableSet.singleton (receiptRademacherValue b))]
  cases b <;>
    norm_num [PMF.map_apply, receiptRademacherValue,
      PMF.uniformOfFintype_apply]

theorem receiptSignFlipBranch_mass (b : Bool) :
    (trajectoryMeasure receiptStateKernel 0)
        (receiptSignFlipBranch b) = 1 / 4 := by
  let u0 : (i : Finset.Iic 0) → Real := fun _ ↦ 0
  let one : Finset.Iic 1 := ⟨1, Finset.mem_Iic.mpr le_rfl⟩
  let S : Set ((i : Finset.Iic 1) → Real) :=
    {u | u one = receiptRademacherValue b}
  let T : Set Real := {receiptRademacherValue (!b)}
  have hS : MeasurableSet S := by
    change MeasurableSet
      ((fun u : (i : Finset.Iic 1) → Real ↦ u one) ⁻¹'
        ({receiptRademacherValue b} : Set Real))
    exact (measurable_pi_apply one)
      (MeasurableSet.singleton (receiptRademacherValue b))
  have hT : MeasurableSet T :=
    MeasurableSet.singleton (receiptRademacherValue (!b))
  have hprefixMap :
      (Kernel.partialTraj
        (X := fun _ : Nat ↦ Real) receiptStateKernel 0 1 u0).map
          (fun u : (i : Finset.Iic 1) → Real ↦ u one) =
        receiptStateKernel 0 u0 := by
    have h := congrArg (fun K ↦ K u0)
      (Kernel.map_partialTraj_succ_self
        (X := fun _ : Nat ↦ Real) (κ := receiptStateKernel) 0)
    rw [← Kernel.map_apply _ (measurable_pi_apply one) u0]
    exact h
  have hprefix :
      Kernel.partialTraj
        (X := fun _ : Nat ↦ Real) receiptStateKernel 0 1 u0 S = 1 / 2 := by
    have h := congrArg (fun μ : Measure Real ↦
      μ ({receiptRademacherValue b} : Set Real)) hprefixMap
    rw [Measure.map_apply (measurable_pi_apply one)
      (MeasurableSet.singleton (receiptRademacherValue b))] at h
    have hset :
        (fun u : (i : Finset.Iic 1) → Real ↦ u one) ⁻¹'
            ({receiptRademacherValue b} : Set Real) = S := by
      ext u
      simp [S]
    rw [hset] at h
    have hrhs :
        receiptStateKernel 0 u0
            ({receiptRademacherValue b} : Set Real) = 1 / 2 := by
      change receiptStatePMF.toMeasure
        {receiptRademacherValue b} = 1 / 2
      exact receiptState_singleton_mass b
    exact h.trans hrhs
  have hnext : ∀ u : (i : Finset.Iic 1) → Real,
      receiptStateKernel 1 u T = 1 / 2 := by
    intro u
    change receiptStatePMF.toMeasure
      {receiptRademacherValue (!b)} = 1 / 2
    exact receiptState_singleton_mass (!b)
  have hjoint := Kernel.partialTraj_compProd_eq_map_traj
    (X := fun _ : Nat ↦ Real) (κ := receiptStateKernel) (a := 0) (b := 1)
    (x₀ := u0) (Nat.zero_le 1)
  have h := congrArg
    (fun μ : Measure (((i : Finset.Iic 1) → Real) × Real) ↦ μ (S ×ˢ T))
    hjoint
  rw [Measure.compProd_apply_prod hS hT,
    Measure.map_apply (by fun_prop) (hS.prod hT)] at h
  have hleft :
      ∫⁻ u in S, receiptStateKernel 1 u T
          ∂Kernel.partialTraj
            (X := fun _ : Nat ↦ Real) receiptStateKernel 0 1 u0 = 1 / 4 := by
    simp_rw [hnext]
    rw [setLIntegral_const]
    rw [hprefix]
    apply (ENNReal.toReal_eq_toReal_iff'
      (x := (1 / 2 : ENNReal) * (1 / 2 : ENNReal))
      (y := (1 / 4 : ENNReal))
      (ENNReal.mul_ne_top (by norm_num) (by norm_num))
      (by norm_num)).mp
    norm_num
  rw [hleft] at h
  have hpreimage :
      (fun x : Nat → Real ↦
          (Preorder.frestrictLe 1 x, x (1 + 1))) ⁻¹' (S ×ˢ T) =
        receiptSignFlipBranch b := by
    ext x
    simp [S, T, one, receiptSignFlipBranch,
      Preorder.frestrictLe_apply]
  rw [hpreimage] at h
  simpa [trajectoryMeasure, u0] using h.symm

theorem receiptSignFlipBranch_real_mass (b : Bool) :
    (trajectoryMeasure receiptStateKernel 0).real
        (receiptSignFlipBranch b) = 1 / 4 := by
  rw [measureReal_def, receiptSignFlipBranch_mass]
  norm_num

/-! ## The common event and theorem-produced paths -/

theorem receiptEvent_exists :
    ∃ goodEvent : Set (Nat → Real),
      (trajectoryMeasure receiptStateKernel 0).real goodEventᶜ ≤ receiptDelta ∧
      ∀ x ∈ goodEvent,
        continuousTrajectoryPosteriorAverageConditionalRisk
            receiptStateKernel receiptScore receiptPosterior
            receiptHorizon x <
          continuousTrajectoryPosteriorEmpiricalPrequentialRisk
              receiptScore receiptPosterior receiptHorizon x +
            continuousTrajectoryEmpiricalBernsteinPACBayesBoundary
              receiptPrior receiptWeight receiptTilt receiptScore
              receiptPosterior receiptDelta () receiptHorizon x := by
  obtain ⟨goodEvent, hmass, hgood⟩ :=
    exists_continuousMeasurableTrajectoryEmpiricalBernsteinPACBayes_event
      receiptStateKernel 0 receiptScore receiptScore_mem_Icc
      receiptScore_joint receiptPrior receiptWeight_pos receiptWeight_sum
      (delta := receiptDelta) (lam := receiptTilt)
      (by norm_num [receiptDelta]) receiptTilt_pos receiptTilt_lt_one
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx
  exact hgood x hx () receiptPosterior receiptPosterior_probability
    receiptPosterior_absolutelyContinuous receiptPosterior_llr_integrable
    receiptHorizon (by norm_num [receiptHorizon])

def receiptGoodEvent : Set (Nat → Real) :=
  Classical.choose receiptEvent_exists

theorem receiptGoodEvent_mass_le :
    (trajectoryMeasure receiptStateKernel 0).real receiptGoodEventᶜ ≤
      receiptDelta := by
  exact (Classical.choose_spec receiptEvent_exists).1

theorem receiptGoodEvent_certificate
    {x : Nat → Real} (hx : x ∈ receiptGoodEvent) :
    continuousTrajectoryPosteriorAverageConditionalRisk
        receiptStateKernel receiptScore receiptPosterior receiptHorizon x <
      continuousTrajectoryPosteriorEmpiricalPrequentialRisk
          receiptScore receiptPosterior receiptHorizon x +
        continuousTrajectoryEmpiricalBernsteinPACBayesBoundary
          receiptPrior receiptWeight receiptTilt receiptScore receiptPosterior
          receiptDelta () receiptHorizon x := by
  exact (Classical.choose_spec receiptEvent_exists).2 x hx

theorem receiptGoodPath_in_each_branch (b : Bool) :
    ∃ x : Nat → Real,
      x ∈ receiptSignFlipBranch b ∧ x ∈ receiptGoodEvent := by
  by_contra h
  push Not at h
  have hsubset : receiptSignFlipBranch b ⊆ receiptGoodEventᶜ := by
    intro x hx
    exact h x hx
  have hmono := measureReal_mono
    (μ := trajectoryMeasure receiptStateKernel 0) hsubset
  rw [receiptSignFlipBranch_real_mass] at hmono
  have hmass := receiptGoodEvent_mass_le
  norm_num [receiptDelta] at hmass
  linarith

/-! ## Positive observed variance on both branches -/

theorem receiptObservedScore_pair
    {b : Bool} {x : Nat → Real} (hx : x ∈ receiptSignFlipBranch b)
    (theta : Hypothesis) :
    (observedTrajectoryScore (receiptScore theta) 0 x = 0 ∧
        observedTrajectoryScore (receiptScore theta) 1 x = 1) ∨
      (observedTrajectoryScore (receiptScore theta) 0 x = 1 ∧
        observedTrajectoryScore (receiptScore theta) 1 x = 0) := by
  have hone : x 1 = receiptRademacherValue b := hx.1
  have htwo : x 2 = receiptRademacherValue (!b) := hx.2
  cases b <;> cases htheta : theta.2 <;>
    by_cases hsign : 0 ≤ theta.1 0 <;>
    norm_num [observedTrajectoryScore, receiptScore, receiptPrediction,
      receiptRealLabel, receiptRademacherValue, hone, htwo, htheta, hsign]

theorem receiptBesselQ_pos
    {b : Bool} {x : Nat → Real} (hx : x ∈ receiptSignFlipBranch b)
    (theta : Hypothesis) :
    0 < forwardBesselQ
      (fun k ↦ observedTrajectoryScore (receiptScore theta) k x)
      receiptHorizon := by
  let s : Nat → Real := fun k ↦
    observedTrajectoryScore (receiptScore theta) k x
  let mean : Real := forwardPrefixMean s receiptHorizon
  have hZeroMem : 0 ∈ Finset.range receiptHorizon := by
    norm_num [receiptHorizon]
  have hOneMem : 1 ∈ Finset.range receiptHorizon := by
    norm_num [receiptHorizon]
  have hZeroLe : (s 0 - mean) ^ 2 ≤ forwardBesselQ s receiptHorizon := by
    unfold forwardBesselQ
    exact Finset.single_le_sum
      (fun k _hk ↦ sq_nonneg (s k - forwardPrefixMean s receiptHorizon))
      hZeroMem
  have hOneLe : (s 1 - mean) ^ 2 ≤ forwardBesselQ s receiptHorizon := by
    unfold forwardBesselQ
    exact Finset.single_le_sum
      (fun k _hk ↦ sq_nonneg (s k - forwardPrefixMean s receiptHorizon))
      hOneMem
  have hQnonneg := forwardBesselQ_nonneg s receiptHorizon
  have hpair := receiptObservedScore_pair hx theta
  dsimp [mean] at hZeroLe hOneLe
  change 0 < forwardBesselQ s receiptHorizon
  rcases hpair with ⟨hzero, hone⟩ | ⟨hzero, hone⟩
  · change s 0 = 0 at hzero
    change s 1 = 1 at hone
    rw [hzero] at hZeroLe
    rw [hone] at hOneLe
    nlinarith [sq_nonneg (forwardPrefixMean s receiptHorizon),
      sq_nonneg ((1 : Real) - forwardPrefixMean s receiptHorizon)]
  · change s 0 = 1 at hzero
    change s 1 = 0 at hone
    rw [hzero] at hZeroLe
    rw [hone] at hOneLe
    nlinarith [sq_nonneg (forwardPrefixMean s receiptHorizon),
      sq_nonneg ((1 : Real) - forwardPrefixMean s receiptHorizon)]

theorem receiptSampleVariance_pos
    {b : Bool} {x : Nat → Real} (hx : x ∈ receiptSignFlipBranch b)
    (theta : Hypothesis) :
    0 < FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
      (fun i : Fin receiptHorizon ↦
        observedTrajectoryScore (receiptScore theta) i x) := by
  have hQ := receiptBesselQ_pos hx theta
  have heq := forwardBesselQ_eq_card_sub_one_mul_sampleVarianceBessel
    (x := fun k ↦ observedTrajectoryScore (receiptScore theta) k x)
    (n := receiptHorizon) (by norm_num [receiptHorizon])
  rw [heq] at hQ
  have hfactor : (0 : Real) < receiptHorizon - 1 := by
    norm_num [receiptHorizon]
  nlinarith

/-! ## End-to-end informative receipts -/

/-- Each oriented sign-flip cylinder contains a path on the theorem's common
good event.  On that path the posterior has nonzero KL, every fixed
hypothesis has positive observed Bessel variance, and the complete
empirical-plus-boundary right-hand side is strictly below one. -/
theorem receiptInformative_goodPath_exists (b : Bool) :
    ∃ x : Nat → Real,
      x ∈ receiptSignFlipBranch b ∧
      x ∈ receiptGoodEvent ∧
      (∀ theta : Hypothesis,
        0 < FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
          (fun i : Fin receiptHorizon ↦
            observedTrajectoryScore (receiptScore theta) i x)) ∧
      (∀ s : Finset Hypothesis, receiptPosterior s = 0) ∧
      (InformationTheory.klDiv receiptPosterior receiptPrior).toReal =
        (1 : Real) / 32 ∧
      0 < (InformationTheory.klDiv receiptPosterior receiptPrior).toReal ∧
      continuousTrajectoryPosteriorAverageConditionalRisk
          receiptStateKernel receiptScore receiptPosterior receiptHorizon x =
        (1 : Real) / 2 ∧
      continuousTrajectoryPosteriorEmpiricalPrequentialRisk
          receiptScore receiptPosterior receiptHorizon x = (1 : Real) / 2 ∧
      continuousTrajectoryEmpiricalBernsteinPACBayesBoundary
          receiptPrior receiptWeight receiptTilt receiptScore receiptPosterior
          receiptDelta () receiptHorizon x < (1 : Real) / 2 ∧
      continuousTrajectoryPosteriorAverageConditionalRisk
          receiptStateKernel receiptScore receiptPosterior receiptHorizon x <
        continuousTrajectoryPosteriorEmpiricalPrequentialRisk
            receiptScore receiptPosterior receiptHorizon x +
          continuousTrajectoryEmpiricalBernsteinPACBayesBoundary
            receiptPrior receiptWeight receiptTilt receiptScore
            receiptPosterior receiptDelta () receiptHorizon x ∧
      continuousTrajectoryPosteriorEmpiricalPrequentialRisk
            receiptScore receiptPosterior receiptHorizon x +
          continuousTrajectoryEmpiricalBernsteinPACBayesBoundary
            receiptPrior receiptWeight receiptTilt receiptScore
            receiptPosterior receiptDelta () receiptHorizon x < 1 := by
  obtain ⟨x, hxBranch, hxGood⟩ := receiptGoodPath_in_each_branch b
  have hvar : ∀ theta : Hypothesis,
      0 < FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
        (fun i : Fin receiptHorizon ↦
          observedTrajectoryScore (receiptScore theta) i x) := by
    intro theta
    exact receiptSampleVariance_pos hxBranch theta
  have hfinite : ∀ s : Finset Hypothesis, receiptPosterior s = 0 :=
    receiptPosterior_finite_set_mass_zero
  have hKL := receiptPosterior_kl_eq
  have hKLpos :
      0 < (InformationTheory.klDiv receiptPosterior receiptPrior).toReal := by
    rw [receiptPosterior_kl_eq]
    norm_num
  have hrisk := receiptPosteriorAverageConditionalRisk_eq_half
    (n := receiptHorizon) (by norm_num [receiptHorizon]) x
  have hemp := receiptPosteriorEmpiricalRisk_eq_half
    (n := receiptHorizon) (by norm_num [receiptHorizon]) x
  have hboundary := receiptBoundary_lt_half x
  have hcertificate := receiptGoodEvent_certificate hxGood
  refine ⟨x, hxBranch, hxGood, hvar, hfinite, hKL, hKLpos,
    hrisk, hemp, hboundary, hcertificate, ?_⟩
  rw [hemp]
  linarith

/-- Both orientations of the sign-flip cylinder contain a theorem-produced
good path.  The two witnesses lie on the same common event but need not be the
same path. -/
theorem receiptInformative_bothBranches_exist :
    (∃ x : Nat → Real,
      x ∈ receiptSignFlipBranch false ∧ x ∈ receiptGoodEvent ∧
      (∀ theta : Hypothesis,
        0 < FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
          (fun i : Fin receiptHorizon ↦
            observedTrajectoryScore (receiptScore theta) i x)) ∧
      continuousTrajectoryPosteriorEmpiricalPrequentialRisk
            receiptScore receiptPosterior receiptHorizon x +
          continuousTrajectoryEmpiricalBernsteinPACBayesBoundary
            receiptPrior receiptWeight receiptTilt receiptScore
            receiptPosterior receiptDelta () receiptHorizon x < 1) ∧
    (∃ x : Nat → Real,
      x ∈ receiptSignFlipBranch true ∧ x ∈ receiptGoodEvent ∧
      (∀ theta : Hypothesis,
        0 < FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
          (fun i : Fin receiptHorizon ↦
            observedTrajectoryScore (receiptScore theta) i x)) ∧
      continuousTrajectoryPosteriorEmpiricalPrequentialRisk
            receiptScore receiptPosterior receiptHorizon x +
          continuousTrajectoryEmpiricalBernsteinPACBayesBoundary
            receiptPrior receiptWeight receiptTilt receiptScore
            receiptPosterior receiptDelta () receiptHorizon x < 1) := by
  constructor
  · obtain ⟨x, hxBranch, hxGood, hvar, _hfinite, _hKL, _hKLpos,
      _hrisk, _hemp, _hboundary, _hcertificate, hrhs⟩ :=
        receiptInformative_goodPath_exists false
    exact ⟨x, hxBranch, hxGood, hvar, hrhs⟩
  · obtain ⟨x, hxBranch, hxGood, hvar, _hfinite, _hKL, _hKLpos,
      _hrisk, _hemp, _hboundary, _hcertificate, hrhs⟩ :=
        receiptInformative_goodPath_exists true
    exact ⟨x, hxBranch, hxGood, hvar, hrhs⟩

/-! ## Public receipt and axiom audit -/

#check exists_continuousMeasurableTrajectoryEmpiricalBernsteinPACBayes_event
#check receiptPosterior_kl_eq
#check receiptBoundary_le
#check receiptBoundary_lt_half
#check receiptSignFlipBranch_mass
#check receiptInformative_goodPath_exists
#check receiptInformative_bothBranches_exist

#print axioms receiptBoolPMF_isPMF
#print axioms receiptPosterior_finite_set_mass_zero
#print axioms receiptPosterior_absolutelyContinuous
#print axioms receiptPosterior_llr_integrable
#print axioms receiptPosterior_kl_eq
#print axioms receiptPrediction_measurable
#print axioms receiptRealLabel_measurable
#print axioms receiptScore_joint
#print axioms receiptScore_mem_Icc
#print axioms receiptScore_attains_endpoints
#print axioms receiptScore_uses_gaussian_and_bool
#print axioms receiptConditionalRisk_eq_half
#print axioms receiptTrajectoryAverageConditionalRisk_eq_half
#print axioms receiptPosteriorAverageConditionalRisk_eq_half
#print axioms receiptTwoBoolEmpiricalRisk_add_eq_one
#print axioms receiptBoolIntegralEmpiricalRisk_eq_half
#print axioms receiptPosteriorEmpiricalRisk_eq_half
#print axioms receiptWeight_pos
#print axioms receiptWeight_sum
#print axioms receiptTilt_pos
#print axioms receiptTilt_lt_one
#print axioms receiptPosteriorHybridPenalty_le
#print axioms receiptLogEight_le_three
#print axioms receiptPsiHalf_le_half
#print axioms receiptBoundary_le
#print axioms receiptBoundary_lt_half
#print axioms receiptSignFlipBranch_measurable
#print axioms receiptState_singleton_mass
#print axioms receiptSignFlipBranch_mass
#print axioms receiptSignFlipBranch_real_mass
#print axioms receiptEvent_exists
#print axioms receiptGoodEvent_mass_le
#print axioms receiptGoodEvent_certificate
#print axioms receiptGoodPath_in_each_branch
#print axioms receiptObservedScore_pair
#print axioms receiptBesselQ_pos
#print axioms receiptSampleVariance_pos
#print axioms receiptInformative_goodPath_exists
#print axioms receiptInformative_bothBranches_exist

end

end FormalSLT.Examples.CheckContinuousMeasurableTrajectoryGaussianWitness
