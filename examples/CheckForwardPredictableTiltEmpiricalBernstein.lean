import FormalSLT.AnytimeValid.ForwardPredictableTiltEmpiricalBernstein
import FormalSLT.AnytimeValid.BettingCS

/-!
# Predictable-tilt forward empirical-Bernstein checker

Checks the per-time, past-measurable tilt construction.  The endpoint is an
e-process for bounded observations and predictable conditional means.  It is
not a post-hoc tilt catalog and does not assert an unweighted Bessel boundary.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid

variable {Omega : Type*} [mOmega : MeasurableSpace Omega]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  {F : Filtration ℕ mOmega}

noncomputable section

/-- Focused receipt for the predictable-tilt empirical-Bernstein e-process. -/
theorem forwardPredictableTilt_eProcess_receipt
    {X mean lambda : ℕ → Omega → ℝ} {L : ℝ}
    (hL1 : L < 1)
    (hX_adapted : IncrementAdapted F X)
    (hmean_adapted : StronglyAdapted F mean)
    (hlambda_adapted : StronglyAdapted F lambda)
    (hX_unit : ∀ k omega, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hlambda_range : ∀ k omega,
      0 ≤ lambda k omega ∧ lambda k omega ≤ L)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] mean k) :
    EProcess mu F
      (forwardPredictableTiltMeanEmpiricalBernsteinProcess
        X mean lambda) :=
  forwardPredictableTiltMeanEmpiricalBernsteinProcess_eProcess_of_bounded
    hL1 hX_adapted hmean_adapted hlambda_adapted hX_unit
    hlambda_range hmean

namespace ForwardPredictableTiltWitness

open FormalSLT.AnytimeValid.BettingNonVacuityWitness

/-- One Bernoulli observation, followed by zero observations. -/
def witnessX : ℕ → Bool → ℝ :=
  fun k omega => if k = 0 then (if omega then 1 else 0) else 0

/-- The predictable conditional mean of `witnessX`. -/
def witnessMean : ℕ → Bool → ℝ :=
  fun k _ => if k = 0 then 1 / 2 else 0

/-- A predictable schedule that changes after observing the first outcome. -/
def witnessLambda : ℕ → Bool → ℝ :=
  fun k omega =>
    if k = 1 then (if omega then 1 / 2 else 1 / 4) else 1 / 4

theorem witnessX_incrementAdapted : IncrementAdapted filtBool witnessX := by
  intro k
  have hfilt : filtBool (k + 1) = ⊤ := by simp [filtBool]
  rw [show (StronglyMeasurable[filtBool (k + 1)] (witnessX k)) =
      (StronglyMeasurable[⊤] (witnessX k)) from by rw [hfilt]]
  exact measurable_from_top.stronglyMeasurable

theorem witnessMean_stronglyAdapted :
    StronglyAdapted filtBool witnessMean := by
  intro k
  exact stronglyMeasurable_const

theorem witnessLambda_stronglyAdapted :
    StronglyAdapted filtBool witnessLambda := by
  intro k
  by_cases hk : k = 0
  · subst k
    rw [show filtBool 0 = ⊥ by simp [filtBool]]
    have hfun : witnessLambda 0 = fun _ : Bool => (1 / 4 : ℝ) := by
      funext omega
      norm_num [witnessLambda]
    rw [hfun]
    exact stronglyMeasurable_const
  · have hfilt : filtBool k = ⊤ := by simp [filtBool, hk]
    rw [show (StronglyMeasurable[filtBool k] (witnessLambda k)) =
        (StronglyMeasurable[⊤] (witnessLambda k)) from by rw [hfilt]]
    exact measurable_from_top.stronglyMeasurable

theorem witnessX_unit (k : ℕ) (omega : Bool) :
    0 ≤ witnessX k omega ∧ witnessX k omega ≤ 1 := by
  by_cases hk : k = 0
  · subst k
    cases omega <;> norm_num [witnessX]
  · simp [witnessX, hk]

theorem witnessLambda_range (k : ℕ) (omega : Bool) :
    0 ≤ witnessLambda k omega ∧ witnessLambda k omega ≤ (1 / 2 : ℝ) := by
  by_cases hk : k = 1
  · subst k
    cases omega <;> norm_num [witnessLambda]
  · norm_num [witnessLambda, hk]

theorem witness_center (k : ℕ) :
    μBool[witnessX k | filtBool k] =ᵐ[μBool] witnessMean k := by
  by_cases hk : k = 0
  · subst k
    have hF0 : filtBool 0 = ⊥ := by simp [filtBool]
    rw [hF0, condExp_bot]
    have hint : ∫ x, witnessX 0 x ∂μBool = (1 / 2 : ℝ) := by
      haveI : IsFiniteMeasure
          ((1 / 2 : ENNReal) • Measure.dirac (true : Bool)) :=
        Measure.smul_finite _ (by norm_num)
      haveI : IsFiniteMeasure
          ((1 / 2 : ENNReal) • Measure.dirac (false : Bool)) :=
        Measure.smul_finite _ (by norm_num)
      rw [μBool, integral_add_measure (Integrable.of_finite) (Integrable.of_finite),
        integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
      simp only [witnessX, smul_eq_mul]
      norm_num
    rw [hint]
    exact Filter.Eventually.of_forall (by
      intro omega
      norm_num [witnessMean])
  · have hXk : witnessX k = 0 := by
      funext omega
      simp [witnessX, hk]
    have hMk : witnessMean k = 0 := by
      funext omega
      simp [witnessMean, hk]
    rw [hXk, hMk, condExp_zero]

/-- The schedule genuinely depends on the observed first outcome at time one. -/
theorem witnessLambda_path_dependent :
    witnessLambda 1 true ≠ witnessLambda 1 false := by
  norm_num [witnessLambda]

/-- Concrete e-process witness with a nonconstant predictable tilt. -/
theorem witness_eProcess :
    EProcess μBool filtBool
      (forwardPredictableTiltMeanEmpiricalBernsteinProcess
        witnessX witnessMean witnessLambda) := by
  exact forwardPredictableTiltMeanEmpiricalBernsteinProcess_eProcess_of_bounded
    (L := (1 / 2 : ℝ)) (by norm_num)
    witnessX_incrementAdapted witnessMean_stronglyAdapted
    witnessLambda_stronglyAdapted witnessX_unit witnessLambda_range
    witness_center

end ForwardPredictableTiltWitness

#check forwardPredictableTiltMeanEmpiricalBernsteinFactor
#check forwardPredictableTiltMeanEmpiricalBernsteinProcess
#check forwardPredictableTiltMeanEmpiricalBernsteinProcess_succ
#check forwardPredictableTiltMeanEmpiricalBernsteinFactor_condExp_le_one
#check stronglyAdapted_forwardPredictableTiltMeanEmpiricalBernsteinProcess
#check forwardPredictableTiltMeanEmpiricalBernsteinFactor_le_exp
#check forwardPredictableTiltMeanEmpiricalBernsteinProcess_le_exp
#check forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_le_exp
#check forwardPredictableTiltMeanEmpiricalBernsteinProcess_eProcess_of_bounded
#check forwardPredictableTiltMeanEmpiricalBernstein_typeI_control
#check forwardPredictableTiltMeanEmpiricalBernsteinFactor_const_tilt_eq
#check forwardPredictableTiltMeanEmpiricalBernsteinProcess_const_tilt_eq
#check forwardPredictableTilt_eProcess_receipt
#check ForwardPredictableTiltWitness.witnessLambda_path_dependent
#check ForwardPredictableTiltWitness.witness_eProcess

#print axioms forwardPredictableTiltMeanEmpiricalBernsteinFactor_condExp_le_one
#print axioms stronglyAdapted_forwardPredictableTiltMeanEmpiricalBernsteinProcess
#print axioms forwardPredictableTiltMeanEmpiricalBernsteinFactor_le_exp
#print axioms forwardPredictableTiltMeanEmpiricalBernsteinProcess_le_exp
#print axioms forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_le_exp
#print axioms forwardPredictableTiltMeanEmpiricalBernsteinProcess_eProcess_of_bounded
#print axioms forwardPredictableTiltMeanEmpiricalBernstein_typeI_control
#print axioms forwardPredictableTiltMeanEmpiricalBernsteinFactor_const_tilt_eq
#print axioms forwardPredictableTiltMeanEmpiricalBernsteinProcess_const_tilt_eq
#print axioms forwardPredictableTilt_eProcess_receipt
#print axioms ForwardPredictableTiltWitness.witnessLambda_path_dependent
#print axioms ForwardPredictableTiltWitness.witness_eProcess
