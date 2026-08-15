/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayes.TimeUniformTiltMixture
import FormalSLT.AnytimeValid.BettingCS

/-!
# Checked finite hypothesis--tilt master e-process

This receipt instantiates the generic master process with two Boolean
hypotheses, two distinct positive tilts, and normalized positive weights.  One
hypothesis uses the nonzero Rademacher increment from the betting-CS witness;
the other uses the zero increment process.  The resulting mixture is a genuine
e-process, exceeds one on the positive outcome, and satisfies one Ville bound
controlling every posterior and both declared tilts.  The family is finite and
predeclared; this is not a countable or all-real tilt theorem.
-/

namespace FormalSLT.Examples.CheckTimeUniformTiltMixture

open MeasureTheory ProbabilityTheory
open Finset Real BigOperators
open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.BettingNonVacuityWitness
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.TimeUniform

noncomputable section

local instance (q : Prop) : Decidable q := Classical.propDecidable q

/-- Uniform full-support prior on the two hypotheses. -/
def uniformPrior : Bool → ℝ := fun _ => (1 : ℝ) / 2

theorem uniformPrior_isFullSupportPMF : IsFullSupportPMF uniformPrior := by
  constructor
  · constructor <;> simp [uniformPrior]
  · intro i
    simp [uniformPrior]

/-- Uniform full-support weights on the two declared tilts. -/
def uniformTiltWeight : Bool → ℝ := fun _ => (1 : ℝ) / 2

theorem uniformTiltWeight_isFullSupportPMF :
    IsFullSupportPMF uniformTiltWeight := by
  constructor
  · constructor <;> simp [uniformTiltWeight]
  · intro j
    simp [uniformTiltWeight]

/-- Two distinct admissible tilts, `1/4` and `1/2`. -/
def twoTilts : Bool → ℝ := fun j => if j then (1 : ℝ) / 2 else (1 : ℝ) / 4

theorem twoTilts_pos (j : Bool) : 0 < twoTilts j := by
  cases j <;> norm_num [twoTilts]

theorem twoTilts_lt_three (j : Bool) : twoTilts j < 3 := by
  cases j <;> norm_num [twoTilts]

/-- One hypothesis uses the zero process and the other the Rademacher process. -/
def incrementFamily : Bool → ℕ → Bool → ℝ :=
  fun i => if i then XBool else 0

theorem incrementFamily_meas (i : Bool) (k : ℕ) :
    Measurable (incrementFamily i k) :=
  measurable_from_top

theorem incrementFamily_int (i : Bool) (k : ℕ) :
    Integrable (incrementFamily i k) BettingNonVacuityWitness.μBool := by
  cases i
  · simp [incrementFamily]
  · change Integrable (XBool k) BettingNonVacuityWitness.μBool
    exact XBool_int k

theorem incrementFamily_adapted (i : Bool) :
    IncrementAdapted filtBool (incrementFamily i) := by
  cases i
  · intro k
    change StronglyMeasurable[filtBool (k + 1)]
      (fun _ : Bool => (0 : ℝ))
    exact stronglyMeasurable_const
  · simpa [incrementFamily] using XBool_incrementAdapted

theorem incrementFamily_exp_int (i j : Bool) (n : ℕ) :
    Integrable
      (subGammaExponentialProcess
        (incrementFamily i) 1 1 (twoTilts j) n)
      BettingNonVacuityWitness.μBool :=
  Integrable.of_finite

theorem incrementFamily_bound (i : Bool) (k : ℕ) :
    ∀ᵐ ω ∂BettingNonVacuityWitness.μBool,
      |incrementFamily i k ω| ≤ (1 : ℝ) := by
  cases i
  · simp [incrementFamily]
  · refine Filter.Eventually.of_forall ?_
    intro ω
    by_cases hk : k = 0
    · subst hk
      cases ω <;> norm_num [incrementFamily, XBool]
    · simp [incrementFamily, XBool, hk]

theorem incrementFamily_center (i : Bool) (k : ℕ) :
    BettingNonVacuityWitness.μBool[incrementFamily i k | filtBool k]
      =ᵐ[BettingNonVacuityWitness.μBool] 0 := by
  cases i
  · simp [incrementFamily]
  · simpa [incrementFamily] using XBool_center k

theorem incrementFamily_condSecondMoment_le_one (i : Bool) (k : ℕ) :
    BettingNonVacuityWitness.μBool[
        fun ω => (incrementFamily i k ω) ^ 2 | filtBool k]
      ≤ᵐ[BettingNonVacuityWitness.μBool] fun _ => (1 : ℝ) := by
  cases i
  · have hsq :
        (fun ω => (incrementFamily false k ω) ^ 2) =
          (0 : Bool → ℝ) := by
      funext ω
      simp [incrementFamily]
    rw [hsq, condExp_zero]
    exact Filter.Eventually.of_forall (by intro ω; norm_num)
  · by_cases hk : k = 0
    · subst hk
      have hsq :
          (fun ω => (incrementFamily true 0 ω) ^ 2) =
            (fun _ : Bool => (1 : ℝ)) := by
        funext ω
        cases ω <;> norm_num [incrementFamily, XBool]
      rw [hsq, condExp_const (filtBool.le 0)]
    · have hzero : incrementFamily true k = 0 := by
        funext ω
        simp [incrementFamily, XBool, hk]
      have hsq :
          (fun ω => (incrementFamily true k ω) ^ 2) =
            (0 : Bool → ℝ) := by
        funext ω
        rw [hzero]
        simp
      rw [hsq, condExp_zero]
      exact Filter.Eventually.of_forall (by intro ω; norm_num)

/-- The concrete two-hypothesis, two-tilt master process. -/
def twoTiltMaster : ℕ → Bool → ℝ :=
  pacBayesPriorTiltMixtureProcess
    uniformPrior uniformTiltWeight incrementFamily 1 1 twoTilts

/-- The two-tilt master is a genuine e-process. -/
theorem twoTiltMaster_eProcess :
    EProcess BettingNonVacuityWitness.μBool filtBool twoTiltMaster := by
  exact pacBayesPriorTiltMixture_eProcess
    (μ := BettingNonVacuityWitness.μBool) (ℱ := filtBool)
    (X := incrementFamily) (sigma2 := 1) (b := 1) (lam := twoTilts)
    uniformPrior_isFullSupportPMF uniformTiltWeight_isFullSupportPMF
    (by norm_num) (by norm_num) twoTilts_pos
    (fun j => by simpa using twoTilts_lt_three j)
    incrementFamily_meas incrementFamily_int incrementFamily_adapted
    incrementFamily_exp_int incrementFamily_bound incrementFamily_center
    incrementFamily_condSecondMoment_le_one

/-- Nontriviality: on the positive Rademacher outcome the master exceeds one. -/
theorem twoTiltMaster_exceeds_one : (1 : ℝ) < twoTiltMaster 1 true := by
  have hsmallPos := Real.add_one_lt_exp (show (19 : ℝ) / 88 ≠ 0 by norm_num)
  have hsmallZero := Real.add_one_le_exp (-(3 : ℝ) / 88)
  have hlargePos := Real.add_one_lt_exp (show (7 : ℝ) / 20 ≠ 0 by norm_num)
  have hlargeZero := Real.add_one_le_exp (-(3 : ℝ) / 20)
  simp only [twoTiltMaster, pacBayesPriorTiltMixtureProcess,
    pacBayesPriorMixtureProcess, uniformPrior, uniformTiltWeight,
    incrementFamily, twoTilts, Fintype.sum_bool,
    subGammaExponentialProcess, runningSum, Finset.sum_range_one,
    subGammaCgf]
  norm_num [XBool]
  nlinarith [hsmallPos, hsmallZero, hlargePos, hlargeZero]

/-- One Ville event controls both tilts and every posterior at all times. -/
theorem twoTiltMaster_allPosteriors_mass_le_quarter :
    BettingNonVacuityWitness.μBool.real
        (timeUniformPACBayesTiltMixtureAnyPosteriorUpperFailure
          uniformPrior uniformTiltWeight incrementFamily 1 1 twoTilts
            ((1 : ℝ) / 4))
      ≤ (1 : ℝ) / 4 := by
  exact timeUniformPACBayes_tiltMixture_allPosteriors_bound
    (μ := BettingNonVacuityWitness.μBool) (ℱ := filtBool)
    (X := incrementFamily) (sigma2 := 1) (b := 1) (lam := twoTilts)
    (delta := (1 : ℝ) / 4)
    uniformPrior_isFullSupportPMF uniformTiltWeight_isFullSupportPMF
    (by norm_num) (by norm_num) (by norm_num)
    twoTilts_pos (fun j => by simpa using twoTilts_lt_three j)
    incrementFamily_meas incrementFamily_int
    incrementFamily_adapted incrementFamily_exp_int incrementFamily_bound
    incrementFamily_center incrementFamily_condSecondMoment_le_one

#check pacBayesPriorTiltMixtureProcess
#check pacBayesPriorTiltMixtureProcess_nonneg
#check pacBayesPriorTiltMixtureProcess_zero
#check pacBayesPriorTiltMixture_supermartingale
#check pacBayesPriorTiltMixture_eProcess
#check pacBayesPriorTiltMixture_optionalContinuation
#check timeUniformPACBayesTiltMixtureAnyPosteriorUpperFailure
#check timeUniformPACBayes_tiltMixture_crossing_bound
#check timeUniformPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_crossing
#check timeUniformPACBayes_tiltMixture_allPosteriors_bound
#check timeUniformPACBayes_tiltMixture_allPosteriors_of_not_mem
#check timeUniformPACBayes_tiltMixture_selected_of_not_mem
#check twoTiltMaster_eProcess
#check twoTiltMaster_exceeds_one
#check twoTiltMaster_allPosteriors_mass_le_quarter

#print axioms pacBayesPriorTiltMixtureProcess_nonneg
#print axioms pacBayesPriorTiltMixtureProcess_zero
#print axioms pacBayesPriorTiltMixture_supermartingale
#print axioms pacBayesPriorTiltMixture_eProcess
#print axioms pacBayesPriorTiltMixture_optionalContinuation
#print axioms timeUniformPACBayes_tiltMixture_crossing_bound
#print axioms timeUniformPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_crossing
#print axioms timeUniformPACBayes_tiltMixture_allPosteriors_bound
#print axioms timeUniformPACBayes_tiltMixture_allPosteriors_of_not_mem
#print axioms timeUniformPACBayes_tiltMixture_selected_of_not_mem
#print axioms twoTiltMaster_eProcess
#print axioms twoTiltMaster_exceeds_one
#print axioms twoTiltMaster_allPosteriors_mass_le_quarter

end

end FormalSLT.Examples.CheckTimeUniformTiltMixture
