import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Tactic

/-!
# Continuous PAC-Bayes change of measure

This module packages the Radon-Nikodym/tilting change-of-measure step used by
continuous-posterior PAC-Bayes certificates.
-/

namespace FormalSLT.PACBayes.ContinuousChangeOfMeasure

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {Θ : Type*} [MeasurableSpace Θ]

/--
Continuous Donsker-Varadhan variational inequality.

For probability measures `ρ ≪ π`, the posterior integral of `g` is bounded by
`KL(ρ‖π)` plus the prior log-moment of `g`.
-/
theorem continuous_donsker_varadhan
    (ρ π : Measure Θ) [IsProbabilityMeasure ρ] [IsProbabilityMeasure π]
    (hρπ : ρ ≪ π) (g : Θ → ℝ)
    (hg_exp : Integrable (fun x => Real.exp (g x)) π)
    (hg_int : Integrable g ρ)
    (h_llr : Integrable (llr ρ π) ρ) :
    ∫ x, g x ∂ρ ≤
      (InformationTheory.klDiv ρ π).toReal +
        Real.log (∫ x, Real.exp (g x) ∂π) := by
  haveI : IsProbabilityMeasure (π.tilted g) :=
    isProbabilityMeasure_tilted hg_exp
  have hπ_tilted : π ≪ π.tilted g := absolutelyContinuous_tilted hg_exp
  have hρπ_tilted : ρ ≪ π.tilted g := hρπ.trans hπ_tilted
  have h_llr_tilted : Integrable (llr ρ (π.tilted g)) ρ :=
    integrable_llr_tilted_right hρπ hg_int h_llr hg_exp
  have h_nonneg : 0 ≤ (InformationTheory.klDiv ρ (π.tilted g)).toReal :=
    ENNReal.toReal_nonneg
  have h_kl_tilted :
      (InformationTheory.klDiv ρ (π.tilted g)).toReal =
        ∫ x, llr ρ (π.tilted g) x ∂ρ := by
    rw [InformationTheory.toReal_klDiv hρπ_tilted h_llr_tilted]
    simp [measureReal_def]
  have h_kl_base :
      (InformationTheory.klDiv ρ π).toReal =
        ∫ x, llr ρ π x ∂ρ := by
    rw [InformationTheory.toReal_klDiv hρπ h_llr]
    simp [measureReal_def]
  have h_tilted_integral :
      ∫ x, llr ρ (π.tilted g) x ∂ρ =
        ∫ x, llr ρ π x ∂ρ - ∫ x, g x ∂ρ +
          Real.log (∫ x, Real.exp (g x) ∂π) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      integral_llr_tilted_right hρπ hg_int hg_exp h_llr
  have h_identity :
      (InformationTheory.klDiv ρ (π.tilted g)).toReal =
        (InformationTheory.klDiv ρ π).toReal - ∫ x, g x ∂ρ +
          Real.log (∫ x, Real.exp (g x) ∂π) := by
    rw [h_kl_tilted, h_tilted_integral, h_kl_base]
  linarith

/--
Continuous Catoni fixed-`lambda` change-of-measure bound.

The prior log-MGF certificate is supplied in log form:
`log E_π exp(lambda * (risk - empiricalRisk)) ≤ lambda^2 * B + log(1/delta)`.
-/
theorem continuous_catoni_changeOfMeasure_bound
    (ρ π : Measure Θ) [IsProbabilityMeasure ρ] [IsProbabilityMeasure π]
    (hρπ : ρ ≪ π)
    (risk empiricalRisk : Θ → ℝ)
    {lambda delta B : ℝ}
    (hlambda : 0 < lambda) (hdelta : 0 < delta)
    (hrisk_int : Integrable risk ρ)
    (hempirical_int : Integrable empiricalRisk ρ)
    (hllr : Integrable (llr ρ π) ρ)
    (hmgf_int :
      Integrable (fun θ => Real.exp (lambda * (risk θ - empiricalRisk θ))) π)
    (hlog_mgf :
      Real.log
          (∫ θ, Real.exp (lambda * (risk θ - empiricalRisk θ)) ∂π)
        ≤ lambda ^ (2 : Nat) * B + Real.log (1 / delta)) :
    ∫ θ, risk θ ∂ρ ≤
      ∫ θ, empiricalRisk θ ∂ρ +
        ((InformationTheory.klDiv ρ π).toReal + Real.log (1 / delta)) / lambda +
          lambda * B := by
  have _ := hdelta
  let gap : Θ → ℝ := fun θ => lambda * (risk θ - empiricalRisk θ)
  have hgap_int : Integrable gap ρ := by
    dsimp [gap]
    exact (hrisk_int.sub hempirical_int).const_mul lambda
  have hdv :=
    continuous_donsker_varadhan ρ π hρπ gap hmgf_int hgap_int hllr
  have hgap_integral :
      ∫ θ, gap θ ∂ρ =
        lambda * (∫ θ, risk θ ∂ρ - ∫ θ, empiricalRisk θ ∂ρ) := by
    dsimp [gap]
    rw [integral_const_mul, integral_sub hrisk_int hempirical_int]
  have hgap_bound :
      lambda * (∫ θ, risk θ ∂ρ - ∫ θ, empiricalRisk θ ∂ρ) ≤
        (InformationTheory.klDiv ρ π).toReal +
          (lambda ^ (2 : Nat) * B + Real.log (1 / delta)) := by
    rw [← hgap_integral]
    linarith
  have hdiff :
      ∫ θ, risk θ ∂ρ - ∫ θ, empiricalRisk θ ∂ρ ≤
        ((InformationTheory.klDiv ρ π).toReal +
          lambda ^ (2 : Nat) * B + Real.log (1 / delta)) / lambda := by
    rw [le_div_iff₀ hlambda]
    nlinarith
  calc
    ∫ θ, risk θ ∂ρ
        = ∫ θ, empiricalRisk θ ∂ρ +
            (∫ θ, risk θ ∂ρ - ∫ θ, empiricalRisk θ ∂ρ) := by ring
    _ ≤ ∫ θ, empiricalRisk θ ∂ρ +
            ((InformationTheory.klDiv ρ π).toReal +
              lambda ^ (2 : Nat) * B + Real.log (1 / delta)) / lambda :=
        by linarith
    _ = ∫ θ, empiricalRisk θ ∂ρ +
          ((InformationTheory.klDiv ρ π).toReal + Real.log (1 / delta)) / lambda +
            lambda * B := by
        field_simp [ne_of_gt hlambda]
        ring

/-! ### Concrete non-vacuity witness -/

/-- Two-point parameter space for a concrete continuous-measure witness. -/
abbrev TwoPointParameter := Bool

/-- A Dirac prior on the two-point parameter space. -/
def twoPointPriorMeasure : Measure TwoPointParameter := Measure.dirac true

/-- A matching Dirac posterior, so the KL term is finite and equal to zero. -/
def twoPointPosteriorMeasure : Measure TwoPointParameter := Measure.dirac true

/-- A nonzero gap observable on the two-point space. -/
def twoPointGap : TwoPointParameter → ℝ := fun θ => if θ then (1 : ℝ) / 4 else 0

/-- A nonzero risk observable for the Catoni witness. -/
def twoPointRisk : TwoPointParameter → ℝ := twoPointGap

/-- Zero empirical risk for the Catoni witness. -/
def twoPointEmpiricalRisk : TwoPointParameter → ℝ := fun _ => 0

instance twoPointPrior_isProbabilityMeasure :
    IsProbabilityMeasure twoPointPriorMeasure := by
  unfold twoPointPriorMeasure
  infer_instance

instance twoPointPosterior_isProbabilityMeasure :
    IsProbabilityMeasure twoPointPosteriorMeasure := by
  unfold twoPointPosteriorMeasure
  infer_instance

/-- The two-point posterior is absolutely continuous with respect to the prior. -/
theorem twoPoint_absolutelyContinuous :
    twoPointPosteriorMeasure ≪ twoPointPriorMeasure :=
  Measure.AbsolutelyContinuous.rfl

/-- The continuous Donsker-Varadhan theorem applies to a nonzero two-point gap. -/
theorem twoPoint_continuous_dv_nonvacuous :
    ∫ θ, twoPointGap θ ∂twoPointPosteriorMeasure ≤
      (InformationTheory.klDiv twoPointPosteriorMeasure twoPointPriorMeasure).toReal +
        Real.log (∫ θ, Real.exp (twoPointGap θ) ∂twoPointPriorMeasure) := by
  refine continuous_donsker_varadhan
    twoPointPosteriorMeasure twoPointPriorMeasure
    twoPoint_absolutelyContinuous twoPointGap ?_ ?_ ?_
  · simp [twoPointPriorMeasure, twoPointGap]
  · simp [twoPointPosteriorMeasure]
  · unfold twoPointPosteriorMeasure twoPointPriorMeasure
    rw [integrable_congr (llr_self (Measure.dirac true))]
    exact integrable_zero TwoPointParameter ℝ (Measure.dirac true)

/-- The two-point gap is strictly below the trivial unit bound. -/
theorem twoPoint_gap_strictly_below_one :
    ∫ θ, twoPointGap θ ∂twoPointPosteriorMeasure < (1 : ℝ) := by
  norm_num [twoPointPosteriorMeasure, twoPointGap]

/-- The continuous Catoni theorem gives a finite nonzero two-point certificate. -/
theorem twoPoint_continuous_certificate_nonvacuous :
    ∫ θ, twoPointRisk θ ∂twoPointPosteriorMeasure ≤
      ∫ θ, twoPointEmpiricalRisk θ ∂twoPointPosteriorMeasure +
        ((InformationTheory.klDiv twoPointPosteriorMeasure twoPointPriorMeasure).toReal +
            Real.log (1 / (1 : ℝ))) / (1 : ℝ) +
          (1 : ℝ) * 1 := by
  refine continuous_catoni_changeOfMeasure_bound
    twoPointPosteriorMeasure twoPointPriorMeasure
    twoPoint_absolutelyContinuous twoPointRisk twoPointEmpiricalRisk
    (lambda := 1) (delta := 1) (B := 1)
    (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_
  · simp [twoPointPosteriorMeasure, twoPointRisk]
  · simp [twoPointPosteriorMeasure]
  · unfold twoPointPosteriorMeasure twoPointPriorMeasure
    rw [integrable_congr (llr_self (Measure.dirac true))]
    exact integrable_zero TwoPointParameter ℝ (Measure.dirac true)
  · simp [twoPointPriorMeasure, twoPointRisk, twoPointEmpiricalRisk, twoPointGap]
  · norm_num [twoPointPriorMeasure, twoPointRisk, twoPointEmpiricalRisk, twoPointGap]

end

end FormalSLT.PACBayes.ContinuousChangeOfMeasure
