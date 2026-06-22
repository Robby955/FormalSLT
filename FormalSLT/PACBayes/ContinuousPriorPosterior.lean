import FormalSLT.PACBayes.ContinuousChangeOfMeasure
import FormalSLT.PACBayes.VitaleLemma

/-!
# Continuous prior/posterior PAC-Bayes certificate

This module records the continuous-prior/posterior certificate data used by the
Bernstein PAC-Bayes bound. The prior and posterior are measures on an arbitrary
measurable parameter space. The high-probability PAC-Bayes gate is supplied as
an explicit hypothesis; it is not derived in this file.
-/

namespace FormalSLT.PACBayes

open MeasureTheory

/-- Continuous-prior PAC-Bayes certificate data. -/
structure ContinuousPriorPosteriorSpec (Θ : Type*) [MeasurableSpace Θ] where
  prior : Measure Θ
  posterior : Measure Θ
  sampleSize : ℕ
  lossBound : ℝ
  empiricalRisk : ℝ
  populationRisk : ℝ
  varianceBound : ℝ
  klBound : ℝ
  confidencePenalty : ℝ
  complexityBound : ℝ
  pacPenalty : ℝ

/-- Complexity term after adding the confidence penalty. -/
def continuousPriorPosteriorComplexity
    {Θ : Type*} [MeasurableSpace Θ]
    (spec : ContinuousPriorPosteriorSpec Θ) : ℝ :=
  spec.klBound + spec.confidencePenalty

/-- PAC risk upper side for the continuous prior/posterior certificate. -/
def continuousPriorPosteriorBound
    {Θ : Type*} [MeasurableSpace Θ]
    (spec : ContinuousPriorPosteriorSpec Θ) : ℝ :=
  spec.empiricalRisk + spec.pacPenalty

/--
Continuous prior/posterior PAC-Bayes certificate, conditional on explicit KL
and high-probability PAC gates.

The theorem does not assume a finite hypothesis class. It also does not derive
the high-probability gate; that gate is the hypothesis `hpacGate`.
-/
theorem continuousPriorPosterior_certificate_of_kl
    {Θ : Type*} [MeasurableSpace Θ]
    (spec : ContinuousPriorPosteriorSpec Θ)
    (hcomplexity :
      continuousPriorPosteriorComplexity spec ≤ spec.complexityBound)
    (hpacGate :
      spec.populationRisk ≤ continuousPriorPosteriorBound spec) :
    spec.populationRisk ≤ continuousPriorPosteriorBound spec := by
  have _ := hcomplexity
  exact hpacGate

/--
Continuous prior/posterior PAC-Bayes certificate with the PAC gate derived by
the Radon-Nikodym change-of-measure theorem.

The finite-sample prior log-MGF certificate is still an explicit hypothesis;
this theorem discharges only the continuous posterior change-of-measure step.
-/
theorem continuousPriorPosterior_certificate_derived
    {Θ : Type*} [MeasurableSpace Θ]
    (spec : ContinuousPriorPosteriorSpec Θ)
    [IsProbabilityMeasure spec.posterior] [IsProbabilityMeasure spec.prior]
    (hcomplexity :
      continuousPriorPosteriorComplexity spec ≤ spec.complexityBound)
    (hρπ : spec.posterior ≪ spec.prior)
    (risk empiricalRisk : Θ → ℝ)
    {lambda delta B : ℝ}
    (hlambda : 0 < lambda) (hdelta : 0 < delta)
    (hrisk_int : Integrable risk spec.posterior)
    (hempirical_int : Integrable empiricalRisk spec.posterior)
    (hllr : Integrable (llr spec.posterior spec.prior) spec.posterior)
    (hmgf_int :
      Integrable
        (fun θ => Real.exp (lambda * (risk θ - empiricalRisk θ)))
        spec.prior)
    (hlog_mgf :
      Real.log
          (∫ θ, Real.exp (lambda * (risk θ - empiricalRisk θ)) ∂spec.prior)
        ≤ lambda ^ (2 : Nat) * B + Real.log (1 / delta))
    (hpopulation :
      spec.populationRisk = ∫ θ, risk θ ∂spec.posterior)
    (hempirical :
      spec.empiricalRisk = ∫ θ, empiricalRisk θ ∂spec.posterior)
    (hpenalty :
      ((InformationTheory.klDiv spec.posterior spec.prior).toReal +
          Real.log (1 / delta)) / lambda + lambda * B ≤ spec.pacPenalty) :
    spec.populationRisk ≤ continuousPriorPosteriorBound spec := by
  have _ := hcomplexity
  have hgate :=
    ContinuousChangeOfMeasure.continuous_catoni_changeOfMeasure_bound
      spec.posterior spec.prior hρπ risk empiricalRisk
      hlambda hdelta hrisk_int hempirical_int hllr hmgf_int hlog_mgf
  calc
    spec.populationRisk = ∫ θ, risk θ ∂spec.posterior := hpopulation
    _ ≤ ∫ θ, empiricalRisk θ ∂spec.posterior +
          ((InformationTheory.klDiv spec.posterior spec.prior).toReal +
              Real.log (1 / delta)) / lambda + lambda * B := hgate
    _ ≤ ∫ θ, empiricalRisk θ ∂spec.posterior + spec.pacPenalty := by
      linarith
    _ = spec.empiricalRisk + spec.pacPenalty := by rw [hempirical]
    _ = continuousPriorPosteriorBound spec := rfl

end FormalSLT.PACBayes
