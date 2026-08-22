import FormalSLT.PACBayes.Compiler
import FormalSLT.PACBayes.GaussianKL

/-!
# General-width PAC-Bayes regression stub

Concrete bounded-regression certificate with loss bound `b = 5`, sample size
1000, confidence `δ = 0.05`, and a Gaussian-posterior KL check derived from
the finite-dimensional Gaussian measure backend.
-/

namespace FormalSLT.Examples.RegressionStubGeneralWidthCertificate

open FormalSLT.PACBayes
open FormalSLT.PACBayesKL

noncomputable section

def lossBoundMilli : Int := 5000

def sampleSize : Nat := 1000

def confidencePercent : Nat := 95

def empiricalRiskMilli : Int := 1750

def generalPenaltyMilli : Int := 250

def generalBoundMilli : Int := empiricalRiskMilli + generalPenaltyMilli

def gaussianPrior : SphericalGaussianParams 3 where
  mean := fun _ => 0
  variance := 1
  variance_pos := by norm_num

def gaussianPosterior : SphericalGaussianParams 3 where
  mean := fun _ => 1
  variance := 1
  variance_pos := by norm_num

def gaussianPosteriorKL : ℝ :=
  sphericalGaussianKL gaussianPosterior gaussianPrior

def gaussianPosteriorKLCap : ℝ := 100

/-- Gaussian posterior KL value used by the finite regression stub. -/
theorem gaussianPosterior_kl_eq :
    gaussianPosteriorKL = (3 : ℝ) / 2 := by
  rw [gaussianPosteriorKL, sphericalGaussianKL_eq_closedForm]
  norm_num [gaussianPrior, gaussianPosterior, squaredMeanDistance,
    sphericalGaussianKLClosedForm]

/-- Gaussian posterior KL cap used by the finite regression stub. -/
theorem gaussianPosterior_kl_within_cap :
    gaussianPosteriorKL ≤ gaussianPosteriorKLCap := by
  rw [gaussianPosterior_kl_eq]
  norm_num [gaussianPosteriorKLCap]

/-- The displayed general-width bound side is within the declared loss width. -/
theorem regressionStubGeneralWidth_bound_certificate :
    generalBoundMilli ≤ lossBoundMilli := by
  norm_num [generalBoundMilli, empiricalRiskMilli, generalPenaltyMilli,
    lossBoundMilli]

namespace Stub

noncomputable def dataLaw : Fin 3 → ℝ := fun _ => (1 : ℝ) / 3

noncomputable def prior : Fin 4 → ℝ := fun _ => (1 : ℝ) / 4

noncomputable def loss : Fin 4 → Fin 3 → ℝ := fun _ z =>
  if z = 0 then 0 else if z = 1 then (5 : ℝ) / 2 else 5

noncomputable def spec : PACBayesCertificateSpec (Fin 4) (Fin 3) where
  lossBound := 5
  sampleSize := FormalSLT.Examples.RegressionStubGeneralWidthCertificate.sampleSize
  hypothesisCardinality := 4
  dataLaw := dataLaw
  prior := prior
  posterior := fun i => if i = 0 then 1 else 0
  loss := loss
  delta := (1 : ℝ) / 20
  complexityBound := (2 : ℝ)

theorem dataLaw_isPMF : IsPMF dataLaw := by
  refine ⟨?_, ?_⟩
  · intro _; norm_num [dataLaw]
  · simp [dataLaw]

theorem prior_isFullSupportPMF : IsFullSupportPMF prior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro _; norm_num [prior]
  · simp [prior]
  · intro _; norm_num [prior]

theorem loss_mem_Icc_general :
    ∀ i : Fin 4, ∀ z : Fin 3, 0 ≤ loss i z ∧ loss i z ≤ 5 := by
  intro _ z
  fin_cases z <;> norm_num [loss, Fin.ext_iff]

/-- Compiled general-width bounded-regression PAC-Bayes certificate. -/
theorem certificate : PACBayesCertificateCompiler.compileGeneralWidth spec.lossBound spec := by
  exact PACBayesCertificateCompiler.compileGeneralWidth_sound
    spec
    spec.lossBound
    (by
      norm_num [spec, FormalSLT.Examples.RegressionStubGeneralWidthCertificate.sampleSize])
    dataLaw_isPMF
    prior_isFullSupportPMF
    (by norm_num [spec])
    (by norm_num [spec])
    (by norm_num [spec])
    loss_mem_Icc_general

end Stub

#eval lossBoundMilli
#eval sampleSize
#eval confidencePercent
#eval generalBoundMilli

#check @FormalSLT.PACBayes.sphericalGaussianKL_eq_closedForm
#check Stub.certificate

end

end FormalSLT.Examples.RegressionStubGeneralWidthCertificate
