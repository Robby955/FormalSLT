import FormalSLT.Applications.CompactHalfTiltBrierCertificate

open FormalSLT.Applications.CompactHalfTiltBrierCertificate
open FormalSLT.PACBayesKL

namespace FormalSLT.Generated.CompactBrierCertificate

noncomputable section

inductive Model | m0 | m1
  deriving DecidableEq, Fintype

theorem model_univ : (Finset.univ : Finset Model) = {Model.m0, Model.m1} := by decide

def prior : Model → Real
  | .m0 => ((1 : Real) / 2)
  | .m1 => ((1 : Real) / 2)

def posterior : Model → Real
  | .m0 => (0 : Real)
  | .m1 => (1 : Real)

def logExponent : Model → Nat
  | .m0 => 0
  | .m1 => 1

def logRemainder : Model → Real
  | .m0 => (1 : Real)
  | .m1 => (1 : Real)

def empiricalRisk : Real := ((2161547227007 : Real) / 35320733114400)
def quadraticVariationUpper : Real := ((252237278248593 : Real) / 1099511627776)
def confidenceDelta : Real := ((1 : Real) / 20)
def horizon : Nat := 8224
def klUpper : Real := ((7 : Real) / 10)
def confidenceLogUpper : Real := ((61 : Real) / 20)
def certifiedUpperRisk : Real := ((18317 : Real) / 250000)

def protocolSha256 : String := "eb01873c40cf286fed55381dae98e2767fc83d4dd4f69fb4ad7003422e10b4c3"
def normalizedStreamSha256 : String := "f171dfffb3c796d0259c6e8ce226144527b1c34b469791fc112bca57825ce8e4"

theorem prior_isFullSupportPMF : IsFullSupportPMF prior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro model
    cases model <;> norm_num [prior]
  · rw [model_univ]
    simp [prior] <;> norm_num
  · intro model
    cases model <;> norm_num [prior]

theorem posterior_isPMF : IsPMF posterior := by
  refine ⟨?_, ?_⟩
  · intro model
    cases model <;> norm_num [posterior]
  · rw [model_univ]
    simp [posterior] <;> norm_num

theorem certificateInputsValid :
    IsFullSupportPMF prior ∧ IsPMF posterior ∧
      0 < confidenceDelta ∧ 0 < horizon := by
  exact ⟨prior_isFullSupportPMF, posterior_isPMF, by
    norm_num [confidenceDelta], by norm_num [horizon]⟩

theorem posterior_ratio_factorization :
    ∀ model, posterior model = 0 ∨
      (0 < logRemainder model ∧
        posterior model / prior model =
          (2 : Real) ^ logExponent model * logRemainder model) := by
  intro model
  cases model <;>
    norm_num [posterior, prior, logExponent, logRemainder]

theorem posterior_kl_le : klDiv posterior prior ≤ klUpper := by
  calc
    klDiv posterior prior ≤
        posteriorAverage posterior
          (fun model => dyadicLogUpper
            (logExponent model) (logRemainder model)) :=
      klDiv_le_dyadicLogUpper posterior_isPMF logExponent logRemainder
        posterior_ratio_factorization
    _ = klUpper := by
      unfold posteriorAverage
      rw [model_univ]
      simp [posterior, logExponent, logRemainder,
        dyadicLogUpper, klUpper]

theorem confidence_log_le :
    Real.log (1 / confidenceDelta) ≤ confidenceLogUpper := by
  calc
    Real.log (1 / confidenceDelta) =
        Real.log ((2 : Real) ^ 4 *
          ((5 : Real) / 4)) := by
      congr 1
      norm_num [confidenceDelta]
    _ ≤ dyadicLogUpper 4
        ((5 : Real) / 4) :=
      log_two_pow_mul_le_dyadicLogUpper 4 (by norm_num)
    _ = confidenceLogUpper := by
      norm_num [dyadicLogUpper, confidenceLogUpper]

theorem certificateBoundary_lt :
    summaryEndpoint empiricalRisk quadraticVariationUpper posterior prior
        confidenceDelta horizon < certifiedUpperRisk := by
  apply summaryEndpoint_lt_of_bounds (klUpper := klUpper)
    (logUpper := confidenceLogUpper)
  · norm_num [horizon]
  · norm_num [quadraticVariationUpper]
  · exact posterior_kl_le
  · exact confidence_log_le
  · norm_num [empiricalRisk, quadraticVariationUpper, klUpper,
      confidenceLogUpper, certifiedUpperRisk, horizon]

#print axioms certificateBoundary_lt
#print axioms certificateInputsValid
#eval IO.println "FORMALSLT_COMPACT_BRIER_CERTIFICATE_PASS"

end

end FormalSLT.Generated.CompactBrierCertificate
