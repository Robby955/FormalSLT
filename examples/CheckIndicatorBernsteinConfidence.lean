import FormalSLT.PACBayes.IndicatorBernsteinConfidence

/-!
# Checks for the finite indicator PAC-Bayes Bernstein confidence theorem

The concrete receipt uses a fair Boolean data law, two constant classifiers, a
uniform full-support prior, sample size two, tilt one, and confidence level
one-half.  It instantiates the actual bad-sample mass bound.
-/

namespace FormalSLT.Examples.CheckIndicatorBernsteinConfidence

open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.IndicatorBernsteinConfidence

noncomputable section

def fairBool : Bool → ℝ := fun _ => (1 : ℝ) / 2

theorem fairBool_isPMF : IsPMF fairBool := by
  constructor <;> simp [fairBool]

def uniformBoolPrior : Bool → ℝ := fun _ => (1 : ℝ) / 2

theorem uniformBoolPrior_isFullSupportPMF :
    IsFullSupportPMF uniformBoolPrior := by
  constructor
  · constructor <;> simp [uniformBoolPrior]
  · intro i
    simp [uniformBoolPrior]

def disagreementBad : Bool → Bool → Bool := fun classifier label =>
  classifier != label

example :
    (∑ S ∈ indicatorFinitePACBayesBernsteinBadSamples
        2 fairBool uniformBoolPrior disagreementBad 1 ((1 : ℝ) / 2),
        finiteProductSampleWeight fairBool S) ≤ (1 : ℝ) / 2 := by
  exact indicator_finitePACBayesBernstein_fixedLambda_badEventMass_le_delta
    (n := 2) (ι := Bool) (Z := Bool)
    (by norm_num) fairBool fairBool_isPMF
    uniformBoolPrior_isFullSupportPMF disagreementBad
    1 ((1 : ℝ) / 2) (by norm_num) (by norm_num) (by norm_num)

#check indicatorFinitePACBayesBernsteinBadSamples
#check indicator_posteriorGeneralizationGap_le_of_not_mem
#check indicator_finitePACBayesBernstein_fixedLambda_badEventMass_le_delta
#check fairBool_isPMF
#check uniformBoolPrior_isFullSupportPMF
#print axioms indicator_finitePACBayesBernstein_fixedLambda_badEventMass_le_delta

end

end FormalSLT.Examples.CheckIndicatorBernsteinConfidence
