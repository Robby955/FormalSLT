import FormalSLT.PACBayes.IndicatorBernsteinMoment

/-!
# Checks for prior-averaged indicator Bernstein moments

The concrete receipt uses two hypotheses, a fair Boolean data law, a uniform
prior, sample size two, and fixed tilt one. It instantiates the expected prior
moment itself rather than only resolving theorem names.
-/

namespace FormalSLT.Examples.CheckIndicatorBernsteinMoment

open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.IndicatorVariance
open FormalSLT.PACBayes.IndicatorBernsteinMoment

noncomputable section

def fairBool : Bool → ℝ := fun _ => (1 : ℝ) / 2

theorem fairBool_isPMF : IsPMF fairBool := by
  constructor <;> simp [fairBool]

def uniformBoolPrior : Bool → ℝ := fun _ => (1 : ℝ) / 2

theorem uniformBoolPrior_isPMF : IsPMF uniformBoolPrior := by
  constructor <;> simp [uniformBoolPrior]

def disagreementBad : Bool → Bool → Bool := fun classifier label =>
  classifier != label

example :
    expectedPriorBernsteinExpMoment
        (finiteProductSampleWeight (n := 2) fairBool)
        uniformBoolPrior 1 (indicatorBernsteinScale 2)
        (indicatorPopulationRisk fairBool disagreementBad)
        (fun S i => finiteEmpiricalRisk (indicatorLoss disagreementBad) i S)
        (indicatorBernsteinVarianceProxy 2 fairBool disagreementBad) ≤
      1 := by
  exact indicator_expectedPriorBernsteinExpMoment_le_one
    (n := 2) (ι := Bool) (Z := Bool)
    (by norm_num) fairBool fairBool_isPMF
    uniformBoolPrior uniformBoolPrior_isPMF disagreementBad
    (lambda := 1) (by norm_num) (by norm_num)

#check indicatorBernsteinScale
#check indicatorBernsteinVarianceProxy
#check indicatorBernstein_normalization_eq_budget
#check indicator_expectedPriorBernsteinExpMoment_le_one
#check fairBool_isPMF
#check uniformBoolPrior_isPMF
#print axioms indicator_expectedPriorBernsteinExpMoment_le_one

end

end FormalSLT.Examples.CheckIndicatorBernsteinMoment
