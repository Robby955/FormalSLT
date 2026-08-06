import FormalSLT.PACBayes.FiniteProductBernstein

/-!
# Checks for finite-product indicator Bernstein moments

The concrete receipt uses a fair Boolean data law, a nonconstant predicate,
sample size two, and fixed tilt one. It exercises the exact product
normalization rather than only resolving theorem names.
-/

namespace FormalSLT.Examples.CheckFiniteProductBernstein

open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.IndicatorVariance
open FormalSLT.PACBayes.FiniteProductBernstein

noncomputable section

def fairBool : Bool → ℝ := fun _ => (1 : ℝ) / 2

theorem fairBool_isPMF : IsPMF fairBool := by
  constructor <;> simp [fairBool]

def identityBad : Unit → Bool → Bool := fun _ z => z

example : IsPMF (finiteProductSampleWeight (n := 2) fairBool) :=
  finiteProductSampleWeight_isPMF fairBool_isPMF

example :
    (∑ S : Fin 2 → Bool,
        finiteProductSampleWeight fairBool S *
          Real.exp
            ((1 : ℝ) *
                (indicatorPopulationRisk fairBool identityBad () -
                  finiteEmpiricalRisk (indicatorLoss identityBad) () S) -
              indicatorBernsteinMGFBudget 2 1
                (indicatorPopulationRisk fairBool identityBad ()))) ≤ 1 := by
  exact indicator_product_normalizedMGF_le_one
    (n := 2) (ι := Unit) (Z := Bool)
    (by norm_num) fairBool fairBool_isPMF identityBad ()
    (lambda := 1) (by norm_num) (by norm_num)

#check finiteProductSampleWeight_isPMF
#check indicator_oneCoordinateDeviationMGF_le
#check indicator_product_mgf_le
#check indicator_product_normalizedMGF_le_one
#check fairBool_isPMF
#print axioms indicator_product_normalizedMGF_le_one

end

end FormalSLT.Examples.CheckFiniteProductBernstein
