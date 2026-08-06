import FormalSLT.PACBayes.IndicatorVariance

/-!
# Checks for exact finite indicator variance

These checks exercise the distribution-generic theorem on constant and
nonconstant Boolean predicates. The main theorem remains stated for arbitrary
finite PMFs and arbitrary finite data domains.
-/

namespace FormalSLT.Examples.CheckIndicatorVariance

open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.IndicatorVariance

noncomputable section

def fairBool : Bool → ℝ := fun _ => (1 : ℝ) / 2

theorem fairBool_isPMF : IsPMF fairBool := by
  constructor
  · intro z
    simp [fairBool]
  · simp [fairBool]

def identityBad : Unit → Bool → Bool := fun _ z => z

example : indicatorPopulationRisk fairBool identityBad () = (1 : ℝ) / 2 := by
  simp [indicatorPopulationRisk, FormalSLT.PACBayesFiniteProductMGF.finitePopulationRisk,
    indicatorLoss, fairBool, identityBad]

example :
    (∑ z : Bool,
        fairBool z *
          (indicatorPopulationRisk fairBool identityBad () - indicatorLoss identityBad () z) ^
            (2 : Nat)) = (1 : ℝ) / 4 := by
  rw [indicatorDeviation_secondMoment_eq fairBool fairBool_isPMF identityBad ()]
  simp [indicatorPopulationRisk, FormalSLT.PACBayesFiniteProductMGF.finitePopulationRisk,
    indicatorLoss, fairBool, identityBad]
  norm_num

def neverBad : Unit → Bool → Bool := fun _ _ => false

example : indicatorPopulationRisk fairBool neverBad () = 0 := by
  simp [indicatorPopulationRisk, FormalSLT.PACBayesFiniteProductMGF.finitePopulationRisk,
    indicatorLoss, fairBool, neverBad]

def alwaysBad : Unit → Bool → Bool := fun _ _ => true

example : indicatorPopulationRisk fairBool alwaysBad () = 1 := by
  simp [indicatorPopulationRisk, FormalSLT.PACBayesFiniteProductMGF.finitePopulationRisk,
    indicatorLoss, fairBool, alwaysBad]

#check indicatorPopulationRisk_mem_Icc
#check indicatorDeviation_centered
#check indicatorDeviation_secondMoment_eq
#check fairBool_isPMF
#print axioms indicatorDeviation_secondMoment_eq

end

end FormalSLT.Examples.CheckIndicatorVariance
