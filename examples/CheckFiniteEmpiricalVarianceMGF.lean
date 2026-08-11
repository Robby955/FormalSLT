import FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF

/-!
# Concrete finite empirical-variance MGF checker

The fair two-point law and a nonconstant `[0,1]` loss instantiate the
source-normalized lower-tail MGF at `n = 2` and `eta = 1`.
-/

namespace FormalSLT.Examples.CheckFiniteEmpiricalVarianceMGF

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF

noncomputable section

def fairBool : Bool → ℝ := fun _ => 1 / 2

theorem fairBool_isPMF : IsPMF fairBool := by
  constructor
  · intro z
    norm_num [fairBool]
  · norm_num [fairBool]

def indicatorLoss (_ : Unit) (z : Bool) : ℝ := if z then 1 else 0

theorem indicatorLoss_mem_Icc (z : Bool) :
    indicatorLoss () z ∈ Set.Icc (0 : ℝ) 1 := by
  cases z <;> norm_num [indicatorLoss]

theorem fairBool_normalizedLowerTailMGF_le_one :
    (∑ S : Fin 2 → Bool,
        finiteProductSampleWeight fairBool S *
          Real.exp
            ((1 : ℝ) * (2 : ℝ) *
                (finitePopulationVariance fairBool indicatorLoss () -
                  finiteEmpiricalVariance indicatorLoss () S) -
              (1 : ℝ) ^ (2 : Nat) * (2 : ℝ) ^ (2 : Nat) *
                finitePopulationVariance fairBool indicatorLoss () /
                  (2 * ((2 : ℝ) - 1)))) ≤ 1 := by
  exact finiteEmpiricalVariance_normalizedLowerTailMGF_le_one
    (n := 2) (by norm_num) fairBool fairBool_isPMF indicatorLoss ()
    indicatorLoss_mem_Icc (eta := 1) (by norm_num)

#check finiteEmpiricalVariance_lowerTailMGF_randomMatching
#check finiteEmpiricalVariance_lowerTailMGF_tolstikhinSeldin
#check finiteEmpiricalVariance_normalizedLowerTailMGF_le_one

#print axioms finiteEmpiricalVariance_lowerTailMGF_randomMatching
#print axioms finiteEmpiricalVariance_lowerTailMGF_tolstikhinSeldin
#print axioms finiteEmpiricalVariance_normalizedLowerTailMGF_le_one
#print axioms fairBool_normalizedLowerTailMGF_le_one

end

end FormalSLT.Examples.CheckFiniteEmpiricalVarianceMGF
