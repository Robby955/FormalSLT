import FormalSLT.PACBayes.FiniteExponentialTiltProduct

/-!
# Finite-product exponential-tilt audit

The concrete receipt lifts the unequal Boolean tilt to two iid coordinates.
It checks the pointwise product-weight identity on the all-true sample and the
exact change-of-measure identity for a nonconstant signed sample functional.
-/

namespace FormalSLT.Examples.CheckFiniteExponentialTiltProduct

open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteExponentialTilt
open FormalSLT.PACBayes.FiniteExponentialTiltProduct

noncomputable section

def fairBool (_z : Bool) : ℝ := 1 / 2

abbrev fairBoolPMF : IsPMF fairBool := by
  constructor <;> simp [fairBool]

def unequalScore : Bool → ℝ
  | false => 0
  | true => 1

def allTruePair : Fin 2 → Bool := fun _k ↦ true

def signedPairObservable (S : Fin 2 → Bool) : ℝ :=
  if S 0 then
    if S 1 then 3 else 1
  else
    -2

example : (∑ k : Fin 2, unequalScore (allTruePair k)) = 2 := by
  norm_num [Fin.sum_univ_two, unequalScore, allTruePair]

example :
    finiteProductSampleWeight fairBool allTruePair *
        Real.exp (∑ k : Fin 2, unequalScore (allTruePair k)) =
      finiteExponentialTiltNormalizer fairBool unequalScore ^ 2 *
        finiteProductSampleWeight
          (finiteExponentialTiltPMF fairBool unequalScore) allTruePair := by
  exact finiteProductSampleWeight_mul_exp_sum_eq
    fairBoolPMF unequalScore allTruePair

example :
    (∑ S : Fin 2 → Bool,
        finiteProductSampleWeight fairBool S *
          Real.exp (∑ k : Fin 2, unequalScore (S k)) *
            signedPairObservable S) =
      finiteExponentialTiltNormalizer fairBool unequalScore ^ 2 *
        ∑ S : Fin 2 → Bool,
          finiteProductSampleWeight
              (finiteExponentialTiltPMF fairBool unequalScore) S *
            signedPairObservable S := by
  exact finiteProductExponentialTilt_changeOfMeasure
    fairBoolPMF unequalScore signedPairObservable

#check finiteProductSampleWeight_mul_exp_sum_eq
#check finiteProductExponentialTilt_changeOfMeasure

#print axioms finiteProductSampleWeight_mul_exp_sum_eq
#print axioms finiteProductExponentialTilt_changeOfMeasure

end

end FormalSLT.Examples.CheckFiniteExponentialTiltProduct
