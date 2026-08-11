import FormalSLT.PACBayes.FiniteExponentialTilt

/-!
# Finite exponential-tilt audit

The concrete receipt tilts a fair Boolean law by unequal scores.  It checks
normalization, strict reweighting toward the larger score, and the exact
finite change-of-measure identity.
-/

namespace FormalSLT.Examples.CheckFiniteExponentialTilt

open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.FiniteExponentialTilt

noncomputable section

def fairBool (_z : Bool) : ℝ := 1 / 2

abbrev fairBoolPMF : IsPMF fairBool := by
  constructor <;> simp [fairBool]

def unequalScore : Bool → ℝ
  | false => 0
  | true => 1

def signedObservable : Bool → ℝ
  | false => -1
  | true => 2

example : IsPMF (finiteExponentialTiltPMF fairBool unequalScore) :=
  finiteExponentialTiltPMF_isPMF fairBoolPMF unequalScore

example :
    finiteExponentialTiltPMF fairBool unequalScore false <
      finiteExponentialTiltPMF fairBool unequalScore true := by
  apply div_lt_div_of_pos_right _
    (finiteExponentialTiltNormalizer_pos fairBoolPMF unequalScore)
  have hexp : Real.exp (0 : ℝ) < Real.exp 1 :=
    Real.exp_lt_exp.mpr zero_lt_one
  exact mul_lt_mul_of_pos_left hexp (show (0 : ℝ) < 1 / 2 by norm_num)

example :
    (∑ z : Bool, fairBool z * Real.exp (unequalScore z) * signedObservable z) =
      finiteExponentialTiltNormalizer fairBool unequalScore *
        ∑ z : Bool,
          finiteExponentialTiltPMF fairBool unequalScore z * signedObservable z := by
  exact finiteExponentialTilt_changeOfMeasure
    fairBoolPMF unequalScore signedObservable

#check finiteExponentialTiltNormalizer
#check finiteExponentialTiltPMF
#check finiteExponentialTiltNormalizer_pos
#check finiteExponentialTiltPMF_isPMF
#check finiteExponentialTiltPMF_mul_normalizer
#check finiteExponentialTilt_changeOfMeasure

#print axioms finiteExponentialTiltNormalizer_pos
#print axioms finiteExponentialTiltPMF_isPMF
#print axioms finiteExponentialTiltPMF_mul_normalizer
#print axioms finiteExponentialTilt_changeOfMeasure

end

end FormalSLT.Examples.CheckFiniteExponentialTilt
