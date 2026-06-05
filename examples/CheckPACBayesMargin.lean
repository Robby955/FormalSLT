import FormalSLT.PACBayesMargin

/-!
# PAC-Bayes classifier-margin adapter audit

Checks the concrete classifier-margin surface that specializes the finite
PAC-Bayes Bernstein shell.
-/

namespace FormalSLT.PACBayesMargin.Check

inductive ToyHyp
  | left
  | right
  deriving DecidableEq, Fintype

instance : Nonempty ToyHyp := ⟨ToyHyp.left⟩

inductive ToyPoint
  | neg
  | pos
  deriving DecidableEq, Fintype

def toyLabel : ToyPoint → Bool
  | ToyPoint.neg => false
  | ToyPoint.pos => true

def toyScore : ToyHyp → ToyPoint → ℝ
  | ToyHyp.left, ToyPoint.neg => -1
  | ToyHyp.left, ToyPoint.pos => 1
  | ToyHyp.right, ToyPoint.neg => 1
  | ToyHyp.right, ToyPoint.pos => -1

#check FormalSLT.PACBayesMargin.signedBool
#check FormalSLT.PACBayesMargin.classifierMargin
#check FormalSLT.PACBayesMargin.classifierMarginLoss
#check FormalSLT.PACBayesMargin.classifierMarginLoss_mem_Icc_zero_one
#check FormalSLT.PACBayesMargin.classifierMarginPopulationRisk
#check FormalSLT.PACBayesMargin.classifierMarginEmpiricalRisk
#check FormalSLT.PACBayesMargin.classifierMarginEmpiricalRiskFn
#check FormalSLT.PACBayesMargin.classifierMarginVarianceProxy
#check FormalSLT.PACBayesMargin.classifierMarginSampleVarianceProxy
#check FormalSLT.PACBayesMargin.posteriorClassifierMarginVarianceProxy
#check FormalSLT.PACBayesMargin.posteriorClassifierMarginSampleVarianceProxy
#check FormalSLT.PACBayesMargin.classifierMarginPopulationRisk_mem_Icc_zero_one
#check FormalSLT.PACBayesMargin.classifierMarginLoss_sq
#check FormalSLT.PACBayesMargin.classifierMarginVariance_le_risk
#check FormalSLT.PACBayesMargin.oneCoordinate_classifierMarginLoss_mgf_subgamma
#check FormalSLT.PACBayesMargin.finiteProduct_classifierMarginLoss_mgf_subgamma
#check FormalSLT.PACBayesMargin.expectedPriorBernsteinExpMoment_classifierMargin_iid_le_one
#check FormalSLT.PACBayesMargin.finiteProductSampleWeight_isPMF
#check FormalSLT.PACBayesMargin.finitePACBayesClassifierMarginBernsteinBadSamples

#check (FormalSLT.PACBayesMargin.classifierMarginLoss
  (ι := ToyHyp) (Z := ToyPoint) 0 toyScore toyLabel ToyHyp.left ToyPoint.pos)

#check (FormalSLT.PACBayesMargin.finitePACBayesClassifierMarginBernstein_badEventMass_le_delta
  (n := 2) (Z := ToyPoint) (ι := ToyHyp))
#print axioms FormalSLT.PACBayesMargin.finitePACBayesClassifierMarginBernstein_badEventMass_le_delta

#check (FormalSLT.PACBayesMargin.finitePACBayesClassifierMarginBernstein_iid_badEventMass_le_delta
  (n := 2) (Z := ToyPoint) (ι := ToyHyp))
#print axioms FormalSLT.PACBayesMargin.expectedPriorBernsteinExpMoment_classifierMargin_iid_le_one
#print axioms FormalSLT.PACBayesMargin.finitePACBayesClassifierMarginBernstein_iid_badEventMass_le_delta

end FormalSLT.PACBayesMargin.Check
