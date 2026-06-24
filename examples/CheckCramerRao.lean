import FormalSLT.Statistics.CramerRao

open FormalSLT.Statistics
open FormalSLT.Statistics.FisherInformation
open FormalSLT.Statistics.CramerRao
open scoped BigOperators

#check weightedVariance
#check weightedCovariance
#check scoreFunction
#check fisherInformation
#check score_mean_zero_of_finite_regular
#check covariance_score_eq_deriv_mean
#check covariance_cauchy_schwarz
#check cramerRao_unbiased
#check bernoulliFisherInformation
#check bernoulliHalfFisherInformation
#check bernoulliHalfCramerRaoWitness

/-- Concrete Bernoulli Fisher-information witness: at `p = 1/2`, `I(p) = 4`. -/
example : bernoulliFisherInformation ((1 : ℝ) / 2) = 4 := by
  exact bernoulliHalfFisherInformation

/-- Concrete Cramer-Rao witness: the Bernoulli identity estimator has variance
`1/4`, matching the lower bound `1 / I(1/2) = 1/4`. -/
example :
    weightedVariance (bernoulliWeights ((1 : ℝ) / 2)) bernoulliIdentityEstimator
      = 1 / bernoulliFisherInformation ((1 : ℝ) / 2) := by
  exact bernoulliHalfCramerRaoWitness

#print axioms score_mean_zero_of_finite_regular
#print axioms covariance_score_eq_deriv_mean
#print axioms covariance_cauchy_schwarz
#print axioms cramerRao_unbiased
#print axioms bernoulliHalfCramerRaoWitness
