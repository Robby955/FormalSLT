import FormalSLT.Statistics.ExponentialFamily

open FormalSLT.Statistics
open FormalSLT.Statistics.ExponentialFamily

#check finiteLogPartition_hasDerivAt
#check finiteLogPartition_hasDerivAt_of_positiveBase
#check finiteExponentialFamily_mean_eq_logPartition_deriv
#check finiteLogPartition_hasSecondDerivAt
#check finiteLogPartition_hasSecondDerivAt_of_positiveBase
#check finiteExponentialFamily_variance_eq_logPartition_secondDeriv
#check finiteExponentialFamily_fisherInformation_eq_variance
#check finiteExponentialFamily_logPartition_secondDeriv_eq_fisherInformation
#check bernoulliNatural_logPartition_deriv_zero
#check bernoulliNatural_logPartition_secondDeriv_zero
#check bernoulliNatural_fisher_eq_variance_zero
#check bernoulliNatural_witness

example :
    ClassicalEstimation.weightedExpectation
        (finiteExponentialPMF bernoulliNaturalBase bernoulliNaturalStatistic 0)
        bernoulliNaturalStatistic = (1 : ℝ) / 2 ∧
      FisherInformation.weightedVariance
        (finiteExponentialPMF bernoulliNaturalBase bernoulliNaturalStatistic 0)
        bernoulliNaturalStatistic = (1 : ℝ) / 4 ∧
      FisherInformation.fisherInformation
        (fun u => finiteExponentialPMF bernoulliNaturalBase bernoulliNaturalStatistic u)
        (fun u => finiteExponentialPMFDeriv bernoulliNaturalBase bernoulliNaturalStatistic u)
        0 = (1 : ℝ) / 4 :=
  bernoulliNatural_witness

#print axioms finiteLogPartition_hasDerivAt
#print axioms finiteLogPartition_hasDerivAt_of_positiveBase
#print axioms finiteExponentialFamily_mean_eq_logPartition_deriv
#print axioms finiteLogPartition_hasSecondDerivAt
#print axioms finiteLogPartition_hasSecondDerivAt_of_positiveBase
#print axioms finiteExponentialFamily_variance_eq_logPartition_secondDeriv
#print axioms finiteExponentialFamily_fisherInformation_eq_variance
#print axioms finiteExponentialFamily_logPartition_secondDeriv_eq_fisherInformation
#print axioms bernoulliNatural_logPartition_deriv_zero
#print axioms bernoulliNatural_logPartition_secondDeriv_zero
#print axioms bernoulliNatural_fisher_eq_variance_zero
#print axioms bernoulliNatural_witness
