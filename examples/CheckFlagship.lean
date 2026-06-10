import FormalSLT.TestTimeMeta.Flagship

/-!
# Axiom audit for the paper-ready PAC-Bayes test-time flagship API
-/

open FormalSLT.TestTimeMeta
open FormalSLT.TestTimeMeta.FlagshipWorkedExample

#print axioms flagshipBound_eq_testTimeMetaBound
#print axioms pacBayesTestTimeFlagship_theorem
#print axioms flagshipWorkedExample_certificate

#check @FlagshipUserSupplied
#check @FlagshipDerivedContributions
#check @FlagshipCertificate
#check @pacBayesTestTimeFlagship_theorem

#eval sampleSize
#eval empiricalRiskMilli
#eval boundSideMilli

example : flagshipWorkedExampleConclusion := flagshipWorkedExample_certificate
