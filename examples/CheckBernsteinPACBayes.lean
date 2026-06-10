import FormalSLT.PACBayes.BernsteinBound

/-!
# Axiom audit for continuous Bernstein PAC-Bayes certificates
-/

open FormalSLT.PACBayes

#print axioms vitaleContinuousKL_certificate
#print axioms continuousPriorPosterior_certificate_of_kl
#print axioms bernsteinPACBayes_continuousPriorPosterior_certificate

#check @vitaleContinuousKL_certificate
#check @continuousPriorPosterior_certificate_of_kl
#check @bernsteinPACBayes_continuousPriorPosterior_certificate

example : True := trivial
