import FormalSLT.PACBayes.Compiler

/-!
# Axiom audit for PAC-Bayes certificate compiler examples
-/

open FormalSLT.PACBayes

#print axioms mcAllesterBoundedLoss_badEventMass_le_delta
#print axioms PACBayesCertificateCompiler.compile_sound
#print axioms BinaryClassifierExample.certificate
#print axioms BoundedRegressionStub.certificate
#print axioms DecisionStumpExample.certificate

example : BinaryClassifierExample.spec.sampleSize = 4000 := rfl
example : BoundedRegressionStub.spec.sampleSize = 2500 := rfl
example : DecisionStumpExample.spec.sampleSize = 6000 := rfl
