import FormalSLT.PACBayes.Compiler

/-!
# Axiom audit for the general-width PAC-Bayes compiler
-/

open FormalSLT.PACBayes

#print axioms mcAllesterBoundGeneral_badEventMass_le_delta
#print axioms PACBayesCertificateCompiler.compileGeneralWidth_sound

#check @mcAllesterBoundGeneral_badEventMass_le_delta
#check @PACBayesCertificateCompiler.compileGeneralWidth
#check @PACBayesCertificateCompiler.compileGeneralWidth_sound

example : True := trivial
