import FormalSLT.PACBayes.StabilityBridge

open FormalSLT.PACBayes.StabilityBridge

#print axioms diracPosterior_klDiv_eq_neg_log_prior
#print axioms pointMass_pacBayes_generalization
#print axioms deterministicHypothesis_pacBayes_generalization

example :
    FormalSLT.PACBayesKL.IsPMF
      (diracPosterior (0 : Fin 1)) := by
  exact diracPosterior_isPMF (0 : Fin 1)
