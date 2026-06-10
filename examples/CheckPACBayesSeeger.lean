import FormalSLT.PACBayesSeeger

open FormalSLT.PACBayesSeeger

#print axioms posteriorBinaryKL_le_of_priorSeegerKLMoment_le
#print axioms pacbayes_seeger_klForm_of_priorMoment_and_binaryKLJensen
#print axioms pacbayes_seeger_klForm_implies_mcallester_sqrt_of_pinsker

example : binKL (1 / 2) (1 / 2) = 0 := by
  norm_num [binKL]
