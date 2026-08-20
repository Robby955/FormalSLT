import FormalSLT.PACBayes

open FormalSLT.PACBayes.FiniteEmpiricalVariance

#check FormalSLT.PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch.exists_continuousInfiniteEmpiricalBernstein_event

example {ι Z : Type*} (ℓ : ι → Z → ℝ) (i : ι) (S : Fin 2 → Z) :
    finiteEmpiricalVariance ℓ i S =
      finitePairwiseEmpiricalVariance ℓ i S :=
  finiteEmpiricalVariance_eq_pairwise (by norm_num) ℓ i S
