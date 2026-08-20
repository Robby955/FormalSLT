import FormalSLT.VC

open scoped BigOperators

def singletonFamily : Finset (Finset (Fin 2)) := {∅}

example :
    singletonFamily.card ≤
      ∑ k ∈ Finset.Iic singletonFamily.vcDim,
        (Fintype.card (Fin 2)).choose k :=
  FormalSLT.VC.VCDimension.sauerShelahFiniteSetFamily singletonFamily
