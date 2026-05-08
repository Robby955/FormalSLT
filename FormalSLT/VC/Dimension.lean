import Mathlib.Combinatorics.SetFamily.Shatter

namespace FormalSLT.VC.Dimension

/--
Sauer-Shelah lemma for finite set families, binomial-sum form.

This claim-facing wrapper is the finite combinatorial core behind the
`vc-dimension` page's growth-function statement. A hypothesis class restricted
to a fixed finite sample is represented as a finite family of subsets of the
sample. Mathlib's `Finset.card_le_card_shatterer` gives Pajor's trace bound,
and `Finset.card_shatterer_le_sum_vcDim` gives the Sauer-Shelah binomial
bound in terms of the VC dimension of that finite family.
-/
theorem sauerShelahFiniteSetFamily
    {α : Type*} [DecidableEq α] [Fintype α] (𝒜 : Finset (Finset α)) :
    𝒜.card ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, (Fintype.card α).choose k :=
  (Finset.card_le_card_shatterer 𝒜).trans
    (Finset.card_shatterer_le_sum_vcDim (𝒜 := 𝒜))

end FormalSLT.VC.Dimension
