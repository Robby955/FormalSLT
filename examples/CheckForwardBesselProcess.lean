import FormalSLT.AnytimeValid.ForwardBesselProcess

/-!
# Forward exact-Bessel process checks

This focused receipt checks the deterministic Welford bridge, the honest
e-process interface, and the sharp two-observation Boolean witness.  The path
`(false,true)`, encoded as `(0,1)`, is an atom of the fair two-Bool product
model.  On that path coefficient `1` fails, while coefficient `3/2` is attained
exactly.
-/

open FormalSLT.AnytimeValid

noncomputable section

namespace FormalSLT.Examples.CheckForwardBesselProcess

/-- The Boolean path `(false,true)`, encoded by losses `(0,1)`. -/
def falseTrueSample : ℕ → ℝ := fun k ↦ if k = 0 then 0 else 1

theorem falseTrue_predictableQuadratic :
    forwardPredictableQuadratic falseTrueSample 2 = (5 : ℝ) / 4 := by
  norm_num [falseTrueSample, forwardPredictableQuadratic_two]

theorem falseTrue_besselQ :
    forwardBesselQ falseTrueSample 2 = (1 : ℝ) / 2 := by
  norm_num [falseTrueSample, forwardBesselQ_two]

/-- Coefficient `1` is strictly too small on the fair-Bool path. -/
theorem falseTrue_coefficient_one_fails :
    (1 : ℝ) / 2 + forwardBesselQ falseTrueSample 2 <
      forwardPredictableQuadratic falseTrueSample 2 := by
  rw [falseTrue_predictableQuadratic, falseTrue_besselQ]
  norm_num

/-- The repaired coefficient `3/2` is exact on the same path. -/
theorem falseTrue_three_halves_exact :
    forwardPredictableQuadratic falseTrueSample 2 =
      (1 : ℝ) / 2 + (3 : ℝ) / 2 * forwardBesselQ falseTrueSample 2 := by
  rw [falseTrue_predictableQuadratic, falseTrue_besselQ]
  norm_num

#check forwardBesselQ_eq_card_sub_one_mul_sampleVarianceBessel
#check forwardBesselQ_succ
#check forwardPredictableQuadratic_le_half_add_three_halves_besselQ
#check forwardBessel_coefficient_one_bool_obstruction
#check forwardPlugIn_eProcess_of_condExp_step
#check forwardBesselExponentialEnvelope_le_forwardPlugIn
#check forwardBesselEnvelope_certified_by_eProcess

#print axioms forwardBesselQ_eq_card_sub_one_mul_sampleVarianceBessel
#print axioms forwardBesselQ_succ
#print axioms forwardPredictableQuadratic_le_half_add_three_halves_besselQ
#print axioms forwardBessel_coefficient_one_bool_obstruction
#print axioms forwardPlugIn_eProcess_of_condExp_step
#print axioms forwardBesselEnvelope_certified_by_eProcess
#print axioms falseTrue_coefficient_one_fails
#print axioms falseTrue_three_halves_exact

end FormalSLT.Examples.CheckForwardBesselProcess
