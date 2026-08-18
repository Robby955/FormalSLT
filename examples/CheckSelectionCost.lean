import FormalSLT.AnytimeValid.SelectionCost

/-!
# Adaptive-selection cost checker

This checker exercises the exact diagonal witness on a two-atom law.  Each
coordinate score is an e-value with expectation one.  Selecting the winning
coordinate after observing the atom has expectation two without correction,
while predeclared `1/2` weights restore expectation one exactly.
-/

namespace FormalSLT.Examples.SelectionCost

open Finset BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.AnytimeValid.SelectionCost

noncomputable section

def fairBool : Bool -> Real := fun _ => 1 / 2

theorem fairBool_fullSupport : IsFullSupportPMF fairBool where
  nonneg := by intro b; simp [fairBool]
  sum_one := by simp [fairBool]
  pos := by intro b; simp [fairBool]

theorem bool_diagonal_each_mean_one (i : Bool) :
    finiteExpectation fairBool (diagonalSpike fairBool i) = 1 :=
  diagonalSpike_expectation_eq_one fairBool fairBool_fullSupport i

theorem bool_diagonal_selected_uncorrected_mean_two :
    finiteExpectation fairBool (fun omega => diagonalSpike fairBool omega omega) = 2 := by
  simpa using diagonalSpike_selected_expectation_eq_card fairBool fairBool_fullSupport

theorem bool_diagonal_selected_weighted_mean_one :
    finiteExpectation fairBool
        (selectedWeightedScore fairBool (diagonalSpike fairBool) id) = 1 :=
  diagonalSpike_selectedWeightedScore_expectation_eq_one fairBool fairBool_fullSupport

theorem bool_diagonal_scalarCorrection_safe_iff_two_le
    {correction : Real} (hcorrection : 0 < correction) :
    finiteExpectation fairBool
        (fun omega => diagonalSpike fairBool omega omega / correction) <= 1 <->
      2 <= correction := by
  simpa using diagonalSpike_scalarCorrection_safe_iff_card_le
    fairBool fairBool_fullSupport hcorrection

theorem bool_diagonal_logCorrection_ge_log_two
    {correction : Real} (hcorrection : 0 < correction)
    (hsafe : finiteExpectation fairBool
      (fun omega => diagonalSpike fairBool omega omega / correction) <= 1) :
    Real.log 2 <= Real.log correction := by
  simpa using diagonalSpike_logCorrection_ge_logCard
    fairBool fairBool_fullSupport hcorrection hsafe

theorem bool_diagonal_reciprocal_union_exact :
    finiteEventMass fairBool
        (fun omega => exists i, (1 / fairBool i) <= diagonalSpike fairBool i omega) = 1 /\
      (∑ i : Bool, 1 / (1 / fairBool i)) = 1 :=
  diagonalSpike_reciprocal_union_sharp fairBool fairBool_fullSupport

example : Real.log ((Fintype.card Bool : Real) / (1 / 20 : Real)) =
    Real.log (Fintype.card Bool : Real) + Real.log (1 / (1 / 20 : Real)) := by
  apply symmetric_log_selection_penalty
  norm_num

#check finiteEventMass_upperTail_le_expectation_div
#check finiteEventMass_upperTail_le_alpha
#check finiteScoreMixture_expectation_le_one
#check selectedWeightedScore_expectation_le_one
#check simultaneous_upperTail_mass_le_sum_reciprocal
#check simultaneous_kraft_upperTail_mass_le_alpha
#check selected_kraft_upperTail_mass_le_alpha
#check diagonalSpike_expectation_eq_one
#check diagonalSpike_selectedWeightedScore_expectation_eq_one
#check diagonalSpike_selected_expectation_eq_card
#check diagonalSpike_selectedCoefficient_expectation_eq_sum
#check diagonalSpike_selectedCoefficient_safe_iff
#check diagonalSpike_kraftCorrection_safe_iff
#check diagonalSpike_scalarCorrection_expectation_eq_card_div
#check diagonalSpike_scalarCorrection_safe_iff_card_le
#check diagonalSpike_logCorrection_ge_logCard
#check diagonalSpike_reciprocal_union_sharp
#check symmetric_simultaneous_upperTail_mass_le_alpha
#check symmetric_selected_upperTail_mass_le_alpha
#check symmetric_log_selection_penalty

#print axioms finiteEventMass_upperTail_le_expectation_div
#print axioms finiteEventMass_upperTail_le_alpha
#print axioms finiteScoreMixture_expectation_le_one
#print axioms selectedWeightedScore_expectation_le_one
#print axioms simultaneous_upperTail_mass_le_sum_reciprocal
#print axioms simultaneous_kraft_upperTail_mass_le_alpha
#print axioms selected_kraft_upperTail_mass_le_alpha
#print axioms diagonalSpike_expectation_eq_one
#print axioms diagonalSpike_selectedWeightedScore_expectation_eq_one
#print axioms diagonalSpike_selected_expectation_eq_card
#print axioms diagonalSpike_selectedCoefficient_expectation_eq_sum
#print axioms diagonalSpike_selectedCoefficient_safe_iff
#print axioms diagonalSpike_kraftCorrection_safe_iff
#print axioms diagonalSpike_scalarCorrection_expectation_eq_card_div
#print axioms diagonalSpike_scalarCorrection_safe_iff_card_le
#print axioms diagonalSpike_logCorrection_ge_logCard
#print axioms diagonalSpike_reciprocal_union_sharp
#print axioms symmetric_simultaneous_upperTail_mass_le_alpha
#print axioms symmetric_selected_upperTail_mass_le_alpha
#print axioms symmetric_log_selection_penalty

#print axioms bool_diagonal_each_mean_one
#print axioms bool_diagonal_selected_uncorrected_mean_two
#print axioms bool_diagonal_selected_weighted_mean_one
#print axioms bool_diagonal_scalarCorrection_safe_iff_two_le
#print axioms bool_diagonal_logCorrection_ge_log_two
#print axioms bool_diagonal_reciprocal_union_exact

end

end FormalSLT.Examples.SelectionCost
