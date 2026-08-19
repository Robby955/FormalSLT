import FormalSLT.AnytimeValid.AllocationLogLog

/-!
# Countable-allocation log-log checker

The generic checks record the blockwise and geometric-epoch obstruction.  The
concrete checks exercise the telescoping polynomial allocation, including an
exact four-atom prefix receipt and the exact log-price identity.
-/

namespace FormalSLT.Examples.AllocationLogLog

open Finset BigOperators
open FormalSLT.AnytimeValid.AllocationLogLog

noncomputable section

theorem polynomial_first_four_mass :
    ∑ k ∈ Finset.range 4, polynomialEpochWeight k = 4 / 5 := by
  rw [polynomialEpochWeight_sum_range]
  norm_num

theorem polynomial_atom_three :
    polynomialEpochWeight 3 = 1 / 20 := by
  norm_num [polynomialEpochWeight]

theorem polynomial_atom_three_log_cost :
    Real.log (1 / polynomialEpochWeight 3) = Real.log 20 := by
  rw [polynomialEpochWeight_log_cost]
  norm_num
  rw [← Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
    (by norm_num : (5 : ℝ) ≠ 0)]
  norm_num

#check exists_small_weight_on_dyadicBlock
#check exists_logCost_ge_log_blockCard
#check exists_logCost_ge_indexLog_sub_log_two
#check frequently_logCost_ge_indexLog_sub_log_two
#check geometricEpochTime
#check geometricEpochScale
#check geometricEpochIteratedLog
#check geometricEpochTime_natLog
#check geometricEpochScale_log
#check geometricEpochIteratedLog_eq
#check exists_geometricEpoch_loglogCost
#check frequently_geometricEpoch_loglogCost
#check polynomialEpochWeight
#check polynomialEpochWeight_pos
#check polynomialEpochWeight_eq_sub
#check polynomialEpochWeight_sum_range
#check polynomialEpochWeight_hasSum
#check polynomialEpochWeight_summable
#check polynomialEpochWeight_tsum
#check polynomialEpochWeight_log_cost
#check polynomialGeometricEpoch_log_cost
#check polynomial_first_four_mass
#check polynomial_atom_three
#check polynomial_atom_three_log_cost

#print axioms exists_small_weight_on_dyadicBlock
#print axioms exists_logCost_ge_log_blockCard
#print axioms exists_logCost_ge_indexLog_sub_log_two
#print axioms frequently_logCost_ge_indexLog_sub_log_two
#print axioms geometricEpochTime_natLog
#print axioms geometricEpochScale_log
#print axioms geometricEpochIteratedLog_eq
#print axioms exists_geometricEpoch_loglogCost
#print axioms frequently_geometricEpoch_loglogCost
#print axioms polynomialEpochWeight_pos
#print axioms polynomialEpochWeight_eq_sub
#print axioms polynomialEpochWeight_sum_range
#print axioms polynomialEpochWeight_hasSum
#print axioms polynomialEpochWeight_summable
#print axioms polynomialEpochWeight_tsum
#print axioms polynomialEpochWeight_log_cost
#print axioms polynomialGeometricEpoch_log_cost

#print axioms polynomial_first_four_mass
#print axioms polynomial_atom_three
#print axioms polynomial_atom_three_log_cost

end

end FormalSLT.Examples.AllocationLogLog
