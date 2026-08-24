import FormalSLT.AnytimeValid.PolynomialStitchedLIL

/-!
# Polynomial stitched LIL checker

Checks the generic optimizer, the exact first-epoch budget, and the two
all-time endpoints.  The stochastic theorem inherits the nonzero-increment
model checked for `optimized_lambda_two_sided_confidence_sequence`; this file
also verifies that its first allocated epoch has a positive admissible tilt
and a nonzero budget.
-/

open FormalSLT.AnytimeValid

noncomputable section

namespace FormalSLT.Examples.PolynomialStitchedLIL

theorem first_epoch_index :
    polynomialGeometricEpochIndex 4 = 0 := by
  norm_num [polynomialGeometricEpochIndex]

theorem first_epoch_floor :
    polynomialGeometricEpochFloor 0 = 4 := by
  norm_num [polynomialGeometricEpochFloor]

theorem first_epoch_budget :
    polynomialGeometricEpochBudget (1 / 2) 0 = Real.log 8 := by
  norm_num [polynomialGeometricEpochBudget,
    FormalSLT.AnytimeValid.AllocationLogLog.polynomialEpochWeight]

theorem first_epoch_tilt_pos :
    0 < polynomialGeometricEpochTilt 1 1 (1 / 2) 0 := by
  exact polynomialGeometricEpochTilt_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 0

theorem first_epoch_tilt_admissible :
    polynomialGeometricEpochTilt 1 1 (1 / 2) 0 < 3 := by
  simpa using polynomialGeometricEpochTilt_admissible
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) <= 1) 0

theorem first_epoch_exact_optimizer :
    subGammaBoundary 1 1 (polynomialGeometricEpochBudget (1 / 2) 0) 4
        (polynomialGeometricEpochTilt 1 1 (1 / 2) 0) =
      subGammaWidthAtBudget 1 1 4
        (polynomialGeometricEpochBudget (1 / 2) 0) := by
  exact subGammaBoundary_eq_widthAtBudget_optTilt
    (by norm_num) (by norm_num) (by norm_num)
    (polynomialGeometricEpochBudget_pos (by norm_num) (by norm_num) 0)

#check optTiltAtBudget
#check optTiltAtBudget_pos
#check optTiltAtBudget_admissible
#check optTiltAtBudget_eq_optTilt_exp
#check subGammaBoundary_eq_widthAtBudget_optTilt
#check polynomialGeometricEpochFloor_pos
#check polynomialGeometricEpochHorizon_eq_four_mul_floor
#check polynomialGeometricEpochBudget_eq
#check polynomialGeometricEpochBudget_pos
#check polynomialGeometricEpochIndex_spec
#check polynomialGeometricEpochTilt_pos
#check polynomialGeometricEpochTilt_admissible
#check integrable_subGammaExponentialProcess_of_bounded
#check subGammaBoundary_mono_time
#check subGammaWidthAtBudget_epoch_le
#check polynomialStitchedLILAtomFailure_mass_le
#check polynomialStitchedLILFailure_mass_le
#check polynomialStitchedLIL_lt_epochWidth_of_not_mem
#check polynomialStitchedLIL_lt_explicit_of_not_mem
#check exists_polynomialStitchedLIL_event
#check exists_polynomialStitchedLIL_explicit_event

#print axioms optTiltAtBudget_pos
#print axioms optTiltAtBudget_admissible
#print axioms subGammaBoundary_eq_widthAtBudget_optTilt
#print axioms polynomialGeometricEpochBudget_eq
#print axioms polynomialStitchedLILAtomFailure_mass_le
#print axioms polynomialStitchedLILFailure_mass_le
#print axioms polynomialStitchedLIL_lt_epochWidth_of_not_mem
#print axioms polynomialStitchedLIL_lt_explicit_of_not_mem
#print axioms exists_polynomialStitchedLIL_event
#print axioms exists_polynomialStitchedLIL_explicit_event
#print axioms first_epoch_budget
#print axioms first_epoch_exact_optimizer

end FormalSLT.Examples.PolynomialStitchedLIL

end
