import FormalSLT.Covering.MeasureDudley

/-!
# Arbitrary-measure continuous Dudley entropy integral checker

This checker records the measure-theoretic generalization of the continuous
Dudley entropy integral: the left side is a genuine Bochner integral
`∫ ω, supFunctional ω ∂μ` against an arbitrary probability measure `μ`, not the
finite weighted sum `finiteExpectation P.weight supFunctional` of the
`Fintype Ω` lane.

Each `#print axioms` line must report only `[propext, Classical.choice,
Quot.sound]`. The non-vacuity witness (`uniformBool`, a genuine non-Dirac
mixture, with mean `½` strictly between the two outcome values) confirms the
bound is instantiated against a real averaging measure, not a domain-collapsing
point evaluation. The witness uses a STRICT coarse budget `¼ < ½ = mean`
(`nonvacuous_coarseBudget_lt_integral`), so the `4·√(2σ²)·entropy` term is
load-bearing, not absorbed slack.

`lake env lean examples/CheckMeasureDudley.lean` exits 0 iff every theorem below
type-checks with the clean axiom profile.
-/

-- The terminal measure-theoretic Dudley entropy integral bound.
#check @FormalSLT.Covering.MeasureDudley.continuous_dudley_entropy_integral_of_measure
#print axioms FormalSLT.Covering.MeasureDudley.continuous_dudley_entropy_integral_of_measure

-- The covering-number `√(log N)` specialization.
#check @FormalSLT.Covering.MeasureDudley.continuous_dudley_entropy_integral_of_measure_coveringNumber
#print axioms FormalSLT.Covering.MeasureDudley.continuous_dudley_entropy_integral_of_measure_coveringNumber

-- The integral-level sub-Gaussian engine.
#check @FormalSLT.Covering.MeasureDudley.integral_le_of_shifted_exp_mgf
#print axioms FormalSLT.Covering.MeasureDudley.integral_le_of_shifted_exp_mgf

#check @FormalSLT.Covering.MeasureDudley.integral_expectedSup_le_of_shifted_mgf
#print axioms FormalSLT.Covering.MeasureDudley.integral_expectedSup_le_of_shifted_mgf

#check @FormalSLT.Covering.MeasureDudley.integral_finiteSup_le_of_mgf_log
#print axioms FormalSLT.Covering.MeasureDudley.integral_finiteSup_le_of_mgf_log

-- Non-vacuity: a genuine non-Dirac probability measure with a real average mean.
#check @FormalSLT.Covering.MeasureDudley.uniformBool
#check @FormalSLT.Covering.MeasureDudley.integral_witnessSup_uniformBool
#print axioms FormalSLT.Covering.MeasureDudley.integral_witnessSup_uniformBool

#check @FormalSLT.Covering.MeasureDudley.continuous_dudley_entropy_integral_of_measure_nonvacuous
#print axioms FormalSLT.Covering.MeasureDudley.continuous_dudley_entropy_integral_of_measure_nonvacuous

-- The strict-budget guarantee: coarseBudget ¼ < ½ = mean, so the entropy term bites.
#check @FormalSLT.Covering.MeasureDudley.nonvacuous_coarseBudget_lt_integral
#print axioms FormalSLT.Covering.MeasureDudley.nonvacuous_coarseBudget_lt_integral
