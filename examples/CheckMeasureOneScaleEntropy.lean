import FormalSLT.Covering.MeasureDudley

/-!
# Arbitrary-measure one-scale finite-net entropy checker

The capstone below derives a square-root bound in the chosen-net cardinalities
for the realized projection-pair increments between two finite nets. Its
outcome space is an arbitrary probability space: there is no `[Fintype Ω]`,
supplied `MeasureChainingBudget`, coarse budget, or terminal-boundary
certificate.

The Boolean witness moves from a one-point coarse net to the exact two-point
net. Its projection-pair maximum has integral exactly `1/2`, so this checker
cannot pass through a zero-valued or singleton-only example.

Every `#print axioms` report must be exactly
`[propext, Classical.choice, Quot.sound]`.
-/

open FormalSLT.Covering.MeasureDudley

#check @MeasureSubGaussianProcess
#check @integrable_finiteSup_of_integrable
#check @integral_finiteSup_le_of_subGaussian_mgf_sqrt_nonempty
#check @MeasureSubGaussianProcess.integral_incrementFamilySup_le_radius_sqrt_nonempty

#check @MeasureSubGaussianProcess.integral_projectionPairSup_le_coveringNumber_sqrt
#print axioms MeasureSubGaussianProcess.integral_projectionPairSup_le_coveringNumber_sqrt

#check @boolCoarseNet
#check @boolFullNet
#check @integral_boolProjectionPairSup_eq_half
#print axioms integral_boolProjectionPairSup_eq_half

#check @integral_boolProjectionPairSup_pos
#print axioms integral_boolProjectionPairSup_pos

#check @integral_boolProjectionPairSup_le_coveringNumber_sqrt
#print axioms integral_boolProjectionPairSup_le_coveringNumber_sqrt
