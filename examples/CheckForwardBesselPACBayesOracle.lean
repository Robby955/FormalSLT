import FormalSLT.PACBayes.ForwardBesselPACBayesOracle

/-!
# Observable forward PAC-Bayes oracle checker

This file records the public oracle surface, its exact reporting-time catalog
arithmetic, and the axiom dependencies of the load-bearing results.
-/

open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open FormalSLT.PACBayes.ForwardBesselPACBayesOracle

namespace FormalSLT.Examples.CheckForwardBesselPACBayesOracle

/-- At `n = 512`, the observable oracle minimizes over atoms `0, ..., 5`. -/
theorem growingPrefixMaxIndex_512 :
    growingPrefixForwardBesselPACBayesMaxIndex 512 = 5 := by
  norm_num [growingPrefixForwardBesselPACBayesMaxIndex,
    geometricForwardTiltIndex, Nat.log]

/-- The largest effective scale at `n = 512` is exactly `64`. -/
theorem growingPrefixEffectiveScale_512 :
    geometricForwardEffectiveScale 5 = 64 := by
  norm_num [geometricForwardEffectiveScale]

/-- Exact polynomial atom-selection charge at `n = 512` and
`delta = 1/160`. -/
theorem growingPrefixComplexity_512_eq
    {ι : Type*} [Fintype ι] (prior posterior : ι → ℝ) :
    growingPrefixForwardBesselPACBayesComplexity
        prior posterior (1 / 160) 512 =
      klDiv posterior prior + Real.log 6720 := by
  rw [growingPrefixForwardBesselPACBayesComplexity_eq_logLog
    prior posterior (1 / 160) (by norm_num)]
  norm_num [Nat.log]

/-- At `n = 2048`, the available prefix has grown by one atom. -/
theorem growingPrefixMaxIndex_2048 :
    growingPrefixForwardBesselPACBayesMaxIndex 2048 = 6 := by
  norm_num [growingPrefixForwardBesselPACBayesMaxIndex,
    geometricForwardTiltIndex, Nat.log]

/-- The largest effective scale at `n = 2048` is exactly `128`. -/
theorem growingPrefixEffectiveScale_2048 :
    geometricForwardEffectiveScale 6 = 128 := by
  norm_num [geometricForwardEffectiveScale]

/-- Exact polynomial atom-selection charge at `n = 2048` and
`delta = 1/160`. -/
theorem growingPrefixComplexity_2048_eq
    {ι : Type*} [Fintype ι] (prior posterior : ι → ℝ) :
    growingPrefixForwardBesselPACBayesComplexity
        prior posterior (1 / 160) 2048 =
      klDiv posterior prior + Real.log 8960 := by
  rw [growingPrefixForwardBesselPACBayesComplexity_eq_logLog
    prior posterior (1 / 160) (by norm_num)]
  norm_num [Nat.log]

/-! Public surface. -/

#check countableForwardBesselPACBayesFinitePrefixArgmin
#check countableForwardBesselPACBayesFinitePrefixArgmin_mem
#check countableForwardBesselPACBayesFinitePrefixArgmin_le
#check growingPrefixForwardBesselPACBayesMaxIndex
#check geometricForwardEffectiveScale
#check geometricForwardEffectiveScale_pos
#check geometricForwardEffectiveScale_zero
#check geometricForwardEffectiveScale_succ
#check geometricForwardEffectiveScale_sq
#check geometricForwardBesselPACBayesComplexity
#check geometricForwardBesselPACBayesComplexity_mono
#check growingPrefixForwardBesselPACBayesComplexity
#check growingPrefixForwardBesselPACBayesComplexity_half_le
#check growingPrefixForwardBesselPACBayesComplexity_eq_logLog
#check growingPrefixForwardBesselPACBayesLILEnvelope
#check growingPrefixForwardBesselPACBayes_scale_sq_gt_four_mul
#check growingPrefixForwardBesselPACBayesArgmin
#check growingPrefixForwardBesselPACBayesArgmin_mem
#check growingPrefixForwardBesselPACBayesArgmin_le
#check countableForwardBesselPACBayesBoundary_le_observableRate
#check growingPrefixForwardBesselPACBayesBoundary_le_observableRate
#check growingPrefixForwardBesselPACBayesBoundary_le_LILEnvelope
#check growingPrefixForwardBesselPACBayesBoundary_le_allTimeRate
#check growingPrefixForwardBesselPACBayesBoundary_tendsto_zero
#check exists_growingPrefixForwardBesselPACBayesOracle_event
#check growingPrefixMaxIndex_512
#check growingPrefixEffectiveScale_512
#check growingPrefixComplexity_512_eq
#check growingPrefixMaxIndex_2048
#check growingPrefixEffectiveScale_2048
#check growingPrefixComplexity_2048_eq

/-! Load-bearing axiom receipt. -/

#print axioms countableForwardBesselPACBayesFinitePrefixArgmin_mem
#print axioms countableForwardBesselPACBayesFinitePrefixArgmin_le
#print axioms geometricForwardBesselPACBayesComplexity_mono
#print axioms growingPrefixForwardBesselPACBayesComplexity_half_le
#print axioms growingPrefixForwardBesselPACBayesComplexity_eq_logLog
#print axioms growingPrefixForwardBesselPACBayes_scale_sq_gt_four_mul
#print axioms growingPrefixForwardBesselPACBayesArgmin_mem
#print axioms growingPrefixForwardBesselPACBayesArgmin_le
#print axioms countableForwardBesselPACBayesBoundary_le_observableRate
#print axioms growingPrefixForwardBesselPACBayesBoundary_le_observableRate
#print axioms growingPrefixForwardBesselPACBayesBoundary_le_LILEnvelope
#print axioms growingPrefixForwardBesselPACBayesBoundary_le_allTimeRate
#print axioms growingPrefixForwardBesselPACBayesBoundary_tendsto_zero
#print axioms exists_growingPrefixForwardBesselPACBayesOracle_event
#print axioms growingPrefixMaxIndex_512
#print axioms growingPrefixEffectiveScale_512
#print axioms growingPrefixComplexity_512_eq
#print axioms growingPrefixMaxIndex_2048
#print axioms growingPrefixEffectiveScale_2048
#print axioms growingPrefixComplexity_2048_eq

end FormalSLT.Examples.CheckForwardBesselPACBayesOracle
