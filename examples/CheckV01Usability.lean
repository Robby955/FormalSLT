import FormalSLT

/-!
# FormalSLT v0.1 usability checker

This file is the short import-and-verify entrypoint for the v0.1 package.
It checks the named theorem surfaces that downstream notes and TheoremPath
should cite:

* the finite-class countable-time Hoeffding confidence-sequence API;
* the unit-interval rounded-dyadic Dudley bridge;
* the reusable finite dyadic-net sequence API, instantiated on two examples.

Run it directly with:

```bash
lake env lean examples/CheckV01Usability.lean
```
-/

/-! ## Finite-class confidence-sequence API -/

#check FormalSLT.UniformConvergence.FiniteClassConfidenceSequence

#check FormalSLT.UniformConvergence.finiteClassConfidenceSequenceFailureEvent

#check FormalSLT.UniformConvergence.FiniteClassConfidenceSequence.failure_probability_le
#print axioms FormalSLT.UniformConvergence.FiniteClassConfidenceSequence.failure_probability_le

#check FormalSLT.UniformConvergence.zeroOneDyadicFiniteClassConfidenceRadius_le_of_sampleSize_ge
#print axioms FormalSLT.UniformConvergence.zeroOneDyadicFiniteClassConfidenceRadius_le_of_sampleSize_ge

/-! ## Reusable finite dyadic-net sequence API -/

#check FormalSLT.Covering.FiniteSubGaussianChaining.FiniteSubGaussianProcess.FiniteDyadicNetSequence

#check FormalSLT.Covering.FiniteSubGaussianChaining.FiniteSubGaussianProcess.FiniteDyadicNetSequence.projectedNet_dudley_bound
#print axioms FormalSLT.Covering.FiniteSubGaussianChaining.FiniteSubGaussianProcess.FiniteDyadicNetSequence.projectedNet_dudley_bound

#check FormalSLT.Covering.FiniteSubGaussianChaining.FiniteSubGaussianProcess.FiniteDyadicNetSequence.supFunctional_dudley_bound
#print axioms FormalSLT.Covering.FiniteSubGaussianChaining.FiniteSubGaussianProcess.FiniteDyadicNetSequence.supFunctional_dudley_bound

/-! ## Unit-interval non-finite Dudley bridge -/

#check FormalSLT.Covering.UnitIntervalDudley.unitIntervalRoundedDyadicGridNetSequence

#check FormalSLT.Covering.UnitIntervalDudley.unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound_prefixFree
#print axioms FormalSLT.Covering.UnitIntervalDudley.unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound_prefixFree

#check FormalSLT.Covering.UnitIntervalDudley.unitIntervalRademacherLinearSup_dudley_m1_bound_constEntropy_eval
#print axioms FormalSLT.Covering.UnitIntervalDudley.unitIntervalRademacherLinearSup_dudley_m1_bound_constEntropy_eval

/-! ## Second dyadic-net instantiation -/

#check FormalSLT.Covering.TwoPointDudley.twoPointDyadicNetSequence
#print axioms FormalSLT.Covering.TwoPointDudley.twoPointDyadicNetSequence

#check FormalSLT.Covering.TwoPointDudley.twoPointRademacher_projected_dudley_m_bound
#print axioms FormalSLT.Covering.TwoPointDudley.twoPointRademacher_projected_dudley_m_bound

#check FormalSLT.Covering.TwoPointDudley.twoPointRademacherSup_dudley_m_bound
#print axioms FormalSLT.Covering.TwoPointDudley.twoPointRademacherSup_dudley_m_bound
