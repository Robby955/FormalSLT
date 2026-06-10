import FormalSLT.OnlineToPAC.CesaBianchi

/-!
# IID-derived online-to-PAC concentration surface

This module re-exports the q059 online-to-PAC iid concentration route:

* `FormalSLT.Probability.IIDConcentration.iidDeviationBadEventMass_le_exp_of_sharpMcDiarmid`
  proves the finite-time bad-event probability from q049's sharp McDiarmid
  theorem.
* `regretConversion_iid` consumes the complement of that bad event instead of
  an externally supplied deviation gate.
* `cesaBianchi_iid` adds the finite-time regret-rate wrapper.

The older gate-taking q055 theorems remain available side by side in
`FormalSLT.OnlineToPAC.RegretConversion` and `FormalSLT.OnlineToPAC.CesaBianchi`.
-/
