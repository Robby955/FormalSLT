import FormalSLT.TestTimeMeta.CompositionLemmas

/-!
# PAC-Bayes test-time framework adapter

This module states the q057 named-assumption adapter. It keeps the scalar
contributions from the McAllester compiler, online-to-PAC conversion,
continuous-prior Bernstein certificate, anytime-valid Ville step, and prefix
conditional-kernel route in one closed-form bound, but the public flagship
theorem is supplied by the four-component assembly.

The theorem is intentionally explicit about narrowed inputs inherited from the
building blocks: q053 is unit-interval-normalized before q057 applies the loss
width, q055's original finite-time route remains deviation-gate-conditional,
q059 supplies an iid-derived finite-time route through the sharp-McDiarmid
bad-event complement, q056 is certificate-form for continuous
priors/posteriors, and the prefix-kernel route is supplied as a named
contribution.
-/

namespace FormalSLT.TestTimeMeta

/-- Framework adapter with all narrowed assumptions named. -/
theorem pacBayesTestTimeMeta_theorem
    (assumptions : TestTimeMetaAssumptions)
    (hmcAllesterScaled :
      0 ≤ assumptions.lossWidth.lossWidth *
        assumptions.mcAllester.unitIntervalCompilerContribution)
    (hbound :
      assumptions.populationRisk ≤ testTimeMetaBound assumptions) :
    testTimeMetaConclusion assumptions := by
  have _ := hmcAllesterScaled
  simpa [testTimeMetaConclusion] using hbound

end FormalSLT.TestTimeMeta
