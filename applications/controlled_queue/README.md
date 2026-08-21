# Controlled queue preprocessing

Status: **PREPROCESSING, STRUCTURED ROW-TV CONFIDENCE, FIXED-CATALOG EVENT, ONE
EXACT INVARIANT/RISK ATOM, AND AN ALIGNED KNOWN-KERNEL RECEIPT CHECKED** /
**STRUCTURED OPE COMPOSITION, NAMED-PATH EVENT MEMBERSHIP, AND UNKNOWN-DYNAMICS
NUMERICAL CERTIFICATE OPEN**

This directory freezes and compiles the deterministic model inputs for the
24-state, two-action controlled-queue benchmark. The trace slice is a frozen,
deterministically replayable data artifact. It is not a statistical
certificate, a theorem-produced good path, Lean-verified trace data, or a proof
of unknown-kernel target-policy OPE.

## Files

- `model-v1.json`: exact input schema and benchmark parameters. Rational values
  are canonical strings such as `3/4`; JSON floats are forbidden.
- `generated/model-v1-tables.json`: full exact rational candidate-kernel,
  policy, fixed-predictor, control-cost, outcome, and Brier-loss tables.
- `generated/model-v1-manifest.json`: schema/model/generator identifiers,
  frozen future parameters, and SHA-256 bindings for the input and outputs.
- `../../FormalSLT/Applications/ControlledQueueData.lean`: generated Lean
  definitions and tables. It intentionally contains no theorem or certificate.
- `../../FormalSLT/Applications/ControlledQueueReindex.lean`: checked row-order,
  tuple-swap, and controlled-edge selection bridge.
- `../../FormalSLT/Applications/ControlledQueueTypedModel.lean`: checked
  table-backed kernel and policy PMFs with exact mass identities and the static
  uniform-behavior probability and TV transfers.
- `../../FormalSLT/Applications/ControlledQueueTargetPolicyScores.lean`:
  checked fixed Brier and control-cost scores, unit-range bounds, target-policy
  overlap, the exact `3/2` ratio cap, and a universal centered row-risk
  oscillation envelope `D = 1` for each fixed Brier score. The two causal Beta
  predictors remain outside this stationary-score interface.
- `../../FormalSLT/Applications/ControlledQueueContraction.lean`: checked
  candidate cell minorization, uniform physical-state reference, Dobrushin
  upper bounds `5/8`, `3/4`, and `7/8`, and target-policy oscillation
  contraction. The coefficient is bounded above, not claimed exact.
- `../../FormalSLT/Applications/ControlledQueuePersistenceConfidence.lean`:
  checked arbitrary-parameter refresh-family PMFs, a direct/complement
  persistence-hit outer-mass event, the exact identity between hit-probability
  discrepancy and every physical-row TV discrepancy, and simultaneous budgets
  for all three generated candidates.
- `../../FormalSLT/Applications/ControlledQueueOPECatalog.lean`: locally
  checked 12-atom catalog obtained from four fixed target policies and three
  fixed Brier predictors, together with its fixed-nominal-candidate empirical
  finite-depth OPE event.
- `../../FormalSLT/Applications/ControlledQueueInvariantRisk.lean`: locally
  checked explicit 24-state invariant PMF for the nominal environment and
  queue-threshold target policy, its equality to the catalog's canonical
  invariant witness, and the exact nominal-model overload Brier risk.
- `../../FormalSLT/Applications/ControlledQueueKnownKernelReceipt.lean`:
  checked fixed-initial `39/40` known-kernel OPE event and exact selected
  `< 7/100` endpoint conditional on the aligned suffix histogram and event
  inequality.
- `known-kernel-receipt-v1.json` and the generated receipt/manifest/Lean data:
  exact depth-twelve potential, suffix histogram, score moments, residual, and
  rational endpoint bound, independently reconstructed from the model tables
  and raw trace.
- `../../FormalSLT/StochasticDynamics/StationaryTargetPolicyEmpiricalFiniteDepthOPE.lean`:
  generic same-path intersection of signed-residual target-policy OPE and
  augmented empirical-transition confidence for a fixed candidate, depth, and
  certificate package.
- `trace-v1.json`: exact initial state, horizon, source candidate, behavior
  policy, weight tables, binary layout, SHA-256 counter-stream contract, and
  unbiased rejection-sampling contract.
- `generated/trace-v1.bin`: 200,000 transitions as explicit state and action
  arrays plus the exact pre-outcome numerator/denominator stream for both
  causal Beta predictors.
- `generated/trace-v1-counts.json`: exact state, action, state-action, edge, and
  outcome counts together with final causal sufficient statistics and PRNG
  consumption counts.
- `generated/trace-v1-manifest.json`: SHA-256 bindings for both inputs, both
  generators, the independent verifier, and both generated outputs.

Both generators and the independent trace verifier under `../../scripts/` use
only the Python standard library.

## Regenerate and verify

```bash
make generate-controlled-queue-model
make generate-controlled-queue-trace
make generate-controlled-queue-known-kernel-receipt
~/.elan/bin/lake exe cache get
make verify-controlled-queue-model
make verify-controlled-queue-trace
make verify-controlled-queue-known-kernel-receipt
```

The model verification target fails if any generated model byte or manifest
hash is stale, runs the narrow arithmetic/schema tests, and compiles only the
generated Lean data module. The trace target separately regenerates the full
byte stream, then an implementation-independent verifier replays every random
draw, transition, count, and causal update. It also runs tamper, rejection,
no-look-ahead, and stale-artifact tests. The known-kernel receipt target runs a
second independent arithmetic implementation, adversarial schema/provenance
tests, the memory-bounded Lean receipt build, and its public theorem checker.

The binary stores `state_t` and `action_t` separately. FormalSLT's
`ControlledObservation Z A` is represented as `A × Z`, while the generated
model's 48 rows use state-major indices `2 * state + action`.
`ControlledQueueReindex` proves the required swap, index equivalence, and
controlled-edge row selection. `ControlledQueueTypedModel` constructs typed
PMFs from the generated compact persistence/destination kernel specification
and policy table, and proves that each candidate mass equals the corresponding
exported generated-table lookup.
`ControlledQueueTargetPolicyScores` reconstructs the three fixed Brier scores
from the generated forecast and outcome tables and types the generated
control-cost score. `ControlledQueueContraction` lifts each generated
candidate's common cell floor through every state-Markov target policy.
`ControlledQueuePersistenceConfidence` instead treats the true environment as
`(1 - gamma) * Uniform24 + gamma * delta_step` for arbitrary fixed
`gamma in [0,1)`. A destination hit includes both persistence and an accidental
uniform refresh to the step state, so its mean is `(1 + 23 * gamma) / 24`, not
`gamma`. One outer-mass event is simultaneous over declared tilts and times,
and after that event the candidate may be chosen from the three generated
values. The result is not uniform over `gamma`, does not test family membership,
and is not yet composed with target-policy OPE or a frozen path.
`ControlledQueueOPECatalog` then fixes the nominal candidate `Q`, the uniform
finite-depth reference, contraction upper bound `alpha = 3/4`, centered
row-risk envelope `D = 1`, and ratio cap `C = 3/2`. For an arbitrary true
environment `P` and an initial observation and depth fixed before the event, it
uses the canonical noncomputable `finiteInvariantPMF` of each true
target-policy kernel. With fresh uniform full-support priors over the 12
hypotheses and all 4,608 augmented transition coordinates, singleton risk and
transition tilts `1/4`, and failure budgets `1/40` each, it gives one event of
complement mass at most `1/20`. The event is simultaneous over every posterior
PMF and time `n >= 2`; its normalized bound at the displayed time assumes all
48 augmented source rows were visited.

The uniform reference is not asserted invariant, and `alpha = 3/4` is an upper
bound rather than an exact Dobrushin coefficient. The catalog event theorem
does not prove named-trace or good-event membership, resolve the
initial-observation offset, select the candidate or depth from data, or
establish a numerically useful confidence endpoint.

Separately, `ControlledQueueInvariantRisk` fixes target-policy index `1`
(queue-threshold) and fixed-predictor index `2` (nominal-model overload) under
the nominal candidate. It constructs an explicit rational 24-state invariant
PMF, proves invariance, and uses strict Dobrushin contraction to identify that
PMF with the catalog's canonical noncomputable witness. Its exact stationary
Brier risk is

```text
4338268437 / 67816493056 < 13 / 200
```

This exact risk is a deterministic known-model calculation. It does not use
the frozen trace and is not a confidence bound, a good-event membership proof,
an unknown-kernel result, or permission for post-data policy, predictor,
candidate, or depth selection.

`ControlledQueueKnownKernelReceipt` then fixes the same catalog atom, depth
`12`, ratio cap `3/2`, a uniform twelve-atom prior, tilt `1/16`, and failure
budget `1/40`. The aligned physical suffix uses transitions `1` through
`199999`, hence `199999` controlled scores and fixed initial observation
`(action = 1, state = 1)`. The generated `24 x 2 x 24` histogram determines
the exact score and squared-score sums in Lean; those give a conservative
rational boundary-plus-residual endpoint below `7/100`. Scalar moments alone
are intentionally insufficient because the adjacent wrong slice has the same
two moments but a different histogram.

The theorem does not prove that the named trace belongs to its probabilistic
good event. It separately proves the event mass statement and the deterministic
histogram-to-endpoint statement, and a final corollary accepts both premises.
In particular, it does not prove `39/40` coverage conditional on observing the
receipt histogram: the mass bound is for the fixed-initial path law, while the
histogram is a separate deterministic premise for the endpoint calculation.
It is a known-kernel result, not the empirical-transition certificate.

The theorem deliberately does not instantiate the weight tables in
`trace-v1.json` for the empirical-kernel event: that file supplies only 48 coordinate weights, while the
transition-coordinate prior here needs 4,608 atoms; its tilt grid includes `1`,
which violates the theorem's strict `< 1` premise; and its five-predictor prior
includes the causal predictors and has no target-policy factor. The fresh
12-hypothesis and 4,608-coordinate priors and singleton `1/4` tilts are separate
checked declarations.
Likewise, the causal Beta predictors currently support dynamic
behavior-encountered comparison only. They are not fixed stationary
target-policy scores unless learner memory is added to the state and a
corresponding theorem is proved.

The stored path is `S_0, A_0, S_1, ..., A_{H-1}, S_H`. The current
deterministic-initial `controlledTrajectoryMeasure` instead fixes an initial
controlled observation `(A_0, S_1)`. The known-kernel receipt explicitly uses
the realized fixed pair `(1, 1)` and the aligned suffix. This gives
fixed-initial-law coverage, not histogram-conditioned coverage; an
unconditional statement for the upstream simulator still requires a
random-initial mixture or conditioning bridge.
