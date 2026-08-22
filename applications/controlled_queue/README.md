# Controlled queue preprocessing

Status: **PREPROCESSING, STRUCTURED ADAPTIVE OPE EVENT, FIXED SHARP
UNKNOWN-DYNAMICS EVENT, ONE EXACT INVARIANT/RISK ATOM, AND AN ALIGNED
KNOWN-KERNEL RECEIPT CHECKED** / **PROSPECTIVE PROTOCOL FROZEN LOCALLY;
INDEPENDENT GENERATOR/VERIFIER IMPLEMENTATION CHECKED LOCALLY; IMMUTABLE
PUBLIC BINDING, FRESH TRACE, HISTOGRAM, NUMERICAL `< 0.10` RECEIPT, MATCHED
BASELINES, AND NAMED-PATH EVENT MEMBERSHIP OPEN**

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
- `../../FormalSLT/Applications/ControlledQueueStructuredOPE.lean`: checked
  same-path intersection of preallocated risk events and scalar persistence
  confidence. Its `21 = 3 x 7` candidate--depth catalog, four admissible risk
  tilts, four admissible persistence tilts, posterior PMFs, and times are all
  selectable inside one outer-mass event.
- `../../FormalSLT/Applications/ControlledQueueRefreshSensitivity.lean`:
  checked exact affine identity for refresh-family target-policy Poisson drift
  and its residual transfer from candidate-drift and normalized-sensitivity
  oscillation certificates.
- `../../FormalSLT/Applications/ControlledQueueSharpStructuredOPE.lean`:
  checked fixed selected-atom sharp event using the nominal candidate, supplied
  shifted depth-twelve potential, and queue-threshold/nominal-model Dirac
  posterior. Its prospectively frozen wrapper fixes true `gamma = 149/200`,
  initial observation `(eco, state 0)`, and horizon `200000`.
- `../../FormalSLT/Applications/ControlledQueueSharpStructuredReceiptCore.lean`:
  checked pre-data reduction from any matching `24 x 2 x 24` physical
  transition histogram to the frozen primary endpoint. It uses only the
  preregistered affine Bessel branch, log-cost bounds `9` and `7`, and cumulant
  bounds `1/480` and `1/8064`; it contains no prospective counts or threshold
  conclusion.
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
- `structured-ope-protocol-v1.json` and its Markdown companion: fail-closed
  prospective contract for one independent structured unknown-dynamics trace.
  It freezes the source law, future-beacon seed rule, full-horizon indexing,
  fixed sharp primary, adaptive secondary, matched baselines, reporting rule,
  and required theorem/code-freeze work. It contains no fresh trace or result
  and is not publicly preregistered until one immutable OSF registration binds
  both the protocol commit and the completed code-freeze commit.
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
make check-controlled-queue-structured-ope-protocol
python3 -m pip install -r requirements-dev.txt
~/.elan/bin/lake exe cache get
make verify-controlled-queue-structured-ope-code-freeze
make verify-controlled-queue-model
make verify-controlled-queue-trace
make verify-controlled-queue-known-kernel-receipt
```

Only after the immutable registration and the single authorized prospective
generation exist, run
`make verify-controlled-queue-structured-ope-prospective-receipt`. That
post-beacon gate checks the trace generator's bytes, independently verifies the
beacon signature and every PRNG transition, checks the receipt generator's
bytes, independently reconstructs its arithmetic, and finally elaborates the
generated Lean certificate in that order. It never generates or overwrites an
artifact and is expected to fail before the future evidence exists.

The prospective protocol check validates canonical JSON, exact source hashes,
analytic constants and allocations, future drand-beacon derivation, and the
publish-regardless chronology. It also fails if any declared fresh trace,
receipt, manifest, or generated Lean output already exists. It does not fetch a
beacon or generate data.

The pre-beacon code-freeze target runs the four prospective generator/verifier
test lanes, verifies the pinned `py-ecc` quicknet signature path, builds the
generic histogram reduction, and elaborates both branches of the future
generated Lean module. The below-threshold compilation smoke uses the already
observed retrospective histogram only to exercise the conditional theorem
template; it is not prospective evidence or a receipt. The target finishes by
reasserting that all six reserved prospective outputs are absent and performs
no network fetch or canonical generation.

The model verification target fails if any generated model byte or manifest
hash is stale, runs the narrow arithmetic/schema tests, and builds the full
controlled-queue model, score, contraction, confidence, OPE, and invariant-risk
module/checker chain. The trace target separately regenerates the full byte
stream, then an implementation-independent verifier replays every random draw,
transition, count, and causal update. It also runs tamper, rejection,
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
and does not by itself certify a frozen path.
`ControlledQueueStructuredOPE` composes that scalar row-TV event with the
signed-residual target-policy OPE event. It allocates risk confidence uniformly
over all three generated candidates crossed with generated depths
`[0, 1, 2, 3, 5, 8, 12]`, and uses the admissible generated tilt prefix
`[1/16, 1/8, 1/4, 1/2]`; the terminal generated tilt `1` is excluded because
the event theorem requires a strict tilt below one. With risk and persistence
budgets `1/40` each, one event has complement mass at most `1/20`. On that
event, candidate, depth, both tilt atoms, posterior, and time may be selected
from their predeclared typed catalogs. For candidate `c`, depth `m`, and scalar
physical row-TV budget `eta`, the added residual is exactly
`gamma_c^m + 2 * (1 + B_c,m) * eta`. No all-row visitation premise or behavior
mass factor is used in this structured transfer.
The candidate/depth and tilt supports are bound to generated tables, while the
uniform `1/21` and `1/4` confidence weights are new checked Lean allocations;
they are not claimed to be the still-open next-trace weight contract in the
model input.
These selectors are pointwise substitutions into the common event, not a
measurable selected process or selected e-process.
`ControlledQueueRefreshSensitivity` uses the affine refresh-family structure
to identify the true-minus-candidate drift exactly as the observable
persistence-hit discrepancy times a normalized sensitivity. Consequently its
residual transfer is

```text
candidate drift oscillation
  + sensitivity oscillation * persistence-hit discrepancy budget,
```

with no extra total-variation factor `2 * (1 + B)`. The fixed sharp module
instantiates this formula with the nominal candidate, the supplied shifted
depth-twelve potential, the queue-threshold/nominal-model Dirac atom, risk tilt
`1/16`, persistence tilt `1/64`, and two failure budgets `1/40`. For the fixed
true parameter and fixed initial observation, its prospective wrapper gives an
outer event with complement mass at most `1/20` and evaluates the bound at
horizon `200000`.

That theorem is not an empirical receipt. No fresh prospective trace or
histogram has been generated, no named path has been proved to lie in the good
event, and no numerical endpoint below the protocol threshold `< 0.10` has
been checked. The local protocol is not publicly preregistered; public
registration must bind the protocol and completed independent
generator/verifier code freeze before its future-beacon seed is read.
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

The uniform reference is not asserted invariant, and each candidate's
persistence weight is a contraction upper bound rather than an asserted exact
Dobrushin coefficient. Neither catalog event proves named-trace or good-event
membership, resolves the initial-observation offset for an arbitrary upstream
trace, or establishes a prospectively selected useful numerical endpoint.

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
