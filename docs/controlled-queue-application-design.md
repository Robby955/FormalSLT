# Controlled queue application design

Status: **STRUCTURED ADAPTIVE QUEUE OPE EVENT, FIXED SHARP UNKNOWN-DYNAMICS
EVENT, ONE EXACT INVARIANT/RISK ATOM, AND AN ALIGNED KNOWN-KERNEL `< 0.07`
RECEIPT CHECKED LOCALLY** / **PROSPECTIVE PROTOCOL FROZEN LOCALLY;
INDEPENDENT GENERATOR/VERIFIER IMPLEMENTATION CHECKED LOCALLY; PUBLIC
PREREGISTRATION AND IMMUTABLE CODE BINDING, FRESH TRACE AND HISTOGRAM,
NUMERICAL `< 0.10` RECEIPT, MATCHED BASELINES, AND NAMED-PATH EVENT MEMBERSHIP
OPEN**

Original design base: FormalSLT release-candidate commit
`93c42192f8e66f2d77c35578e49dc39ff82b1324`.

Banked theorem-integration snapshot through fixed-candidate robust OPE: local
commit
`de4b2f02761d50ae86276b1fd4ae8bdce83fc018` (tree
`b63d0bf9358558bb38e1d208222f4f1af20b355c`). The same-path empirical-event
intersection is checked in the current local integration worktree beyond that
snapshot. Neither local state is evidence of inclusion in public `main`, draft
PR #99, or v0.2.

This packet specifies the smallest controlled finite-state application that can
serve as a journal-grade demonstration of FormalSLT's trajectory, stationary,
unknown-kernel, and policy-comparison layers. The frozen model input, exact
rational table generator, deterministic 200,000-transition trace, exact causal
prediction streams, independent replay verifier, generated Lean model-data
module, and SHA-256 manifests are implemented. Separate Lean modules now check
the generated table-to-`PMF` semantics, uniform behavior policy, pointwise
`3/2` target-to-behavior probability bound, sharp factor-two physical-row TV
transfer, fixed Brier and control-cost score semantics, unit-range bounds, and
history-interface overlap/ratio certificates. The bounded-score adapter also
supplies a universal centered row-risk oscillation envelope `D = 1` for every
generated fixed Brier score, candidate, target policy, and reference PMF.
Generic target-policy candidate robustness, fixed-envelope
approximate-Poisson OPE, and fixed-candidate finite-depth robust OPE are also
checked. A further generic theorem intersects the signed-residual OPE event
with augmented empirical-transition confidence under the same controlled path
law. With exact behavior mass `1/2` and every augmented source row visited, it
uses `etaEnv = 2 * etaAug` and the residual
`alpha ^ m * D + 4 * ((1 + B_m) * etaAug)`, with separate failure budgets
`deltaRisk + deltaTransition`. The candidate environment, depth, reference
PMFs, scores, and contraction certificates remain fixed before the event. The
queue specialization now fixes the nominal candidate and the 12 hypotheses
formed from four target policies and three fixed Brier predictors. For an
arbitrary true environment, initial observation, and depth fixed before the
event, it targets the canonical noncomputable `finiteInvariantPMF` witnesses,
uses the uniform reference, `alpha = 3/4` as a contraction upper bound, `D = 1`,
and `C = 3/2`. Fresh uniform full-support priors cover the 12 hypotheses and
4,608 augmented transition coordinates; singleton risk and transition tilts
are both `1/4`, and budgets `1/40` plus `1/40` give complement mass at most
`1/20`. The event is simultaneous over posterior PMFs and time, under positive
visits to all 48 augmented source rows at the displayed time. A separate
deterministic module fixes target-policy index `1` (queue-threshold) and
fixed-predictor index `2` (nominal-model overload) under the nominal candidate.
It constructs an explicit 24-state rational invariant PMF, identifies it with
the corresponding catalog witness by strict-contraction uniqueness, and proves
the exact stationary Brier risk
`4338268437 / 67816493056 < 13 / 200`. A further known-kernel receipt fixes the
realized initial observation `(1, 1)`, depth `12`, tilt `1/16`, and the aligned
199,999-score suffix. Python independently reconstructs the exact suffix
histogram from the raw bytes; Lean proves histogram-to-score arithmetic and a
selected boundary-plus-residual endpoint below `7/100`. The named trace is not
proved to belong to the theorem-produced good event. A separate structured
module now embeds the three candidates in the arbitrary-parameter refresh
family and obtains simultaneous time-uniform physical-row TV budgets from one
scalar hit statistic. A further checked module intersects preallocated OPE
events for the `3 x 7` generated candidate--depth catalog with that scalar
event. Candidate, depth, two admissible tilt atoms, posterior, and time may be
selected inside its common `19/20` outer-mass event. Its prospective numerical
endpoint and matched baselines remain open. A separate local prospective
protocol now freezes an independent off-grid refresh parameter, fixed initial
observation, future-public-beacon seed rule, sharp selected-potential primary,
adaptive secondary, comparison rows, and publish-regardless rule. It has not
yet received a public immutable timestamp and contains no fresh trace or
result. The sharp analytic lane is now checked locally: an exact affine
refresh-family identity replaces the generic TV transfer by candidate-drift
oscillation plus sensitivity oscillation times the path-dependent scalar
persistence budget. Its fixed wrapper uses the nominal candidate, supplied
shifted depth-twelve potential, queue-threshold/nominal-model Dirac posterior,
true `gamma = 149/200`, initial observation `(eco, state 0)`, and horizon
`200000`, with outer complement mass at most `1/20`. It does not provide the
still-absent fresh histogram, good-event membership, or numerical `< 0.10`
receipt.

The existing 20-state random-refresh load example remains a checked synthetic
worked example. It is not relabeled as a controlled queue: it has no actions or
policies, its predictors are fixed scores followed by post-prefix selection,
and its named-path numerical certificate is conditional on unproved good-event
membership.

## Frozen model specification

### State and action spaces

- Physical state: `Fin 8 × Fin 3`, interpreted as queue length and arrival
  regime, for 24 states.
- Actions: `eco` and `boost`, serving at most one or two jobs respectively.
- Markovized behavior state: `State × Action`, for 48 states.

The state encoding, action encoding, update order, truncation at queue length
seven, and regime transition rule must be fixed in a versioned input file
before paths or certificates are generated.

### Rational environment family

For physical state `z`, action `a`, and rational persistence parameter `gamma`,
use the benchmark kernel

```text
P_gamma(z, a) = gamma * delta(queueStep(z, a))
              + (1 - gamma) * Uniform(24).
```

The predeclared candidate catalog is
`gamma ∈ {5/8, 3/4, 7/8}`, with nominal value `3/4`.

The uniform-refresh component is a modeling assumption chosen to make the
finite-state contraction and invariant-law certificates tractable. It is not a
claim that real queues reset uniformly.

### Policies

- Behavior policy: uniform over the two actions.
- Target policies: conservative, queue-threshold, regime-aware, and aggressive.
- Each target action probability is either `1/4` or `3/4`.
- Under the uniform behavior policy, the importance-ratio cap is `3/2`.

The typed-model bridge checks exact rational policy normalization and
positivity, behavior mass `1/2`, and the pointwise target-to-behavior
probability bound `3/2`.

### Outcomes and bounded losses

Control cost:

```text
(8 * nextQueue + 7 * indicator(action = boost)) / 63 ∈ [0, 1].
```

Brier outcome:

```text
indicator(nextQueue >= 6).
```

Both targets are bounded before any statistical theorem is instantiated.

### Predictor catalog

Fixed predictors:

1. global climatology;
2. queue/action threshold forecast;
3. exact nominal-model overload forecast.

Causal predictors:

1. global Beta(1,1) posterior mean;
2. queue-band/action-cell Beta(1,1) posterior mean.

At time `t`, a causal predictor may use transitions with indices strictly below
`t` and no part of the outcome at `t`. Fixed predictors may be compared under
stationary target-policy risk. History-dependent causal predictors use the
dynamic encountered-risk comparator unless a new stationary-risk theorem is
proved for them.

## Existing FormalSLT support

The following pieces are checked at the local theorem-integration snapshot.
The generic modules do not by themselves instantiate the queue application.

| Requirement | Existing module | Supported scope |
|---|---|---|
| Controlled behavior paths, overlap, bounded importance scores | `StochasticDynamics.ControlledTrajectory` | Finite controlled trajectories and exact score identities |
| Markov behavior-law reduction | `StochasticDynamics.ControlledMarkovization` | Exact controlled-prefix and path-law equality with the homogeneous chain on `Action × State` |
| Action-conditioned TV transfer | `StochasticDynamics.ControlledKernelTV` | Exact shared-behavior TV decomposition; positive behavior mass gives the sharp inverse-probability row bound |
| Generated queue row ordering | `Applications.ControlledQueueReindex` | Exact state-major/action-minor indexing and the `(S_t, A_t)` row selected by a controlled edge |
| Typed generated queue model | `Applications.ControlledQueueTypedModel` | Exact table-backed kernel and policy PMFs, behavior mass `1/2`, target/behavior bound `3/2`, and physical-row TV at most twice augmented-row TV |
| Queue target-policy scores | `Applications.ControlledQueueTargetPolicyScores` | Fixed Brier scores reconstructed from generated forecasts/outcomes, generated control cost, unit-range bounds, universal centered row-risk envelope `D = 1`, overlap, and exact ratio cap `3/2`; causal Beta predictors excluded |
| Queue candidate contraction | `Applications.ControlledQueueContraction` | Table-backed common uniform minorization and induced target-policy Dobrushin upper bounds `5/8`, `3/4`, and `7/8`; the uniform reference is not claimed invariant |
| Structured queue persistence confidence | `Applications.ControlledQueuePersistenceConfidence` | Arbitrary fixed `gamma in [0,1)` in the generated refresh family; one direct/complement hit outer-mass event; exact all-row TV identity; simultaneous budgets for all three candidates, but no family-membership test |
| Structured adaptive queue OPE | `Applications.ControlledQueueStructuredOPE` | Same-path finite union over all three candidates and generated depths `[0,1,2,3,5,8,12]`, intersected with scalar persistence confidence; candidate, depth, two four-atom tilt choices, posterior, and time are selectable inside one event of complement mass at most `1/20` |
| Refresh-family drift sensitivity | `Applications.ControlledQueueRefreshSensitivity` | Exact true-minus-candidate Poisson-drift identity in the observable hit-probability coordinate, and residual bound `candidate drift oscillation + sensitivity oscillation * hit-discrepancy budget`, without the generic `2 * (1 + B)` TV factor |
| Fixed sharp structured queue OPE | `Applications.ControlledQueueSharpStructuredOPE` | Nominal candidate, supplied shifted depth-twelve potential, queue-threshold/nominal-model Dirac posterior, risk tilt `1/16`, persistence tilt `1/64`, and two `1/40` budgets; the frozen `gamma = 149/200`, `(eco, state 0)`, horizon-`200000` wrapper has outer complement mass at most `1/20`, but no trace or numerical receipt |
| Fixed queue OPE catalog | `Applications.ControlledQueueOPECatalog` | Twelve fixed hypotheses from four target policies and three fixed Brier predictors; nominal `Q`, canonical noncomputable true invariant witnesses, uniform reference, `alpha = 3/4`, `D = 1`, `C = 3/2`, fresh uniform 4,608-coordinate prior, singleton tilts `1/4`, and outer complement mass at most `1/20` for fixed true `P`, initial observation, and depth |
| Explicit queue invariant/risk atom | `Applications.ControlledQueueInvariantRisk` | Explicit 24-state rational invariant PMF for nominal `Q` and target-policy index `1`, equality to the canonical catalog witness by strict-contraction uniqueness, exact row risks for fixed-predictor index `2`, and stationary Brier risk `4338268437 / 67816493056 < 13 / 200` |
| Known-kernel aligned numerical receipt | `Applications.ControlledQueueKnownKernelReceipt` | Fixed-initial `39/40` event, exact depth-twelve potential/residual, aligned `24 x 2 x 24` suffix-histogram bridge, and selected risk endpoint below `7/100`, conditional on the histogram and event inequality |
| Known-environment target-policy OPE | `StochasticDynamics.StationaryTargetPolicyOPE` | Supplied invariant laws and exact Poisson potentials |
| Target-policy candidate robustness | `StochasticDynamics.StationaryTargetPolicyRobustCandidate` | Induced-kernel TV transfer, `(1 + B) * etaEnv` drift perturbation, and a supplied-invariant residual envelope |
| Approximate-Poisson target-policy OPE | `StochasticDynamics.StationaryTargetPolicyApproximateOPE` | One event over time, posterior, and declared tilt atoms for fixed environment, invariant PMFs, potentials, and pointwise residual envelopes |
| Fixed-candidate finite-depth robust OPE | `StochasticDynamics.StationaryTargetPolicyRobustFiniteDepthOPE` | Candidate finite-depth potential and residual `alpha ^ m * D + 2 * ((1 + B_m) * etaEnv)` for candidate, depth, certificates, and envelope fixed before the event |
| Same-path empirical robust OPE | `StochasticDynamics.StationaryTargetPolicyEmpiricalFiniteDepthOPE` | Intersects risk and augmented-transition events with mass cost `deltaRisk + deltaTransition`; under behavior mass `1/2` and all augmented rows visited, uses `etaEnv = 2 * etaAug` and residual `alpha ^ m * D + 4 * ((1 + B_m) * etaAug)` |
| Fixed and history-dependent score comparison | `StochasticDynamics.DynamicTargetPolicyComparator` | Behavior-encountered histories |
| Finite-depth Poisson selection | `StochasticDynamics.StationaryPoissonDepthSelection` | Ordinary finite-state Markov scores |
| Empirical transition confidence | `StochasticDynamics.EmpiricalTransitionConfidence` | State-only transition rows and candidate TV budgets |
| Same-path stationary candidate selection | `StochasticDynamics.EmpiricalStationaryCatalog` | Candidate, posterior, depth, and tilt catalogs |

These modules now provide both the generic empirical-transition/OPE event
intersection, its fixed 12-atom queue specialization, and the structured
refresh-family event with preallocated candidate--depth selection. The new
declarations are outside the 19-name v0.2 compatibility allowlist.

## Remaining theorem and application work

The typed queue-table instantiation, sharp factor-two deterministic row-TV
transfer, target-policy scores and overlap, candidate target-kernel
contraction, target-policy robustness, approximate and finite-depth OPE,
generic same-path empirical-event intersection, and fixed 12-atom queue event
are checked. One executable known-model atom is also checked: the explicit
queue-threshold/nominal-model invariant law equals its canonical catalog
witness, and its stationary Brier risk is exactly
`4338268437 / 67816493056 < 13 / 200`. The aligned known-kernel receipt now
proves the selected endpoint below `7/100` from the suffix histogram and event
inequality. The following application items remain **OPEN**.

1. Prospective structured unknown-dynamics receipt and matched baselines: the
   fresh 4,608-coordinate empirical-transition allocation is vacuous on the
   current trace. The scalar persistence route and its checked sharp
   drift-sensitivity composition avoid that allocation within the refresh
   family. The local v1 protocol freezes the primary and comparisons, but the
   independent generator/verifier implementation and pre-beacon gate are
   completed and checked locally. One public OSF registration must still bind
   the protocol and code-freeze commits
   before the formula-selected future beacon round is read or a fresh trace is
   generated. The resulting trace, histogram, selected numerical `< 0.10`
   receipt, and every matched comparison must then be reported whether the
   primary succeeds or fails.
2. Probabilistic trace interpretation: the known-kernel receipt resolves the
   deterministic initial-offset and histogram alignment for the realized
   suffix, but does not prove named-path good-event membership or unconditional
   coverage for the upstream random first observation. Those require a
   separate membership witness or random-initial mixture/conditioning bridge.
3. Broader selection remains outside this result: candidates and depths may be
   selected only from the predeclared `3 x 7` catalog, tilts only from its four
   admissible atoms, and scores only through posterior PMFs on the twelve fixed
   policy--predictor hypotheses. No path-fitted kernel, depth, potential, or
   causal predictor is licensed. These are pointwise substitutions into one
   common event, not a measurable selected process or selected e-process.

Until those steps close, the known-kernel result is a checked retrospective
receipt: it demonstrates the exact theorem-to-histogram arithmetic, but no
external record currently establishes that the depth, tilt, and potential were
selected before this trace was inspected. It is therefore not presented as a
prospectively calibrated report for the already-observed trace. The controlled
queue's end-to-end unknown-dynamics numerical certificate remains open. No
named-path good-event membership, histogram-conditioned coverage,
unconditional simulator coverage, or useful prospective numerical endpoint is
claimed. The protocol-only file is not a numerical result or public
preregistration merely because it exists in a local Git commit.

## Frozen input and generator contract

Use one versioned JSON input with exact rational fields:

- schema and model versions;
- candidate environment kernels;
- behavior and target policy tables;
- fixed predictor tables and causal predictor specifications;
- horizon and random seed;
- confidence allocation;
- posterior, depth, and tilt grids.

The trace schema now supplies the exact initial state; versioned,
language-independent PRNG and exact sampling contracts; and exact rational
prior, posterior, candidate, coordinate, and tilt weight tables. Its PRNG is a
SHA-256 counter stream with a frozen test vector. Exact categorical draws use
unsigned 64-bit big-endian words and rejection sampling before reduction
modulo the common integer-weight denominator. A seed alone would not have been
a reproducible sampling contract.

Those frozen weight tables are not instantiated by the checked 12-atom event.
The trace file has 48 source-row coordinate weights, whereas the theorem uses a
fresh uniform full-support prior on all `48 * 48 * 2 = 4,608` transition
coordinates. Its tilt grid contains `1`, but every theorem tilt must be strictly
below one. Its five-predictor prior also includes both causal predictors and has
no target-policy factor. The application theorem therefore uses a separate
uniform prior on the four-target-policy by three-fixed-predictor catalog and
separate singleton risk and transition tilts equal to `1/4`.

A dependency-free deterministic generator now emits:

1. the controlled trace;
2. transition, action, visit, and binary-outcome count tables;
3. exact pre-outcome numerator/denominator streams for both causal Beta
   predictors;
4. a machine-readable manifest containing schema version, generator revision,
   parameters, and SHA-256 hashes for every consumed input, generator, verifier,
   and output.

The generator and independent replay verifier are preprocessing only. The
trace is deliberately not embedded in Lean. Checked adapters already discharge
row ordering, table normalization and positivity, typed-PMF conversion, and
the static probability and TV transfers. The queue application now composes
the risk and empirical augmented-transition events for the fixed 12-atom
catalog and uses canonical noncomputable true invariant witnesses. That general
4,608-coordinate route still requires compact count and all-row-visit witnesses.
The structured persistence route instead scores one row-independent statistic
and needs no all-row-visit premise. Its checked adaptive OPE composition uses
the generated candidate/depth and admissible-tilt supports, together with new
uniform `1/21` and `1/4` Lean confidence allocations that are not generated
model fields. The fixed sharp route further checks the selected nominal
depth-twelve residual as candidate-drift oscillation plus refresh-sensitivity
oscillation times a path-dependent persistence budget; it has no extra
`2 * (1 + B)` factor. It has not yet been evaluated on a fresh prospectively
generated trace.

The pre-data receipt reduction is now checked separately in
`ControlledQueueSharpStructuredReceiptCore`. Its generic histogram theorem
uses current state `S_k`, newly sampled action `A_(k+1)`, and next state
`S_(k+1)` for all `200000` scored transitions. It fixes the affine Bessel
branch and the protocol's rational log/psi upper bounds before any prospective
counts exist. A future generated receipt may instantiate this theorem with a
verified histogram, but this result alone does not bind raw bytes, establish
good-event membership, or prove the `< 0.10` target.
Later application slices must still
provide any further invariant/risk receipts needed for reported atoms,
trace/event alignment, and final numerical confidence arithmetic. One explicit
invariant law and stationary risk is now checked for the queue-threshold/
nominal-model atom. The generic centered row-risk envelope `D = 1` is already
checked; any sharper queue-specific constant remains a refinement.

### Implemented preprocessing slice

The first slice freezes the model before any trajectory is sampled:

- `applications/controlled_queue/model-v1.json` fixes the 24-state encoding,
  service-before-arrival update, cyclic regime transition, candidate gammas,
  exact behavior and target policy vectors, predictor specifications, bounded
  outcomes, and future trace/catalog parameters;
- the model input marks the initial state, language-independent PRNG/sampling
  contracts, and prior/posterior/candidate/coordinate/tilt weights as required
  inputs for a separate trace schema; `trace-v1.json` supplies and freezes all
  of those values without changing the model schema;
- `scripts/generate_controlled_queue_model.py` rejects duplicate keys, floats,
  noncanonical rationals, unknown fields, and schema drift, then compiles full
  exact rational kernel, policy, fixed-predictor, control-cost, and Brier-loss
  tables;
- `applications/controlled_queue/generated/model-v1-tables.json` is the
  machine-readable generated table set;
- `FormalSLT/Applications/ControlledQueueData.lean` contains generated
  definitions and tables only and is reachable through the opt-in application
  umbrella, not the stable v0.2 API list;
- `applications/controlled_queue/generated/model-v1-manifest.json` binds the
  input, generator source, JSON tables, and Lean module by SHA-256.

Run `make generate-controlled-queue-model` and
`make generate-controlled-queue-trace` to regenerate. After obtaining the
pinned Mathlib cache, run `make verify-controlled-queue-model` to exercise the
model arithmetic tests and build the controlled-queue model, score,
contraction, confidence, OPE, and invariant-risk module/checker chain. Run
`make verify-controlled-queue-trace` for byte-staleness checks, the independent
full replay, and the trace-specific tests; that target does not invoke Lean.
Before any public registration or beacon read, install the pinned development
dependencies and run
`make verify-controlled-queue-structured-ope-code-freeze`. That gate checks
the fail-closed protocol, all four prospective generator/verifier lanes, the
generic Lean histogram reduction, and coherent above- and below-threshold
generated-module smokes without writing a prospective artifact. The
below-threshold smoke deliberately reuses the retrospective histogram only as
a compiler fixture; it is not a confirmatory result or good-event witness.
After the immutable registration and one authorized generation, the separate
`make verify-controlled-queue-structured-ope-prospective-receipt` gate enforces
trace byte checking, independent BLS/PRNG replay, receipt byte checking,
independent receipt arithmetic, and generated-Lean elaboration in that order.
It performs no generation and therefore fails before those future artifacts
exist.

The second preprocessing slice adds `trace-v1.json`, a compact binary trace,
exact empirical count tables, exact causal Beta prediction streams, a SHA-256
manifest, and a separately implemented replay verifier. The verifier checks
all hashes, regenerates every action and transition, reconstructs every count,
and confirms each causal prediction uses only outcomes at indices strictly
below its transition index.

The binary stores physical states and actions as separate arrays. FormalSLT's
`ControlledObservation Z A` is `A × Z`, while the generated augmented-kernel
rows use state-major `(Z, A)` indexing. `ControlledQueueReindex` now proves the
swap, index equivalence, and controlled-edge row selection.
`ControlledQueueTypedModel` constructs typed PMFs from the generated compact
persistence/destination kernel specification and policy table, and identifies
each candidate mass with the corresponding exported generated-table lookup.
`ControlledQueueTargetPolicyScores`
turns the three fixed predictors and the generated control cost into bounded
target-policy scores and closes the static overlap and `3/2` ratio premises.
`ControlledQueueContraction` checks the candidate cell floors and turns them
into target-policy contraction factors. `ControlledQueuePersistenceConfidence`
uses the same compact refresh representation for an arbitrary fixed true
parameter, then turns a direct/complement destination-hit confidence sequence
into exact physical-row TV budgets for all three candidates.
`ControlledQueueOPECatalog` fixes the
12 stationary hypotheses and supplies the same-path empirical event with
canonical noncomputable true invariant witnesses. None of these bridges imports
the frozen trace or proves membership in the resulting event.
`ControlledQueueInvariantRisk` separately supplies the explicit nominal
queue-threshold invariant PMF and exact nominal-model overload risk for one
catalog atom, without making a trace or confidence statement.
The causal Beta predictors remain dynamic behavior-encountered scores. They
are not fixed stationary target-policy scores without augmenting the state by
learner memory and proving the corresponding stationary theorem.

There is also an initial-observation offset. The binary preserves
`S_0, A_0, S_1, ..., A_{H-1}, S_H`, sampling `A_0` and `S_1` after the fixed
physical state `S_0`. The current deterministic-initial
`controlledTrajectoryMeasure` fixes the controlled observation `(A_0, S_1)`.
A future use must therefore condition on and score an explicitly indexed
suffix beginning at the realized first pair, or prove a random-initial
controlled-law bridge. No direct full-trace horizon alignment is claimed.

The application now checks one explicit true invariant law and stationary risk
for the nominal queue-threshold/nominal-model atom and one trace-aligned
known-kernel bound conditional on the aligned suffix histogram and event
inequality. It also checks the fixed sharp unknown-dynamics event for true
`gamma = 149/200`, fixed initial observation, and horizon `200000`, but still
does not check a fresh unknown-dynamics histogram, trace-aligned numerical
bound, or named-path good-event membership. Those remain later certificate
slices, not preprocessing claims.

## Matched comparison contract

All displayed methods must use the same frozen trace, horizon, predictor and
posterior catalog, target policy, and total failure budget.

Compare:

1. empirical-Bernstein primary endpoint;
2. fixed-range endpoint;
3. fixed-depth endpoint;
4. non-variance-adaptive endpoint.

The report must show empirical loss, correction width, total upper endpoint,
and the exact confidence allocation for every row. Report the ordering even if
the primary method does not win.

## Receipt and review contract

The final package needs both:

- a theorem-produced event of mass at least `1 - delta`, simultaneous over the
  declared posterior, depth, and tilt catalogs; and
- an exact Lean theorem evaluating the frozen trace's selected endpoint and all
  matched baselines.

The frozen trace must not be claimed to belong to an existential or
high-probability good event unless membership is separately proved. A useful
certificate requires a final endpoint below the loss range, not merely a
positive or finite width.

Before journal use, obtain two independent reviews:

1. probability/statistics review of conditioning, selector order, confidence
   accounting, OPE semantics, and comparison denominators;
2. Lean review of model encoding, generated witnesses, imports, axiom profiles,
   and end-to-end reproducibility.

## Completion criteria

This application milestone is complete only when all of the following hold:

- actions and target policies materially affect the stated estimand;
- at least one causal predictor is evaluated without look-ahead;
- known-kernel and empirical-kernel results are labeled separately;
- adaptive choices are numerically identified, not only introduced through an
  unspecified `Classical.choose` argmin;
- the generator reproduces byte-identical inputs, Lean witnesses, and manifest;
- the exact Lean receipt gives at least one endpoint below one;
- matched baselines use the same data and failure budget;
- independent probability and Lean reviews are recorded;
- any queue-specific end-to-end unknown-dynamics OPE claim remains `OPEN` until
  executable certificates, trace and good-event alignment, and any claimed
  data-dependent candidate or depth selection are checked.
