# Controlled queue application design

Status: **TYPED MODEL AND FIXED-CANDIDATE ROBUST OPE BRIDGES CHECKED LOCALLY** /
**EMPIRICAL APPLICATION CERTIFICATE OPEN**

Original design base: FormalSLT release-candidate commit
`93c42192f8e66f2d77c35578e49dc39ff82b1324`.

Checked theorem-integration snapshot: local commit
`de4b2f02761d50ae86276b1fd4ae8bdce83fc018` (tree
`b63d0bf9358558bb38e1d208222f4f1af20b355c`). This snapshot is local and is
not evidence of inclusion in public `main`, draft PR #99, or v0.2.

This packet specifies the smallest controlled finite-state application that can
serve as a journal-grade demonstration of FormalSLT's trajectory, stationary,
unknown-kernel, and policy-comparison layers. The frozen model input, exact
rational table generator, deterministic 200,000-transition trace, exact causal
prediction streams, independent replay verifier, generated Lean model-data
module, and SHA-256 manifests are implemented. Separate Lean modules now check
the generated table-to-`PMF` semantics, uniform behavior policy, pointwise
`3/2` target-to-behavior probability bound, and sharp factor-two physical-row
TV transfer. Generic target-policy candidate robustness, fixed-envelope
approximate-Poisson OPE, and fixed-candidate finite-depth robust OPE are also
checked. The trace remains preprocessing: it is not a theorem-produced good
path, Lean-verified trace, empirical-event composition, or numerical
application certificate.

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
| Known-environment target-policy OPE | `StochasticDynamics.StationaryTargetPolicyOPE` | Supplied invariant laws and exact Poisson potentials |
| Target-policy candidate robustness | `StochasticDynamics.StationaryTargetPolicyRobustCandidate` | Induced-kernel TV transfer, `(1 + B) * etaEnv` drift perturbation, and a supplied-invariant residual envelope |
| Approximate-Poisson target-policy OPE | `StochasticDynamics.StationaryTargetPolicyApproximateOPE` | One event over time, posterior, and declared tilt atoms for fixed environment, invariant PMFs, potentials, and pointwise residual envelopes |
| Fixed-candidate finite-depth robust OPE | `StochasticDynamics.StationaryTargetPolicyRobustFiniteDepthOPE` | Candidate finite-depth potential and residual `alpha ^ m * D + 2 * ((1 + B_m) * etaEnv)` for candidate, depth, certificates, and envelope fixed before the event |
| Fixed and history-dependent score comparison | `StochasticDynamics.DynamicTargetPolicyComparator` | Behavior-encountered histories |
| Finite-depth Poisson selection | `StochasticDynamics.StationaryPoissonDepthSelection` | Ordinary finite-state Markov scores |
| Empirical transition confidence | `StochasticDynamics.EmpiricalTransitionConfidence` | State-only transition rows and candidate TV budgets |
| Same-path stationary candidate selection | `StochasticDynamics.EmpiricalStationaryCatalog` | Candidate, posterior, depth, and tilt catalogs |

These modules are reusable substrate. Their existence does not by itself
compose empirical transition confidence with controlled OPE or license
data-dependent candidate, depth, or residual-envelope selection. The new
declarations are outside the 19-name v0.2 compatibility allowlist.

## Remaining theorem and application work

The typed queue-table instantiation, sharp factor-two deterministic row-TV
transfer, generic target-policy candidate robustness, fixed-envelope
approximate-Poisson OPE, and fixed-candidate finite-depth OPE are checked. The
following application and composition items remain **OPEN**.

1. Empirical augmented-transition composition: instantiate transition
   confidence on the 48-state behavior chain and feed its augmented-row bound
   through the checked `2 * eta` physical-row transfer.
2. Executable queue certificates: check exact rational invariant-law and
   Poisson-potential witnesses, concrete cost and Brier score atoms, and final
   numerical bounds.
3. Trace-to-theorem composition: resolve the initial-observation offset, encode
   compact trace witnesses, and separately prove any claimed good-event
   membership.
4. Final unknown-dynamics OPE: intersect the transition-confidence and OPE
   events while preserving the checked posterior and tilt simultaneity, and
   justify every candidate, depth, and other data-dependent input. The checked
   finite-depth theorem fixes the candidate, depth, certificates, and
   environment-row radius before its outer event; it does not license those
   data-dependent selections.

Until those steps close, the generic ingredients are checked but the
controlled queue's empirical unknown-dynamics OPE certificate remains open.

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
the static probability and TV transfers. Later certificate slices must provide
compact witnesses for counts, invariant laws, Poisson identities, trace/event
alignment, selected grid membership, and final arithmetic.

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
model arithmetic tests and compile the generated Lean module. Run
`make verify-controlled-queue-trace` for byte-staleness checks, the independent
full replay, and the trace-specific tests; that target does not invoke Lean.

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
`ControlledQueueTypedModel` reads the generated kernel and policy tables into
typed PMFs with exact mass identities. Neither bridge imports the frozen trace
or supplies an empirical confidence event.
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

This slice still does not check invariant laws, Poisson identities, selected
grids, final bounds, or good-event membership. Those are later model-to-theorem
and certificate slices, not preprocessing claims.

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
- the final unknown-dynamics OPE claim remains `OPEN` until empirical-event
  composition, executable certificates, trace alignment, and final arithmetic
  are checked.
