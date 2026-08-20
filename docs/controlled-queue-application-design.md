# Controlled queue application design

Status: **MODEL/PREPROCESSING ONLY IMPLEMENTED / CERTIFICATE OPEN**

Design base: FormalSLT release-candidate commit
`93c42192f8e66f2d77c35578e49dc39ff82b1324`.

This packet specifies the smallest controlled finite-state application that can
serve as a journal-grade demonstration of FormalSLT's trajectory, stationary,
unknown-kernel, and policy-comparison layers. The frozen model input, exact
rational table generator, generated Lean data module, and SHA-256 manifest are
implemented. This remains preprocessing: it is not a statistical certificate,
a theorem-produced good path, a proof bridge, or a numerical research result.

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
- Markovized behavior state: `Action × State`, for 48 states.

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

Policy tables must be supplied as exact rationals and checked for normalization,
positivity, and the advertised overlap bound.

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

The following pieces are already proved on the design base.

| Requirement | Existing module | Supported scope |
|---|---|---|
| Controlled behavior paths, overlap, bounded importance scores | `StochasticDynamics.ControlledTrajectory` | Finite controlled trajectories and exact score identities |
| Known-environment target-policy OPE | `StochasticDynamics.StationaryTargetPolicyOPE` | Supplied invariant laws and exact Poisson potentials |
| Fixed and history-dependent score comparison | `StochasticDynamics.DynamicTargetPolicyComparator` | Behavior-encountered histories |
| Finite-depth Poisson selection | `StochasticDynamics.StationaryPoissonDepthSelection` | Ordinary finite-state Markov scores |
| Empirical transition confidence | `StochasticDynamics.EmpiricalTransitionConfidence` | State-only transition rows and candidate TV budgets |
| Same-path stationary candidate selection | `StochasticDynamics.EmpiricalStationaryCatalog` | Candidate, posterior, depth, and tilt catalogs |

These modules are reusable substrate. Their existence does not by itself compose
into unknown-dynamics controlled OPE.

## Missing theorem and API work

The following items are **OPEN**.

1. Markovization bridge: identify a stationary Markov behavior policy's
   controlled trajectory with the homogeneous 48-state augmented kernel.
2. Action-conditioned confidence bridge: turn augmented behavior-kernel TV
   confidence into bounds for each physical environment row `P(z, a)`.
3. Unknown-dynamics stationary target-policy OPE. The current OPE layer
   assumes the environment, invariant laws, and Poisson solutions are supplied
   exactly.
4. Finite-depth target-policy OPE. Current adaptive depth applies to ordinary
   Markov scores, not the controlled OPE endpoint.
5. Executable rational invariant-law and Poisson-potential certificates. The
   application should check generated witnesses rather than rely on
   noncomputable existence choices.

The first implementable paper slice should therefore contain:

- known-kernel stationary OPE for fixed policy/cost atoms;
- known-kernel dynamic comparison of fixed and causal Brier predictors;
- empirical-kernel certification of the 48-state behavior chain after the
  Markovization bridge;
- no claim of unified unknown-kernel target-policy OPE until items 2--4 are
  proved.

## Frozen input and generator contract

Use one versioned JSON input with exact rational fields:

- schema and model versions;
- candidate environment kernels;
- behavior and target policy tables;
- fixed predictor tables and causal predictor specifications;
- horizon and random seed;
- confidence allocation;
- posterior, depth, and tilt grids.

A dependency-free deterministic generator must emit:

1. the controlled trace;
2. transition, action, visit, and loss count tables;
3. a generated Lean module containing exact rational witnesses;
4. a machine-readable manifest containing schema version, generator revision,
   parameters, and SHA-256 hashes for every input and output.

The generator is preprocessing only. Lean must check normalization, bounds,
counts, policy overlap, invariant laws, Poisson identities, selected grid
membership, and final arithmetic.

### Implemented preprocessing slice

The first slice freezes the model before any trajectory is sampled:

- `applications/controlled_queue/model-v1.json` fixes the 24-state encoding,
  service-before-arrival update, cyclic regime transition, candidate gammas,
  exact behavior and target policy vectors, predictor specifications, bounded
  outcomes, and future trace/catalog parameters;
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

Run `make generate-controlled-queue-model` to regenerate. After obtaining the
pinned Mathlib cache, run `make verify-controlled-queue-model` to fail on stale
artifacts, exercise the exact arithmetic tests, and compile the generated Lean
module.

This slice deliberately does **not** emit the controlled trace or empirical
count tables in items 1--2 above. It also does not check invariant laws,
Poisson identities, selected grids, final bounds, or good-event membership.
Those are later model-to-theorem and certificate slices, not preprocessing
claims.

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
- all stronger unknown-dynamics OPE claims remain `OPEN` until their bridge
  theorems are checked.
