# Open Formalization Problems

These are the next theorem targets after the current finite Rademacher, VC,
contraction, linear-predictor, and finite-chaining layers.

## Near-term

### 1. Continuous / total-bounded Dudley bridge

**Target.** Move beyond the finite dyadic scaffold by relating finite
covering-number envelopes to total boundedness and a continuous Dudley-style
entropy integral. The eventual target shape is:

`E sup_t X_t <= C * ∫ sqrt(log N(ε)) dε`.

The current code now has finite nets, nearest projections, finite
sub-Gaussian max bounds, projection-pair entropy sums, dyadic radius
schedules, per-scale entropy-budget wrappers, a uniform-entropy discrete
Dudley corollary, a finite dyadic annulus-budget bridge, total-bounded
finite-net extraction, truncated interval-integral comparisons, and a
supplied-supremum boundary adapter with an explicit terminal approximation
error. The next step is the continuous-integral layer, and it should only be
stated after choosing assumptions for measurability and separability or
keeping the supremum as an explicit supplied functional.

**Likely branch.** `feat/lean-continuous-dudley-total-bounded`.

**Dependencies.**

- `finite_dudley_entropy_sum_coveringNumbers_geometric_integral_budget`
- `finite_dudley_entropy_sum_coveringNumbers_geometric_integral_budget_prefix_envelope`
- total boundedness and finite ε-net extraction (closed for the finite bridge)
- entropy functions over positive radii
- measurability/separability assumptions for suprema

**Boundary.** Do not state an arbitrary infinite-class empirical-process
theorem until the topological and measurability assumptions are explicit.

### 2. Algorithmic stability refinements

**Target.** Extend the verified expected-gap and Azuma-constant stability
surface with sharper constants and reusable algorithm-specific interfaces.

The current repo proves bounded-differences scaffolding, a finite expected-gap
adapter under a finite coordinate-swap identity, the finite iid product-weight
specialization, a measure-theoretic iid product-measure lift under explicit
integrability assumptions, bounded-loss adapters that discharge those
integrability assumptions for finite measurable hypothesis interfaces, and
bounded-loss wrappers for the sharp high-probability stability surface.

**Dependencies for the next refinements.**

- product-measure decomposition by coordinate;
- a formal algorithm-as-map interface from samples to hypotheses;
- reusable expectation identities for replacing one coordinate.

**Remaining refinements.** Push toward sharper high-probability constants
through the product-kernel decomposition, and add algorithm-specific stability
interfaces once the theorem assumptions are clean enough to reuse.

### 3. Joint hypothesis--tilt processes and continuous-posterior extensions

**Target.** Replace finite confidence-budget allocation with a normalized
hypothesis--tilt e-process mixture, then extend the current fixed
spherical-Gaussian specialization to broader posterior families. A first
countable theorem should use declared positive tilt weights and expose the
corresponding `log (1 / weight)` cost; it should not claim unrestricted
post-sample optimization over all real tilts.

The current repo proves finite PMFs, KL divergence nonnegativity, Gibbs
inequality, Donsker-Varadhan, the finite iid product MGF bridge, the
`[0,1]` bounded-loss MGF instantiation, the finite Markov confidence event,
and a finite Catoni-style posterior-risk bad-event theorem.
It also proves a fixed-budget McAllester-style corollary: for a fixed positive
complexity budget `C`, posteriors satisfying `KL(ρ‖π)+log(1/δ) ≤ C` obey the
square-root penalty `sqrt(C/(2n))` outside a bad event of mass at most `δ`.
The finite-grid peeling theorem now removes the single fixed-budget
restriction by allocating confidence mass across finitely many complexity
buckets, and the optimized finite-grid wrapper supports posterior-dependent
penalties certified by that finite grid. The current code also includes the
closed finite good-event payoff `pac_bayes_generalization`, obtained by
complementing the Catoni bad event against total iid product mass.
For indicator losses, the weighted finite tilt catalog separately allocates
budgets `delta * w_j` across fixed Bernstein tilts and is simultaneous over
both catalog entries and finite posteriors. Its selector may depend on the
sample and posterior, but neither the catalog nor its weights may be chosen
after observing the sample.
For dependent data, `StochasticDynamics.MarkovPACBayes` now checks a fixed-tilt
(`0 < λ < 3`), all-positive-time theorem simultaneous over every posterior on
a finite predictor catalog under an actual finite Markov path law.
For continuous hypotheses, the repo now also proves a process-level theorem on
arbitrary measurable hypothesis spaces and an end-to-end i.i.d. bounded-loss
specialization for a fixed finite-dimensional spherical-Gaussian prior and
posterior, with an explicit KL formula. This does not make the result
simultaneous over all continuous posteriors.

**Dependencies.**

- add a countable or all-`λ` confidence event beyond finite grids;
- construct a normalized joint hypothesis--tilt process beyond finite union
  bounds;
- derive post-sample tilt selection only from a common checked event;
- extend beyond the fixed spherical-Gaussian posterior family while retaining
  explicit measurable-space and integrability assumptions.

**Boundary.** The finite-hypothesis grid theorem remains finite, and the Markov
posterior-uniform theorem has one fixed declared tilt satisfying `0 < λ < 3`.
The base
continuous-hypothesis i.i.d. theorem is fixed-tilt and fixed-posterior, and is
specialized to spherical Gaussians. Finite fixed catalogs of posterior/tilt
pairs support simultaneous validity and sample-dependent selection, but this is
not an all-posterior or all-`λ` confidence statement.

### PAC-Bayes empirical sample variance

**Target.** Extend the checked fixed-parameter empirical-Bernstein risk theorem
to separately weighted finite variance-tilt and risk-tilt catalogs, permitting
posterior and catalog selection after observing the sample.

The checked foundation defines the population and Bessel empirical loss
variances, proves the exact ordered-pair second-order-statistic identity,
establishes the `[0,1]` bounds `V <= 1/4` and `Vhat <= 1/2`, and discharges IID
unbiasedness under the explicit finite product sample law. The shared-pair
dependence is now handled by a random-matching argument: factor over disjoint
pairs, average over coordinate permutations, and apply finite Jensen. This
gives the source-normalized lower-tail MGF for every `n >= 2` and, after finite
change of measure, one fixed-tilt bad set of mass at most `delta`. Outside that
set, every finite posterior compares its average of per-hypothesis population
variances to the corresponding empirical average. A separate general bounded-
loss Bernstein moment supplies the population-risk event. Their finite union
has mass at most `deltaVariance + deltaRisk`, and outside it the checked final
risk theorem substitutes the observable variance certificate with all
denominators explicit.

**Dependencies.** Allocate confidence across a fixed finite weighted tilt
catalogs and prove posterior- and sample-dependent selection from those
declared families. The variance and risk catalogs should be budgeted
separately so every Cartesian pair is available without paying for every pair.
After that, consider the stronger retained-log Bennett endpoint.

**Boundary.** The current final risk theorem is finite-IID, fixed-sample, and
fixed in both tilts. It is posterior-uniform outside a two-event union, but it
does not authorize tilt-grid or all-real post-hoc optimization and is not
anytime-valid. The random-matching proof formalizes the source variance
inequality; it is not presented as a new inequality or an entropy-method proof.

## Medium-term

### 4. Downstream sharp McDiarmid propagation

**Target.** Continue extending downstream wrappers that can consume the checked
sharp McDiarmid tail.

The kernel-level sharp bounded-differences theorem is now available in
`FormalSLT/Azuma/GenGapTail.lean`:

- `ExposureMartingale.hasBoundedDifferences_tail_sharp`
- `ExposureMartingale.genGap_tail_bound_sharp_explicit`

What remains is theorem plumbing: carrying the sharper genGap tail through the
existing symmetrization, finite-class, VC, and stability wrappers without
changing their hypotheses.

**Dependencies.**

- update high-probability Rademacher wrappers;
- update finite VC sample-complexity wrappers;
- update algorithmic-stability wrappers that still cite the Azuma theorem.

### 5. Continuous Dudley-style entropy integral

**Target.** Move from finite dyadic entropy sums to a continuous entropy
integral over covering numbers.

This requires a separate topological and measure-theoretic layer: total
boundedness, finite ε-nets at arbitrary scales, monotone entropy functions,
integral approximation, and measurability/separability assumptions for
suprema over infinite classes.

**Boundary.** The finite chaining layer is the right foundation, but it does
not by itself provide continuous/infinite empirical-process theory.

## Longer-term

### 6. Generic sub-Gaussian chaining

Move from Dudley-style bounds to sharper generic chaining statements using
admissible sequences or γ₂-style functionals.

### 7. Localized Rademacher complexities

The repo now has the initial finite layer: excess-loss bookkeeping, finite
second-moment localization, finite Bernstein conditions, localized empirical
Rademacher wrappers, monotonicity under predicate inclusion, and the bridge
from excess-risk localization to second-moment localization under Bernstein.
It also has the deterministic fixed-point and localized deviation certificate
interfaces needed to state the finite fast-rate shell, plus a finite
localized upper-deviation event adapter whose membership constructs the
certificate and feeds an event-facing finite fast-rate theorem. The finite
weighted concentration adapter now controls the localized bad-event mass from
supplied pointwise tail budgets over the localized subtype, and the pointwise
Markov layer converts exponential-moment budgets into those tail budgets. The
finite iid product bridge reduces the localized pointwise exponential moments
to one-coordinate MGF budgets for the excess-loss class, and the
product-weight wrapper packages this into a localized bad-event mass bound.
The bounded-excess instantiation now closes the one-coordinate MGF budget for
pointwise `[-1,1]` excess losses and yields a finite iid product-weight
localized bad-event mass bound, including a fixed-threshold delta form.
The fixed-threshold event payoff is also closed: on the localized
upper-deviation event, empirical competitors with nonpositive empirical excess
risk have population excess risk bounded by the event threshold.
These now compose into
`localizedFiniteClassHighConfidence_empirical_nonpos_boundedExcess`, a named
fixed-threshold finite-class theorem pairing bad-event mass at most `δ` with
the deterministic good-event payoff.
The sample-dependent boundary is now explicit as well:
`localizedSampleDependentUpperDeviationEvent` and
`localizedSampleDependentUpperDeviationBadEventMass` name the random-threshold
event and its bad-event mass, while
`localizedSampleDependentHighConfidence_empirical_nonpos` records the
deterministic payoff from any supplied bad-event mass bound. The existing
fast-rate shell now also has the named event wrapper
`localizedFastRateUpperDeviationEvent`.
The conservative finite product-mass bridge is closed as well:
`localizedFastRateUpperDeviationBadEventMass_le_fixed_epsilon` reduces the
named fast-rate bad-event mass to the fixed-`ε` bad-event mass using
nonnegativity of the localized empirical Rademacher term, and
`localizedFastRateUpperDeviationBadEventMass_finiteProduct_le_delta_boundedExcess`
then composes that reduction with the existing bounded-excess finite product
bound.
The random-threshold interface now also has pointwise sample-dependent
bad-event masses, shifted exponential moments, a sample-dependent union-bound
adapter, and a summed shifted-moment bad-event bound. A conservative
shifted-moment instantiation is also closed: pointwise lower bounds on the
random threshold control the shifted moment by the fixed-threshold exponential
moment, and the named fast-rate event has a bounded-excess finite-product
shifted-moment budget through its fixed-`ε` lower envelope. These statements
also have an algebraic "centered" interface: the fixed slack factors out while
the empirical localized complexity term stays syntactically inside the shifted
moment. This interface is conservative-only — because the localized complexity
is nonnegative, each per-hypothesis centered moment is pointwise at most the
fixed moment, so the union bound over it cannot beat the conservative bound. It
exposes the next probability-theorem interface without proving that theorem.

The finite Bernstein variance-localization route is now closed locally:
`localizedFiniteClassBernsteinHighConfidence_empirical_nonpos` uses a
variance-aware Bennett/Bernstein MGF layer, an averaged Bernstein tail, the
localized variance proxy `c·r`, a finite localized union bound, and the
fixed-threshold payoff. It still assumes global `[-1,1]` excess-loss bounds and
`0 < c·r`.

**Remaining target.** The next non-conservative direction is whole-supremum
random-threshold concentration of
  `localizedUpperDeviation - 2·R̂_loc`, combining localized symmetrization
  (`expected_genGap_le_two_expected_empiricalRademacherComplexity`) with the
  McDiarmid/Azuma generalisation-gap tail (`genGap_tail_bound_azuma`). Both
  ingredients exist for the global gap but in the measure-theoretic layer; the
  open work is bridging them to the finite-weight localized layer.

### 8. Sparse regression oracle inequalities

Prove high-dimensional sparse-regression bounds under restricted-eigenvalue
or compatibility assumptions.
