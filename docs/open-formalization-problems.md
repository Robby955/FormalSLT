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

**Target.** Extend the checked finite normalized hypothesis--tilt e-process to
a countable declared tilt mixture, then extend the current fixed
spherical-Gaussian specialization to broader posterior families. A countable
theorem should retain positive predeclared tilt weights and expose the
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
For arbitrary finite `[0,1]` losses, the fixed-sample joint mean/Bessel-variance
score now has a normalized per-hypothesis moment and a one-event finite
hypothesis--tilt master mixture. Its posterior bound uses one KL term at any
selected entry from the predeclared finite catalog. This is not a nested
e-process across sample sizes.
Separately, `PACBayes.TimeUniformTiltMixture` checks a process-level finite
hypothesis--tilt master: positive normalized priors over both finite types are
mixed into one e-process, one Ville event controls all positive times and
finite posterior PMFs, and one declared tilt atom may be selected from the path
and posterior with penalty `log (1 / (delta * weight j))`. This generic module
does not itself turn the fixed-sample Bessel score into a nested process.
`PACBayes.TimeUniformIIDTiltMixture` now supplies its finite-IID bounded-loss
adapter and one measurable exceptional event. It retains finite hypotheses,
finite predeclared tilts, full-support priors, and measurable `[0,1]` losses; it
does not establish empirical-variance or all-real control.
The separate `PACBayes.ForwardBesselPACBayes` lane starts from the actual
predictable-residual empirical-Bernstein e-process and derives a hybrid Bessel
lower envelope for its quadratic penalty. A finite hypothesis--tilt master has
one outer-mass event valid for every `n >= 2`, posterior PMF, and declared atom,
and its IID adapter derives the conditional means from measurable IID `[0,1]`
losses. The posterior and atom may be selected from the path and time, and the
atom may inspect the posterior. The boundary pays one hypothesis KL and the
selected atom's log-weight cost. The hybrid expression is not itself proved to
be an e-process.
For dependent data, `StochasticDynamics.MarkovPACBayesTiltMixture` checks an
all-positive-time theorem simultaneous over every posterior and every atom of
a predeclared full-support finite tilt prior under an actual finite Markov path
law, with `0 < λ_j < 3` for each atom. The posterior and one atom may be
selected after observing the trajectory. The selector endpoint is pointwise:
it needs no measurability or adaptedness assumption and adds no
optional-stopping guarantee beyond the common all-atom event.
For continuous hypotheses, the repo now also proves a process-level theorem on
arbitrary measurable hypothesis spaces and an end-to-end i.i.d. bounded-loss
specialization for a fixed finite-dimensional spherical-Gaussian prior and
posterior, with an explicit KL formula. This does not make the time-uniform
result simultaneous over all continuous posteriors. The separate offline
all-sample-size empirical-Bernstein endpoint is posterior-uniform on an
arbitrary measurable hypothesis space under its finite-observation and
log-likelihood-ratio assumptions.

**Dependencies.**

- add an all-`λ` confidence event beyond the checked fixed-sample
  natural-index selector for a countable tilt-pair catalog;
- extend the finite normalized hypothesis--tilt e-process to a countable
  mixture with the required summability and integrability obligations;
- derive a vanishing optimized all-time boundary from the checked forward
  hybrid-Bessel lane without treating the hybrid expression as an e-process;
- develop a localization penalty for any honest all-`λ` statement;
- extend beyond the fixed spherical-Gaussian posterior family while retaining
  explicit measurable-space and integrability assumptions.

**Boundary.** The normalized process-level tilt master remains finite and
selects one declared atom rather than an arbitrary joint posterior. Its failure
set has outer mass at most `delta`; its finite-IID adapter wraps the concrete
risk failure set in a measurable event of mass at most `delta`. The
finite-hypothesis grid theorem remains finite, and the Markov posterior-uniform
theorem likewise selects one atom from a predeclared finite prior. It is not
countable, an all-real optimizer, a predictable time-varying tilt, or an
arbitrary joint predictor--tilt posterior theorem. The base
continuous-hypothesis i.i.d. theorem is fixed-tilt and fixed-posterior, and is
specialized to spherical Gaussians. Finite fixed catalogs of posterior/tilt
pairs support simultaneous validity and sample-dependent selection, but this is
not an all-posterior or all-`λ` time-uniform confidence statement.

### PAC-Bayes empirical sample variance

**Checked.** The all-sample-size reverse-epoch theorem now extends from finite
hypotheses to an arbitrary measurable hypothesis space. A continuous-prior
mixture submartingale, posterior-uniform finite tilt catalog, closed-form epoch
endpoint, and infinite-product stitch are derived from the bounded-loss model
rather than supplied as assumptions. Separately, the forward lane checks the
predictable-residual e-process, its hybrid Bessel lower envelope, a finite
hypothesis--tilt PAC-Bayes master, and an IID bounded-loss adapter. All-real
tilt optimization remains open in both routes.

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

The one-event finite lane now also derives a closed-form bound rather than
stopping at an abstract balance or grid-coverage interface. Explicit rational
tilts indexed by the predeclared dyadic grid through `Nat.clog 2 n` give
`Rhat + (5/4) * sqrt(2 * Vhat * L / n) + (5/2) * L / n`, where
`L = KL + log((Nat.clog 2 n + 1) / delta)`. The checker combines positive KL,
positive empirical variance, an explicit positive-mass good sample, and a
final ceiling below `99/100` at `delta = 1/20`.

The all-sample-size finite lane is now checked end to end. A
leave-one-coordinate identity makes prefix Bessel variance a reverse martingale
under the exchangeable-prefix filtration. The prefix sample mean and variance
are combined into a reverse joint exponential submartingale, mixed over the
finite prior and a predeclared finite tilt grid, and controlled on every prefix
of one dyadic epoch. A finite-prefix/infinite-product bridge and telescoping
epoch weights then produce one measurable event of mass at most `delta` whose
complement controls every `n >= 2` and every finite posterior. The displayed
bound is
`Rhat_n + (5/2) * sqrt(Vhat_n * L_n / n) + 5 * L_n / n`, with
`L_n = KL + log(r(r+1)^2/delta)` and `r = Nat.log 2 n`.

**Dependencies.** The separately budgeted finite variance-tilt and risk-tilt
catalogs are checked, including posterior- and sample-dependent selection
without paying separately for every Cartesian pair. The retained Bennett factor
is also checked inside one normalized fixed-sample joint score, and one finite
master-mixture event gives the selected posterior bound with one KL term. When
the selected entry satisfies the checked coefficient balance, the retained
logarithm is absorbed and the explicit posterior-risk bound retains empirical
risk, empirical variance, and one KL-plus-catalog-weight confidence term. The
exact three-branch `xi` formula is checked as the attained maximum of the
retained residual on `[0,1/4]`, and the selected posterior-risk endpoint adds
`xi / t` on the same event. A `Nat`-indexed normalized master mixture is now
checked: it includes product-law null samples in the bad set, proves the
weighted moment series summable on every good sample, requires all catalog
weights to be strictly positive for component extraction, and controls every
entry's prior moment on one event. Its downstream layer applies the checked
finite Donsker--Varadhan and residual theorems to each selected entry, giving
raw-gap, exact-`xi` risk, and sample/posterior-dependent natural-index selector
bounds on that same event with one KL term. The posterior remains finite, the
selector receipt is structural rather than numerical, and all-real adaptation
requires a distinct argument. The continuous-hypothesis extension now proves
the joint measurability, arbitrary-prior integration, measure-theoretic
change-of-measure, and common stitched-event obligations. A concrete
product-Gaussian/fair-Boolean receipt checks posterior finite-set mass zero,
`KL = 1/32`, and a genuine zero-one loss attaining both endpoints. At
`n = 2^20` and `delta = 1/2`, its correction is below `1/2` and its
theorem-produced right-hand side is below the trivial ceiling `1`; a checked
corollary gives a path outside the exceptional event. The receipt fixes the
posterior and does not exercise data-dependent continuous-posterior selection.
Remaining evidence work is matched literature comparison and external review.

**Boundary.** The all-sample-size reverse-epoch endpoint is now uniform over
every admissible posterior probability measure on an arbitrary measurable
hypothesis space. It retains a finite-valued IID observation law, strongly
measurable `[0,1]` loss sections, a fixed probability prior, posterior absolute
continuity, and log-likelihood-ratio integrability. It uses one event shared by
every `n >= 2`, but is an offline reverse-exchangeability theorem: it does not
itself construct a forward e-process, predictable betting strategy,
optional-stopping API, continuous-observation result, or all-real post-hoc
optimizer. The separate forward result remains finite-hypothesis and
finite-tilt; its hybrid expression is only a lower envelope, its receipt has no
informative numerical width, and it has no continuous-hypothesis endpoint. The
random-matching proof formalizes the source variance inequality; neither route
is presented with a novelty or priority claim.

## Medium-term

### 4. Algorithm-specific sharp McDiarmid applications

**Checked.** The kernel-level sharp bounded-differences theorem and its
high-probability Rademacher, finite-class, VC, metric-entropy, and stability
wrappers are now available.

The kernel-level sharp bounded-differences theorem is now available in
`FormalSLT/Azuma/GenGapTail.lean`:

- `ExposureMartingale.hasBoundedDifferences_tail_sharp`
- `ExposureMartingale.genGap_tail_bound_sharp_explicit`

**Target.** Prove stability or bounded-difference constants for named learning
algorithms and feed those certificates into the checked sharp wrappers.

**Dependencies.**

- a named algorithm and explicit replacement-sensitivity proof;
- the existing sharp product-kernel theorem;
- the existing high-probability stability or learning wrapper.

### 5. General measurable-supremum Dudley theory

**Checked.** The finite-outcome endpoint
`continuous_dudley_entropy_integral` proves the continuous entropy-integral
comparison under explicit antitonicity, integrability, separable-terminal,
modulus, and boundary hypotheses.

**Target.** Construct the measurable arbitrary supremum and measure-side
chaining budget on a general probability space rather than receiving those
interfaces as hypotheses.

**Boundary.** The checked integral algebra and finite-outcome endpoints do not
by themselves provide unrestricted infinite-class empirical-process theory.

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
