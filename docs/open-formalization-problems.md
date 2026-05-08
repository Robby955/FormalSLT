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
error. The next step is the genuine continuous-integral layer, and it should
only be stated after choosing assumptions for measurability and separability
or keeping the supremum as an explicit supplied functional.

**Likely branch.** `feat/lean-continuous-dudley-total-bounded`.

**Dependencies.**

- `finite_dudley_entropy_sum_coveringNumbers_geometric_integral_budget`
- `finite_dudley_entropy_sum_coveringNumbers_geometric_integral_budget_prefix_envelope`
- total boundedness and finite ε-net extraction (closed for the finite bridge)
- entropy functions over positive radii
- measurability/separability assumptions for suprema

**Boundary.** Do not state an arbitrary infinite-class empirical-process
theorem until the topological and measurability assumptions are explicit.

### 2. Algorithmic stability expected bound

**Target.** If a learning algorithm has uniform stability `β`, prove the
expected generalization-gap bound `E[R(A(S)) - Rhat(A(S),S)] <= β`.

The current repo proves bounded-differences scaffolding, a finite expected-gap
adapter under a finite coordinate-swap identity, the finite iid product-weight
specialization, a measure-theoretic iid product-measure lift under explicit
integrability assumptions, bounded-loss adapters that discharge those
integrability assumptions for finite measurable hypothesis interfaces, and
bounded-loss wrappers for the Azuma-constant high-probability stability
surface.

**Dependencies.**

- product-measure decomposition by coordinate;
- a formal algorithm-as-map interface from samples to hypotheses;
- reusable expectation identities for replacing one coordinate.

**Remaining refinements.** Push toward sharper high-probability constants
through the product-kernel decomposition, and add algorithm-specific stability
interfaces once the theorem assumptions are clean enough to reuse.

### 3. PAC-Bayes all-real-`λ` and continuous-posterior extensions

**Target.** Extend the finite PAC-Bayes layer beyond finite λ-grids toward
all-real-`λ` optimization and, later, continuous posterior families.

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

**Dependencies.**

- add an all-`λ` confidence event beyond finite grids;
- justify optimizing `λ` posterior-by-posterior after the sample is drawn;
- state any continuous-posterior theorem with the required measurable-space
  assumptions.

**Boundary.** The repo should not claim infinite-hypothesis, continuous
posterior, or arbitrary measurable-space PAC-Bayes bounds from this finite
grid layer.

## Medium-term

### 4. Sharp McDiarmid constant

**Target.** Improve the high-probability exponent from the current Azuma
constant `8B²` to the sharp McDiarmid constant.

The current proof uses bounded increments in an exposure martingale. The
sharper route needs a product-kernel conditional expectation decomposition
that exposes the range of each coordinate replacement more directly.

**Dependencies.**

- product-measure conditional-expectation kernel;
- coordinate-wise replacement kernel;
- range-based Hoeffding lemma for martingale increments.

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

The repo now has the finite first layer: excess-loss bookkeeping, finite
second-moment localization, finite Bernstein conditions, localized empirical
Rademacher wrappers, monotonicity under predicate inclusion, and the bridge
from excess-risk localization to second-moment localization under Bernstein.
It also has the deterministic fixed-point and localized deviation certificate
interfaces needed to state the finite fast-rate shell without yet proving the
probabilistic concentration event.

**Remaining target.** Prove a high-probability finite localized concentration
theorem that constructs the localized deviation certificate, then package the
certificate shell as a finite oracle-inequality statement.

### 8. Sparse regression oracle inequalities

Prove high-dimensional sparse-regression bounds under restricted-eigenvalue
or compatibility assumptions.
