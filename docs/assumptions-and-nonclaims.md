# Scope and Assumptions

This page records the assumptions behind the current theorem spine.

## Scope

### Finite hypothesis classes

Most learning-theory results are stated for an index type `ι : Type*` with
`[Fintype ι]`. This means:

- the hypothesis class has finitely many elements;
- suprema over hypotheses are finite maxima;
- the core finite-class bounds avoid measurable-supremum issues.

This covers finite function classes, finite discretizations, decision stumps
on finite grids, and other explicitly finite model families.

The main finite-class theorem spine does not cover a general uncountable
neural-network parameter space or an arbitrary infinite kernel class.

### Bounded losses

The high-probability generalization bounds require a known range bound:

```lean
∀ i z, |ℓ i z| ≤ B
```

The 0-1 classification loss satisfies this with `B = 1`. Squared loss on an
unbounded domain needs additional assumptions before these bounds apply.

### Product samples

For the main learning spine, the sample `S : Fin n → Z` is drawn from the
product measure `piMeasure μ n = μ^⊗n`. Each coordinate is independent and
identically distributed.

The sharp heterogeneous McDiarmid API separately permits coordinate laws
`μ : Fin n → Measure Z` and works over `Measure.pi μ`; the coordinates remain
independent but need not be identically distributed. Its public upper, lower,
and two-sided endpoints are checked in
[`CheckHeterogeneousMcDiarmid.lean`](../examples/CheckHeterogeneousMcDiarmid.lean).

These product-sample results do not cover time series, active learning, or
dependent data without additional assumptions. The repository's separate
online-to-PAC and anytime-valid modules state their own sequential assumptions.

### Finite prefix-dependent trajectory semantics and PAC-Bayes

`StochasticDynamics.TrajectoryRisk` constructs an Ionescu--Tulcea path law on
a finite state type from a deterministic initial state and a supplied family
of probability kernels. At step `n`, the kernel may depend on the complete
prefix indexed by `Finset.Iic n`. A supplied real-valued score may likewise
depend on that prefix and the next state, and is assumed pointwise to lie in
`[0,1]`.

Under those assumptions, the module identifies the exact prefix-conditional
expectation of the observed score. Observed score minus conditional risk is
next-step adapted, bounded in absolute value by one, conditionally centered,
and has conditional second moment at most `1/4`. The existing finite Markov
squared-loss definitions are recovered by definitional bridge lemmas.

Because the score may inspect the whole available prefix, it can encode the
prediction emitted by an online update rule fixed in advance. The theorem
requires only that this time-`n` score be determined before coordinate `n+1`
is observed. `TrajectoryRisk` itself is the semantic and
conditional-expectation layer; by itself it does not provide a confidence
event or PAC-Bayes bound.

`StochasticDynamics.TrajectoryPACBayes` lifts that semantic layer to a finite
catalog of bounded prefix-dependent scores declared before the trajectory.
The catalog may therefore contain fixed-in-advance online update rules. With a
full-support prior on the finite catalog and a full-support finite tilt prior
whose atoms satisfy `0 < lambda_j < 3`, one measurable exceptional event has
probability at most `delta`. On its complement, the bound holds simultaneously
for every positive time, every posterior PMF, and every declared tilt atom.
The posterior and one tilt atom may be selected after the trajectory.

This does not validate creating new catalog members after observing the
outcomes on which they are scored. It also does not itself provide a
controlled kernel or policy interface, action-dependent dynamics, random
initial law, continuous-state theorem, multistep forecast, optional-stopping theorem,
empirical-variance boundary, countable tilt family, or stationary long-run
conclusion. The checked target is the posterior average of the one-step
prefix-conditional risks encountered along the realized trajectory.

### Finite Markov prequential risk

`StochasticDynamics.MarkovRisk` constructs a dependent path law from an actual
finite-state transition PMF and a deterministic initial state. For fixed
functions `f q : Z -> R` valued in `[0,1]`, it derives the conditional
expectation of the next-step squared loss, proves the sharp universal `1/4`
conditional second-moment bound for the resulting centered innovation, and
applies an anytime finite tilt grid with that variance proxy.

`StochasticDynamics.MarkovPACBayes` lifts the same path-law argument to a
finite catalog of fixed predictors with a full-support prior.
`StochasticDynamics.MarkovPACBayesTiltMixture` additionally mixes over a
full-support finite tilt prior with `0 < lambda_j < 3` for every atom. One
measurable exceptional event has probability at most `delta`; on its
complement the bound holds simultaneously for every positive time, every
posterior PMF, and every declared tilt atom. The posterior and one atom may be
selected after observing the trajectory. Entry `j` has KL-confidence term
`(KL(rho || prior) + log (1 / (delta * weight j))) / (n * lambda_j)` and
sub-Gamma variance term `lambda_j / (8 * (1 - lambda_j / 3))`.

`StochasticDynamics.MarkovPACBayesTiltMixtureInitialLaw` mixes the checked
deterministic-start path laws against an arbitrary supplied finite-state PMF.
The initial PMF need not have full support. Because the raw all-time,
all-posterior, all-tilt failure set is common to every deterministic start,
the mixed law retains the same `delta` bound without a union bound or an added
confidence penalty. A point-mass initial PMF recovers the deterministic-start
path law.

The selector corollary is pointwise and imposes no measurability or adaptedness
condition on the selector. It evaluates the common all-atom event; it does not
construct a selected process or add an optional-stopping guarantee.

The checked target is the posterior average of the one-step conditional risks
encountered along the realized trajectory. The theorem does not require
stationarity, mixing, or irreducibility. It also does not cover a predictor
catalog fitted or updated on the same trajectory, non-homogeneous or
controlled kernels, continuous state spaces, multistep forecasts, stationary
long-run risk, countable or predictable tilt mixtures, an arbitrary joint
posterior on predictor--tilt pairs, empirical-variance control, or post-sample
optimization over an uncontrolled real tilt. The random-initial extension is
finite-state and Markov; it does not extend the deterministic-start
prefix-dependent trajectory theorem to random starts.

### Supplied-Poisson stationary risk

`StochasticDynamics.StationaryPoissonPACBayes` is a separate deterministic
bridge from the trajectory empirical-Bernstein event to stationary Markov
risk. Its inputs are a finite homogeneous transition PMF, a deterministic
initial state, a supplied invariant PMF, a finite catalog of `[0,1]`
transition scores, and one supplied bounded Poisson potential per hypothesis.
The declared finite tilt atoms satisfy `0 < lambda_j < 1`.

The affine Poisson correction stays in `[0,1]` under the explicit span bound.
The module proves exact conditional-risk and telescoping identities. One
outer-mass event is then simultaneous over every `n >= 2`, posterior PMF, and
declared tilt atom. For exact Poisson solutions, the residual vanishes and the
remaining endpoint correction is at most `B / n`. For approximate solutions,
the public envelope theorem retains the posterior average of the supplied
pointwise residual envelope.

The result does not construct or prove uniqueness of the invariant PMF, solve
the Poisson equation, construct a potential from the kernel, infer a span or
residual bound from contraction, establish irreducibility or mixing, learn an
unknown kernel, or cover random initial laws, controlled dynamics, continuous
states, continuous hypotheses, countable tilts, or arbitrary real-tilt
optimization. The common event is an outer-probability package; no separate
measurability theorem for that event is claimed.

### Finite-depth Poisson construction and Dobrushin contraction

`StochasticDynamics.StationaryPoissonContraction` constructs the truncated
Neumann potential `h_m = sum_{t < m} T^t (g - R)` for a known finite kernel, a
supplied invariant PMF, and a fixed depth `m`. If
the Markov expectation operator contracts finite oscillation by
`0 <= alpha < 1` and the centered row-risk oscillation is at most `D`, the
module proves the exact residual identity, the closed span bound
`D * (1 - alpha^m) / (1 - alpha)`, and the pointwise residual bound
`alpha^m * D`. Its capstone substitutes those quantities into the
supplied-Poisson empirical-Bernstein event.

`StochasticDynamics.StationaryPoissonDobrushin` defines finite total variation
as one half of the row `L1` distance, computes the maximum pairwise row total
variation, and proves that this Dobrushin coefficient contracts oscillation
without an extra factor two. The unit-range capstone therefore constructs the
potential and discharges the contraction and centered-risk envelopes directly
from the known kernel and score range.

These fixed-depth results remain finite-state, finite-hypothesis, and
finite-tilt. They do not construct or prove uniqueness of the invariant PMF,
estimate an unknown kernel, prove a mixing time or irreducibility, cover random
initial laws or controlled dynamics, or turn the outer-mass confidence package
into a separately measurable event.

### Confidence-allocated Poisson depth selection

`StochasticDynamics.StationaryPoissonDepthSelection` keeps the finite kernel,
invariant PMF, finite score catalog, contraction factor, and centered-risk
oscillation envelope fixed. It allocates depth mass
`q_m = 1 / ((m+1)(m+2))` and uses the existing countable geometric tilt
allocation within each depth. The resulting one outer event is simultaneous
over every finite depth, tilt index, time `n >= 2`, and posterior PMF. Hence a
depth, tilt, and finite posterior may depend on the realized path and reported
time by pointwise substitution into that event.

The exact boundary includes the joint cost
`log (((m+1)(m+2)(j+1)(j+2))/delta)`, the observed corrected-score
hybrid-Bessel penalty, the endpoint term `B_m / n`, and residual
`alpha^m D`. Under `0 <= alpha < 1`, the deterministic selector
`m(n) = floor(log_2 n)` together with the geometric all-time tilt has complete
width tending to zero, including the allocation, endpoint, and residual terms.

This theorem does not turn the selected boundary into an e-process or assert
that the countable depth union is a master e-process. The common event is
controlled by outer mass and is not separately proved measurable. The theorem
does not learn the kernel, construct the invariant PMF, justify selecting a
candidate-kernel Poisson catalog from the same data, or extend beyond finite
state and hypothesis spaces.

### Candidate-kernel robustness and invariant-target uniqueness

`StochasticDynamics.StationaryPoissonRobustCandidate` separates the true
finite kernel `P` from a fixed candidate kernel `Q` used to construct the
Poisson correction. It assumes a deterministic rowwise bound
`TV(P(z), Q(z)) <= eta`, `[0,1]` transition scores, a supplied invariant PMF
of `P`, and a candidate potential with span at most `B`. The checked drift
transfer is `|g_P(z) - g_Q(z)| <= (1 + B) * eta`; centering at the invariant
target therefore yields the uniform residual envelope
`oscillation(g_Q) + 2 * (1 + B) * eta`. A second endpoint uses the observed
candidate-drift maximum minus its running mean and is derived from the same
outer-mass event, not from an additional concentration claim.

The finite-depth capstone fixes a reference PMF and depth `m`, constructs the
potential from `Q`, and retains the residual price
`alpha_Q^m * D + 2 * (1 + B_m) * eta`. The hypothesis, candidate, reference
PMF, depth, and tilt catalog are all fixed before applying the theorem.

`StochasticDynamics.StationaryPoissonRobustInvariant` proves the deterministic
perturbation bound
`Dobrushin(P) <= Dobrushin(Q) + 2 * eta`. If the right-hand side is strictly
below one, the true kernel contracts finite oscillation and any two supplied
invariant PMFs of `P` are equal. Consequently the stationary risk and its
posterior average are independent of which supplied invariant witness is used.
This is an at-most-one result: it does not construct an invariant PMF or prove
that one exists.

These modules do not estimate `P`, `eta`, or the candidate kernel from data;
construct a confidence set; permit post-data candidate or depth selection;
prove invariant-law existence or a quantitative mixing time; or cover random
initial laws, controlled dynamics, continuous states, or unrestricted tilts.

### Empirical transition confidence and selected candidates

`StochasticDynamics.EmpiricalTransitionConfidence` treats each finite
source--destination transition indicator and its complement as a bounded
trajectory score. For a finite homogeneous kernel and deterministic initial
state, one outer-mass event is simultaneous over all `n >= 2`, source and
destination coordinates, and atoms of a supplied finite tilt catalog. Before
normalization, the theorem compares observed transition mass with predictable
visit-gated transition mass and remains meaningful for an unvisited row.

Normalizing to a transition-probability radius requires strictly positive
source visit mass. Summing the simultaneous coordinate radii gives a row-TV
certificate. The candidate kernel is introduced only after the common event,
so it may be selected from the observed path without another selection cost.
If every source row has positive visit mass, the maximum row certificate feeds
the deterministic Dobrushin perturbation theorem and can certify contraction
of the true kernel and uniqueness among supplied invariant PMFs.

The result is finite-state and does not provide a positive normalized radius
for an unvisited row. It does not construct an invariant PMF or prove one
exists, estimate a mixing time, cover a random initial law, or extend to
continuous states. Post-data candidate validity here is limited to the row-TV
and deterministic contraction conclusions already uniform in the candidate;
it does not justify selecting a candidate Poisson potential or stationary-risk
score from the same data without a predeclared uniform catalog, auxiliary data,
or sample splitting. The common confidence set is an outer-mass package; no
separate measurability theorem is claimed.

### Same-trajectory empirical stationary catalogs

`StochasticDynamics.EmpiricalStationaryCatalog` supplies the predeclared
uniform catalog required by the preceding nonclaim. The theorem fixes a finite
candidate type, candidate kernels, reference PMFs, nonnegative centered-risk
envelopes, full-support candidate weights, and a finite score prior before the
trajectory is observed. Every candidate must have finite Dobrushin coefficient
strictly below one. Candidate `c` and depth `m` receive risk-event mass
`deltaRisk * candidateWeight c / ((m+1)(m+2))`; the existing countable
geometric allocation then covers every risk-tilt index, time `n >= 2`, and
finite-class posterior within that atom.

The risk-catalog event and the finite transition-coordinate event are
intersected on the same path, with complement outer mass bounded by
`deltaRisk + deltaTransition`. No independence or sample split is assumed.
When all source visit masses are positive, the candidate, depth, risk tilt,
finite transition tilt, and posterior may depend on the path and time by
pointwise substitution into the common event. The selected row-TV radius feeds
the boundary

`(1 + 2 B_m) * hybridBesselKL + B_m / n + alpha_c^m D_c + 2 (1 + B_m) eta`,

where the first term contains the candidate--depth--tilt allocation cost. The
same conclusion returns the candidate perturbation bound for the true
Dobrushin coefficient, an oscillation-contraction certificate, and uniqueness
conditional on the selected strict inequality
`Dobrushin(Q_c) + 2 eta < 1`.

`StochasticDynamics.FiniteInvariantExistence` proves that every kernel on a
nonempty finite state space has an invariant PMF. The proof takes Cesaro
averages in the real probability simplex, extracts a convergent subsequence by
compactness, and converts the fixed point back to a PMF.
`finiteInvariantPMF P` is a noncomputable `Classical.choose` witness, not a
closed-form or executable stationary solver. The canonical catalog corollary
targets this chosen invariant PMF without a caller-supplied existence premise.
`StochasticDynamics.FiniteInvariantUniqueness` combines existence with either
a strict true-kernel Dobrushin coefficient or a strict candidate row-TV
certificate to prove `ExistsUnique`.

The catalog does not authorize kernels, reference PMFs, or score/potential
entries invented after their scored trajectory has been observed; selection
is only among the finite declarations already controlled by the common risk
event. The normalized transition component remains unavailable for unvisited
rows. The theorem has a deterministic initial state, finite state and
hypothesis spaces, finite candidates and transition tilts, and the fixed
countable geometric risk-tilt family. It does not prove a measurable version
of the common outer-mass event or that the selected boundary is an e-process.
Finite invariant existence does not imply irreducibility, uniqueness without a
strict certificate, convergence of arbitrary initial laws, a convergence
rate, or a mixing time.
### Controlled trajectory semantics

`StochasticDynamics.ControlledTrajectory` supplies a separate finite
state--action behavior-law interface. The behavior and each target policy may
inspect the complete available decision--outcome prefix. Under explicit
overlap and a common importance-ratio cap, a predeclared finite catalog of
bounded transition scores is normalized into `[0,1]`. The module proves the
exact behavior-law conditional mean of that one-step importance score and
discharges the `IncrementAdapted`, `StronglyAdapted`, and conditional-
expectation premises consumed by the forward predictable-mean PAC-Bayes layer.

The state, action, and policy-catalog types are finite; the initial
decision--state pair is deterministic; and the controlled environment is a
supplied homogeneous state--action kernel. This is not a target-trajectory
change-of-measure theorem, a target-versus-behavior occupancy correction, a
stationary target-policy value theorem, a full-trajectory importance-sampling
result, or a guarantee for learned propensities or an unknown environment.

### Stationary target-policy off-policy evaluation

`StochasticDynamics.StationaryTargetPolicyOPE` specializes the controlled
interface to a finite catalog of state-Markov target policies. The environment
kernel and history-dependent behavior propensities are known. Each target
policy has a supplied invariant state PMF and supplied exact bounded Poisson
potential. Explicit overlap, a common positive action-ratio cap, bounded
transition scores, a full-support finite hypothesis prior, and a full-support
finite tilt prior with atoms in `(0,1)` are theorem assumptions.

Under those assumptions, one behavior-law outer event is simultaneous over
every `n >= 2`, posterior PMF, and declared tilt atom. The theorem controls the
posterior stationary target-policy risk using the normalized one-step
importance-weighted, Poisson-corrected observed scores and their checked hybrid
Bessel penalty. Pointwise posterior and tilt substitution uses the already
simultaneous event; it does not construct a selected process.

The theorem does not estimate the environment or behavior policy, construct
or estimate invariant PMFs or Poisson potentials, handle history-dependent
target policies, correct target-law occupancy through a full-trajectory
likelihood ratio, or establish doubly robust, continuous-space, or
unknown-kernel OPE.

### Dynamic target-policy comparators

`StochasticDynamics.DynamicTargetPolicyComparator` accepts finite catalogs of
history-dependent target policies and bounded full-prefix transition scores
under a known homogeneous controlled environment and history-dependent
behavior policy. `StochasticDynamics.PrefixDynamicTargetPolicyComparator`
replaces the homogeneous environment with a supplied kernel that may depend on
time and the complete available prefix. Both the behavior and target policies
may inspect that prefix.

The assumptions are explicit overlap, a common positive action-ratio cap, a
full-support finite hypothesis prior, and a full-support finite tilt prior with
atoms in `(0,1)`. One behavior-law outer event is simultaneous over every
`n >= 2`, posterior PMF, and declared tilt atom. Pointwise posterior and tilt
substitution is valid only because those choices are made inside the already
simultaneous conclusion; no selected process is constructed.

The controlled target is the posterior average of target one-step conditional
risks at prefixes encountered under the behavior law. These theorems do not
identify target-policy occupancy or value, construct a full-trajectory
likelihood ratio, estimate the environment or propensities, supply a doubly
robust or learned-nuisance guarantee, or cover continuous state or action
spaces.

### Finite-horizon target-path change of measure

`StochasticDynamics.TargetPathChangeOfMeasure` constructs the recursive
finite-prefix target-policy expectation and proves that it agrees with the
corresponding finite marginal of the actual infinite target trajectory law.
Under policy overlap, every finite-prefix target expectation equals the
behavior-path expectation weighted by the cumulative product of one-step
target-to-behavior action likelihood ratios. Checked corollaries cover
measurable prefix cylinders, finite-horizon payoff risk, terminal-state
occupancy, and normalization of the likelihood ratio.

State and action types are finite; the initial decision--state pair is
deterministic; the prefix/time-dependent environment and both policies are
supplied; and the horizon is fixed. A supplied one-step ratio cap `C` yields
the explicit bound `W_n <= C ^ n`. The module proves no anytime concentration
or PAC-Bayes result for these cumulative weights, no vanishing target-value
boundary, no learned propensity or environment guarantee, and no
continuous-space change-of-measure theorem.
### Finite adaptive-selection cost guardrail

`AnytimeValid.SelectionCost` works with arbitrary finite observations and
finite score catalogs. If every score is nonnegative with expectation at most
one and the nonnegative predeclared weights sum to at most one, multiplying an
observation-selected score by its declared weight preserves expectation at
most one. Equivalent simultaneous upper-tail statements expose the reciprocal
weight or Kraft correction.

The diagonal-spike family gives an exact finite adversarial witness. Each
coordinate has expectation one, the uncorrected selected expectation is the
catalog cardinality, and a common positive correction is safe on this witness
if and only if it is at least that cardinality. This proves the corresponding
`log |I|` lower bound for the symmetric correction on the checked witness.

These are finite Markov/union/Kraft facts, not a new concentration theorem or
a universal minimax result for every structured sequential tilt family. They
do not establish countable or continuous selection costs, an LIL lower bound,
or optimality of the constants in the repository's coupled PAC-Bayes process
families.

### Countable-allocation log-log guardrail

`AnytimeValid.AllocationLogLog` assumes a nonnegative summable sequence of
predeclared confidence weights with total mass at most one. Every inclusive
integer block `[N, 2N]` then contains an atom of weight at most
`1 / (N + 1)`. If all weights are positive, the corresponding logarithmic
price is at least `log (N + 1)` somewhere in every block. At geometric times
`4^(k+1)`, this yields an explicit iterated-logarithm price along an unbounded
subsequence. The polynomial weights `1 / ((k+1)(k+2))` supply an exact
telescoping receipt with total mass one.

This result is specific to countable confidence allocation and union-bound
stitching. It does not prove a minimax lower bound over all confidence
sequences, a law of the iterated logarithm, or optimality of a structured
mixture boundary.

### Universal fair-sign anytime-boundary lower bound

`AnytimeValid.UniversalBoundaryLowerBound` uses the infinite fair-Rademacher
product law and deterministic one-sided boundaries. Its unconditional route
combines the one-dimensional CLT, Portmanteau, disjoint rapidly growing
coordinate blocks, and the second Borel--Cantelli lemma. If the probability of
ever crossing a boundary is strictly below one, the boundary exceeds every
fixed nonnegative multiple of `sqrt n` infinitely often. At a fixed constant
whose standard-Gaussian upper tail exceeds the crossing budget, the boundary
is eventually at least that constant times `sqrt n`.

The sharp iterated-logarithm endpoint is conditional. The proposition
`FairSignUpperLIL` names the missing almost-sure upper-LIL crossing theorem;
`fairSign_anytimeBoundary_limsup_ge_one_of_upperLIL` derives the constant-one
boundary conclusion only after receiving that proposition and a boundedness
side condition. The library does not prove `FairSignUpperLIL`, a general
process-level LIL, randomized or data-dependent boundary lower bounds, or a
two-sided minimax theorem.

### Azuma and sharp McDiarmid constants

The high-probability Rademacher bounds use
`P(genGap ≥ threshold + ε) ≤ exp(-ε² * n / (2 * B²))`.

The sharp genGap-tail layer is now checked separately as
`ExposureMartingale.genGap_tail_bound_sharp_explicit`, with exponent
`exp(-ε² * n / (2 * B²))`. The Rademacher, VC, and stability wrappers now cite
the sharp tail where their high-probability statements expose the concentration
exponent.

### Effective-class growth assumptions

The VC-style theorems assume a user-supplied finite-sample growth bound on the
effective loss patterns:

```lean
hGrowth_uniform : ∀ z : Fin n → Z,
  (effectiveClass ℓ z).card ≤ ∑ k ∈ Finset.range (d + 1), n.choose k
```

For binary classifiers with 0-1 loss, the repo proves the bridge from binary
traces to effective loss patterns. For arbitrary real-valued loss classes, a
generic VC bridge is not yet part of the library.

### Finite chaining

`Covering.FiniteSubGaussianChaining` is finite infrastructure:

- finite index class;
- finite outcome support;
- scalar real-valued process;
- finite nets and nearest-net projections;
- finite multiscale chains;
- finite entropy sums and entropy-budget wrappers.

It is finite infrastructure for Dudley-style arguments. It is not the
continuous Dudley entropy integral.

### Unit-interval Dudley example

`Covering.UnitIntervalDudley` instantiates the total-bounded finite-net bridge
on the non-finite metric index space `[0,1]`. It constructs explicit half and
quarter meshes, packages the Rademacher process
`X(b,t) = signOfBool b * t`, and routes a nonzero supplied supremum through a
projected finite-net Dudley bound with a concrete `sqrt (log 15)` entropy
envelope.

This example still uses the supplied-supremum interface. It does not construct
arbitrary measurable suprema, prove a general separability theorem, or state
the full continuous Dudley entropy integral.

### Conditional sub-Gamma extraction

`Concentration.SubGamma.Extractor` proves a conditional MGF bound for a
single bounded real increment. The headline theorem
`condSubGammaMGF_of_bounded_centered_condVariance` assumes:

- an a.s. bound `|X| ≤ b`;
- conditional centering `μ[X | m] = 0`;
- a conditional second-moment proxy `μ[X² | m] ≤ σ²`;
- the parameter regime `0 ≤ λ` and `b * λ < 3`.

The theorem converts those assumptions into a conditional sub-Gamma MGF bound.
It does not by itself construct a filtration, prove independence, or state a
full sequential concentration inequality.

## Open Work

### VC-to-PAC equivalence

The repo proves upper-bound components for the finite VC/Rademacher route. It
does not prove the full equivalence between finite VC dimension and
PAC-learnability.

### Infinite classes

The main Rademacher and VC statements are finite-index theorems. Moving to
general infinite classes requires covering-number APIs, measurable suprema,
separability assumptions, and approximation arguments that are outside the
current theorem spine.

The unit-interval Dudley example is the current concrete bridge beyond a
finite ambient index type. It verifies finite-net machinery on `[0,1]`, but it
does not remove the remaining measurable-supremum and separability obligations
for arbitrary non-finite classes.

### Downstream sharp-tail propagation

The product-measure sharp McDiarmid theorem is checked, and the main
Rademacher, VC, and stability high-probability wrappers now consume the sharp
tail. The current non-claim is that every possible concentration theorem in
the repository has been audited for sharp constants.

### Neural-network generalization

The repo does not prove generalization bounds for neural networks. Such
statements would require additional structure, such as PAC-Bayes, compression,
margin, stability, or norm-controlled function-class arguments.

### PAC-Bayes sample bounds

`PACBayesKL` proves finite KL divergence facts, Gibbs inequality, and the
Donsker-Varadhan variational inequality. `PACBayesFiniteProductMGF` proves the
finite iid product factorization and prior-averaged MGF bridge.
`PACBayesBoundedLoss` instantiates the `[0,1]` bounded-loss one-coordinate MGF,
adds the finite Markov confidence event, and proves a finite Catoni-style
posterior-risk bad-event bound plus a fixed-budget McAllester-style
square-root corollary. It also proves a finite-grid peeling wrapper that
allocates confidence mass across finitely many complexity buckets and supports
posterior-dependent penalties certified by that finite grid. The closed
`pac_bayes_generalization` theorem complements the Catoni bad event against
total iid product mass to state the finite high-confidence good event directly.
`PACBayesBernstein` adds a finite Bernstein margin-proxy shell: the variance
proxy is supplied per hypothesis, and the theorem consumes a normalized
Bernstein prior-moment certificate. The finite indicator specialization derives
the exact Bernoulli proxy `R_i(1 - R_i)/n`; its observable low-risk corollary
uses `R_i(1 - R_i) <= R_i` and therefore has empirical risk, but not empirical
sample variance, on its right-hand side. Its finite weighted tilt catalog
allocates entry `j` the budget `delta * w_j` and is simultaneous over every
catalog entry and finite posterior, so a selector may depend on both the
sample and posterior. The finite catalog and positive weights satisfying
`∑ j, w_j ≤ 1` must be declared in advance; this is not unrestricted
optimization over real `λ`.

`PACBayes.TimeUniformTiltMixture` is a separate generic process-level layer.
It assumes finite nonempty hypothesis and tilt types, full-support normalized
priors on both, adapted centered bounded increments with a common conditional
second-moment proxy, and predeclared tilts satisfying `0 < lambda_j` and
`b * lambda_j < 3`. The finite outer mixture is one e-process, so one Ville
crossing controls every positive time, posterior PMF, and declared tilt atom.
The selected boundary contains one hypothesis-posterior KL term and
`log (1 / (delta * weight j))`; there is no second tilt KL or finite union
bound. The selector chooses one atom after observing the path and posterior.
`PACBayes.TimeUniformIIDTiltMixture` separately discharges these process
assumptions for finite-class measurable IID `[0,1]` losses. It assumes
measurable IID coordinates with a common probability law, full-support finite
hypothesis and tilt priors, positive declared tilts below three, and positive
`delta`. It provides one measurable exceptional event and the same
path/posterior-dependent selected-atom endpoint. Neither module provides a
countable or all-real mixture, an arbitrary joint hypothesis--tilt posterior,
or an exact-Bessel empirical-Bernstein process.

`AnytimeValid.ForwardBesselProcess` supplies a distinct forward
empirical-Bernstein route. Under `[0,1]` increments with a fixed conditional
mean, its stochastic object is the known predictable-residual e-process. The
module proves two deterministic Bessel upper envelopes for the accumulated
predictable squared residuals and uses their pointwise minimum.
`PACBayes.ForwardBesselPACBayes` mixes those actual processes over finite
full-support hypothesis and tilt priors, with `0 < lambda_j < 1`. One atTop
crossing event has outer mass at most `delta`; outside it, every `n >= 2`,
posterior PMF, and declared atom obeys the bound. The posterior and selected
atom may depend on the path and time, and the atom may additionally inspect the
posterior. The boundary has one hypothesis KL term,
`log (1 / (delta * weight j))`, and the posterior average of the
per-hypothesis hybrid Bessel penalties. The minimum is taken before posterior
averaging.

`PACBayes.ForwardBesselPACBayesIID` derives adaptedness, integrability, and the
conditional-mean identity from strongly measurable IID `[0,1]` losses. The
separate `PACBayes.ContinuousForwardPredictableMeanBesselPACBayes` engine
integrates the actual parameterized processes over an arbitrary measurable
hypothesis space. It requires a fixed probability prior, a finite positive
normalized tilt prior with `0 < lambda_j < 1`, explicit filtered and ambient
product-measurability interfaces, and the usual posterior absolute-continuity
and log-likelihood-ratio integrability conditions. Its single outer event is
uniform over every eligible posterior measure and every declared tilt atom.

`StochasticDynamics.ContinuousTrajectoryEmpiricalBernsteinPACBayes` derives
those process-measurability interfaces for finite-state, deterministic-start,
full-prefix trajectories from coordinatewise strong measurability of the
bounded score in the hypothesis parameter. The separate
`StochasticDynamics.ContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes`
adapter permits arbitrary measurable state and hypothesis spaces. It derives
the same process interfaces from one supplied `[0,1]` score contract jointly
strongly measurable in the hypothesis, complete prefix, and next state, under
full-prefix Markov kernels and a deterministic initial state.

These trajectory endpoints control posterior-average encountered one-step
conditional risk, not stationary or long-run risk. They do not construct a
measurable posterior selector or selected process, provide a random initial
law, estimate an unknown kernel, or validate a score family fitted after its
scored outcomes are observed. The `Real` checker uses a two-atom Rademacher
transition law to prove positive conditional variance; it is not an atomless
dynamics receipt and does not evaluate or compare the PAC-Bayes boundary.

The hybrid Bessel expression is a lower envelope of the actual e-process, not
itself a proved e-process. The basic arbitrary-state `Real` checker remains a
structural receipt: its two-atom Rademacher transition law proves positive
conditional variance without evaluating the PAC-Bayes boundary. The separate
Gaussian/fair-Boolean trajectory receipt has state space `Real`, hypothesis
space `(Fin 1 -> Real) x Bool`, posterior finite-set mass zero, `KL = 1/32`,
positive observed Bessel variance on a theorem-produced good path in each of
two mass-`1/4` sign-flip branches, and, at `n = 64`, `delta = 1/8`, and
`lambda = 1/2`, boundary `<= 489/1024 < 1/2` with complete right-hand side
below one. That receipt fixes the posterior and tilt, and its real-state
transition law has only two atoms. It is not an atomless-dynamics receipt, a
selected-process result, or a matched comparison against another boundary.
The finite-hypothesis IID receipts remain separate.
The separate finite-IID informative biased-Boolean receipt has Bessel variance
`1/32`, `KL = log 2`, a theorem-produced good path with risk below `343/1000`,
and a same-prefix
boundary comparison of approximately `0.312` versus `0.760`. There is no
countable or all-real tilt optimizer, vanishing optimized all-time boundary,
or novelty/priority claim.

`PACBayes.FiniteEmpiricalVariance` supplies the finite empirical-variance
foundation for arbitrary real-valued per-hypothesis losses: population
variance, Bessel-corrected empirical variance, its exact ordered-pair
representation, and finite-IID unbiasedness for sample size at least two. The
universal population bound `1/4`, empirical bound `1/2`, and empirical-risk
self-bound additionally assume losses in `[0,1]`.

`PACBayes.FiniteEmpiricalVarianceMatching` and
`PACBayes.FiniteEmpiricalVarianceMGF` turn that foundation into the
source-normalized lower-tail exponential moment for finite IID samples and
`n >= 2`. The proof averages disjoint-pair factorizations over coordinate
permutations and applies finite Jensen. It is a random-matching proof, not an
entropy-method proof, and no new statistical inequality is claimed.

`PACBayes.FiniteBoundedLossExponentialTilt` specializes finite exponential
tilting to the lower-tail score `-t * ell i z`, proves the exact coordinate and
product change-of-measure identities, and transports population variance via
`exp (-t) * V_p <= V_{q_t}` without assuming full support. Building on it,
`PACBayes.FiniteJointMeanVarianceMGF` combines the lower-tail mean score and
Bessel empirical-variance score into one fixed-sample per-hypothesis
exponential moment. It assumes finite data, `[0,1]` losses, `n >= 2`,
nonnegative tilts, and a nonnegative linear-minus-quadratic variance
coefficient. The module does not yet mix over a prior, invoke a variational
inequality, define a confidence event, support post-data tilt selection, or
construct a time-uniform process.

`PACBayes.FiniteJointMeanVariancePACBayes` lifts the joint moment through a
finite prior mixture and a finite weighted catalog of joint pairs
`c ↦ (t c, eta c)`. One master mixture statistic is thresholded at
`1 / delta`, giving one bad-sample set of product mass at most `delta`; on
its complement a per-entry Donsker-Varadhan step yields a retained-variance
inequality with one KL term for every posterior and every entry, so the entry
may be selected after seeing the sample and the posterior. The mass theorem
assumes finite data, hypothesis, and catalog types, an iid finite product PMF,
`n >= 2`, `[0,1]` losses, nonnegative tilts with nonnegative variance
coefficients, nonnegative weights of total at most one, and `0 < delta`. The
entrywise posterior bounds require every catalog weight to be strictly
positive, while the variational side additionally assumes a full-support
prior. There is one shared
confidence event and one KL term per selected bound, not one syntactic
variational invocation across entries. The population-variance log term is
stated at the posterior-averaged variance via concavity of the logarithm, and
both variance quantities are posterior averages of per-hypothesis variances.
The fixed-time normalized score is not an e-process, and no time-uniform, countable-catalog,
or all-real optimization claim is made; broader time-uniform
empirical-Bernstein PAC-Bayes results already exist in the literature (Jang,
Jun, Kuzborskij, and Orabona, COLT 2023; Chugg, Wang, and Ramdas, JMLR 2023).

`PACBayes.FiniteEmpiricalBernsteinSqrt` derives a direct closed-form endpoint
from the one-event joint score rather than assuming the balance condition or
an optimizer certificate at its public boundary. It maps each declared scale
`0 < s <= 2` to explicit mean and variance tilts, proves the balance condition,
and fixes the finite dyadic catalog `s_j = 2 / 2^j` through
`j = Nat.clog 2 n` before observing the sample. For `0 < delta < 1`, the final
event has product-law mass at most `delta` and the risk bound is simultaneous
over every finite posterior. The finite hypothesis catalog and full-support
prior are fixed before the sample. Its complexity is
`L = KL(rho || prior) + log((Nat.clog 2 n + 1) / delta)` and its displayed
penalty is `(5/4) * sqrt(2 * Vhat * L / n) + (5/2) * L / n`.
Here `Vhat` is the posterior average of each hypothesis's Bessel empirical
variance, not the empirical variance of the posterior-averaged loss. The
result is finite IID and fixed-sample. It is not an all-real optimizer, a
countable-catalog selector, or by itself an all-sample-size theorem.

`PACBayes.FiniteEmpiricalVarianceReverse` proves the leave-one-coordinate
identity that makes prefix Bessel variance a reverse martingale under the
exchangeable-prefix filtration. The downstream reverse modules combine this
with the prefix sample-mean martingale, exponentiate the joint score, apply the
finite maximal inequality, mix over the finite prior and a predeclared finite
tilt catalog, and recover the reverse closed-form empirical-Bernstein bound on
one dyadic epoch. These are proved probability arguments; the public endpoint
does not assume a reverse MGF, maximal bound, posterior event, or grid-coverage
certificate.

`PACBayes.InfiniteEmpiricalBernsteinStitch` pulls every finite reverse-epoch
event onto the infinite IID product space and allocates confidence with the
telescoping weights `1 / ((q+1)(q+2))`. For finite data and hypothesis types,
a fixed full-support prior, measurable-singleton data, `[0,1]` losses, and
`0 < delta < 1`, `exists_infiniteEmpiricalBernstein_event` produces one
measurable exceptional event of mass at most `delta`. Outside it, every
`n >= 2` and every posterior PMF satisfy
`Rrho < Rhatrho,n + (5/2) sqrt(Vhatrho,n Lrho,n / n) + 5 Lrho,n / n`,
where `Lrho,n = KL(rho || prior) + log(r(r+1)^2/delta)` and
`r = Nat.log 2 n`. Because the event is pointwise uniform over all posteriors,
a path-dependent posterior can be substituted without another union bound.
The result remains finite-hypothesis and finite-outcome. It is an offline
reverse-epoch stitch, not a forward e-process, predictable betting strategy,
optional-stopping theorem, all-real tilt optimizer, or continuous-hypothesis
PAC-Bayes theorem. Its checker supplies an explicit all-`n` event and
path-selected posterior. The deterministic flagship comparison evaluates the
stitched boundary on the balanced-Bernoulli statistics and finds its exact
epoch form below one from even `n = 128`; this is floating-point evidence about
the constants, not a proof that a particular infinite path is outside the
exceptional event. The separate balanced-64 fixed-sample receipt remains the
Lean-checked positive-mass numerical witness.

`PACBayes.ContinuousJointMeanVarianceReversePACBayes` replaces the finite prior
sum in the reverse-epoch argument by integration over an arbitrary measurable
hypothesis space. It derives the prior-mixture submartingale, endpoint moment,
and bounded-loss integrability obligations from the fixed-hypothesis reverse
process and explicit Fubini arguments; it does not assume the integrated MGF or
posterior confidence event. `ContinuousJointMeanVarianceReverseCatalog` and
`ContinuousEmpiricalBernsteinReverseSqrt` add the same predeclared finite
dyadic tilt catalog and closed-form epoch endpoint for posterior probability
measures.

`PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch` then gives the
all-sample-size endpoint over arbitrary measurable hypotheses. It assumes a
finite observation type with measurable singletons, a finite-valued IID PMF,
a probability prior fixed before the data, strongly measurable `[0,1]` loss
sections in the hypothesis parameter, and `0 < delta < 1`. Its one measurable
exceptional event depends on the law, prior, and loss but not on the posterior.
Outside it, every `n >= 2` and every posterior probability measure absolutely
continuous with respect to the prior with an integrable log-likelihood ratio
satisfy the same `5/2` square-root plus `5` linear bound with one
measure-theoretic KL term. The variance is the posterior integral of each
hypothesis's Bessel empirical variance, not the empirical variance of a
posterior-averaged loss. Pointwise uniformity permits substitution of an
admissible path-dependent posterior, but does not prove that such a selector is
measurable or adapted. The Gaussian receipt uses `Theta = (Fin 1 -> Real) x
Bool`, an `N(0,1)` product fair-Boolean prior, and a fixed `N(1/4,1)` product
fair-Boolean posterior. It proves posterior finite-set mass zero, checks `KL =
1/32`, and uses an unscaled zero-one sign-flip mismatch loss that depends on
both coordinates and attains both endpoints. Every nonempty-sample posterior
empirical risk is `1/2`; at `n = 2^20` and `delta = 1/2`, the correction is
below `1/2` and the theorem-produced right-hand side is below the trivial
ceiling `1`. A checked corollary also proves that a path exists outside the
exceptional event. This receipt fixes the posterior and does not exercise
data-dependent continuous-posterior selection.
The theorem still has finite-valued observations and is an offline reverse-
epoch result, not a forward e-process, optional-stopping theorem, all-real tilt
optimizer, or continuous-observation theorem.

`PACBayes.CountableJointMeanVariancePACBayes` extends only the fixed-sample
master-event layer to a predeclared `Nat`-indexed catalog. Its nonnegative
weights are summable with total `tsum` at most one. Because a nonsummable real
series has `tsum = 0`, the bad set explicitly includes every product-law null
sample; these samples cost zero mass, while positive-mass samples admit the
summability proof needed for component extraction. Its mass theorem requires
`0 < delta`, nonnegative summable weights, and `tsum w <= 1`; it gives one
event and a prior-moment bound for every positive-weight entry.

The downstream `PACBayes.CountableJointMeanVariancePosterior` layer reduces
each selected entry to a singleton finite catalog and applies the already
checked finite Donsker--Varadhan and residual theorems. Conditional on a sample
outside that same event, it gives raw-gap, exact-`xi` risk, and sample/posterior-
dependent natural-index selector bounds with one KL term. These endpoints
assume a full-support prior and a posterior PMF on the finite hypothesis type,
strictly positive summable weights, and positive selected tilts. The receipt is
structural and existential in the good sample; it does not evaluate a selected
numerical bound below one. This is not a posterior on a countable hypothesis
space, all-real optimization, or an e-process.

`PACBayes.FiniteEmpiricalVariancePACBayes` lifts the normalized moment to one
fixed-sample, fixed-tilt exceptional set of finite-product mass at most
`delta`. The mass theorem assumes finite data and hypothesis types, a
full-support finite prior, `[0,1]` losses, `n >= 2`, one declared positive
tilt `eta`, and `0 < delta`. Outside that one set, the confidence statement
holds for every posterior on the finite hypothesis type, including a posterior
selected after seeing the sample. It
controls the posterior average computed after taking each hypothesis's
population or empirical variance; it is not the variance of a
posterior-averaged loss. The rearranged bound additionally requires
`eta * n < 2 * (n - 1)` so its denominator is positive.

`PACBayes.FiniteEmpiricalVarianceTiltCatalog` allocates a single variance
failure budget across a finite, predeclared `eta` catalog using positive
weights whose sum is at most one. Its shared event is simultaneous over every
catalog entry and every posterior on the finite hypothesis type, so the entry
may be selected from the observed sample and posterior. The concrete receipt
uses unequal weights and distinct tilts, exercises two posterior-dependent
selector branches on positive-mass samples, and proves both resulting
certificates below `1/4`.
This is still fixed-sample finite-catalog adaptation, not all-real or
time-uniform optimization.

`PACBayes.FiniteBoundedLossBernstein` proves the complementary one-sided
population-risk Bernstein event for arbitrary finite `[0,1]` losses. Its fixed
tilt satisfies `0 < lambda < 3n`, and its variance term is the posterior
average of the per-hypothesis population variances. It is not the variance of
the posterior-averaged loss.

`PACBayes.FiniteEmpiricalBernsteinRisk` unions that event with the empirical-
variance event. The combined bad mass is at most
`deltaVariance + deltaRisk`; the two arguments use the same sample but do not
assume independence. Outside the union, the final observable risk inequality
holds simultaneously for every finite posterior. Both tilts and both failure
budgets must be declared before observing the sample.

`PACBayes.FiniteEmpiricalBernsteinRiskCatalog` separately allocates the two
failure budgets across finite, predeclared `eta` and `lambda` catalogs using
positive weights whose sums are at most one. Its combined event still costs
only `deltaVariance + deltaRisk`, rather than one budget for every Cartesian
pair. Outside that event, both catalog entries may be selected after observing
the sample and posterior. The receipt separately proves that the two selectors
are nonconstant on concrete positive-mass samples; its existential good-sample
certificate does not identify which branches occur outside the bad set. Its
variance half is the standalone variance catalog,
and its risk half uses the same reusable plain-sum union-bound lemma. The
catalogs, weights, and selector rules are fixed in advance; this is not
optimization over all real tilts.

The repository now has an
arbitrary-measurable-hypothesis process-level PAC-Bayes theorem and an
end-to-end i.i.d. bounded-loss specialization for finite-dimensional spherical
Gaussian priors and posteriors. The latter derives the increment and
mixture-process obligations from a jointly measurable `[0,1]` loss and an
i.i.d. sample stream, displays the checked Gaussian KL closed form, and has a
fair-Bernoulli worked instance whose failure event contains an explicit
cylinder of probability `2⁻¹⁰⁰`. This positive lower bound is a non-vacuity
witness, not a tightness claim. A finite-catalog wrapper additionally supports
sample-dependent selection among finitely many fixed spherical-Gaussian
posterior/tilt pairs by summing their entrywise confidence budgets. It does not
give uniformity over every Gaussian posterior or every real-valued tilt. That
time-uniform i.i.d. learning theorem does not provide uniformity over arbitrary
continuous posterior families or all real-valued tilts on an unrestricted
measurable hypothesis space. The separate offline empirical-Bernstein theorem
covers an arbitrary measurable hypothesis space for one probability prior
fixed before the data and posterior probability measures absolutely continuous
with respect to that prior with an integrable log-likelihood ratio, under finite
measurable-singleton observations and strongly measurable `[0,1]` loss
sections.

The separate-event empirical-Bernstein risk result does not yet use the
fixed-sample joint moment; the one-event joint catalog is a distinct endpoint
and does not replace it. The zero-residual coefficient branch of the one-event
catalog now removes the unknown population variance and gives the explicit
empirical-Bernstein posterior-risk bound. The remaining branches are checked by
the exact attained piecewise `xi` maximum on `[0,1/4]` and add `xi / t` to that
same one-event bound. The countable master-event and finite-posterior layer
described above lift these endpoints to a predeclared `Nat`-indexed tilt-pair
catalog. A separate reverse-exchangeability construction now supplies one
all-sample-size finite-observation IID Bessel-variance event with a closed-form
risk bound, including uniformity over admissible posterior measures on an
arbitrary measurable hypothesis space. The separate forward construction now
supplies an actual predictable-residual e-process, a hybrid Bessel
lower-envelope conversion, a finite-hypothesis/finite-tilt PAC-Bayes master
with an IID adapter, and a continuous-prior master over arbitrary measurable
hypotheses with an arbitrary-measurable-state full-prefix trajectory adapter.
It does not make
the hybrid expression itself an e-process, provide a vanishing optimized
all-time boundary, supply a random initial law, or construct a measurable
posterior selector or selected process. Its arbitrary-state extension requires
a supplied jointly measurable score family. The separate finite-IID
informative biased-Boolean receipt has positive Bessel variance, nonzero KL, a
theorem-produced good path, and the checked same-prefix boundary comparison.
The separate Gaussian/fair-Boolean real-state receipt has a fixed posterior and
tilt, two-atom dynamics, `KL = 1/32`, and boundary at most `489/1024` on both
mass-`1/4` sign-flip branches. Countable and exact all-real `lambda`
optimization, atomless dynamics evidence, and matched arbitrary-state
comparison also remain open.

### Algorithmic stability expected bound

`AlgorithmicStability` proves bounded-differences scaffolding, a finite
expected-gap adapter under a finite coordinate-swap identity, and the finite
iid product-weight coordinate-swap specialization. It also proves the finite
two-sided expected-gap wrapper by applying the one-sided theorem to the negated
loss. It now includes a measure-theoretic iid product-measure expected-gap
wrapper over `Measure.pi`, with explicit integrability assumptions for the
selected losses induced by the algorithm, plus bounded-loss adapters that
discharge those assumptions for finite measurable hypothesis interfaces. The
bounded-loss adapters also compose into the sharp high-probability stability
theorem and its `β = c0 / n` corollary.

### Continuous Dudley integral

The finite chaining layer proves finite max and finite entropy-budget bounds,
total-bounded finite-net wrappers, truncated interval-integral comparisons,
and a supplied-supremum boundary adapter with an explicit terminal
approximation error. The finite-outcome theorem
`continuous_dudley_entropy_integral` checks the continuous integral endpoint
under explicit antitonicity, integrability, separable-terminal, modulus, and
boundary hypotheses. The library does not yet construct arbitrary measurable
suprema or a general measure-side chaining budget, and it does not prove a
full unrestricted empirical-process chaining theorem.

### Stochastic-dynamics extensions

The prefix-dependent semantic layer lets a fixed-in-advance kernel family and
score functional inspect the observed finite prefix. Thus it can represent an
online update rule whose time-`n` prediction is fixed before the next state is
revealed. The finite `TrajectoryPACBayes` adapter packages a predeclared
catalog of such rules and gives posterior-uniform, all-positive-time control
from one measurable event. A posterior over that catalog and one atom of a
predeclared finite tilt prior may be selected from the trajectory.

The catalog itself must still be fixed before the scored trajectory is
observed; the result does not validate inventing or fitting new catalog
members after seeing their scored outcomes. Separate modules now provide a
forward empirical-Bernstein trajectory boundary, a normalized countable
declared-tilt selector, the supplied-Poisson stationary-risk bridge above, and
finite-depth potentials under supplied or computed Dobrushin contraction. A
fixed candidate kernel can now be transferred under a deterministic row-TV
envelope, including uniqueness among supplied invariant PMFs under strict
candidate contraction. Empirical transition-coordinate bands now add
time-uniform visited-row confidence radii and post-data candidate contraction
certificates for unknown finite kernels. A finite predeclared candidate--depth
catalog now combines those bands with the stationary risk event on the same
path, and every nonempty finite kernel has a chosen invariant PMF. Natural next
layers are path-fitted candidates outside a predeclared catalog, a random
initial law, controlled/action-dependent kernels, auxiliary-data construction
of valid stationary-score catalogs, mixing guarantees, and continuous-state
stationary inference.
declared-tilt selector, and the supplied-Poisson stationary-risk bridge above.
Natural next layers are a random initial law, target-law occupancy and dynamic
policy comparators, auxiliary-data catalog construction, automatic finite-depth
Poisson potentials from contraction, and continuous-state stationary
inference.
members after seeing their scored outcomes. The arbitrary supplied initial
PMF is checked for the homogeneous finite-state Markov weighted-tilt theorem,
not for this general prefix-dependent trajectory layer. Natural next layers
are random starts for prefix-dependent kernels, controlled/action-dependent
kernels, auxiliary-data catalog construction, empirical-variance adaptation,
and normalized countable or predictable tilt families. Continuous-state
kernels and stationary-risk conclusions require separate formal interfaces
and are not consequences of the current results.
