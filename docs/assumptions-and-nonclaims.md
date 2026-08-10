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

### Finite Markov prequential risk

`StochasticDynamics.MarkovRisk` constructs a dependent path law from an actual
finite-state transition PMF and a deterministic initial state. For fixed
functions `f q : Z -> R` valued in `[0,1]`, it derives the conditional
expectation of the next-step squared loss, proves the sharp universal `1/4`
conditional second-moment bound for the resulting centered innovation, and
applies an anytime finite tilt grid with that variance proxy.

`StochasticDynamics.MarkovPACBayes` lifts the same path-law argument to a
finite catalog of predictors with a full-support prior. At one fixed declared
tilt satisfying `0 < lambda < 3`, one measurable exceptional event works
simultaneously for every positive time and every posterior PMF, including a
posterior selected after observing the trajectory. The KL-confidence term is
`(KL(rho || prior) + log (1 / delta)) / (n * lambda)`. The certificate also
adds the sub-Gamma variance term `lambda / (8 * (1 - lambda / 3))`.

The checked target is the posterior average of the one-step conditional risks
encountered along the realized trajectory. The theorem does not require
stationarity, mixing, or irreducibility. It also does not cover a predictor
catalog fitted or updated on the same trajectory, a random initial
distribution, continuous state spaces, multistep forecasts, stationary
long-run risk, or post-sample selection of an arbitrary real tilt.

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

`PACBayes.FiniteEmpiricalVariance` supplies the finite empirical-variance
foundation for arbitrary real-valued per-hypothesis losses: population
variance, Bessel-corrected empirical variance, its exact ordered-pair
representation, and finite-IID unbiasedness for sample size at least two. The
universal population bound `1/4`, empirical bound `1/2`, and empirical-risk
self-bound additionally assume losses in `[0,1]`. Unbiasedness is an
expectation identity; it does not itself provide a tail event or confidence
bound, and it is not the variance of the posterior-averaged loss.

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
give uniformity over every Gaussian posterior or every real-valued tilt. The
i.i.d. learning theorem still does not cover arbitrary prior/posterior families
on an unrestricted measurable hypothesis space.

The source-faithful empirical-variance exponential-moment inequality and its
posterior-uniform PAC-Bayes empirical-Bernstein confidence theorem are not yet
implemented. A countable indicator-Bernstein catalog and exact all-real `λ`
optimization are also open.

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
approximation error. It does not yet prove a continuous entropy integral,
infinite-class separability theorem, or full empirical-process chaining
theorem.

### Stochastic-dynamics extensions

The current finite Markov results freeze the observable and finite predictor
catalog before the trajectory is generated. A posterior over that fixed
catalog may be selected from the trajectory, but this does not validate
fitting new predictors on the same observations. Natural next layers are a
random initial law, predictable or independently trained catalogs, and a
declared selectable tilt family. Same-trajectory training, continuous-state
kernels, and stationary-risk conclusions require separate formal interfaces
and are not consequences of the current certificate.
