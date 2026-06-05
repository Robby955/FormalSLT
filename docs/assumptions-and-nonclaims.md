# Assumptions and Current Boundaries

This page records the assumptions behind the current theorem spine and the
current boundaries for public summaries.

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

### IID samples

The sample `S : Fin n → Z` is drawn from the product measure
`piMeasure μ n = μ^⊗n`. Each coordinate is independent and identically
distributed.

The current bounds do not cover time series, online learning, active learning,
or dependent data without additional assumptions.

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

It is a foundation for Dudley-style arguments. It is not the continuous
Dudley entropy integral.

## Current Boundaries

### VC-to-PAC equivalence

The repo proves upper-bound components for the finite VC/Rademacher route. It
does not prove the full equivalence between finite VC dimension and
PAC-learnability.

### Infinite classes

The main Rademacher and VC statements are finite-index theorems. Moving to
general infinite classes requires covering-number APIs, measurable suprema,
separability assumptions, and approximation arguments that are outside the
current theorem spine.

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
Bernstein prior-moment certificate. `PACBayesMargin` specializes that shell to
thresholded classifier-margin losses, proves the iid finite classifier-margin
MGF budget, derives the normalized Bernstein prior-moment certificate, and
packages the fixed-`lambda` iid bad-event theorem with the sample-size-scaled
variance proxy. Exact all-real `λ`, finite-grid Bernstein optimization,
infinite-hypothesis, and continuous-posterior PAC-Bayes theorems remain future
work.

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
