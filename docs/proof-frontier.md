# Proof Frontier Manifest

`docs/proof-frontier-manifest.json` is a generated index of the current
FormalSLT proof surface. It records source counts, proof-debt scan results,
curated theorem-map entries, and the documented next proof lanes.

The manifest is for review and tooling. It does not replace the Lean checker,
and it does not infer new mathematical dependency structure.

## Regenerate

```bash
python3 scripts/generate_proof_frontier_manifest.py
```

## Check

```bash
python3 scripts/generate_proof_frontier_manifest.py --check
lake build FormalSLT
lake env lean examples/CheckShowcaseTheorems.lean
lake env lean examples/CheckUnitIntervalDudley.lean
```

The generated audit section should report empty `sorry_or_admit` and
`custom_axiom_or_constant` arrays. Public theorem axioms should remain limited
to `[propext, Classical.choice, Quot.sound]`, as checked by the Lean example
files.

## Current Next Lanes

- `finite-markov-prequential-risk`: full-prefix semantics and the sharp `1/4`
  variance proxy are checked for finite and arbitrary measurable state spaces.
  Finite-catalog, countable-tilt, and continuous-prior adapters give common
  all-time events over their stated posterior and predeclared-tilt classes.
  The general prefix-dependent and measurable-state endpoints retain a
  deterministic start; the homogeneous finite-state Markov weighted-tilt
  endpoint separately accepts any supplied finite-state initial PMF.

  The finite stationary layer constructs finite-depth Poisson corrections,
  computes Dobrushin contraction, transfers fixed candidate kernels under
  row-TV error, estimates visited-row transition error, selects within a finite
  predeclared candidate--depth catalog, and constructs an invariant PMF for
  every nonempty finite kernel. Uniqueness requires a strict contraction
  certificate. The controlled layer proves one-step behavior-law semantics,
  stationary state-Markov OPE with supplied nuisance objects, encountered-
  prefix dynamic comparators, and exact fixed-horizon path-law change of
  measure with worst-case `C ^ n` weights.

  Catalogs must be declared before their scored outcomes. Same-path stationary
  selection is limited to the finite predeclared candidate catalog and visited
  rows; the arbitrary-state endpoint requires a jointly measurable bounded
  score; and
  none of the controlled results supplies learned nuisances or an anytime
  cumulative-weight value boundary. Open work includes auxiliary-data catalog
  construction, random starts beyond the homogeneous finite-state endpoint,
  unvisited-row and mixing interfaces, continuous-state stationary risk,
  countable tilts for continuous-prior and arbitrary-state layers, predictable
  or all-real tilts, and stronger multistate and atomless evidence.

- `localized-rademacher-finite-concentration`: finite, reviewable, and now
  packaged through the iid product-weight bad-event adapter with a
  bounded-excess MGF instantiation, fixed-threshold event payoff, and named
  fixed-threshold high-confidence finite-class statement. The sample-dependent
  fast-rate event interface is also named, and a conservative fixed-`ε`
  lower-envelope bridge now controls its bad-event mass under the same
  bounded-excess finite product assumptions. The sample-dependent union-bound
  and shifted exponential-moment adapters are also available, including a
  generic high-confidence wrapper from supplied shifted-moment budgets. A
  conservative bounded-excess shifted-moment instantiation for the named
  fast-rate event is now available through the fixed-`ε` lower envelope. An
  algebraic "centered" interface factors the fixed slack `ε` out of the shifted
  moment, leaving the empirical localized complexity term syntactically inside
  it. This interface is conservative-only: because the localized complexity is
  nonnegative, each per-hypothesis centered moment is pointwise at most the
  fixed moment, so the union bound over it cannot beat the conservative bound.
  It names — but does not discharge — the whole-supremum random-threshold
  obligation for `localizedUpperDeviation - 2·R̂_loc` (localized symmetrization
  plus McDiarmid/Azuma). Separately, the finite Bernstein
  variance-localization route is now closed locally through
  `localizedFiniteClassBernsteinHighConfidence_empirical_nonpos`, which uses a
  Bennett/Bernstein MGF layer, an averaged Bernstein tail, the localized
  variance proxy `c·r`, a finite union bound, and the fixed-threshold payoff.
  The next deeper theorem target is the whole-supremum bound, not a broader
  claim about the finite Bernstein theorem.
- `continuous-dudley-entropy-integral`: the finite-outcome continuous integral
  and `iSup` endpoints are checked under explicit antitonicity, integrability,
  separable-terminal, modulus, and boundary hypotheses. What remains is the
  construction of arbitrary measurable suprema and a general measure-side
  chaining budget rather than supplied interfaces.
- `anytime-boundary-lower-bounds`: for the fair-Rademacher walk, the CLT and
  Portmanteau give a fixed-Gaussian-tail `sqrt n` boundary floor, while a
  disjoint-block Borel--Cantelli argument proves that every valid deterministic
  one-sided anytime boundary exceeds every fixed nonnegative multiple of
  `sqrt n` infinitely often. The sharp `sqrt(2 n log log n)` constant-one
  conclusion is only a checked reduction from the explicitly unproved
  `FairSignUpperLIL` premise; no full LIL is claimed.
- `pac-bayes-all-real-lambda`: the base fixed-tilt, fixed-posterior
  spherical-Gaussian i.i.d. specialization and finite fixed catalogs with
  sample-dependent selection are checked. The finite indicator-Bernstein lane
  additionally has a posterior-uniform weighted tilt catalog. At process level,
  one normalized finite hypothesis--tilt e-process now gives a common Ville
  event, all-posterior validity, and post-path selection of a declared atom with
  its exact weight penalty. A separate finite selection-cost guardrail proves
  the predeclared-weight/Kraft correction and an exact diagonal witness forcing
  a common raw correction of at least the catalog size. A countable-allocation
  guardrail separately proves that positive summable weights incur an explicit
  iterated-logarithm atom cost along an unbounded geometric-epoch subsequence;
  this is an allocation/union-stitching obstruction, not a universal LIL or
  minimax lower bound. The checked fixed-sample countable joint master now
  has a downstream finite-posterior exact-`xi` selector over its predeclared
  `Nat`-indexed tilt-pair catalog. A separate forward lane now checks the
  predictable-residual empirical-Bernstein e-process, two Bessel envelopes and
  their per-hypothesis hybrid minimum, finite and normalized countable
  finite-hypothesis masters, and an IID bounded-loss adapter. The countable
  master is an actual e-process supporting every `n >= 2`, posterior PMF, and
  declared atom with its exact weight cost; an explicit geometric selector has
  boundary tending to zero. The finite-state full-prefix trajectory adapter
  obtains the analogous conclusion by countable confidence allocation, not by
  asserting that its event union is a countable master e-process. Countable
  continuous-prior or arbitrary-state masters, predictable or all-real tilt
  control, and a vanishing optimized boundary remain open. The hybrid Bessel
  expression is a lower envelope of the actual e-process, not itself a proved
  e-process.
- `pac-bayes-empirical-bernstein`: the finite per-hypothesis foundation,
  random-matching representation, and source-normalized lower-tail MGF are
  checked for `[0,1]` losses under the explicit finite IID product law and
  sample size at least two. A normalized prior moment now yields one
  fixed-sample, fixed-tilt bad set of mass at most `delta`; outside it, every
  posterior on the finite hypothesis type satisfies the checked comparison
  between its average of per-hypothesis population variances and the
  corresponding empirical average. A separate general bounded-loss Bernstein event now combines with
  that variance event; their union has mass at most the sum of the two declared
  budgets, and outside it every finite posterior satisfies the observable
  fixed-parameter empirical-Bernstein risk bound. Separate finite weighted
  catalogs for the two tilts now support sample- and posterior-dependent
  selection on one shared event. The variance catalog is independently exposed
  and witnessed with unequal weights and two selected branches; the final risk
  layer reuses it rather than duplicating its event. A retained-Bennett joint
  mean/Bessel-variance score and one-event finite joint-pair posterior catalog
  are also checked. The zero-residual coefficient branch now gives an explicit
  selected posterior-risk bound using empirical risk, empirical variance, and
  one KL-plus-catalog-weight confidence term. The other residual branches are
  now closed by an exact attained three-piece maximum on `[0,1/4]`, yielding
  the explicit `xi / t` penalty on the same event. A support-aware countable
  normalized master event, per-entry prior-moment extraction, finite-posterior
  bound, and sample/posterior-dependent natural-index `xi` selector are also
  checked on that one fixed-sample event with one KL term per selected bound.
  The selector receipt is structural and existential in the good sample. A
  predeclared dyadic scale grid through `Nat.clog 2 n` now gives the
  direct square-root-plus-linear posterior-risk endpoint with constants `5/4`
  and `5/2`, one KL term, and a 95%-confidence positive-KL/positive-variance
  positive-sample-mass receipt below `99/100`. Reverse exchangeability and
  telescoping dyadic stitching then give one infinite-IID event shared by every
  `n >= 2`. The finite-hypothesis endpoint has a structural path-selected
  posterior receipt. A separate continuous-prior integration layer derives the
  reverse mixture submartingale and extends the all-sample-size endpoint to
  every posterior probability measure on an arbitrary measurable hypothesis
  space that is absolutely continuous with respect to the prior and has an
  integrable log-likelihood ratio. A product-Gaussian/fair-Boolean receipt
  checks posterior finite-set mass zero, `KL = 1/32`, and an unscaled zero-one
  sign-flip mismatch loss that depends on both hypothesis coordinates and
  attains both endpoints. Every nonempty-sample posterior empirical risk is
  `1/2`; at `n = 2^20` and `delta = 1/2`, the correction is below `1/2` and
  the theorem-produced right-hand side is below `1`. A checked corollary gives
  a path outside the exceptional event. The receipt fixes the posterior and
  does not exercise data-dependent continuous-posterior
  selection.
  Observations remain finite-valued. Separately, the checked forward lane mixes
  the actual predictable-residual e-process over finite hypothesis and tilt
  priors and also integrates it over an arbitrary measurable hypothesis space;
  its arbitrary-measurable-state full-prefix trajectory adapter derives the
  parameterized process measurability assumptions from one supplied score
  contract jointly strongly measurable in the hypothesis, complete prefix,
  and next state. It retains a deterministic initial state. The hybrid Bessel
  term remains a lower envelope. Its common continuous-prior event supports
  every `n >= 2`, every eligible posterior measure, and every declared finite
  tilt atom, with one hypothesis KL and the selected atom's log-weight penalty.
  The separate finite-IID informative forward receipt has positive Bessel
  variance `1/32`, `KL = log
  2`, a theorem-produced good path, a risk ceiling below `343/1000`, and a
  same-prefix boundary comparison of approximately `0.312` versus `0.760`.
  The basic arbitrary-state `Real` checker separately uses a two-atom
  transition law and proves positive conditional variance without evaluating
  the PAC-Bayes boundary. The numerical Gaussian/fair-Boolean trajectory
  receipt has posterior finite-set mass zero, `KL = 1/32`, positive observed
  Bessel variance for every fixed hypothesis on a theorem-produced good path
  in each of two mass-`1/4` sign-flip branches, and boundary at most `489/1024`
  at `n = 64` and `delta = 1/8`. It fixes the posterior and tilt, and its
  real-state transition law has two-point support. The hybrid expression is not
  itself an e-process. The finite-hypothesis countable master and finite-state
  geometric vanishing selector are checked separately; countable
  continuous-prior/arbitrary-state, predictable/all-real, optimized-boundary,
  random-start, atomless-dynamics, and matched arbitrary-state comparison
  endpoints remain open. The continuous event is posterior-uniform but does
  not construct a measurable selector or selected process.
  Neither forward nor reverse result carries a novelty or priority claim.
- `sharp-mcdiarmid-product-kernel`: closed for independent finite product
  coordinates, including heterogeneous marginal laws and sharp downstream
  Rademacher, VC, metric-entropy, and stability wrappers. Dependent-coordinate
  extensions remain a separate problem.
