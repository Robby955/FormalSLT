# Roadmap

## Completed

- [x] Population risk, empirical risk, ERM definitions
- [x] Finite-sample Rademacher complexity definition
- [x] Ghost sample replacement and genGap
- [x] Rademacher symmetrization (E[genGap] ≤ 2·E[Rad])
- [x] Doob exposure martingale construction
- [x] Bounded-differences → Azuma-Hoeffding chain
- [x] High-probability Rademacher genGap tail
- [x] Massart's finite-class Rademacher bound
- [x] Finite-class high-probability generalization (Massart + Azuma)
- [x] Two-sided uniform deviation bound
- [x] VC dimension wrapper (Mathlib's `Finset.vcDim`)
- [x] Binary class trace and Sauer-Shelah growth bound
- [x] Sauer-Shelah polynomial closed form
- [x] Effective-class Rademacher (distinct loss patterns)
- [x] VC-style pointwise Rademacher bound
- [x] VC high-probability genGap tail
- [x] VC uniform deviation (two-sided)
- [x] VC ERM excess-risk tail
- [x] VC ERM closed-form sample-complexity theorem:
  inverts the VC ERM tail into the explicit condition
  `n * ε^2 >= 72 * B^2 * (d * log(en/d) + log(2/δ))`
- [x] Rademacher-route ERM generalization
- [x] Binary-class VC → effective loss-pattern bridge (equality + Sauer-Shelah corollary)
- [x] Contraction lemma (Ledoux-Talagrand): comparison, one-step, full iteration, empirical wrapper
- [x] Linear predictor Rademacher bound: Rad ≤ R·n⁻¹·√(∑‖xₖ‖²), corollary RB/√n
- [x] Covering number ε-net peeling: Rad(F) ≤ ε + Rad(N_ε)
- [x] Covering + Massart composition: Rad(F) ≤ ε + B·√(2·log|N|/n)
- [x] Two-scale Dudley chaining: Rad(F) ≤ ε₁ + ε₂ + B·√(2·log|N₂|/n)
- [x] Finite sub-Gaussian max bounds:
  MGF control ⇒ finite expected-sup entropy budget
- [x] Finite sub-Gaussian chaining scaffold:
  finite nets, nearest projections, projection-pair entropy, finite multiscale
  decomposition
- [x] Finite Dudley-style entropy sums:
  projection-pair and covering-number versions, dyadic/geometric radius
  schedules, and per-scale entropy-budget wrappers
- [x] Finite Dudley discrete entropy-bound refinement:
  uniform per-scale entropy caps collapse the finite dyadic sum to a
  geometric-series `2 * radiusScale` budget
- [x] Finite Dudley annulus-budget bridge:
  rewrites finite dyadic entropy sums through dyadic annulus widths, giving a
  finite integral-comparison scaffold without claiming the continuous entropy
  integral
- [x] Finite entropy-sum to finite integral-comparison wrapper:
  bounds the finite chaining estimate by a dyadic upper Riemann-style entropy
  budget with a user-supplied finite entropy envelope
- [x] Monotone finite entropy-envelope refinement:
  packages finite covering-number upper bounds into a monotone prefix-sup
  entropy envelope for the finite Dudley integral-budget wrapper
- [x] Total-bounded finite-net extraction bridge:
  converts `TotallyBounded Set.univ` into the repo's explicit finite-net
  records and provides a dyadic net schedule whose adjacent radii satisfy the
  finite chaining radius budget
- [x] Finite-terminal total-bounded dyadic Dudley wrapper:
  composes the total-bounded dyadic net schedule with the finite Dudley
  entropy-budget theorem using an identity terminal net on a finite index type
- [x] Projected-sup total-bounded dyadic Dudley wrapper:
  composes the total-bounded dyadic net schedule with the projected finite
  Dudley entropy-budget theorem, bounding the terminal projected supremum
  without an identity terminal net
- [x] Projected finite-net image total-bounded dyadic Dudley wrapper:
  replaces the finite ambient index assumption with a finite terminal-net image
  supremum, preserving finite-scale entropy-budget scope
- [x] Finite dyadic-budget to entropy-at-radius upper-sum comparison:
  compares the finite Dudley prefix-envelope budget to a supplied
  entropy-at-radius upper sum/integral budget, then composes it with the
  projected total-bounded finite-net wrapper. This is still finite-scale and
  does not prove continuous Dudley, separability, or measurable arbitrary
  suprema.
- [x] Finite shifted-annulus to truncated interval-integral comparison:
  proves the shifted dyadic annulus integrals compose into one truncated
  interval integral and feeds that directly into the projected total-bounded
  finite-net Dudley wrapper.
- [x] Projected-sup to supplied-supremum boundary adapter:
  transfers the projected finite-net Dudley bound to a caller-supplied
  supremum functional under an explicit terminal approximation error. This is
  the current continuous-boundary interface; it does not construct arbitrary
  measurable suprema or prove separability.
- [x] Finite-skeleton projected-sup boundary adapter:
  separates the supplied supremum functional into an explicit finite
  skeleton/dense-net approximation error plus a terminal projection error,
  then composes that adapter into the finite and total-bounded Dudley wrappers.
  This is still a finite-scale boundary theorem; it does not prove a
  separability theorem or construct measurable arbitrary suprema.
- [x] Usable finite-skeleton boundary hypotheses:
  terminal net radius plus a pathwise modulus discharges the terminal
  approximation, and approximate maximizers plus a finite skeleton selector
  discharge the supplied-supremum skeleton approximation. The composed
  total-bounded wrapper remains finite-scale and does not construct arbitrary
  measurable suprema.
- [x] Epsilonized total-bounded Dudley boundary adapter:
  for every positive error budget, a finite skeleton and terminal dyadic scale
  certificate yields the truncated-interval Dudley bound with a single `+ eta`
  boundary term. This is still a finite-choice interface, not a separability or
  arbitrary measurable-supremum theorem.
- [x] Finite-cover total-bounded Dudley boundary certificate:
  finite-cover radius plus a pathwise modulus discharges the finite-skeleton
  approximation hypothesis, then composes into the epsilonized total-bounded
  Dudley wrapper. This remains a finite-choice boundary layer.
- [x] Dudley boundary epsilon elimination:
  if a single global budget uniformly dominates the finite Dudley budgets
  selected by the epsilonized certificates, the boundary adapter loses the
  explicit `+ eta` term. This is still not a full continuous Dudley theorem.
- [x] Separable-terminal Dudley boundary adapter:
  finite skeleton separability plus terminal projection approximation now
  compose directly with a uniform global budget. This exposes the assumptions
  used by continuous-boundary arguments without claiming arbitrary measurable
  suprema.
- [x] Pathwise terminal-modulus Dudley boundary constructor:
  explicit finite-skeleton separability plus a pathwise terminal modulus now
  discharge the separable-terminal boundary certificate used by the
  total-bounded Dudley lane.
- [x] Finite-cover to separable-terminal Dudley bridge:
  finite-cover/pathwise-modulus certificates now discharge the cleaner
  separable-terminal boundary interface, connecting usable finite-cover
  hypotheses to the global-budget Dudley boundary statement.
- [x] Guarded unit-interval pair-count Dudley endpoint:
  the concrete `[0,1]` Rademacher process now has a guarded continuous Dudley
  capstone whose integrand is the pair-count chaining envelope
  `unitIntervalChainingPairCountEnvelope`, not a metric covering number
  `N(ε)`. The exported surface includes
  `unitIntervalPairCountEntropy_eq_pair_count_sample`,
  `unitInterval_pairCountEntropy_nonconstant`,
  `unitInterval_pairCountEntropy_integral_positive`, and
  `continuous_dudley_oneStep_entropy_integral_iSup_unitInterval_pairCountEnvelope`.
  This remains the concrete unit-interval endpoint, not the general
  totally-bounded or measurable-supremum lane.
- [x] Algorithmic stability bounded differences (Bousquet-Elisseeff 2002):
  training loss constant β + 2B/n, gen gap constant 2β + 2B/n
- [x] Finite algorithmic stability expected-gap adapter:
  uniform stability gives `E[genGap] ≤ β` under finite
  coordinate-swap weights
- [x] Finite iid coordinate-swap identity:
  product sample weights `∏ k, p(S k)` satisfy the finite coordinate-swap
  identity, yielding the finite iid expected-gap specialization
- [x] PAC-Bayes KL divergence and Donsker-Varadhan variational inequality:
  KL(ρ‖π) ≥ 0 (Gibbs inequality), ∑ ρ_i·f_i ≤ KL(ρ‖π) + log(∑ π_i·exp(f_i))
- [x] Finite PMF, measure, and KL interoperability with Mathlib:
  real-valued finite PMFs convert to `PMF`, weighted sums agree with Bochner
  integrals, and the finite KL sum agrees with Mathlib's extended-real KL under
  posterior-support inclusion in the prior
- [x] PAC-Bayes finite iid product MGF bridge:
  exact finite product factorization for `E_S exp(lam * (R_i - Rhat_i(S)))`
  and prior-averaged MGF bound from per-hypothesis one-coordinate MGF budgets
- [x] PAC-Bayes finite bounded-loss confidence layer:
  `[0,1]` one-coordinate MGF instantiation, sample/prior averaged MGF bounds,
  finite Markov confidence event, deterministic posterior-risk adapter, and
  finite Catoni-style bad-event theorem
- [x] PAC-Bayes closed high-confidence generalization payoff:
  complements the Catoni bad event against total iid product mass, giving the
  textbook good-event statement that all finite posteriors simultaneously obey
  the Catoni-form risk bound with probability at least `1 - δ`
- [x] Localized Rademacher finite Bernstein scaffold:
  excess-loss and second-moment localization definitions, localized empirical
  Rademacher wrappers, monotonicity under predicate inclusion, and the
  Bernstein bridge from excess-risk localization to second-moment localization
- [x] Localized Rademacher deterministic fixed-point certificate layer:
  a finite envelope certificate `FixedPointUpperCertificate`, a
  second-moment localized empirical-complexity wrapper, and a Bernstein
  composition controlling the excess-risk localized empirical complexity by
  the second-moment radius `c * r`
- [x] Localized Rademacher deterministic deviation certificate layer:
  empirical excess-risk bookkeeping, a localized upper-deviation certificate,
  and a finite fast-rate shell that composes localized deviation with the
  Bernstein/fixed-point certificate
- [x] Finite Markov prequential-risk certificate:
  an Ionescu--Tulcea path law for finite transition PMFs, a derived next-step
  conditional-expectation identity, a sharp `1/4` conditional-variance proxy
  for the centered `[0,1]` loss, and a measurable all-positive-time finite-grid
  event comparing observed squared loss with average conditional risk
- [x] Finite-catalog Markov PAC-Bayes certificate:
  a fixed-tilt (`0 < λ < 3`), all-positive-time, all-posterior theorem under the
  actual finite Markov path law, with a measurable exceptional event and an
  asymmetric data-selected-posterior receipt
- [x] Finite weighted-tilt Markov PAC-Bayes certificate:
  one full-support finite tilt prior and one measurable exceptional event of
  mass at most `delta`; its complement supports all-time, all-posterior,
  all-atom validity and post-path selection of one predeclared tilt atom. The
  checker gives an asymmetric path-selected posterior/tilt receipt; its two
  explicit selector paths exercise branches but are not proved good or
  positive-probability
- [x] Supplied finite-state initial-law Markov PAC-Bayes extension:
  an arbitrary initial PMF mixes the common raw failure mass across the
  deterministic-start path laws before one measurable hull is taken. The
  asymmetric receipt uses initial masses `1/3` and `2/3`, bounds exceptional
  mass by `1/20`, and proves good-complement mass at least `19/20`
- [x] All-sample-size empirical-Bernstein PAC-Bayes certificate:
  the leave-one-coordinate Bessel identity, reverse Bessel martingale, reverse
  joint mean/variance exponential submartingale, epoch-level posterior/catalog
  maximal event, reverse square-root endpoint, finite-prefix product-law
  bridge, and telescoping dyadic stitch now yield one measurable infinite-IID
  event of mass at most `delta`. Its complement controls every `n >= 2` and
  every posterior PMF on a fixed finite hypothesis type with one KL term and
  posterior-averaged per-hypothesis Bessel variance. This is an offline
  reverse-epoch theorem, not a forward e-process or optional-stopping result.
- [x] Forward hybrid-Bessel PAC-Bayes certificate:
  the predictable-residual empirical-Bernstein process is checked as the
  stochastic e-process, while two Bessel envelopes and their hybrid minimum
  give the observable lower-envelope conversion. A finite full-support
  hypothesis--tilt master and a separate continuous-prior master over arbitrary
  measurable hypotheses each have one outer-mass event for every `n >= 2`,
  admissible posterior, and declared finite tilt atom. The full-prefix
  trajectory adapter permits arbitrary measurable state and hypothesis spaces
  and derives the continuous master's process-measurability interfaces from one
  supplied score jointly strongly measurable in the hypothesis, complete
  prefix, and next state. It retains a deterministic start. The separate
  basic `Theta = Real`, `Z = Real` checker uses a two-atom Rademacher kernel and
  proves positive conditional variance without evaluating the PAC-Bayes
  boundary. A separate Gaussian/fair-Boolean trajectory receipt has posterior
  finite-set mass zero, `KL = 1/32`, positive observed Bessel variance on a
  theorem-produced good path in each of two mass-`1/4` sign-flip branches, and
  boundary `<= 489/1024 < 1/2` at `n = 64`, `delta = 1/8`, and
  `lambda = 1/2`. It fixes posterior and tilt and uses a two-atom state law, so
  it does not cover atomless dynamics, selected processes, or a matched
  comparison. The IID bounded-loss adapter and a structural fair-Boolean
  good-path receipt are checked separately. A second biased-Boolean receipt
  proves positive Bessel variance
  `1/32`, `KL = log 2`, a theorem-produced good path below `343/1000`, and a
  same-prefix empirical-Bernstein versus fixed-proxy boundary comparison of
  approximately `0.312` versus `0.760`.
- [x] General-measurable-hypothesis all-sample-size extension:
  continuous-prior integration, the reverse joint mean/variance epoch,
  predeclared dyadic tilt catalog, closed-form prefix endpoint, and infinite
  stitch now give the same all-`n` event for every posterior probability
  measure absolutely continuous with respect to a fixed prior and having an
  integrable log-likelihood ratio. The observation space remains finite. A
  product-Gaussian/fair-Boolean receipt checks posterior finite-set mass zero,
  `KL = 1/32`, and an unscaled zero-one sign-flip mismatch loss that depends on
  both coordinates and attains both endpoints. Every nonempty-sample posterior
  empirical risk is `1/2`; at `n = 2^20` and `delta = 1/2`, the correction is
  below `1/2` and the theorem-produced right-hand side is below the trivial
  ceiling `1`; a checked corollary gives a path outside the exceptional event.
  The receipt fixes the posterior and does not exercise data-dependent
  continuous-posterior selection.

## Planned

### Near-term

- [ ] **All-sample-size and forward empirical-Bernstein evidence**
  - Freeze the exact theorem commit and archive the full build, example,
    axiom, statement-fidelity, witness, documentation, and metadata gates.
  - Compare the stitched constants and all-sample-size nonvacuity region against
    PAC-Bayes-kl, Hoeffding/Catoni, Tolstikhin--Seldin, and existing anytime
    PAC-Bayes boundaries on identical inputs.
  - Obtain independent PAC-Bayes/constants and Lean probability reviews.
  - [x] Add a positive-KL, positive-variance forward receipt with an
    informative numerical width.
  - [x] Add the normalized countable finite-hypothesis master and the
    finite-state full-prefix geometric selector whose boundary tends to zero.
  - Extend that countable control to continuous priors and arbitrary states;
    study predictable or all-real tilts, optimized boundaries, random starts
    beyond the homogeneous finite-state Markov endpoint, atomless-dynamics
    receipts, and matched comparisons. Do not treat the hybrid Bessel lower
    envelope as an e-process.

- [ ] **Stochastic-dynamics extensions**
  - [x] Support finite predeclared catalogs of prefix-dependent scores,
    including fixed-in-advance online update rules whose time-`n` prediction
    is determined before the next state is observed.
  - [x] Convert the trajectory empirical-Bernstein event to finite-state
    stationary risk from a supplied invariant PMF and supplied bounded exact
    or approximate Poisson potentials.
  - [x] Construct finite-depth Poisson potentials automatically from explicit
    kernel-contraction data, with checked residual and span bounds, and compute
    a valid contraction factor from the finite Dobrushin coefficient.
  - [x] Confidence-allocate one outer event over every finite Poisson depth and
    countable geometric tilt, permit post-path depth and tilt substitution, and
    prove that the full logarithmic-depth stationary boundary vanishes.
  - [x] Transfer the stationary certificate from a fixed candidate kernel
    under a deterministic row-TV envelope, including the doubled perturbation
    price and uniqueness among supplied invariant PMFs under strict candidate
    contraction.
  - [x] Build time-uniform empirical transition-coordinate confidence bands,
    normalize them on visited rows, and permit post-data candidate-kernel
    selection for row-TV and Dobrushin contraction certificates.
  - [x] Uniformize a finite predeclared candidate--depth Poisson catalog, join
    its risk event with transition confidence on the same path, and permit
    post-path candidate, depth, risk-tilt, transition-tilt, and posterior
    substitution on visited rows.
  - [x] Construct an invariant PMF for every nonempty finite kernel by Cesaro
    compactness, choose a canonical invariant target, and prove uniqueness
    under strict true-kernel or candidate row-TV contraction.
  - Extend same-data stationary selection beyond a finite predeclared
    candidate catalog, or use auxiliary data/sample splitting, before plugging
    a newly fitted candidate into a stationary-risk score.
  - [x] Add finite state--action behavior-law semantics for full-history
    behavior and target policies, including exact one-step normalized
    importance-score conditional means under overlap and a declared ratio cap.
  - [x] Add stationary state-Markov target-policy OPE for known dynamics and
    behavior propensities with supplied invariant laws and exact bounded
    Poisson potentials.
  - [x] Add encountered-prefix comparators for history-dependent target
    policies under homogeneous and known prefix/time-dependent controlled
    environments.
  - [x] Add exact finite-horizon target-path change of measure, measurable
    cylinder, and terminal-state occupancy identities, with explicit `C ^ n`
    cumulative-weight range inflation.
  - Extend the controlled interface to an anytime-valid cumulative-weight or
    dynamic-policy value theorem, or learned nuisance quantities, under
    separate assumptions.
  - [x] Extend deterministic-start full-prefix semantics and the continuous-
    prior forward endpoint to arbitrary measurable state spaces under a
    supplied jointly measurable score contract.
  - [x] Generalize the finite homogeneous-Markov weighted-tilt certificate
    from a deterministic initial state to an arbitrary supplied finite-state
    initial PMF, without a union bound or added confidence penalty.
  - Generalize random starts to prefix-dependent, measurable-state, and
    controlled trajectory endpoints.
  - Add an interface for catalogs constructed from auxiliary random training
    data without claiming validity for catalog members created after observing
    their scored outcomes.
  - Extend the checked normalized countable finite-hypothesis and finite-state
    trajectory results to continuous priors and arbitrary states; study
    predictable tilt families without optimizing an uncontrolled real
    parameter after observing the path.
  - Keep unvisited-row normalization, quantitative mixing, continuous-state
    stationary risk, multistep conclusions, and atomless transition evidence
    as separate later theorem families.

- [x] **Sharp McDiarmid constant**
  - `ExposureMartingale.hasBoundedDifferences_tail_sharp` proves the product
    bounded-differences tail `exp(-2ε² / ∑k c_k²)`.
  - `Concentration.mcdiarmid_twoSided_of_hasBoundedDifferences_sharp` packages
    the matching two-sided homogeneous product form
    `P(|f - E[f]| >= ε) <= 2 exp(-2ε² / ∑k c_k²)`.
  - `ExposureMartingale.genGap_tail_bound_sharp_explicit` specializes it to the
    generalization gap, replacing `exp(-ε²n/(8B²))` by
    `exp(-ε²n/(2B²))` at the genGap-tail layer.
  - The Rademacher, VC, and stability high-probability wrappers now consume the
    sharp tail where their statements expose the concentration exponent.

- [x] **Algorithmic stability: expected bound**
  - Measure-theoretic iid `E[R(A(S)) − R̂(A(S),S)] ≤ β` via product-measure
    coordinate-swap symmetry, with explicit integrability assumptions.
  - Bounded-loss adapters now discharge those integrability assumptions for
    common finite-class measurable algorithm interfaces.
  - The bounded-loss adapters now compose into the sharp high-probability
    stability surface for finite measurable hypothesis interfaces.
  - Next refinements: add concrete algorithm-specific
    stability examples.

- [ ] **Localized Rademacher: finite fixed-point layer**
  - The deterministic fixed-point certificate layer is closed.
  - The deterministic localized deviation certificate shell is closed.
  - Next prove a high-probability construction of the localized deviation
    certificate for finite classes.
  - Target a finite fast-rate/oracle-inequality scaffold without claiming
    infinite-class or measurable-supremum generality.

- [x] **Continuous Dudley entropy-integral endpoint under explicit certificates**
  - The finite-terminal and projected-sup dyadic wrappers are closed.
  - The finite dyadic budget now compares to a supplied entropy-at-radius
    upper sum/integral budget for projected finite nets.
  - `continuous_dudley_entropy_integral` and its finite-outcome `iSup`
    variants check the integral endpoint under explicit antitonicity,
    integrability, separable-terminal, modulus, and boundary hypotheses.
- [ ] **General measurable-supremum Dudley lift**
  - Construct the measure-side chaining budget and measurable arbitrary
    supremum on a general probability space.
  - Do not infer those constructions from the checked finite-outcome or
    supplied-boundary endpoint.

### Medium-term

- [x] **PAC-Bayes finite-grid McAllester square-root peeling**
  - ~~Step 1: KL divergence on finite types~~ ✓ (`PACBayesKL.klDiv`)
  - ~~Step 2: Donsker-Varadhan variational inequality~~ ✓ (`PACBayesKL.donsker_varadhan`)
  - ~~Step 3a: finite iid product MGF bridge~~ ✓ (`PACBayesFiniteProductMGF`)
  - ~~Step 3b: instantiate the one-coordinate MGF budget from bounded losses
    and add the Markov confidence adapter~~ ✓ (`PACBayesBoundedLoss`)
  - ~~Step 4a: fixed-budget McAllester-style square-root corollary. For a
    fixed complexity budget `C`, if `KL(ρ‖π) + log(1/δ) ≤ C`, then outside a
    bad event of finite product-sample mass at most `δ`,
    `R(ρ) ≤ R̂(ρ,S) + √(C/(2n))`.~~ ✓
    (`PACBayesBoundedLoss.finiteMcAllesterBoundedComplexity_badEventMass_le_delta`)
  - ~~Step 4b: finite-grid McAllester peeling. Remove the single fixed-budget
    assumption by assigning positive confidence mass and complexity budgets to
    finitely many buckets, then union-bound the bucket failures.~~ ✓
    (`PACBayesBoundedLoss.finiteMcAllesterGridPeeling_badEventMass_le_delta`)
  - ~~Step 4c: finite-grid optimized wrapper. Allow a posterior-dependent
    penalty whenever every posterior PMF has a finite bucket certificate whose
    square-root bucket penalty is no larger than that penalty.~~ ✓
    (`PACBayesBoundedLoss.finiteMcAllesterGridOptimized_badEventMass_le_delta`)
  - ~~Step 5: Catoni PAC-Bayes. λ-parameterized version giving the tighter
    `R(ρ) ≤ R̂(ρ,S) + (KL(ρ‖π) + log(1/δ))/(λn) + λ/8` trade-off.
    In Lean this is stated with the sample-level exponent `lam` as
    `R(ρ) ≤ R̂(ρ,S) + (KL(ρ‖π) + log(1/δ))/lam + lam/(8n)`~~ ✓
    (`PACBayesBoundedLoss.finiteCatoni_badEventMass_le_delta`)
  - The continuous-hypothesis layer now includes a process theorem and an
    end-to-end fixed-posterior spherical-Gaussian i.i.d. specialization with
    explicit KL. Remaining extensions include exact all-real-`λ`
    optimization, posterior-uniform continuous families, and general infinite
    hypothesis classes.

- [x] **PAC-Bayes finite Bernstein margin-proxy shell**
  - ~~Step 1: add a posterior average of a supplied per-hypothesis variance
    proxy.~~ ✓ (`PACBayesBernstein.posteriorMarginVarianceProxy`)
  - ~~Step 2: define the normalized Bernstein prior exponential moment with
    variance and scale terms.~~ ✓ (`PACBayesBernstein.priorBernsteinExpMoment`)
  - ~~Step 3: prove the deterministic fixed-sample PAC-Bayes Bernstein
    adapter from a prior-moment certificate.~~ ✓
    (`PACBayesBernstein.posteriorGeneralizationGap_le_bernstein_of_priorBernsteinExpMoment_le`)
  - ~~Step 4: prove finite Markov bad-event bounds for fixed `lambda` and for
    posterior-dependent margin-style penalties under explicit complexity and
    penalty certificates.~~ ✓
    (`PACBayesBernstein.finitePACBayesBernsteinMargin_badEventMass_le_delta`)
  - The finite indicator-loss specialization now derives exact Bernoulli
    variance and the observable self-bound `V_rho <= R_rho/n`; at
    `lambda = 2n/3` it yields the checked low-risk coefficients `7/4` and
    `21/(8n)`, including a non-vacuous evaluated example. A finite weighted
    indicator-Bernstein tilt catalog now gives one simultaneous event and
    supports sample- and posterior-dependent selection from a fixed family,
    with an unequal-weight four-entry receipt. The finite empirical-variance
    foundation now proves the exact Bessel/pairwise identity, `[0,1]` bounds,
    and finite-IID unbiasedness under the actual product weights. Random
    matching, disjoint-pair factorization, and finite Jensen now prove the
    source-normalized empirical-variance exponential moment for every
    `n >= 2`. Its fixed-tilt PAC-Bayes lift gives one bad set of mass at most
    `delta` and a variance comparison simultaneous over every finite posterior.
    A separate arbitrary bounded-loss Bernstein event and an explicit finite
    union now yield the fixed-parameter observable empirical-Bernstein risk
    theorem with total failure `deltaVariance + deltaRisk`. Separately weighted
    finite catalogs for both tilts now give sample- and posterior-dependent
    selectors on one shared event without a Cartesian-pair confidence charge.
    The variance catalog is also a standalone reusable module with a concrete
    unequal-weight, two-branch receipt, and the final risk layer imports it. A
    retained-Bennett joint mean/Bessel-variance score and one-event finite
    joint-pair posterior catalog are also checked, with one KL term at the
    selected entry. Its zero-residual coefficient branch now gives the explicit
    selected posterior-risk bound in terms of empirical risk and empirical
    variance. The other residual branches are checked as an exact attained
    three-piece maximum on `[0,1/4]`, and the selected endpoint adds `xi / t`.
    A concrete dyadic scale catalog of depth `Nat.clog 2 n` now removes the
    public optimizer hypothesis and yields the direct one-event endpoint
    `Rhat + (5/4) * sqrt(2 * Vhat * L / n) + (5/2) * L / n`, with
    `L = KL + log((Nat.clog 2 n + 1) / delta)` and a positive-KL,
    positive-variance, positive-sample-mass receipt below `99/100`.
    A support-aware normalized countable weighted joint `(t, eta)` master
    mixture, per-entry prior-moment extraction, finite-posterior bound, and
    sample/posterior-dependent exact-`xi` natural-index selector are now
    checked on one fixed-sample event with one KL term per selected bound. A
    normalized finite hypothesis--tilt e-process with one Ville event and a
    selected-atom weight penalty is checked separately at the generic process
    level, together with a measurable-event finite-IID `[0,1]` loss adapter.
    A finite adaptive-selection guardrail now proves the corresponding
    predeclared-weight and Kraft upper bounds and gives an exact diagonal
    witness forcing a common raw correction of at least the catalog size. A
    separate countable-allocation guardrail proves a blockwise reciprocal-
    weight obstruction and an explicit log-log atom cost along an unbounded
    geometric-epoch subsequence, with exact telescoping polynomial weights.
    It is not a universal confidence-sequence or LIL lower bound.
    A second forward lane now checks the predictable-residual
    empirical-Bernstein e-process, its hybrid Bessel lower envelope, and a
    finite hypothesis--tilt PAC-Bayes master with an IID adapter and
    path/time/posterior-dependent atom selection. Its separate finite-IID
    informative receipt has positive Bessel variance and KL, a theorem-produced
    good path, and a checked same-prefix improvement over the fixed-proxy
    boundary.
    The arbitrary-state Gaussian/fair-Boolean receipt separately checks
    posterior finite-set mass zero, `KL = 1/32`, and boundary
    `<= 489/1024 < 1/2` on theorem-produced good paths in both mass-`1/4`
    sign-flip branches. It fixes the posterior and tilt and uses a two-atom
    Rademacher state law.
    The reverse-exchangeability lane now separately gives one all-sample-size
    empirical-Bernstein event for finite IID data and finite hypotheses, with
    constants `5/2` and `5`. The finite-hypothesis forward lane now has a
    normalized countable master, and its finite-state full-prefix adapter has a
    geometric selected boundary tending to zero. Extending those results to
    countable continuous-prior or arbitrary-state control, predictable or
    all-real tilts, an optimized boundary, and infinite hypothesis classes
    remains open. The separate reverse continuous lane covers arbitrary
    measurable hypotheses for finite-valued observations; it does not close
    these forward extensions.

### Long-term

- [ ] **Dudley beyond the checked boundary-certificate endpoint**
  - Arbitrary measurable suprema and non-finite outcome constructions
  - Generic chaining (Talagrand)

- [ ] **Minimax lower bounds**
  - [x] Fair-sign deterministic one-sided anytime boundaries have an
    unconditional unbounded `sqrt n` floor, with a separate fixed-Gaussian-tail
    eventual lower bound
  - [ ] Prove the fair-sign upper LIL needed by the checked sharp
    `sqrt(2 n log log n)` constant-one reduction
  - [ ] Fano, Assouad, Le Cam and matching lower bounds for the structured
    PAC-Bayes/tilt families

## Design Principles

1. **One theorem per PR.** Each result is a focused addition.
2. **No sorry/admit.** Every merged theorem is fully proved.
3. **Axioms: [propext, Classical.choice, Quot.sound] only.**
4. **Assumptions stated in types.** If a theorem requires bounded loss, the type signature says so.
5. **Scope documented.** Public summaries distinguish closed theorems from
   current boundaries and future work.
