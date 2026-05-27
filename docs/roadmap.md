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
  `n * ε^2 >= 128 * B^2 * (d * log(en/d) + log(2/δ))`
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
- [x] Localized Rademacher upper-deviation event adapter:
  a finite localized upper-deviation statistic, the sample event where it is
  bounded, monotonicity of deviation certificates under predicate restriction,
  an adapter from that event to the deterministic localized deviation
  certificate, and an event-facing finite fast-rate theorem
- [x] Localized Rademacher finite concentration adapter:
  a weighted finite union bound controls the localized upper-deviation bad-event
  mass from supplied pointwise tail budgets over the localized subtype
- [x] Localized Rademacher pointwise MGF tail adapter:
  a finite Markov/exponential-moment layer converts each pointwise upper-deviation
  MGF budget into a bad-event mass and composes those budgets over the localized
  subtype
- [x] Localized Rademacher finite iid product MGF bridge:
  the pointwise localized exponential moment under finite product sample weights
  is controlled by a supplied one-coordinate MGF budget for the excess-loss class
- [x] Localized Rademacher bounded-excess concentration wrapper:
  pointwise `[-1,1]` excess-loss assumptions instantiate the one-coordinate MGF
  budget and yield finite iid product-weight localized bad-event mass and
  delta-form concentration bounds
- [x] Localized Rademacher fixed-threshold event payoff:
  membership in a localized upper-deviation event plus nonpositive empirical
  excess risk gives a deterministic population excess-risk bound at that fixed
  threshold
- [x] Localized Rademacher fixed-threshold high-confidence statement:
  the bounded-excess finite product bad-event mass bound now composes with the
  fixed-threshold event payoff into one named finite-class theorem
- [x] Localized Rademacher sample-dependent event interface:
  random-threshold upper-deviation events now have a named event, bad-event
  mass, supplied-mass high-confidence adapter, and fast-rate event wrapper
- [x] Localized Rademacher conservative fast-rate bad-event bridge:
  nonnegativity of the localized empirical Rademacher term gives a pointwise
  lower envelope by the fixed `ε` threshold, so the named fast-rate bad-event
  mass is controlled by the existing fixed-threshold bounded-excess finite
  product theorem. This is a conservative finite statement, not the sharp
  random-threshold concentration theorem.
- [x] Localized Rademacher conservative fast-rate high-confidence wrapper:
  the conservative fast-rate bad-event mass bound now composes with the
  Bernstein/fixed-point event payoff into one named finite theorem, keeping
  the finite product-mass bound separate from the deterministic payoff
  hypotheses.
- [x] Localized Rademacher sample-dependent union and shifted-moment adapters:
  sample-dependent localized bad-event mass now has a pointwise union-bound
  adapter and a shifted exponential-moment interface. This is the exact
  assumption-facing surface needed for sharper random-threshold concentration
  work, without claiming that concentration theorem yet.
- [x] Localized Rademacher conservative shifted-moment instantiation:
  a sample-dependent shifted moment is controlled by the fixed-threshold
  exponential moment whenever the random threshold has a pointwise lower
  envelope, and the named fast-rate random-threshold event now has a
  bounded-excess finite-product shifted-moment budget through that fixed-`ε`
  lower envelope.
- [x] Localized Rademacher centered shifted-moment interface (algebraic):
  fixed slack added to a sample-dependent threshold factors out of the shifted
  exponential moment, yielding a named fast-rate high-confidence wrapper from
  supplied centered random-threshold shifted-moment budgets. This leaves the
  empirical localized complexity term syntactically inside the moment. It is an
  interface, not a non-conservative result: because the localized complexity is
  nonnegative, each per-hypothesis centered moment is pointwise at most the
  fixed moment, so the union bound over these budgets cannot improve on the
  conservative fixed-threshold bound. The genuine non-conservative obligation is
  a whole-supremum random-threshold concentration of
  `localizedUpperDeviation - 2·R̂_loc`, which this interface names but does not
  discharge.

## Planned

### Near-term

- [ ] **Sharp McDiarmid constant**
  - Improve 8B² → 2B² in the exponent
  - Current proofs bound the sub-Gaussian parameter by ‖c_k‖₊², giving
    exp(-ε²/(2·∑c_k²)). The sharp bound uses the range 2c_k with classical
    Hoeffding, giving exp(-2ε²/(∑(2c_k)²)) = exp(-ε²/(2·∑c_k²)) — same
    numerics but obtained via a different decomposition.
  - Actual gap: our proof uses |Δ_k| ≤ c_k as sub-Gaussian with param c_k²,
    while the sharp route needs conditional Hoeffding on [a_k, b_k] with
    b_k - a_k ≤ 2c_k. This requires `MeasureTheory.condExpKernel` (product-
    measure disintegration) which Mathlib does not yet export in usable form.

- [x] **Algorithmic stability — expected bound**
  - Measure-theoretic iid `E[R(A(S)) − R̂(A(S),S)] ≤ β` via product-measure
    coordinate-swap symmetry, with explicit integrability assumptions.
  - Bounded-loss adapters now discharge those integrability assumptions for
    common finite-class measurable algorithm interfaces.
  - The bounded-loss adapters now compose into the Azuma-constant
    high-probability stability surface for finite measurable hypothesis
    interfaces.
  - Next refinements: sharpen the high-probability constants through
    product-kernel decomposition, or add concrete algorithm-specific
    stability examples.

- [ ] **Localized Rademacher — random-threshold concentration refinement**
  - The deterministic fixed-point certificate layer is closed.
  - The deterministic localized deviation certificate shell is closed.
  - The localized upper-deviation event adapter is closed.
  - The event-facing finite fast-rate wrapper is closed.
  - The finite weighted concentration adapter for the localized
    upper-deviation event is closed.
  - The pointwise exponential-moment-to-tail adapter is closed.
  - The finite iid product MGF bridge for localized excess losses is closed.
  - The bounded-excess one-coordinate MGF instantiation is closed for
    pointwise `[-1,1]` excess losses.
  - The fixed-threshold event payoff is closed.
  - The fixed-threshold high-confidence finite-class theorem is closed.
  - The sample-dependent fast-rate event interface is closed.
  - A conservative bad-event mass bridge for the named sample-dependent
    fast-rate event is closed by reducing it to the fixed-`ε` bounded-excess
    theorem.
  - The sample-dependent pointwise union-bound and shifted exponential-moment
    adapters are closed.
  - The conservative shifted-moment instantiation through the fixed-`ε`
    lower envelope is closed under bounded excess losses.
  - The centered shifted-moment interface is closed as an *algebraic* layer:
    only the fixed slack is factored out, while the empirical localized
    complexity term stays syntactically inside the pointwise moment budget.
    This layer is conservative-only — each per-hypothesis centered moment is
    pointwise at most the fixed moment (nonnegativity of `R̂_loc`), so the
    union bound over it cannot beat the conservative fixed-threshold bound.
  - The finite Bernstein variance-localization route is now closed locally:
    `localizedFiniteClassBernsteinHighConfidence_empirical_nonpos` combines a
    reusable Bennett/Bernstein MGF layer, an averaged Bernstein tail, the
    localized variance proxy `c·r`, a finite union bound, and the fixed-threshold
    payoff. The theorem still assumes global `[-1,1]` excess-loss bounds and
    `0 < c·r`.
  - Next non-conservative direction: whole-supremum random-threshold
      concentration of `localizedUpperDeviation - 2·R̂_loc`, via localized
      symmetrization (`expected_genGap_le_two_expected_empiricalRademacherComplexity`)
      and McDiarmid/Azuma (`genGap_tail_bound_azuma`). Both ingredients already
      exist for the global generalization gap but in the measure-theoretic
      world; the work is bridging them to the finite-weight localized layer.
  - Then consider sub-Gaussian or Bernstein-style excess-loss MGF
    instantiations if the hypotheses can be stated cleanly.
  - Target a finite fast-rate/oracle-inequality scaffold without claiming
    infinite-class or measurable-supremum generality.

- [ ] **Continuous Dudley entropy-integral lift**
  - The finite-terminal and projected-sup dyadic wrappers are closed.
  - The finite dyadic budget now compares to a supplied entropy-at-radius
    upper sum/integral budget for projected finite nets.
  - Next, prove an analytic domination theorem from that finite upper sum to
    an actual Riemann/Lebesgue entropy integral under monotonicity and
    integrability assumptions.
  - Do not claim separability, measurable arbitrary suprema, or the continuous
    entropy integral until those layers are proved.

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
  - Remaining PAC-Bayes extensions: exact all-real-`λ` optimization,
    continuous posteriors, and infinite hypothesis classes.

### Long-term

- [ ] **Full Dudley entropy integral**
  - Continuous covering number integral
  - Generic chaining (Talagrand)

- [ ] **Minimax lower bounds**
  - Fano, Assouad, Le Cam
  - Matching the upper bounds

## Design Principles

1. **One theorem per PR.** Each result is a focused addition.
2. **No sorry/admit.** Every merged theorem is fully proved.
3. **Axioms: [propext, Classical.choice, Quot.sound] only.**
4. **Assumptions stated in types.** If a theorem requires bounded loss, the type signature says so.
5. **Scope documented.** Public summaries distinguish closed theorems from
   current boundaries and future work.
