# Next lane: continuous / total-bounded Dudley bridge

Status on `release-candidate` after `v0.1.0-rc1`: the finite Dudley
entropy-budget chain, total-bounded finite-net bridge, truncated
interval-integral comparison, and supplied-supremum boundary adapter are
closed.
The PAC-Bayes finite confidence layer (Catoni-style, fixed-budget McAllester,
finite-grid peeling, posterior-dependent grid wrapper) is closed. The
Bousquet-Elisseeff sharp high-probability stability bound is closed with
bounded-loss adapters. With the finite spine stable, the next lane is the
continuous/total-bounded extension of the Dudley layer.

This document tracks the lane plan and the bridge steps already started. The
current Lean layer extracts finite nets from `TotallyBounded Set.univ`, adds a
dyadic net schedule whose adjacent radii match the finite chaining radius
budget, composes that schedule with the existing finite entropy-budget theorem
in a finite-terminal wrapper, adds projected finite-net wrappers that no
longer require an identity terminal net, replaces the finite ambient index
assumption with a supremum over the terminal finite-net image, and compares
the finite dyadic budget with a supplied entropy-at-radius upper-sum/integral
budget, and transfers the projected finite-net bound to a caller-supplied
supremum functional under an explicit terminal approximation error.

## Lane branch

Current code is on `release-candidate`. The next theorem branch should start
from that branch after the supplied-supremum boundary adapter, not from the
older dyadic upper-sum branch.

## Goal

Lift the finite covering-number chaining wrappers in
`FormalSLT.Covering.FiniteSubGaussianChaining` to a total-bounded metric-space
statement so that the conclusion can be stated for an arbitrary totally
bounded index set rather than `[Fintype T]`.

The target shape, in informal notation, is:

```
E sup_{t ∈ T} X_t ≤ C * ∫_0^D √(log N(T, d, ε)) dε
```

where `T` is totally bounded under a pseudo-metric `d` of diameter `D`,
`X_t` is a centered sub-Gaussian process indexed by `T`, `N(T, d, ε)` is
the covering number at scale `ε`, and the integral is the Riemann/Lebesgue
entropy integral.

For this lane we are not yet aiming at the full continuous Dudley integral;
the first concrete target is a **total-bounded dyadic Dudley wrapper** that
replaces `[Fintype T]` and explicit per-scale finite nets with an existence
hypothesis "for every `j ≤ m`, there is a `2^{-j}·D`-net of size at most
`Nj`". This isolates the topological lift from the analytic step of passing
from finite dyadic sums to the continuous integral.

## Existing finite ingredients (do not re-prove)

These already exist in [FormalSLT/Covering/FiniteSubGaussianChaining.lean](../FormalSLT/Covering/FiniteSubGaussianChaining.lean)
and are the intended dependency boundary of the new layer:

- `finite_dudley_entropy_sum_coveringNumbers_geometric_integral_budget`
 : finite dyadic entropy-integral budget for finite covering numbers with a
  user-supplied envelope.
- `finite_dudley_entropy_sum_coveringNumbers_geometric_integral_budget_prefix_envelope`
 : same with a prefix-sup envelope built from finite cover counts.
- `finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_integral_budget_prefix_envelope`
 : projected finite-net-image wrapper that does not assume `[Fintype T]`.
- `finiteDyadicEntropyAtRadiusUpperSum`
 : finite dyadic entropy-at-radius upper sum sampled at lower annulus
  endpoints.
- `finiteDyadicEntropyIntegralBudget_le_entropyAtRadiusUpperSum`
 : finite comparison from the dyadic prefix-envelope budget to that upper
  sum.
- `finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_entropy_integral_comparison`
 : projected finite-net-image wrapper with a supplied entropy-at-radius
  upper-sum/integral budget.
- `shiftedDyadicIntervalIntegralSum_eq_truncatedIntervalIntegral`
 : the finite shifted-annulus interval integrals collapse to one truncated
  interval integral.
- `finiteDyadicEntropyAtRadiusUpperSum_le_two_mul_truncatedIntervalIntegral`
 : the entropy-at-radius upper sum is dominated by that truncated interval
  integral under antitonicity and interval-integrability assumptions.
- `finite_supFunctional_dudley_entropy_sum_coveringNumbers_geometric_entropy_truncatedIntervalIntegral_comparison`
 : boundary-layer finite Dudley wrapper for a supplied supremum functional
  plus terminal approximation error.
- `finite_dudley_entropy_sum_coveringNumbers_geometric_uniform_entropy`
 : dyadic sum collapses to `2 * radiusScale` budget under a uniform per-scale
  entropy cap.
- `finite_dudley_entropy_sum_coveringNumbers_geometric_annulus_budget`
 : dyadic annulus-width Riemann-style upper sum.
- `finiteDyadicEntropyIntegralBudget`: the dyadic upper-sum
  functional that the continuous integral will eventually dominate.
- `finitePrefixSupEnvelope`: monotone prefix-sup helper.

Everything below is **new** and built on top of these.

## First bridge now available

The first bridge lives in
[FormalSLT/Covering/TotalBoundedDudley.lean](../FormalSLT/Covering/TotalBoundedDudley.lean):

- `finiteMetricCoverOfTotallyBoundedUniv` extracts finite metric covers from
  `TotallyBounded Set.univ` at each positive real radius.
- `finiteNetOfTotallyBoundedUniv` converts those covers into the repo's
  explicit `FiniteNet` records.
- `dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_le` supplies the
  adjacent-radius inequality needed by the finite chaining API.
- `finite_projectedNet_dudley_entropy_sum_totalBounded_dyadic_coveringNumbers`
  composes the dyadic total-bounded schedule with the projected finite-net
  entropy-budget theorem, bounding the terminal finite-net-image supremum
  without assuming `[Fintype T]`.
- `finite_projectedNet_dudley_entropy_sum_totalBounded_dyadic_entropy_integral_comparison`
  composes the same projected finite-net schedule with a supplied
  entropy-at-radius upper-sum/integral budget.
- `finite_projectedNet_dudley_entropy_sum_totalBounded_dyadic_entropy_intervalIntegral_comparison`
  discharges that finite upper-sum budget from an antitone entropy profile,
  per-annulus interval-integrability, and a finite shifted-annulus integral
  budget. The comparison has the dyadic constant from moving each lower-endpoint
  rectangle to the next annulus.
- `finite_projectedNet_dudley_entropy_sum_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison`
  collapses the shifted finite-annulus budget to a single truncated interval
  integral.
- `finite_supFunctional_dudley_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison`
  transfers the total-bounded projected finite-net Dudley wrapper to a
  caller-supplied supremum functional under an explicit terminal approximation
  error.
- `finite_projected_dudley_entropy_sum_totalBounded_dyadic_coveringNumbers`
  keeps the older finite-ambient projected-sup wrapper for comparison.
- `finite_dudley_entropy_sum_totalBounded_dyadic_coveringNumbers` composes the
  total-bounded dyadic schedule with the finite Dudley entropy-budget theorem,
  using an identity terminal net on a finite index type.
- `totalBoundedCoveringNumberAtRadius` in
  [FormalSLT/Covering/TotalBoundedDudleyCovering.lean](../FormalSLT/Covering/TotalBoundedDudleyCovering.lean)
  packages the selected adjacent dyadic cover-count products into a half-open,
  right-closed real-radius staircase, exposes a finite `ℕ∞` surface, proves the
  guarded closed-annulus entropy condition, and supplies a unit-interval
  non-vacuity witness. This is a selected-net cover-count surface, not the
  minimal metric covering-number theorem.
- `minimalMetricCoveringNumber` in
  [FormalSLT/Covering/TotalBoundedMinimalCovering.lean](../FormalSLT/Covering/TotalBoundedMinimalCovering.lean)
  defines the genuine minimal finite metric covering number at positive radius
  for nonempty totally bounded metric spaces. It proves the valid comparison
  `N_min(T, d, ε_j) ≤ selected_j` at each dyadic selected-net radius, and hence
  `N_min(T, d, ε_j) ≤ selectedEnvelope_j`. This supplies the genuine
  covering-number surface, but it does not by itself justify replacing the
  selected-count entropy upper envelope by the smaller minimal-count entropy in
  the current upper-bound Dudley theorem.
- The same module now also proves the route (a) extractor probe:
  `minimalMetricCoverOfTotallyBoundedUniv` chooses a cardinal-minimal finite
  cover from the `minimalMetricCoveringNumber` witness, packages it as
  `minimalFiniteNetOfTotallyBoundedUniv`, and exposes
  `minimalDyadicChainingFiniteNetOfTotallyBoundedUniv_coveringNumber_eq` at
  each dyadic sampled radius. This avoids adding a separate "covers are
  minimal" hypothesis.
- `continuous_dudley_entropy_integral_iSup_totalBounded_selectedCoverCountEnvelope_not_minimalCoveringNumber`
  in
  [FormalSLT/Covering/TotalBoundedDudleySelectedCapstone.lean](../FormalSLT/Covering/TotalBoundedDudleySelectedCapstone.lean)
  closes the guarded continuous-Dudley capstone for arbitrary totally bounded
  metric index spaces under the existing finite boundary-certificate
  hypothesis. Its entropy integrand is the selected-cover-count envelope
  `totalBoundedCoveringEntropyAtRadius hT hradiusScale`, not the genuine
  minimal covering number.
- `continuous_dudley_entropy_integral_iSup_totalBounded_minimalDyadicCoverCountEnvelope`
  in
  [FormalSLT/Covering/TotalBoundedDudleyMinimalCapstone.lean](../FormalSLT/Covering/TotalBoundedDudleyMinimalCapstone.lean)
  threads the cardinal-minimal dyadic net schedule through the projected
  finite-chain wrapper, rebuilds the half-open real-radius staircase, and
  composes it with the guarded continuous-Dudley wrapper. Its entropy integrand
  is the adjacent-product envelope from cardinal-minimal dyadic covers; each
  factor is a genuine `minimalMetricCoveringNumber`, but the surface is not a
  pure one-radius `sqrt(log N(T,d,ε))` integrand.

The remaining minimal-covering-number work is the tighter one-radius
`sqrt(log N(T,d,ε))` surface, which would need a projection-pair entropy
tightening or another theorem replacing adjacent products by a single-radius
minimal covering number.

## Mathlib tooling available

The lift can use, from current Mathlib:

- `Mathlib.Topology.MetricSpace.Basic`: `PseudoMetricSpace` and friends.
- `Mathlib.Topology.UniformSpace.Cauchy.TotallyBounded` :
  `TotallyBounded` predicate on subsets of a uniform space; the metric
  specialization gives "for every `ε > 0` there is a finite `ε`-net".
- `Mathlib.MeasureTheory.Covering.Vitali` and friends: covering-number
  apparatus; we will mostly only need a bare definition of `coveringNumber`
  rather than Vitali itself.
- `Mathlib.MeasureTheory.Integral.IntervalIntegral` and
  `Mathlib.MeasureTheory.Integral.Lebesgue`: for the Lebesgue/Riemann
  approximation step from dyadic sums to a `∫_0^D` integral.
- `Mathlib.Topology.MetricSpace.Bounded`: `Metric.diam` for the diameter
  hypothesis on `T`.
- `Mathlib.Topology.MetricSpace.Polish` /
  `MeasureTheory.Measure.IsSeparable`: only if a measurable-supremum
  layer is added; the first-pass target should keep `T` as a generic set
  with a sub-Gaussian process whose supremum is treated through monotone
  finite approximations rather than measurable suprema.

## Target signature (first-pass)

```lean
theorem totallyBounded_dudley_expectedSup_le_dyadicIntegralBudget
    {Ω T : Type*}
    [PseudoMetricSpace T] [Nonempty T]
    (P : SubGaussianProcess Ω T)               -- new generalization of
                                               -- FiniteSubGaussianProcess
    (D : ℝ) (m : ℕ) (coarseBudget radiusScale : ℝ)
    (coverCount : ℕ → ℕ)
    (htotallyBounded : TotallyBounded (Set.univ : Set T))
    (hdiameter : Metric.diam (Set.univ : Set T) ≤ D)
    (hvariance : 0 < P.varianceProxy)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hradiusScale_geom : D ≤ radiusScale)
    (hcoverCount : ∀ j ∈ Finset.range m,
      ∃ S : Finset T,
        S.card ≤ coverCount j ∧
        ∀ t : T, ∃ s ∈ S, P.dist t s ≤ radiusScale / (2 : ℝ) ^ j)
    (hcoarse :
      P.expectedSupAt (radiusScale / (2 : ℝ) ^ 0) ≤ coarseBudget) :
    P.expectedSup ≤
      coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
        finiteDyadicEntropyIntegralBudget radiusScale m
          (finitePrefixSupEnvelope
            (fun j => Real.sqrt (Real.log (coverCount j : ℝ))))
```

Names and exact hypotheses are tentative. The two structural changes from
the finite version are:

1. `[Fintype T]` is replaced by `TotallyBounded` plus a finite
   `coverCount j` per scale. The finite per-scale net is given as a
   `Finset T` so that the dyadic chaining argument can still reuse the
   existing finite-net plumbing under the hood.
2. `FiniteSubGaussianProcess` is replaced by a more general
   `SubGaussianProcess` structure that does **not** require `[Fintype Ω]`.
   The first-pass implementation can keep `[Fintype Ω]` and only relax the
   index type `T`; relaxing `Ω` is a separate sub-step.

A second-pass theorem (after the dyadic wrapper is closed) replaces the
finite dyadic sum with a Lebesgue/Riemann integral on `[0, D]`:

```lean
theorem totallyBounded_dudley_expectedSup_le_continuousIntegral
    ... (similar hypotheses) ...
    (hentropyIntegrable : IntervalIntegrable
        (fun ε => Real.sqrt (Real.log (coveringNumber T P.dist ε)))
        MeasureTheory.volume 0 D) :
    P.expectedSup ≤
      coarseBudget +
        C * ∫ ε in (0 : ℝ)..D,
          Real.sqrt (Real.log (coveringNumber T P.dist ε))
```

This is the "true" continuous Dudley statement. It should be reached
**only after** the dyadic total-bounded wrapper above is closed.

## Intermediate steps

The lane should land in this order, one PR per step:

0. **Step C0: total-bounded finite-net extraction.** Closed as the first
   bridge layer: total boundedness gives bundled finite nets at positive
   radii, plus a dyadic schedule compatible with the finite chaining radius
   hypothesis.

0.5. **Step C0.5: finite-terminal dyadic wrapper.** Closed as the first
   composition theorem: the total-bounded dyadic schedule feeds the existing
   finite Dudley entropy-budget theorem, with an identity terminal net on a
   finite index type.

0.75. **Step C0.75: projected-sup dyadic wrapper.** Closed as the first
   non-identity-terminal theorem: the total-bounded dyadic schedule feeds a
   projected finite Dudley entropy-budget theorem and bounds the terminal
   projected supremum.

1. **Step C1: abstract `SubGaussianProcess` structure.** Generalize
   `FiniteSubGaussianProcess` so that `T` is allowed to be any type with
   a pseudo-metric. Keep the finite-`Ω` weight machinery and re-derive
   `expectedSup`, `varianceProxy`, etc., on the new structure. Existing
   `finite_*` theorems get the new structure as their input.

2. **Step C2: extracted-net-from-totally-bounded API.** A small
   constructor `coveringFiniteNet : TotallyBounded ⇒ ε > 0 ⇒ FiniteNet T A`
   that selects a finite ε-net and witnesses the nearest-projection map.
   This isolates the topological extraction from the dyadic chaining
   argument. The existing finite chaining theorems take `FiniteNet` inputs,
   so this constructor is the bridge.

3. **Step C3: finite-index boundary lift for projected nets.** The identity
   terminal boundary is now relaxed for finite-index projected suprema. Next,
   state the projected supremum directly over the finite terminal net's center
   type, rather than over `[Fintype T]`, and translate finite-net cover counts
   through the total-bounded hypothesis.

4. **Step C4: Riemann-step bridge.** Closed through the truncated
   interval-integral comparison: the finite dyadic upper sum is controlled by
   twice a single truncated interval integral under antitonicity and
   interval-integrability assumptions. The supplied-supremum boundary adapter
   is also closed with an explicit terminal approximation error. This is the
   analytic step toward continuous integral language, but it does **not** prove
   separability or measurable arbitrary suprema.

4.5. **Step C4.5: selected-cover-count staircase.** Closed by
   `Covering.TotalBoundedDudleyCovering`: the adjacent cover counts selected by
   total boundedness are wrapped in a monotone prefix envelope and realized as a
   half-open real-radius staircase. The resulting entropy profile satisfies the
   guarded dyadic annulus condition and dominates the finite dyadic entropy
   envelope at dyadic samples. This keeps the proof on selected finite nets; it
   does not identify these counts with the minimal metric covering number
   `N(T, d, ε)`.

4.6. **Step C4.6: genuine minimal-covering-number surface.** Closed by
   `Covering.TotalBoundedMinimalCovering`: define `minimalMetricCoveringNumber`
   from finite metric covers, prove its specification and minimality, prove it
   is positive on nonempty spaces, and compare it to the selected total-bounded
   dyadic covers. The proved direction is
   `minimalMetricCoveringNumber ≤ selected cover count`; this is the only
   direction available for arbitrary selected covers. The later cardinal-minimal
   extractor avoids this arbitrary-selection obstruction by changing the chosen
   net schedule, not by adding a minimality hypothesis.

4.6.1. **Step C4.6.1: cardinal-minimal extractor probe.** Closed by
   `Covering.TotalBoundedMinimalCovering`: choose cardinal-minimal finite
   covers directly from `minimalMetricCoveringNumber`, convert them to
   `BundledFiniteNet`s, and build a dyadic minimal-net schedule whose
   `coveringNumber` is definitionally tied to the genuine minimal covering
   number at each sampled radius. This is route (a); it does not add a
   separate minimality hypothesis.

4.7. **Step C4.7: selected-cover-count continuous capstone.** Closed by
   `Covering.TotalBoundedDudleySelectedCapstone`: compose the selected-count
   guarded staircase into
   `continuous_dudley_entropy_integral_iSup_of_dyadicProfile_guarded`. The
   resulting continuous integral bound is generic over totally bounded metric
   index spaces, but its integrand is explicitly the selected-cover-count
   envelope, not `minimalMetricCoveringNumber`.

5. **Step C5: cardinal-minimal dyadic product capstone.** Closed by
   `Covering.TotalBoundedDudleyMinimalCapstone`: thread the
   cardinal-minimal dyadic net schedule through the finite projected-chain
   wrapper, build the real-radius half-open staircase, prove the guarded
   annulus property, and compose with the guarded continuous-Dudley assembly.
   This removes arbitrary selected-cover counts from the net schedule, but the
   finite chaining entropy still uses adjacent products of minimal counts.

5.1. **Step C5.1: pure one-radius minimal-`N` tightening.** Remaining:
   replace the adjacent-product envelope by a single-radius genuine
   `minimalMetricCoveringNumber` integrand. This needs a projection-pair
   entropy tightening or an explicit theorem bounding the adjacent-product
   entropy by the target one-radius minimal-covering-number profile.

6. **Step C6: measurable-supremum layer (optional, separate lane).**
   Promoting `expectedSup` from a finite-`Ω` sum to a Bochner integral
   over a probability space requires a measurable-supremum theory (Talagrand
   suprema, separable processes, etc.). This is intentionally **out of
   scope** for the first lane. Adding it should be its own lane.

## Boundaries (do not claim until proved)

- The lane should not claim a full empirical-process theorem for arbitrary
  classes of functions until Step C6 is also closed.
- The lane should not claim that downstream Rademacher or VC wrappers have
  inherited the sharp McDiarmid constant until those wrappers are explicitly
  rewired to `Azuma.GenGapTail`.
- The lane should not promise a generic-chaining (`γ_2`-style) statement;
  Talagrand-style admissible-sequence bounds are explicitly longer-term.

## Acceptance criteria for landing

A PR on `feat/lean-continuous-dudley-total-bounded` is considered ready to
merge to `release-candidate` when:

- the target theorem signature is exactly as agreed in this document (or
  this document is updated alongside the PR if the signature must move);
- the proof contains no `sorry`, no `admit`, and no custom `axiom`;
- `[propext, Classical.choice, Quot.sound]` remain the only axioms used;
- a `examples/Check*` companion checks the final theorem and prints its
  axioms;
- `docs/theorem-map.md` and `docs/roadmap.md` are updated to match.

## Branch protection (pre-public-launch)

Before making the release repo public, the maintainer should
configure GitHub branch protection on `release-candidate`:

- **Settings → Branches → Add rule** for branch name pattern
  `release-candidate`.
- Enable: **Require a pull request before merging**, with at least one
  approving review.
- Enable: **Require status checks to pass before merging**, and select the
  `CI` workflow (the badge in `README.md`).
- Enable: **Require linear history** (or at minimum **Do not allow bypassing
  the above settings**).
- Disable: **Allow force pushes** and **Allow deletions** for this branch.

The same protections should be replicated on `main` once the public
default branch is created from `release-candidate`.
