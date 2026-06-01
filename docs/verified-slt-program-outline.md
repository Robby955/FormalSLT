# Verified SLT Program Outline

This note describes the current FormalSLT proof spine as a reusable workbench
for finite-class, finite-net, empirical-process, concentration, and
anytime-valid statistical learning theory.

The current checked development has two complementary directions:

1. analytic covering machinery, used by the non-finite `[0,1]` Dudley example;
2. finite-class probability-budget machinery, used by the emerging
   finite-prefix uniform-convergence route.

The current flagship theorem layer is the finite-class anytime empirical-average
deviation theorem. The code now has the countable-time shell on top of the
finite-prefix version: finite union budgets, dyadic time budgets, fixed
Hoeffding tails, shared-sample wrappers, a uniform range-width interface, and a
natural-time union bound over `N x H`.
The latest theorem layer instantiates the per-time, per-class real failure
budget with the concrete dyadic schedule
`δ * 2^(-1-t) / card(H)`, so callers no longer need to supply the
`ENNReal.ofReal` budget comparison manually. It also exposes the same
finite-prefix event bound through a square-root radius hypothesis, which is the
form a theorem statement can display when the sample size is already fixed.
The latest wrapper compresses the per-time radius hypotheses into one
finite-horizon radius using the smallest dyadic budget in the prefix.
The newest algebra layer rewrites that horizon log budget into the closed form
`log((2 : R)^(T + 1) * card(H) / δ_real)`, which is the display shape expected
from a finite-prefix class-and-time union bound.
The current theorem layer also exposes the same result in sample-size form:
`R^2 / (2 * ε^2) * log((2 : R)^(T + 1) * card(H) / δ_real) <= sampleSize`.
The newest route-facing layer substitutes the displayed unit-range confidence
radius directly into the deviation event, so the teaching theorem no longer
carries a separate caller-supplied `ε` threshold. The latest bounded-loss layer
specializes that theorem to losses in `[0,1]`, removing the caller-supplied
lower and upper range functions from the first route-facing statement and
discharging the negative-integral identity internally with `integral_neg`.
The newest time-varying layer adds threshold-aware finite-prefix union shells
and a route-facing dyadic-radius theorem. That theorem uses the actual per-time
budget `δ * 2^(-1-t) / card(H)` at time `t`. The latest theorem discharges the
pointwise tail at that radius from the fixed-hypothesis Hoeffding wrappers and
checks the finite-prefix union step plus `ENNReal.ofReal` dyadic class-budget
conversion.
The newest countable-time layer proves the full dyadic budget sum, packages a
summable natural-time finite-class union shell, and exposes the corresponding
anytime event over all `(t, h) : N x H` for `[0,1]` losses.
The route-facing version rewrites the indexed union as an existential event,
so the statement reads as "there exists a time and hypothesis whose deviation
crosses its dyadic radius."
The newest wrapper names that radius and states the confidence-sequence failure
event directly: the probability that the simultaneous all-times/all-hypotheses
strict bound fails is at most `δ`.

## Current Checked Spine

### Finite Union Budgets

Module: `FormalSLT.Probability.FiniteUnionBound`

Core declarations:

- `finiteMeasureUnionBound`
- `finiteMeasureUnionBound_budget`
- `finiteMeasureUnionBound_const`
- `finiteMeasureUnionBound_equalBudget`
- `finiteMeasureUnionBound_cardInv`

Role: these declarations isolate the finite probability bookkeeping. Later
theorems can reason about per-event budgets and total failure budgets without
reproving finite union bounds.

### Finite-Time Uniform-Convergence Shell

Module: `FormalSLT.UniformConvergence`

Core declarations:

- `finiteTimeClassUnionBound_timeBudget`
- `finiteTimeClassTwoSidedUniformDeviationUnionBound_timeBudget`
- `finiteTimeClassTwoSidedUniformDeviationUnionBound_timeBudget_threshold`
- `finiteDyadicTimeBudget`
- `finiteDyadicTimeBudget_sum_fin_le`
- `finiteDyadicTimeBudget_tsum_le`
- `countableTimeClassUnionBound_timeBudget`
- `countableTimeClassUnionBound_dyadicBudget`
- `countableTimeClassTwoSidedUniformDeviationUnionBound_dyadicBudget_threshold`
- `countableTimeClass_iUnion_eq_exists`
- `countableTimeClass_not_forall_lt_eq_exists_ge`
- `finiteTimeClassTwoSidedUniformDeviationUnionBound_dyadicBudget_threshold`
- `finiteTimeClassTwoSidedUnionBoundFromOneSidedTails_dyadicBudget`

Role: these declarations turn pointwise one-sided or two-sided tails into
simultaneous finite-horizon and natural-time statements over
`(time, hypothesis)` pairs.

### Hoeffding and Shared-Sample Layer

Module: `FormalSLT.UniformConvergence`

Core declarations:

- `empiricalAverageUpperHoeffdingTail`
- `empiricalAverageLowerHoeffdingTail`
- `empiricalAverageUpperHoeffdingTail_eq_lower`
- `empiricalAverageTwoSidedHoeffdingTail`
- `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_twoSidedTailBudget`
- `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_uniformRangeBudget`

Role: these declarations connect bounded independent empirical averages to the
finite-time finite-class probability shell.

### Uniform Range-Width Interface

Module: `FormalSLT.UniformConvergence`

Core declarations:

- `empiricalAverageUniformRangeTwoSidedHoeffdingTail`
- `empiricalAverageTwoSidedHoeffdingTail_le_uniformRangeTwoSidedHoeffdingTail`
- `empiricalAverageRangeSum_le_card_mul_uniformRange`
- `empiricalAverageRangeSum_pos_of_exists_range_pos`
- `empiricalAverageTwoSidedHoeffdingTail_le_uniformRangeTwoSidedHoeffdingTail_of_rangeBound_of_exists_range_pos`
- `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_uniformRangeBudget_of_rangeBound_of_exists_range_pos`
- `empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail`
- `empiricalAverageUniformRangeTwoSidedHoeffdingTail_eq_sampleSizeTail`
- `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize`
- `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_threshold`
- `empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail_le_of_logBudget`
- `empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail_le_of_explicitRadius`
- `empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail_le_of_sampleSize_ge`
- `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_from_logBudget`
- `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_ge`
- `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_dyadicRealBudget`
- `finiteDyadicRealBudget_classBudget_ofReal`
- `empiricalAverageUniformRangeSampleSize_ge_of_sqrtBudget_le`
- `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_epsilonOfSampleSize_dyadicRealBudget`
- `finiteDyadicRealBudget_horizon_le_time`
- `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_horizonUniformRadius_dyadicRealBudget`
- `finiteDyadicRealBudget_horizon_logBudget_eq_closedForm`
- `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_closedFormHorizonRadius_dyadicRealBudget`
- `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_closedFormHorizonSampleSize_dyadicRealBudget`
- `finitePrefixFiniteClassDeviationFromHoeffding_closedForm`
- `finitePrefixFiniteClassDeviationFromHoeffding_closedForm_cardSample`
- `finitePrefixFiniteClassDeviationFromHoeffding_closedForm_unitRange`
- `finitePrefixFiniteClassDeviationFromHoeffding_unitRange_radius`
- `finitePrefixFiniteClassDeviationFromHoeffding_unitRange_explicitRadius`
- `finitePrefixFiniteClassDeviationFromHoeffding_unitRange_explicitRadius_nonemptySample`
- `finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_explicitRadius`
- `finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius`
- `finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius_fromHoeffding`
- `zeroOneDyadicFiniteClassConfidenceRadius`
- `anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius_fromHoeffding`
- `anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius_exists_fromHoeffding`
- `anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_namedRadius_exists_fromHoeffding`
- `anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_confidenceSequence_fromHoeffding`

Role: these declarations replace per-hypothesis finite range sums with one
uniform range width `R` and one closed-form proxy `card(s) * (R / 2)^2`, while
keeping a concrete nondegeneracy certificate for the Hoeffding denominator. The
sample-size display packages that proxy as the usual
`2 * exp(-2 * sampleSize * ε^2 / R^2)` tail budget. The log-budget layer then
connects that displayed tail to real-valued per-time budgets before comparing
them to the dyadic `ENNReal` budget split. The sample-size lower-bound layer
packages the common closed-form sufficient condition
`sampleSize >= R^2 / (2 * ε^2) * (log 2 - log realBudget)`. The radius layer
then derives the same sample-size condition from a square-root hypothesis of
the form
`sqrt(R^2 / (2 * sampleSize) * (log 2 - log realBudget)) <= ε`.
The finite-horizon radius wrapper then uses dyadic-budget monotonicity to
replace the per-time radius hypotheses by one common horizon-level radius.
The closed-form horizon wrapper then rewrites the remaining log-budget side
condition into `log((2 : R)^(T + 1) * card(H) / δ_real)`.
The closed-form sample-size wrapper presents the same finite-prefix event bound
through the displayed sample-complexity inequality. The route-facing wrapper
keeps that checked proof chain while giving the theorem a shorter name for the
program outline and teaching route. The card-sample wrapper removes the
separate sample-size parameter from the final display and writes the empirical
average denominator directly as `(s.card : R)`. The unit-range wrapper
specializes this route-facing theorem to `R = 1`, leaving the finite horizon,
finite class size, confidence budget, sample size, and deviation threshold as
the displayed parameters. The unit-range radius wrapper presents the same bound
from a displayed confidence-radius side condition. The explicit-radius wrapper
writes that radius directly in the finite-class deviation event. The strict
budget wrapper then proves radius positivity from a nonempty sample and
`δ_real < 2^(T + 1) * card(H)`. The zero-one bounded-loss wrapper then
specializes the same theorem to losses bounded in `[0,1]`.
The time-varying dyadic-radius wrapper then exposes the finite-prefix event
shape needed for an anytime theorem: it keeps a separate confidence radius at
each time. The stronger wrapper discharges those pointwise tails from the
fixed-hypothesis Hoeffding layer for losses bounded in `[0,1]`.
The countable-time wrapper then uses the full dyadic time-budget sum and the
finite-class split at each natural time to prove the event over all
`(t, h) : N x H`.
The existential wrapper rewrites that same bound into the form used by the
technical note and route prose.
The named-radius and confidence-sequence wrappers then expose the same checked
probability core in a form closer to standard time-uniform concentration
statements.

### Dyadic Real-Budget Interface

Module: `FormalSLT.UniformConvergence`

Core declaration:

- `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_dyadicRealBudget`
- `finiteDyadicRealBudget_classBudget_ofReal`
- `empiricalAverageUniformRangeSampleSize_ge_of_sqrtBudget_le`
- `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_epsilonOfSampleSize_dyadicRealBudget`
- `finiteDyadicRealBudget_horizon_le_time`
- `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_horizonUniformRadius_dyadicRealBudget`
- `finiteDyadicRealBudget_horizon_logBudget_eq_closedForm`
- `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_closedFormHorizonRadius_dyadicRealBudget`
- `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_closedFormHorizonSampleSize_dyadicRealBudget`
- `finitePrefixFiniteClassDeviationFromHoeffding_closedForm`
- `finitePrefixFiniteClassDeviationFromHoeffding_closedForm_cardSample`
- `finitePrefixFiniteClassDeviationFromHoeffding_closedForm_unitRange`
- `finitePrefixFiniteClassDeviationFromHoeffding_unitRange_radius`
- `finitePrefixFiniteClassDeviationFromHoeffding_unitRange_explicitRadius`
- `finitePrefixFiniteClassDeviationFromHoeffding_unitRange_explicitRadius_nonemptySample`
- `finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_explicitRadius`
- `finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius`
- `finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius_fromHoeffding`

Role: this declaration chooses the concrete real budget
`δ * 2^(-1-t) / card(H)` and proves that its `ENNReal.ofReal` image is below
the dyadic time/class split. The theorem still assumes a finite horizon and a
positive real total budget. The sample-size theorem exposes the displayed
textbook-style lower bound with no caller-supplied budget comparison. The
radius theorem exposes the equivalent user-facing shape where a fixed sample
size controls the deviation threshold. The horizon-uniform theorem replaces
the per-time radius side condition by one finite-prefix side condition using
the budget at the last possible time in `Fin T`. The closed-form horizon theorem
then presents the same bound with one log-card term depending only on the
finite horizon, class cardinality, and total real budget.
The closed-form sample-size theorem gives the same finite-prefix event bound in
the standard sample-size lower-bound display. The route-facing wrapper exposes
that final statement under a compact theorem name. The card-sample wrapper
presents the same bound with the sample denominator written directly in terms of
the checked finite sample set. The unit-range wrapper is the most compact
sample-size theorem surface for exposition. The unit-range radius wrapper gives
the companion radius-form statement, and the explicit-radius wrapper removes the
separate `ε` parameter from the route-facing event. The nonempty-sample wrapper
removes the raw radius-positivity hypothesis using a strict finite-prefix budget
condition. The zero-one bounded-loss wrapper removes the lower and upper range
function parameters for the first compact finite-class theorem surface and
discharges the negative-integral identity internally.
The time-varying shell is deliberately factored in two: one theorem consumes
pointwise tails at the displayed per-time radius, and the stronger theorem
discharges those tails from the fixed-hypothesis Hoeffding wrappers. This keeps
the route-facing event shape available without one oversized proof term.

### Finite-Net and Dudley Direction

Modules:

- `FormalSLT.Covering.FiniteSubGaussianChaining`
- `FormalSLT.Covering.UnitIntervalDudley`

Core declarations include:

- `FiniteNet`
- `finite_chaining_expectation_bound`
- `finite_projectedNet_chaining_expectation_bound_of_net_sequence_coveringNumbers_sqrt`
- `unitIntervalRoundedDyadicGridNet`
- `unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound`

Role: these declarations show how finite-net machinery reaches a non-finite
index type through explicit finite projections and checked dyadic grids.

## Current Flagship Theorem

Target name:

```lean
finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_explicitRadius
```

Target statement shape:

For a finite horizon `Fin T`, finite hypothesis class `H`, shared finite sample
set `s`, independent losses bounded in `[0,1]`, and total budget `δ`, prove a
simultaneous bound

```lean
μ (⋃ p : Fin T × H,
    {ω |
      sqrt(log((2 : R)^(T + 1) * card(H) / δ_real)
        / (2 * (s.card : R))) ≤
        |risk p.1 p.2 / (s.card : R) -
          (∑ i ∈ s, loss p.1 p.2 i ω) / (s.card : R)|}) ≤ δ
```

from the finite-prefix budget condition

```text
δ_real < (2 : R)^(T + 1) * card(H)
```

The theorem surface now has the event bound, the dyadic real budget, the
range-proxy-to-sample-size algebra, the radius-to-sample-size algebra, and the
finite-horizon dyadic monotonicity and closed-form log-budget rewrites checked
in one finite-prefix sample-size chain. The route-facing wrappers delegate to
the longer
`finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_closedFormHorizonSampleSize_dyadicRealBudget`
theorem, with the card-sample wrapper substituting `sampleSize = (s.card : R)`.
The unit-range wrapper then fixes `R = 1`, which is the version intended for the
first teaching route. The radius wrapper delegates to the checked closed-form
horizon-radius theorem and keeps the same `(s.card : R)` denominator. The
explicit-radius wrapper instantiates the threshold with that radius, leaving a
single displayed finite-prefix event. The nonempty-sample wrapper discharges the
radius-positivity side condition by proving that the log argument is larger than
`1` and the sample denominator is positive. The zero-one wrapper then fixes the
range endpoints at `0` and `1`, so callers supply the direct bounded-loss
assumption `loss t h i ∈ [0,1]`. It also discharges the negative-integral
identity using `integral_neg`.

## Current Sample-Size Theorem

Target name:

```lean
finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_ge
```

Statement shape:

Replace the supplied displayed-tail inequality with an explicit sample-size
lower bound and real-valued per-time budgets. The proof route is:

1. start from a positive real budget for each `(time, hypothesis)` pair;
2. derive the displayed-tail inequality
   `2 * exp(-2 * sampleSize * ε^2 / R^2) <= realBudget t h`
   from
   `(R^2 / (2 * ε^2)) * (log 2 - log (realBudget t h)) <= sampleSize`;
3. compare `ENNReal.ofReal (realBudget t h)` to the dyadic budget split
   `finiteDyadicTimeBudget δ t / card(H)`;
4. invoke
   `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize`.

This is still a finite-horizon theorem. It does not claim an infinite-time
union over all natural-number times.

## Completed Dyadic Real-Budget Target

Target name:

```lean
finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_dyadicRealBudget
```

Statement shape:

Remove the caller-supplied real-budget comparison by choosing the concrete
positive real budget

```text
realBudget t h = δ_real * 2^(-1-t) / card(H)
```

under explicit positivity assumptions on `δ_real`, `ε`, `R`, and `card(H)`.
The theorem is finite-horizon, but its statement reads like the finite-class
union-bound sample-complexity condition.

This is an algebra and coercion layer. It does not alter the probability
argument.

## Completed Radius Target

Target name:

```lean
finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_epsilonOfSampleSize_dyadicRealBudget
```

Statement shape:

Keep the same finite-horizon event bound and dyadic real budget, but expose a
more user-facing radius condition by deriving the sample-size inequality from a
hypothesis of the form

```text
sqrt(R^2 / (2 * sampleSize)
  * (log 2 - log(δ_real * 2^(-1-t) / card(H)))) <= ε
```

This remains a finite-prefix theorem and is another algebra layer over the
checked probability chain.

## Completed Horizon-Uniform Radius Target

Target name:

```lean
finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_horizonUniformRadius_dyadicRealBudget
```

Statement shape:

Keep the finite-horizon event bound, but replace the per-time radius hypotheses
with one common finite-horizon radius using the worst time in the finite prefix.
The checked shape is:

```text
sqrt(R^2 / (2 * sampleSize)
  * (log 2 - log(δ_real * 2^(-T) / card(H)))) <= ε
```

with a checked monotonicity bridge showing this common bound implies the
per-time radius hypotheses for `t : Fin T`.

## Completed Closed-Form Horizon Radius Target

Target name:

```lean
finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_closedFormHorizonRadius_dyadicRealBudget
```

Target statement shape:

Keep the same finite-horizon event bound, but replace

```text
log 2 - log(δ_real * 2^(-T) / card(H))
```

by an explicit closed form such as

```text
log((2 : R) ^ (T + 1) * card(H) / δ_real)
```

under positive-budget assumptions. This is still a finite-prefix algebra
layer, but it gives the theorem the standard finite-class appearance.

Supporting rewrite:

```lean
finiteDyadicRealBudget_horizon_logBudget_eq_closedForm
```

## Completed Closed-Form Horizon Sample-Size Target

Target name:

```lean
finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_closedFormHorizonSampleSize_dyadicRealBudget
```

Target statement shape:

Keep the same finite-horizon event bound, but replace the square-root radius
hypothesis by the displayed sample-size condition

```text
R^2 / (2 * ε^2) * log((2 : R)^(T + 1) * card(H) / δ_real) <= sampleSize
```

This is the final algebra layer before the route-facing finite-prefix theorem
statement presents the same sample-complexity form.

## Completed Route-Facing Finite-Prefix Target

Target name:

```lean
finitePrefixFiniteClassDeviationFromHoeffding_closedForm
```

Target statement shape:

This shorter wrapper keeps the same assumptions and conclusion as the checked
closed-form shared-sample theorem, but exposes the finite-prefix finite-class
Hoeffding result under a name suitable for papers, notes, and TheoremPath
routes.

## Completed Card-Sample Route-Facing Target

Target name:

```lean
finitePrefixFiniteClassDeviationFromHoeffding_closedForm_cardSample
```

Target statement shape:

This wrapper removes the separate `sampleSize : R` parameter from the
route-facing theorem surface by presenting the event bound directly with
`(s.card : R)` wherever the empirical average denominator appears. This makes
the statement closer to the way the theorem is written in a note while
preserving the same checked finite-prefix scope.

## Completed Unit-Range Route-Facing Target

Target name:

```lean
finitePrefixFiniteClassDeviationFromHoeffding_closedForm_unitRange
```

Target statement shape:

This theorem specializes the card-sample theorem to unit-bounded losses by
fixing `R = 1`. It gives a compact display
`log((2 : R)^(T + 1) * card(H) / δ_real) / (2 * ε^2) <= (s.card : R)`,
which is the natural first version for a teaching route before adding more
general range parameters.

## Completed Unit-Range Radius Target

Target name:

```lean
finitePrefixFiniteClassDeviationFromHoeffding_unitRange_radius
```

Target statement shape:

Present the same unit-range finite-prefix guarantee as a confidence-radius
bound, with the displayed deviation threshold determined by the finite horizon,
class cardinality, confidence budget, and sample cardinality. This is the
expository layer after the sample-size condition: sample-size theorem first,
radius theorem second.

## Completed Explicit-Radius Route-Facing Target

Target name:

```lean
finitePrefixFiniteClassDeviationFromHoeffding_unitRange_explicitRadius
```

Target statement shape:

Set the threshold itself to the displayed confidence radius, under a positivity
assumption for that radius. This removes the caller-supplied `ε` parameter from
the teaching-route statement and exposes the textbook-style bound as a single
finite-class event.

## Completed Explicit-Radius Positivity Target

Target name:

```lean
finitePrefixFiniteClassDeviationFromHoeffding_unitRange_explicitRadius_nonemptySample
```

Target statement shape:

Keep the same explicit-radius event, but replace the separate radius-positivity
hypothesis with a usable sufficient condition from the finite sample and budget
assumptions. The checked sufficient condition is
`δ_real < 2^(T + 1) * card(H)`.

## Completed Zero-One Bounded-Loss Target

Target name:

```lean
finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_explicitRadius
```

Target statement shape:

Specialize the unit-range theorem to losses bounded in `[0,1]`, removing the
caller-supplied lower and upper range functions `a` and `b` and the supplied
negative-integral identity. This is the first compact finite-class
uniform-convergence theorem surface in the route.

## Completed Time-Varying Radius Target

Target names:

```lean
finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius
finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius_fromHoeffding
anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius_fromHoeffding
anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius_exists_fromHoeffding
zeroOneDyadicFiniteClassConfidenceRadius
anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_namedRadius_exists_fromHoeffding
anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_confidenceSequence_fromHoeffding
```

Target statement shape:

Keep the zero-one empirical-average event, but replace the horizon-uniform
radius by the per-time dyadic radius

```text
sqrt((log 2 - log(δ_real * 2^(-1-t) / card(H))) / (2 * card(s))).
```

The first theorem assumes the pointwise tail bound at this radius and proves
the simultaneous finite-prefix event over `Fin T × H`. The second theorem
discharges that pointwise tail bound from the fixed-hypothesis Hoeffding
wrappers for losses bounded in `[0,1]`. Both check the exact conversion from
the real budget `δ_real * 2^(-1-t) / card(H)` to the `ENNReal` dyadic
time/class budget.
The anytime theorem keeps the same radius, replaces `Fin T × H` by
`Nat × H`, and uses the countable dyadic time-budget sum.
The existential version presents the same event as
`∃ t : Nat, ∃ h : H`, which is the intended route-facing statement.
The confidence-sequence version presents the same bound as the probability that
the simultaneous statement
`∀ t h, |deviation t h| < radius(t)` fails.

## Next Theorem Target

Target:

Connect the confidence-sequence theorem to the finite-net side of the program:
instantiate the finite hypothesis index with a finite cover/net and state the
first finite-net time-uniform deviation shell. This should stay separate from
the Dudley expectation chain until the event-level finite-net statement is
checked.

## Proof Route

1. Use fixed-hypothesis Hoeffding for each `(time, hypothesis)` pair.
2. Combine upper and lower tails with `empiricalAverageTwoSidedHoeffdingTail`.
3. Replace the finite squared-half-range sum by `card(s) * (R / 2)^2`.
4. Use the explicit nondegenerate range certificate to justify the denominator.
5. Split each time budget across the finite hypothesis class.
6. Sum the finite prefix of the dyadic time schedule.
7. Use the finite-horizon dyadic monotonicity bridge to reduce all per-time
   radii to one horizon-level radius.
8. Rewrite the horizon log budget into the closed horizon/class/budget form.
9. Present the same sufficient condition in sample-size form.
10. Expose the result through the route-facing wrapper theorem.
11. Substitute `sampleSize = (s.card : R)` for the card-sample theorem.
12. Substitute the displayed radius for the threshold in the explicit-radius
    theorem.
13. Prove the displayed radius is positive from the strict budget condition.
14. Specialize the lower and upper range functions to `0` and `1` from the
    direct `[0,1]` bounded-loss assumption.
15. Discharge the negative-integral identity with `integral_neg`.
16. Convert the real dyadic class budget to the `ENNReal` dyadic budget split.
17. Sum the full dyadic time-budget schedule over natural-number times.
18. Conclude the simultaneous countable-time event bound over `Nat × H`.

## What Is Not Claimed

- This is not yet a full empirical-process library.
- This is not yet an optional-stopping or e-process theorem.
- This does not replace the non-finite Dudley direction.
- This does not assert asymptotic optimality or constant optimality.
- This does not remove the finite-class hypothesis.

## TheoremPath Route Shape

A route-ready exposition should have four pages:

1. finite union budgets;
2. dyadic time budgets;
3. bounded empirical averages and Hoeffding tails;
4. the countable-time finite-class theorem.

Each page should name the Lean declarations it depends on, state the exact
nonclaims, and show the proof chain as a dependency diagram.
