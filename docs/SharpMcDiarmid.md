# Sharp McDiarmid (bounded-differences) inequality

## What "sharp" means

McDiarmid's inequality bounds the upper tail of a function `f` of independent
coordinates whose value changes by at most `c_k` when coordinate `k` is altered:

    P( f(X) - E[f(X)] >= t )  <=  exp( -2 t^2 / sum_k c_k^2 ).

The constant `2` in the exponent is optimal: it is the constant that drops out of
the Hoeffding moment-generating-function bound when each martingale increment is
controlled on an interval of width exactly `c_k`. A variable confined to an
interval of width `w` has sub-Gaussian variance proxy `(w/2)^2`; with `w = c_k`
the per-increment proxy is `(c_k/2)^2`, the proxies sum to `(sum_k c_k^2)/4`, and
the Azuma-Hoeffding tail `exp(-t^2 / (2 * proxy_sum))` becomes
`exp(-2 t^2 / sum_k c_k^2)`. This is the form in Boucheron, Lugosi and Massart,
*Concentration Inequalities* (2013), Chapter 6, Theorem 6.2 (the bounded-
differences inequality), proved via the Doob/exposure martingale of Section 6.1.

The weaker **Azuma constant** uses the symmetric increment bound `|Δ_k| <= c_k`
(an interval of width `2 c_k`, proxy `c_k^2`), giving
`exp(-t^2 / (2 sum_k c_k^2))`: four times weaker in the exponent.

## Comparison to mathlib and to this repository

mathlib (toolchain `v4.30.0-rc2`) has **no** McDiarmid / bounded-differences
inequality. It provides the ingredients:

- `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` - Hoeffding's lemma, proxy
  `((b-a)/2)^2` for a variable in `[a,b]`;
- `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` - Hoeffding's inequality for
  sums of independent sub-Gaussian variables;
- `ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF` - the conditional
  Azuma-Hoeffding inequality for martingale differences.

This repository proves two product-measure bounded-differences tails in
`FormalSLT/Azuma/`, via the exposure martingale
`M_k = E[f | first k coordinates]`:

- `ExposureMartingale.hasBoundedDifferences_tail_azuma` uses the symmetric proxy
  `‖c_k‖₊^2` and gives the Azuma constant.
- `ExposureMartingale.hasBoundedDifferences_tail_sharp` uses the sharp proxy
  `(‖c_k‖₊ / 2)^2` and gives the McDiarmid constant
  `exp(-2 t^2 / sum_k c_k^2)`.

## What this module (`FormalSLT/Concentration/SharpMcDiarmid.lean`) adds

1. `mcdiarmid_additive_independent` - the **sharp** constant `2` for the additive,
   independent case: for `sum_i X_i` with the `X_i` independent and each supported
   in `[a_i, b_i]`,

       P( sum_i (X_i - E[X_i]) >= t )  <=  exp( -2 t^2 / sum_i (b_i - a_i)^2 ).

   Here no conditioning is needed: each `X_i` lies directly in a width-`(b_i-a_i)`
   interval, so the sharp proxy is available immediately.

2. `mcdiarmid_of_hasBoundedDifferences_sharp` - the general iid product-measure
   bounded-differences theorem:

       P( f(S) - E[f(S)] >= t )  <=  exp( -2 t^2 / sum_k c_k^2 ).

   It is a public wrapper around
   `ExposureMartingale.hasBoundedDifferences_tail_sharp`.

3. `mcdiarmid_of_hasBoundedDifferences_sharp_lower` - the matching lower-tail
   wrapper:

       P( E[f(S)] - f(S) >= t )  <=  exp( -2 t^2 / sum_k c_k^2 ).

   This is proved by applying the upper-tail theorem to `-f`; the same
   bounded-differences widths apply.

4. `mcdiarmid_twoSided_of_hasBoundedDifferences_sharp` - the two-sided
   textbook iid product-measure form:

       P( |f(S) - E[f(S)]| >= t )  <=  2 * exp( -2 t^2 / sum_k c_k^2 ).

   It combines the upper and lower tails with the two-event union bound.

5. `sharp_mcdiarmid_of_doob_increments` - an abstract reduction: *given* Doob
   increments that are conditionally sub-Gaussian with the sharp proxy
   `(c_i/2)^2`, the sharp tail bound follows from the conditional Azuma-Hoeffding
   engine. It isolates the exponent bookkeeping from the exposure-martingale
   construction.

These declarations are axiom-clean (`[propext, Classical.choice, Quot.sound]`).
The two standard additive instances are checked in
`FormalSLT/Test/SharpMcDiarmidTest.lean`:
`c_i = 1` (unit-range, `exp(-2 t^2 / n)`) and `c_i = 1/n` (sample-mean scaling,
`exp(-2 n t^2)`). The same checker file also checks the general one-sided,
lower-tail, and two-sided product-measure declarations.

## Checked proof sketch (general sharp case)

1. Form the exposure martingale `M_k = E[f | X_1, ..., X_k]`; the increments
   `Δ_k = M_{k+1} - M_k` have conditional mean `0` and, **conditionally on the
   prefix**, range within an interval of width `c_k`.
2. Hoeffding's lemma gives each `Δ_k` conditional sub-Gaussian proxy `(c_k/2)^2`.
3. The conditional Azuma-Hoeffding inequality applied to `sum_k Δ_k = f - E[f]`
   yields `exp(-t^2 / (2 sum_k (c_k/2)^2)) = exp(-2 t^2 / sum_k c_k^2)`.

## Route A completion: range width for the Doob increment

`FormalSLT/Azuma/BoundedIncrementBound.lean` includes the pointwise
partial-integral range-width bridge:

- `abs_partialIntegral_succ_sub_succ_le_of_agree_prefix`
- `abs_partialIntegral_step_sub_step_le_of_agree_prefix`

The second theorem says that if two samples agree on every coordinate before
`k`, then the explicit partial-integral increment
`P_{k+1} - P_k` changes by at most `c k`. This is the width-`c_k` statement for
the explicit Doob-increment representative.

`FormalSLT/Azuma/ExposureIncrementCondMGF.lean` now proves that lift for the
actual exposure increment:

- `exposureIncrement_condRange_width`
- `exposureIncrement_hasCondSubgaussianMGF_sharp`

For almost every prefix state, two samples drawn from the conditional kernel over
that prefix have exposure increments differing by at most `c k`. This supplies
the conditional diameter bound needed before applying the sharp fiberwise
Hoeffding lemma. The second theorem packages the same increment as
`HasCondSubgaussianMGF` with proxy `(‖c k‖₊ / 2)^2`.

`FormalSLT/Azuma/GenGapTail.lean` now routes those sharp per-increment MGF
theorems through mathlib's martingale concentration API:

- `ExposureMartingale.hasBoundedDifferences_tail_sharp`
- `ExposureMartingale.genGap_tail_bound_sharp`
- `ExposureMartingale.genGap_tail_bound_sharp_explicit`
- `Concentration.mcdiarmid_of_hasBoundedDifferences_sharp_lower`
- `Concentration.mcdiarmid_twoSided_of_hasBoundedDifferences_sharp`

For `c_k = 2B/n`, the explicit generalization-gap exponent is
`exp(-n * ε^2 / (2 * B^2))`, replacing the older Azuma exponent
`exp(-n * ε^2 / (8 * B^2))` at this layer.

Downstream Rademacher, VC, and stability wrappers now route through the sharp
tail where their theorem statements expose the concentration exponent.

## Bibliography

- S. Boucheron, G. Lugosi, P. Massart. *Concentration Inequalities: A
  Nonasymptotic Theory of Independence.* Oxford University Press, 2013.
  Chapter 6 (bounded differences and the entropy method); Section 6.1 (the
  martingale / exposure construction); Theorem 6.2 (the bounded-differences
  inequality with the sharp constant `2`).
- C. McDiarmid. On the method of bounded differences. *Surveys in Combinatorics*,
  1989, pp. 148-188.
