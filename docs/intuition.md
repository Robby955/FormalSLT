# Intuition: what each theorem actually says

The Lean files in this repo prove formal statements. This file translates each
main theorem into one or two paragraphs of plain English: what the bound
controls, why the constant is what it is, and what would have to be true for
the theorem to be useful in practice.

For exact statements see [`theorem-map.md`](./theorem-map.md). For visual
dependency structure see [`diagrams.md`](./diagrams.md). For the precise
shape of every assumption see
[`assumptions-and-nonclaims.md`](./assumptions-and-nonclaims.md).

---

## Generalization gap

```
genGap(H, S) = sup_{h ∈ H} ( populationRisk(h) − empiricalRisk(h, S) )
```

How wrong can a worst-case hypothesis look on the training set compared to
its true risk? `genGap` is the *one-sided* worst-case discrepancy: a learner
that minimizes empirical risk can select a bad hypothesis only when some
`h ∈ H` looks better on `S` than it really is. Bounding
`genGap` from above bounds how badly empirical risk minimization can do.

## Rademacher symmetrization — `E[genGap] ≤ 2·E[Rad]`

**What it says.** If you replace the unknown population with an iid copy of
the training set (a "ghost sample"), the expected generalization gap is at
most twice the expected *Rademacher complexity* of the loss class on the
training set. Rademacher complexity is the expected sup over `H` of the
correlation between the loss and a ±1 random sign vector — a measure of how
well the class can fit pure noise.

**Why this halves the problem.** Generalization is a question about
unobserved data. The ghost-sample trick converts it into a question about
*two* observed samples, which is tractable because both are iid from the
same distribution. The factor of 2 is the cost of replacing one sample
with two; it is not slack and cannot be removed without different
techniques.

**Constant in this repo:** the bound is `2 · E[empiricalRademacherComplexity]`
exactly. The factor of 2 follows from the standard symmetrization argument
in Boucheron-Lugosi-Massart (2013), Lemma 4.4.

## Massart's finite-class bound — `Rad(H, S) ≤ B·√(2·log|H| / n)`

**What it says.** When `H` has finitely many hypotheses, the Rademacher
complexity grows only logarithmically in `|H|`. The dependence on the
sample size is `1/√n`, the bounded-loss range is `B`, and the constant is
exactly `√2`.

**Why log of `|H|`.** The bound is a tight maximal inequality on
sub-Gaussian random variables. Each hypothesis contributes a sub-Gaussian
random variable with parameter `B/√n`; the maximum of `K` such variables
grows like `B·√(2·log K / n)` by a union argument that is sharp up to
constants. There is no `√|H|` in finite-class learning theory because the
log is what governs the scaling.

**Use in the proof.** Plugging Massart into symmetrization gives
`E[genGap] ≤ 2B·√(2·log|H| / n)` with no further work. The price of
finiteness is logarithmic; the price of `n` is square-root.

## Azuma generalization-gap tail — `P(genGap − E[genGap] ≥ ε) ≤ exp(−ε²n / 8B²)`

**What it says.** The generalization gap concentrates around its
expectation: deviations of size `ε` are exponentially unlikely in the
sample size. The `8B²` in the denominator is the Azuma constant for a
sample-exposure martingale where each step changes the gap by at most
`2B/n` and there are `n` steps.

**The Azuma constant is loose by 4× compared to the sharp McDiarmid
constant** (which would give `2ε²n / B²`). This repo currently uses the
Azuma route because it composes directly with the high-probability layer
above. The [`assumptions-and-nonclaims.md`](./assumptions-and-nonclaims.md)
doc records this constant choice explicitly.

**What you would change to make this useful.** Bigger `n` shrinks the
tail exponentially. Bigger `B` (looser loss range) loosens the tail
quadratically. To get a 95% confidence interval on the gap, set the
right-hand side equal to 0.05 and solve for `ε`.

## High-probability Rademacher — `P(genGap ≥ 2·E[Rad] + ε) ≤ exp(−ε²n / 8B²)`

**What it says.** Compose Rademacher symmetrization (controls the
expectation) with the Azuma tail (controls the deviation around the
expectation): a learner's worst-case generalization gap stays within
`2·E[Rad] + ε` of its expectation with probability at least
`1 − exp(−ε²n / 8B²)`.

This is the theorem in the chain that turns the earlier expectation work into a finite-sample,
high-probability statement. Everything before this is either an expectation
bound or a single concentration step.

## Finite-class high-probability — `P(genGap ≥ 2B√(2log|H|/n) + ε) ≤ exp(...)`

**What it says.** Specializing to a finite hypothesis class: the gap is at
most `2B√(2·log|H|/n) + ε` with high probability. This is the canonical
finite-class generalization bound used in introductory learning theory
texts.

**How tight is it?** The leading `2B√(2·log|H|/n)` is sharp up to constant
factors for the worst case. The `+ ε` slack is the price of moving from
expectation to high probability via Azuma; that price is `O(B/√n)` to
match the leading term.

## Sauer-Shelah polynomial bound — `Σ_{k≤d} C(n,k) ≤ (en/d)^d`

**What it says.** A class with VC dimension `d` realizes at most
`(en/d)^d` distinct labelings on any sample of size `n`. Combinatorially:
even though there can be infinitely many hypotheses, only finitely many
*behaviors* are realized on any finite sample, and this number grows
polynomially in `n`, not exponentially.

**Why this is the bridge.** All the finite-class machinery above goes
through unchanged once you replace `|H|` with the *number of effective
behaviors on the sample*. Sauer-Shelah is what gives you a polynomial
ceiling on that count, which makes `log(effective class)` grow like
`d · log(en/d)` — the famous `O(d·log n)` rate for VC classes.

## VC pointwise Rademacher — `Rad ≤ B·√(2d·log(en/d) / n)`

**What it says.** The same Massart bound, but with `log|H|` replaced by
`d·log(en/d)` via Sauer-Shelah. This is the canonical VC-dimension
generalization bound: `O(√(d/n))` rate up to log factors.

**The shape.** This is *pointwise* (depends on the realized sample `S`)
but the bound has no `S`-dependent constant — it holds for every sample
in a class with VC dimension `d`. That uniformity is what distinguishes
VC theory from finite-class theory.

## VC ERM excess risk tail — `P(excess risk ≥ 2B√(2d·log(en/d)/n) + ε) ≤ 2·exp(−ε²n / 8B²)`

**The capstone.** Under bounded loss, iid samples, finite VC dimension `d`,
the ERM learner's excess risk over the best-in-class hypothesis is at
most `2B√(2d·log(en/d)/n) + ε` with probability at least
`1 − 2·exp(−ε²n / 8B²)`.

**Reading off sample complexity.** Set the failure probability to `δ` and
the excess risk slack to `ε_0`; solve to get `n ≳ (B²/ε_0²) · (d·log(1/ε_0)
+ log(1/δ))`. This is the canonical VC sample-complexity rate.

**Current boundaries.**
- It is *not* a low-probability bound on a specific learner's true risk; it
  is a bound on excess risk over the in-class optimum.
- The `2·exp` (not `exp`) reflects that the bound is two-sided in the
  uniform-deviation sense; the original Azuma gives a one-sided tail.
- Bounded loss is essential: unbounded loss requires moment or
  sub-Gaussian assumptions that this repo does not formalize.
- iid is essential: the Azuma exposure martingale assumes independent
  samples. Generalizing to `β`-mixing or martingale data needs different
  machinery.

## Binary VC bridge — `effectiveClass(0-1 loss).card = binaryClassTrace.card`

**What it says.** When the loss is the 0-1 loss, the *effective class* on a
sample (the set of distinct loss-vectors realized by hypotheses) has
exactly the same cardinality as the *binary class trace* (the set of
labelings hypotheses produce). This is a small bridge result that lets
the VC machinery for 0-1 loss reuse the effective-class machinery built
for general bounded loss.

**Use in the proof.** Without this bridge, the VC sample-complexity
results would have to be re-proved for the 0-1 case from scratch.
With it, a one-line corollary gives the classical PAC bound for binary
classification.

## Finite scalar contraction — `Rad_S(φ ∘ F) ≤ L·Rad_S(F)`

**What it says.** If `φ` is scalar-valued, Lipschitz, and vanishes at zero,
then composing a finite real-valued function class with `φ` does not increase
empirical Rademacher complexity by more than the Lipschitz constant. This is
the finite-sample, finite-class scalar contraction theorem.

**Use in the proof.** Contraction is the tool that lets Rademacher bounds
move from raw scores to losses or margins. The formalized theorem is not the
full general Talagrand contraction theorem; it is the finite scalar result
that fits the current library spine.

## Linear predictors — `Rad ≤ R·n⁻¹·√(Σ‖xᵢ‖²)`

**What it says.** For finite-dimensional Euclidean linear predictors with
`‖w‖ ≤ R`, empirical Rademacher complexity is bounded by the norm of the
signed sample sum. The public corollary gives `Rad ≤ R·B / √n` when every
input satisfies `‖xᵢ‖ ≤ B`.

**Use in the proof.** This theorem connects the repo to a standard ML model
class rather than only an abstract finite hypothesis class. It
connects the Rademacher machinery to linear prediction in finite-dimensional
Euclidean spaces.

## Finite sub-Gaussian chaining

**What it says.** The finite chaining layer starts with MGF control for a
finite sub-Gaussian process, turns that into expected finite-supremum bounds,
and composes those bounds across finite net projections. The endpoint is a
finite Dudley-style entropy-budget wrapper under a dyadic radius schedule.

**Use in the proof.** This is the finite infrastructure needed before a
continuous Dudley integral theorem can be stated responsibly. It proves the
bookkeeping for finite nets, projection pairs, finite entropy sums, and
per-scale entropy budgets.

---

## Reading order

If you have read a learning theory textbook chapter on VC theory, the
fastest path through this repo is:

1. **`Rademacher.Symmetrization`** — see how the ghost-sample trick is
   formalized as a measurable kernel argument.
2. **`Rademacher.Massart`** — see the maximal-inequality argument that
   turns sub-Gaussian tails into the `√(2·log|H|/n)` bound.
3. **`Azuma.GenGapTail`** — see the bounded-difference martingale that
   gives the Azuma exponential tail.
4. **`VC.SauerShelah`** — see the `(en/d)^d` polynomial bound proved by
   the standard double-counting argument.
5. **`VC.SampleComplexity`** — see how all of the above compose into the
   capstone ERM excess-risk bound.

If you have not read the corresponding textbook chapter, the bounds will
be hard to motivate from the Lean files alone. Recommended companions:

- Boucheron, Lugosi, Massart (2013), *Concentration Inequalities*, Ch. 4
- Mohri, Rostamizadeh, Talwalkar (2018), *Foundations of Machine Learning*, Ch. 3
- Shalev-Shwartz and Ben-David (2014), *Understanding Machine Learning*, Ch. 6, 26
