# G3 Dudley Ladder

This note maps the finite G3 Dudley path added by q085, q086, q087, and the
two-point integral example. The path is a finite theorem spine:

- finite outcome space;
- finite terminal index set;
- explicit finite nets and projections;
- centered finite projection increments;
- a positive antitone finite covering-number envelope.

It is not a continuous Dudley theorem. It does not prove measurable suprema,
separability, or a limit passage from finite nets to an arbitrary function
class.

## Modules

| Step | Module | Main theorem | Role |
|---|---|---|---|
| q085 | `FormalSLT.Probability.SubGaussianFiniteMax` | `subgaussian_finite_max` | finite maximal inequality for a centered one-sided sub-Gaussian family |
| q086 | `FormalSLT.Covering.DudleyChainingSum` | `dudley_chaining_sum` | centered finite-net chaining sum |
| q087 | `FormalSLT.Covering.DudleySumToIntegral` | `dudley_entropy_integral_of_antitone_coveringNumber` | dyadic entropy sum bounded by a truncated entropy integral |
| example | `FormalSLT.Covering.TwoPointDudleyIntegral` | `twoPointRademacher_centered_dudley_entropy_integral` | concrete rooted two-point instantiation of the q087 theorem |
| endpoint | `FormalSLT.Covering.DudleyEntropyIntegral` | re-exported q087 and two-point endpoint declarations | canonical import surface for the finite G3 endpoint |

The old q087 theorem name `dudley_entropy_integral` remains available as a
compatibility wrapper. New callers can use
`dudley_entropy_integral_of_antitone_coveringNumber`, which removes the
boundedness receipt for the covering profile.

## Constant Accounting

q085 proves the finite maximal inequality

```lean
finiteExpectation w (fun ω => finiteSup (fun i : ι => Y i ω)) ≤
  sigma * Real.sqrt (2 * Real.log (Fintype.card ι : ℝ))
```

q086 applies this at each adjacent net scale. A projection increment has
sub-Gaussian scale bounded by

```lean
Real.sqrt P.varianceProxy * ((N j).radius + (N (j + 1)).radius)
```

so the q086 chain pays

```lean
Real.sqrt (2 * P.varianceProxy) *
  ∑ j ∈ Finset.range m,
    ((N j).radius + (N (j + 1)).radius) *
      Real.sqrt
        (Real.log ((N j).coveringNumber *
          (N (j + 1)).coveringNumber : ℝ))
```

q087 compares this dyadic sum with the truncated entropy integral. The
geometric radius rewrite contributes one factor `2`; the upper-sum comparison
contributes another factor `2`. The final finite statement is

```lean
finiteExpectation P.weight
    (fun ω => finiteSup (fun t : T => P.X ω t - P.X ω t₀)) ≤
  4 * Real.sqrt (2 * P.varianceProxy) *
    (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
      Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ)))
```

## Caller Obligations

The q087 theorem requires the caller to supply:

- finite outcome and terminal index types;
- a finite net sequence `N`;
- a root condition `(N 0).projection t = t₀`;
- a terminal condition `(N m).projection t = t`;
- positive adjacent radii on the finite horizon;
- geometric radius control by `radiusScale / 2^j`;
- a positive antitone covering profile;
- an adjacent-cover product bound at each dyadic lower endpoint;
- centered projection increments.

The compatibility theorem also accepts a boundedness receipt on each dyadic
interval, but the cleaner theorem does not need it. Interval integrability is
derived from antitonicity and positivity by
`coveringNumber_entropy_integrable_of_antitone`.

## Concrete Example

`FormalSLT.Covering.TwoPointDudleyIntegral` instantiates q087 on the two-point
Rademacher process.

- `twoPointRootNet` maps every index to the root `false`.
- `twoPointTerminalNet` is the identity two-point net.
- `twoPointRootedNet` uses the root at level `0` and the terminal net at
  level `1`.
- `twoPointIntegralCoverProfile` is the constant profile `4`.

The resulting theorem is:

```lean
twoPointRademacher_centered_dudley_entropy_integral
```

This example checks the rooted form required by q087. It is separate from the
older `TwoPointDudley` module, whose dyadic sequence uses identity nets at all
levels and therefore is not rooted at level `0`.

## Verification Surface

Run the focused checks with:

```bash
~/.elan/bin/lake build FormalSLT.Covering.DudleyEntropyIntegral
~/.elan/bin/lake build FormalSLT.Covering.DudleySumToIntegral
~/.elan/bin/lake build FormalSLT.Covering.TwoPointDudleyIntegral
~/.elan/bin/lake env lean examples/CheckDudleyEntropyIntegral.lean
~/.elan/bin/lake env lean examples/CheckDudleySumToIntegral.lean
~/.elan/bin/lake env lean examples/CheckTwoPointDudleyIntegral.lean
```

The named G3 theorems print the standard axiom surface:

```text
[propext, Classical.choice, Quot.sound]
```
