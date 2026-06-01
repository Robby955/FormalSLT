# FormalSLT Goal 6 dyadic-net sequence handoff

Date: 2026-06-01

Status: local-only proof infrastructure. No push, PR, or public action has been
taken.

## What landed

The rounded-grid Dudley bridge no longer depends only on the concrete
unit-interval proof shape. The reusable API is:

- `FiniteSubGaussianProcess.FiniteDyadicNetSequence`
- `FiniteSubGaussianProcess.FiniteDyadicNetSequence.projectedNet_dudley_bound`
- `FiniteSubGaussianProcess.FiniteDyadicNetSequence.supFunctional_dudley_bound`

These declarations live in:

- `FormalSLT/Covering/FiniteSubGaussianChaining.lean`

The unit-interval rounded grid now instantiates the API through:

- `unitIntervalRoundedDyadicGridNetSequence`

and the arbitrary finite-horizon rounded-grid theorems are routed through that
generic object:

- `unitIntervalRademacherLinear_roundedDyadicGrid_dudley_m_bound`
- `unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound`

## What this changes

Before this change, the `[0,1]` rounded-grid proof carried the finite-net
geometry hypotheses directly at the use site. After this change, those
hypotheses are bundled into a reusable finite dyadic-net sequence. A future
metric example can now prove:

1. its finite nets have the same process distance,
2. adjacent radii decay geometrically,
3. adjacent projection-pair cardinalities are nontrivial, and
4. adjacent covering products are bounded by a cover-count sequence,

then call the generic projected or supplied-supremum Dudley wrapper.

## What is not claimed

This does not prove a continuous Dudley integral, a separability theorem, or a
measurable supremum over an arbitrary process. It is still a finite-scale
projected-net theorem with explicit supplied hypotheses. The improvement is API
shape and reuse, not a stronger analytic theorem.

## Verification targets

The checker file now covers the generic declarations and the concrete
unit-interval instantiation:

- `examples/CheckUnitIntervalDudley.lean`

Expected axiom surface for the new theorem checks remains:

- `[propext, Classical.choice, Quot.sound]`

## Next theorem target

The next useful theorem is a second concrete instantiation of
`FiniteDyadicNetSequence` for a metric index family other than `[0,1]`. A good
candidate should keep the process simple and force the API to prove that it is
not merely a unit-interval rename.
