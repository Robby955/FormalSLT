# FormalSLT second dyadic-net instantiation handoff

Date: 2026-06-01

Status: local-only proof infrastructure. No push, PR, or public action has been
taken.

## What landed

The generic `FiniteDyadicNetSequence` API now has a second concrete
instantiation outside the unit interval:

- Module: `FormalSLT/Covering/TwoPointDudley.lean`
- Index family: `TwoPoint := Bool`
- Metric: discrete two-point distance
- Process: one-coordinate Rademacher process over the two-point index family

The key declarations are:

- `twoPointDyadicNetSequence`
- `twoPointDudleyInstance`
- `twoPointRademacherSupAdapter`
- `twoPointRademacher_projected_dudley_m_bound`
- `twoPointRademacherSup_dudley_m_bound`

## Why this matters

The previous reusable API could still be read as a cleaner wrapper around the
unit-interval rounded grid. This module shows the same wrapper applies to a
different metric family with different net geometry. The two-point example is
finite and intentionally small, but it exercises the same public API:

1. package dyadic finite nets,
2. prove adjacent geometric radius bounds,
3. prove adjacent projection-pair nontriviality,
4. bound adjacent covering products, and
5. call the packaged projected and supplied-supremum Dudley wrappers.

## What is not claimed

This is not a continuous Dudley theorem, not a total-boundedness theorem, and
not a separability result. It is a second finite-scale witness that the
dyadic-net sequence abstraction is reusable.

## Checker

The checker file is:

- `examples/CheckTwoPointDudley.lean`

It checks the metric lemmas, Rademacher MGF bound, dyadic-net sequence
instantiation, projected Dudley bound, and supplied-supremum Dudley bound.

Expected theorem axiom surface remains:

- `[propext, Classical.choice, Quot.sound]`

## Next theorem target

This follow-up has landed as `FormalSLT/Covering/FiniteDiscreteDudley.lean`,
which gives a `Fin n` discrete metric family with nonconstant cover-count
bookkeeping and a nonzero embedded Rademacher process. The next theorem target
is to connect more of the total-bounded and unit-interval boundary layer to the
packaged `FiniteDyadicDudleyInstance` API where the hypotheses match.
