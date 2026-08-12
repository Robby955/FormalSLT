# FormalSLT Anytime Spine Handoff

Date: 2026-06-01
Worktree: `/private/tmp/formalslt-nonfinite-unit-interval`
Base commit before these local commits: `5221f01856d52d15dea0bad71ca825d32a4a3d86`

## Status

This handoff records the local, commit-ready FormalSLT strengthening on top of
the public `unit-interval-dudley` review branch. It has not been pushed.

The new local work has two theorem spines:

1. finite-class probability bookkeeping for finite-prefix and countable-time
   Hoeffding deviation bounds;
2. a reusable rounded dyadic-grid chain for the non-finite `[0,1]` Dudley
   example.

## Verification

Commands run from `/private/tmp/formalslt-nonfinite-unit-interval`:

```bash
lake build
lake env lean examples/CheckUnitIntervalDudley.lean
lake env lean examples/CheckFiniteUnionBound.lean
lake env lean examples/CheckUniformConvergence.lean
git diff --check
python3 /Users/robsneiderman/Desktop/AI4MATH/scripts/audit_public_writing.py \
  docs/roadmap.md docs/theorem-map.md docs/unit-interval-dudley.md \
  docs/verified-slt-program-outline.md \
  FormalSLT/Covering/FiniteSubGaussianChaining.lean \
  FormalSLT/Covering/UnitIntervalDudley.lean \
  FormalSLT/Probability/FiniteUnionBound.lean \
  FormalSLT/UniformConvergence.lean \
  FormalSLT/VC/SampleComplexity.lean
```

Results:

- `lake build`: success, 2947 jobs. Existing warnings remain in unrelated
  Azuma and Rademacher files.
- `CheckUnitIntervalDudley.lean`: success, 105 `#check`s, 78 axiom prints.
- `CheckFiniteUnionBound.lean`: success, 5 `#check`s, 5 axiom prints.
- `CheckUniformConvergence.lean`: success, 69 `#check`s, 62 axiom prints.
- `git diff --check`: clean.
- Public-writing audit: passed.
- Em dash count across touched Lean/doc files: 1 total.
- Added executable `sorry`/`admit` bodies: none.
- Added `axiom`, `constant`, or `unsafe` declarations: none.
- Added literal `Classical.choice` in theorem statements: none.

Axiom status for printed declarations is within the expected mathlib profile:
`[propext, Classical.choice, Quot.sound]`, with a few smaller subsets.

## Main theorem anchors

Finite union budgets:

- `FormalSLT/Probability/FiniteUnionBound.lean:181`
  `finiteMeasureUnionBound_budget`
- `FormalSLT/Probability/FiniteUnionBound.lean:236`
  `finiteMeasureUnionBound_cardInv`

Dyadic and countable-time budget shell:

- `FormalSLT/UniformConvergence.lean:244`
  `finiteDyadicTimeBudget_tsum_le`
- `FormalSLT/UniformConvergence.lean:286`
  `countableTimeClassUnionBound_dyadicBudget`
- `FormalSLT/UniformConvergence.lean:333`
  `zeroOneDyadicFiniteClassConfidenceRadius`

Finite-prefix Hoeffding and route-facing radii:

- `FormalSLT/UniformConvergence.lean:3149`
  `finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius`
- `FormalSLT/UniformConvergence.lean:3224`
  `finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius_fromHoeffding`

Countable-time confidence-sequence surface:

- `FormalSLT/UniformConvergence.lean:3340`
  `anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius_fromHoeffding`
- `FormalSLT/UniformConvergence.lean:3604`
  `anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_namedRadius_exists_fromHoeffding`
- `FormalSLT/UniformConvergence.lean:3646`
  `finiteClassConfidenceSequenceFailureEvent`
- `FormalSLT/UniformConvergence.lean:3663`
  `FiniteClassConfidenceSequence`
- `FormalSLT/UniformConvergence.lean:3685`
  `anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_confidenceSequence_fromHoeffding`
- `FormalSLT/UniformConvergence.lean:3740`
  `FiniteClassConfidenceSequence.failure_probability_le`

Rounded dyadic-grid Dudley chain:

- `FormalSLT/Covering/UnitIntervalDudley.lean:323`
  `unitIntervalDyadicGridRoundProject_dist_le`
- `FormalSLT/Covering/UnitIntervalDudley.lean:983`
  `unitIntervalRademacherLinearSup_sSup_range`
- `FormalSLT/Covering/UnitIntervalDudley.lean:1657`
  `unitIntervalRademacherLinear_roundedDyadicGrid_dudley_m_bound`
- `FormalSLT/Covering/UnitIntervalDudley.lean:2107`
  `unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound`

## What landed

### Finite-class anytime Hoeffding spine

The new probability layer gives finite union bounds with explicit per-event
budgets, finite-prefix dyadic time budgets, countable-time dyadic budget sums,
and shared-sample Hoeffding wrappers for finite hypothesis classes.

The route-facing endpoint is the confidence-sequence theorem:

```lean
anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_confidenceSequence_fromHoeffding
```

It bounds the probability that the simultaneous all-times and all-hypotheses
strict confidence-radius event fails for `[0,1]` losses.

### Rounded dyadic-grid UnitInterval Dudley chain

The UnitInterval bridge now has a reusable nearest-grid projection with radius
`1 / 2^(level + 1)`, a rounded dyadic net sequence, finite-horizon arbitrary
`m` projected Dudley bounds, and supplied-supremum adapters. The supplied
supremum is now connected to the actual process range through `IsLUB` and
`sSup` lemmas rather than only prose.

### Documentation and checkers

The theorem map, roadmap, proof-frontier manifest, UnitInterval note, and new
program outline were updated to describe the finite-class anytime spine and the
rounded-grid non-finite example. New checker files cover the finite union and
uniform-convergence layers.

## Remaining proof debt

The touched executable proof paths add no `sorry` or `admit`. A repo-wide scan
for executable `sorry`/`admit` bodies in `FormalSLT` and `examples` currently
returns zero. Some docs and comments still discuss proof-debt policy using the
word `sorry`; those are not proof holes.

## Next theorem suggestion

The countable-time finite-class Hoeffding theorem now has a cleaner statistical
object:

```lean
FiniteClassConfidenceSequence
```

It bundles the finite hypothesis class, `[0,1]` loss condition, shared sample,
risk functional, named dyadic radius, and failure budget. The next useful step
is to make downstream notes and route metadata cite
`FiniteClassConfidenceSequence.failure_probability_le` instead of the long
measure-theoretic theorem signature.

For the Dudley lane, the next useful step is a total-bounded wrapper that takes
a rounded dyadic-net family abstractly and reuses the UnitInterval proof as the
model instance, instead of adding more named `m = k` corollaries.
