# FormalSLT v0.1 Quickstart

Date: 2026-06-01
Status: local release-candidate quickstart

This is the shortest path for a reader to import and verify the current v0.1
surface.

## What v0.1 Exposes

The v0.1 surface has three citation targets.

| Surface | Lean declaration | Checker |
|---|---|---|
| Finite-class countable-time Hoeffding confidence sequence | `FiniteClassConfidenceSequence.failure_probability_le` | `examples/CheckUniformConvergence.lean` |
| Unit-interval rounded-dyadic Dudley bridge | `unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound_prefixFree` | `examples/CheckUnitIntervalDudley.lean` |
| Reusable finite dyadic-net sequence API | `FiniteDyadicNetSequence.supFunctional_dudley_bound` | `examples/CheckV01Usability.lean` |
| Finite discrete dyadic-net family | `finDiscreteDyadicNetSequence` | `examples/CheckFiniteDiscreteDudley.lean` |

The three concrete dyadic-net instances are:

| Instance | Declaration | Role |
|---|---|---|
| Unit interval | `unitIntervalRoundedDyadicGridNetSequence` | Non-finite index-space example over `[0,1]` |
| Two-point discrete space | `twoPointDyadicNetSequence` | Second API instantiation, independent of `[0,1]` |
| Finite discrete spaces | `finDiscreteDyadicNetSequence` | General `Fin n` discrete-metric family, testing cover-count scaling beyond constant-size examples |

## Ten-Minute Verification Path

From the repository root:

```bash
lake exe cache get
lake env lean examples/CheckV01Usability.lean
```

If `lake` is not on the shell path:

```bash
~/.elan/bin/lake exe cache get
~/.elan/bin/lake env lean examples/CheckV01Usability.lean
```

The checker imports `FormalSLT`, verifies that the v0.1 declarations resolve,
and prints axiom profiles for the headline theorem surfaces.

Expected axiom profile:

```text
[propext, Classical.choice, Quot.sound]
```

Some declarations may print a smaller subset.

## Minimal Import Snippet

Use this shape when citing the v0.1 surface from another Lean file:

```lean
import FormalSLT

#check FormalSLT.UniformConvergence.FiniteClassConfidenceSequence.failure_probability_le
#check FormalSLT.Covering.UnitIntervalDudley.unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound_prefixFree
#check FormalSLT.Covering.FiniteSubGaussianChaining.FiniteSubGaussianProcess.FiniteDyadicNetSequence.supFunctional_dudley_bound
#check FormalSLT.Covering.TwoPointDudley.twoPointDyadicNetSequence
#check FormalSLT.Covering.FiniteDiscreteDudley.finDiscreteDyadicNetSequence
```

For narrower imports:

```lean
import FormalSLT.UniformConvergence
import FormalSLT.Covering.UnitIntervalDudley
import FormalSLT.Covering.TwoPointDudley
import FormalSLT.Covering.FiniteDiscreteDudley
```

## Full Local Verification

Run the focused v0.1 checkers:

```bash
lake env lean examples/CheckV01Usability.lean
lake env lean examples/CheckUniformConvergence.lean
lake env lean examples/CheckUnitIntervalDudley.lean
lake env lean examples/CheckTwoPointDudley.lean
lake env lean examples/CheckFiniteDiscreteDudley.lean
```

Run the full library and manifest checks:

```bash
lake build FormalSLT
python3 scripts/generate_proof_frontier_manifest.py --check
python3 scripts/check_doc_anchors.py \
  docs/formalslt-v0.1-technical-note.md \
  docs/formalslt-v0.1-artifact-map-2026-06-01.md \
  docs/formalslt-v0.1-release-review-2026-06-01.md \
  docs/theorempath-formalslt-v0.1-page-draft.mdx
git diff --check
```

Run proof-debt scans over executable Lean files:

```bash
rg -n --pcre2 '^\s*(?:by\s+)?(?:sorry|admit)\b|:=\s*(?:by\s+)?(?:sorry|admit)\b' FormalSLT examples
rg -n --pcre2 '^\s*(?:axiom|constant)\s+[A-Za-z_]' FormalSLT examples
```

Both scans should return no executable proof debt.

## What This Does Not Claim

- No full continuous Dudley entropy-integral theorem.
- No arbitrary measurable-supremum construction over non-finite classes.
- No general separability theorem.
- No infinite-class confidence sequence.
- No martingale or e-process stopping theorem in the v0.1 confidence-sequence
  surface.

## Reader Route

For a short review, read in this order:

1. `docs/formalslt-v0.1-technical-note.md`
2. `examples/CheckV01Usability.lean`
3. `docs/theorem-map.md`
4. `docs/assumptions-and-nonclaims.md`

That path gives the theorem story, the import surface, the declaration index,
and the proof boundaries without requiring a full source-code audit.
