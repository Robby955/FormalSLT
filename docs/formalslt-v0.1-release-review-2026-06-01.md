# FormalSLT v0.1 Release Review

Date: 2026-06-01
Status: local release-candidate memo, not a public-action approval

## Verdict

FormalSLT v0.1 is locally reviewable as a release candidate. The checked
surface is coherent enough for review: the Lean build passes, all example
checkers pass, the theorem map and proof-frontier manifest are in sync, and the
v0.1 quickstart checker imports the bundled confidence-sequence API, the
unit-interval Dudley bridge, and the reusable dyadic-net sequence API.
The reusable dyadic-net surface now includes the packaged
`FiniteDyadicDudleyInstance` API, a two-point discrete instance, and the
general finite discrete `Fin n` family with a nonzero embedded Rademacher
process.

This is not a public release decision. No push, pull request, merge, post, or
external comment has been made.

## Local Snapshot

FormalSLT worktree:

- Path: `/private/tmp/formalslt-nonfinite-unit-interval`
- Branch: `local/nonfinite-unit-interval-20260531`
- HEAD: run `git rev-parse HEAD` before citing a commit
- Author: `Rob Sneiderman <robbysneiderman@gmail.com>`

This memo records the FormalSLT verification surface. TheoremPath branch state
must be checked in the TheoremPath worktree before any TheoremPath action.

## What Is Proved

### Countable-Time Finite-Class Hoeffding

Main bundled API:

- `FiniteClassConfidenceSequence.failure_probability_le`
- Anchor: `FormalSLT/UniformConvergence.lean:3718`

Supporting declarations:

- `finiteClassConfidenceSequenceFailureEvent`
  (`FormalSLT/UniformConvergence.lean:3624`)
- `FiniteClassConfidenceSequence`
  (`FormalSLT/UniformConvergence.lean:3641`)
- `anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_confidenceSequence_fromHoeffding`
  (`FormalSLT/UniformConvergence.lean:3663`)
- `zeroOneDyadicFiniteClassConfidenceRadius_le_of_sampleSize_ge`
  (`FormalSLT/UniformConvergence.lean:3748`)

Meaning: for a finite nonempty hypothesis class, a fixed finite sample, a
probability measure, coordinate-wise independent `[0,1]` losses, a risk identity,
and a positive real failure budget, the named all-times/all-hypotheses
confidence-sequence failure event has measure at most `ENNReal.ofReal δ`.

The sample-size theorem gives the displayed review-count bridge used by
TheoremPath Stage A:

```text
(log 2 - log(δ * 2^(-1-t) / card(H))) / (2 * ε^2) ≤ sampleSize
```

implies the named dyadic radius is at most `ε`.

### UnitInterval Dudley Bridge

Main local declarations:

- `unitIntervalRademacherLinearSup_expectation`
  (`FormalSLT/Covering/UnitIntervalDudley.lean:912`)
- `unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m2_bound`
  (`FormalSLT/Covering/UnitIntervalDudley.lean:2054`)
- `unitIntervalRoundedDyadicGridDudleyInstance`
  (`FormalSLT/Covering/UnitIntervalDudley.lean:1555`)
- `unitIntervalRademacherLinearSupRoundedDyadicGridAdapter`
  (`FormalSLT/Covering/UnitIntervalDudley.lean:1883`)
- `unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound`
  (`FormalSLT/Covering/UnitIntervalDudley.lean:2088`)
- `unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound_prefixFree`
  (`FormalSLT/Covering/UnitIntervalDudley.lean:2113`)
- `unitIntervalRademacherLinearSup_dudley_m0_bound`
  (`FormalSLT/Covering/UnitIntervalDudley.lean:2178`)

Meaning: the finite-net Dudley machinery reaches a concrete non-finite metric
index space, the unit interval, through supplied supremum and rounded dyadic
finite-grid certificates. The result is a finite-horizon bridge, not a full
continuous Dudley theorem. The rounded-grid bridge also now routes through the
packaged `FiniteDyadicDudleyInstance` API.

### Packaged Finite Dyadic Dudley API

Main local declarations:

- `FiniteDyadicDudleyInstance`
  (`FormalSLT/Covering/FiniteSubGaussianChaining.lean:4573`)
- `FiniteDyadicDudleyInstance.SupremumAdapter`
  (`FormalSLT/Covering/FiniteSubGaussianChaining.lean:4592`)
- `FiniteDyadicDudleyInstance.projected_dudley_bound`
  (`FormalSLT/Covering/FiniteSubGaussianChaining.lean:4607`)
- `FiniteDyadicDudleyInstance.suppliedSup_dudley_bound`
  (`FormalSLT/Covering/FiniteSubGaussianChaining.lean:4626`)
- `dyadicChainingFiniteNetSequenceOfTotallyBounded`
  (`FormalSLT/Covering/TotalBoundedDudley.lean:614`)
- `finiteDyadicDudleyInstanceOfTotallyBounded`
  (`FormalSLT/Covering/TotalBoundedDudley.lean:667`)

Meaning: the finite examples package the finite sub-Gaussian process, dyadic
net sequence, coarse budget, variance positivity, and terminal supplied-supremum
adapter once, then route through the packaged projected and supplied-supremum
Dudley theorems.

### Two-Point Dyadic-Net API Check

Main local declarations:

- `twoPointDyadicNetSequence`
  (`FormalSLT/Covering/TwoPointDudley.lean:174`)
- `twoPointDudleyInstance`
  (`FormalSLT/Covering/TwoPointDudley.lean:220`)
- `twoPointRademacher_projected_dudley_m_bound`
  (`FormalSLT/Covering/TwoPointDudley.lean:229`)
- `twoPointRademacherSupAdapter`
  (`FormalSLT/Covering/TwoPointDudley.lean:265`)
- `twoPointRademacherSup_dudley_m_bound`
  (`FormalSLT/Covering/TwoPointDudley.lean:275`)

Meaning: the generic `FiniteDyadicNetSequence` and packaged
`FiniteDyadicDudleyInstance` wrappers are instantiated on a second metric index
family. This is an API-usability check, not a stronger Dudley theorem.

### Finite Discrete Dyadic-Net API Check

Main local declarations:

- `finDiscreteDyadicNetSequence`
  (`FormalSLT/Covering/FiniteDiscreteDudley.lean:240`)
- `finDiscreteDyadicCoverCount`
  (`FormalSLT/Covering/FiniteDiscreteDudley.lean:171`)
- `finDiscreteDudleyInstance`
  (`FormalSLT/Covering/FiniteDiscreteDudley.lean:286`)
- `finDiscreteRademacher_projected_dudley_m_bound`
  (`FormalSLT/Covering/FiniteDiscreteDudley.lean:295`)
- `finDiscreteRademacherSup_true`
  (`FormalSLT/Covering/FiniteDiscreteDudley.lean:314`)
- `finDiscreteRademacherSupAdapter`
  (`FormalSLT/Covering/FiniteDiscreteDudley.lean:347`)
- `finDiscreteRademacherSup_dudley_m_bound`
  (`FormalSLT/Covering/FiniteDiscreteDudley.lean:357`)

Meaning: the generic `FiniteDyadicNetSequence` wrapper is instantiated for
`Fin n` with the discrete metric under `[Fact (2 ≤ n)]`. The example embeds a
one-coordinate Rademacher process at a distinguished point of `Fin n`, uses the
full finite set as every net, and exposes the nonconstant cover-count envelope
`n * n`. The theorem `finDiscreteRademacherSup_true` records that the supplied
supremum equals `1` on the positive Rademacher outcome. This checks the generic
wrapper's finite-family ergonomics and its supplied-supremum route; it is not a
stronger Dudley theorem than the unit-interval bridge.

## TheoremPath Stage A Alignment

TheoremPath Stage A should point the "Verified in Lean" link at:

```text
FormalSLT.UniformConvergence.FiniteClassConfidenceSequence.failure_probability_le
```

Touched TheoremPath files:

- `src/lib/formal-slt/manifest-link.ts`
- `src/components/mastery/hoeffding-confidence-display.tsx`
- `tests/formal-slt/manifest-link.test.ts`

The dyadic sample-size theorem is still available as a direct helper link, but
the default Stage A citation target is now the bundled API theorem.

Release note: if the Stage A link is hardcoded because the theorem is outside
the current TheoremPath claim manifest, a public PR should mention this as an
infrastructure adjustment unless a later manifest ingestion step removes the
hardcoded path.

## Verification Commands

FormalSLT:

```bash
~/.elan/bin/lake exe cache get
~/.elan/bin/lake build FormalSLT
for f in examples/*.lean; do ~/.elan/bin/lake env lean "$f"; done
~/.elan/bin/lake env lean examples/CheckV01Usability.lean
~/.elan/bin/lake env lean examples/CheckTwoPointDudley.lean
~/.elan/bin/lake env lean examples/CheckFiniteDiscreteDudley.lean
rg -n --pcre2 '^\s*(?:by\s+)?(?:sorry|admit)\b|:=\s*(?:by\s+)?(?:sorry|admit)\b' FormalSLT examples
rg -n --pcre2 '^\s*(?:axiom|constant)\s+[A-Za-z_]' FormalSLT examples
python3 scripts/generate_proof_frontier_manifest.py --check
git diff --check
python3 /Users/robsneiderman/Desktop/AI4MATH/scripts/audit_public_writing.py \
  README.md \
  docs/formalslt-v0.1-quickstart.md \
  docs/formalslt-v0.1-technical-note.md \
  docs/theorem-map.md \
  docs/theorempath-formalslt-v0.1-page-draft.mdx \
  docs/formalslt-v0.1-artifact-map-2026-06-01.md
```

FormalSLT results:

- Mathlib cache: no files to download.
- `lake build FormalSLT`: success, `2948` jobs.
- Example checkers: `23` files, all `EXIT=0`.
- `CheckV01Usability.lean`: exit `0`.
- `CheckTwoPointDudley.lean`: exit `0`.
- `CheckFiniteDiscreteDudley.lean`: exit `0`.
- `sorry` / `admit` scan: no matches.
- custom `axiom` / `constant` scan: no matches.
- proof-frontier manifest check: exit `0`.
- `git diff --check`: exit `0`.
- public-writing audit: passed.

The full build still prints existing unused-variable and unused-section-variable
warnings in unrelated Rademacher/Azuma files. They do not come from the v0.1
release-review memo or the confidence-sequence API changes.

TheoremPath:

```bash
npm test -- tests/formal-slt/manifest-link.test.ts tests/formal-slt/hoeffding-sample-size.test.ts tests/adaptive-feature-flags.test.ts
npm run typecheck
npm run audit:lean-manifest
npm run audit:public-copy
npx eslint src/lib/formal-slt/manifest-link.ts src/components/mastery/hoeffding-confidence-display.tsx tests/formal-slt/manifest-link.test.ts
git diff --check
```

TheoremPath results:

- Focused tests: `3` files, `39` tests passed.
- Typecheck: exit `0`.
- Lean manifest audit: valid, `56` entries, `56` Lean verified, `113` formal
  statements, `0` broken.
- Public-copy audit: passed across `27` page files.
- Targeted ESLint on touched files: exit `0`.
- `git diff --check`: exit `0`.

## What Is Not Proved

- No full continuous Dudley entropy-integral theorem is proved.
- No arbitrary measurable-supremum construction over non-finite classes is
  proved.
- No general separability theorem is proved.
- The confidence-sequence theorem is finite-class; it is not an infinite-class
  empirical-process theorem.
- The confidence-sequence bundle is an API boundary. It does not add probability
  strength beyond the checked Hoeffding chain it wraps.
- The localized Rademacher random-threshold layer remains conservative; the
  sharper whole-supremum theorem remains future work.
- A TheoremPath page may use a hardcoded FormalSLT theorem link until the
  FormalSLT declaration is ingested into a site manifest.

## What Can Be Shown Publicly After Review

After Rob's review and a separate explicit public-action approval, a public
summary can safely say:

- FormalSLT contains a checked finite-class countable-time Hoeffding confidence
  sequence with a bundled API object,
  `FiniteClassConfidenceSequence.failure_probability_le`.
- FormalSLT contains a checked unit-interval rounded-dyadic finite-net Dudley
  bridge for a concrete non-finite metric index space.
- FormalSLT contains a packaged finite dyadic Dudley API used by the two-point
  and finite-discrete examples.
- FormalSLT contains a second concrete finite dyadic Dudley instance over a
  two-point metric space, showing that the wrapper is reusable.
- FormalSLT contains a general finite discrete dyadic Dudley instance over
  `Fin n`, checking the same wrapper with a nonzero embedded Rademacher process
  and explicit nonconstant cover counts.
- TheoremPath Stage A can display a dyadic Hoeffding review-count calculation
  and cite the bundled FormalSLT theorem as the Lean-backed endpoint.

Do not publicly say:

- that FormalSLT proves a full continuous Dudley theorem;
- that FormalSLT proves general empirical-process theory;
- that the unit-interval bridge constructs arbitrary measurable suprema;
- that TheoremPath's current manifest ingests the bundled theorem as a
  first-class manifest entry unless that has been checked in TheoremPath.

## Push and PR Decision

This memo does not approve a push, pull request, release tag, website update, or
external comment. Public action still requires separate exact approval.

## Next Theorem Target

After v0.1 packaging review, the next theorem target is:

```text
Connect the total-bounded and unit-interval boundary layer to the packaged Dudley API where the hypotheses match.
```

The goal is to keep future Dudley examples from restating the same process,
net-sequence, coarse-budget, and terminal-supremum data. This generalizes further
than adding more one-off `m = k` corollaries. It is not a theorem constructing
arbitrary measurable suprema for all non-finite classes.
