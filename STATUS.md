# FormalSLT — live state

Single source of truth for current library state. Update when you merge a PR.

## Current metrics (as of 2026-06-04)

| Metric | Value | How to verify |
|--------|-------|---------------|
| `.lean` files under `FormalSLT/` | **60** | `find FormalSLT -name '*.lean' -type f \| wc -l` |
| `.lean` files (FormalSLT/ + examples/) | **85** | `find FormalSLT examples -name '*.lean' -type f \| wc -l` |
| Total lines (FormalSLT/ + examples/) | **33,427** | `find FormalSLT examples -name '*.lean' -print0 \| xargs -0 wc -l` |
| Axiom profile | `[propext, Classical.choice, Quot.sound]` | `lake env lean examples/CheckShowcaseTheorems.lean` |
| `sorry` / `admit` / custom axioms | **0 / 0 / 0** | `rg -n 'sorry\|admit' FormalSLT examples` |
| Lean toolchain | 4.30.0-rc2 | `cat lean-toolchain` |
| Mathlib pin | 25b7ac7 | `cat lake-manifest.json` |

## Recent theorem ships

### PR #6 — 2026-06-04 (merged `108a139`)
Sharp McDiarmid bundle + PAC-Bayes Bernstein margin shell + README + SVG refresh

- **Sharp McDiarmid** (`Concentration.SharpMcDiarmid`): one-sided, lower-tail, and two-sided tails for a bounded-differences function over a homogeneous product measure. Sharp `2B²` exponent (vs. Azuma's `8B²`). Propagated into Rademacher, VC, and algorithmic-stability wrappers.
- **PAC-Bayes Bernstein margin-proxy shell** (`PACBayesBernstein`): supplied per-hypothesis variance proxy, normalized Bernstein prior-moment certificate, fixed-λ finite bad-event bounds, posterior-dependent square-root-plus-linear wrapper.
- Theorem-chain SVG refreshed.

### PR #5 — 2026-06-04 (merged `fd2720b`)
Sharp McDiarmid from dev (verified, additive): earlier McDiarmid constants + propagation groundwork.

### PR #4 — 2026-06-03 (merged `9cc6133`)
Cross-link FormalSLT README to live TheoremPath portfolio surface.

### PR #3 — 2026-06-02 (merged)
v0.1 docs package.

### PR #2 — 2026-05-31 (merged)
Conditional sub-Gamma extractor.

### PR #1 — 2026-05-27 (merged)
Finite localized Bernstein release route.

## Open PRs

None at 2026-06-04.

## Local-only commits awaiting public push

None at 2026-06-04. Local `main` is in sync with `origin/main` at `108a139`.

## Companion paper status

- **DSAA 2026** (IEEE Research Track): stress-testing-protocol paper repurposed from MoodSpan stress eval. READY, not yet submitted. Deadline: 2026-06-07.
- **CIED 2026** (Spanish ed-tech congress): TheoremPath interactive-Lean-verification. READY, not yet submitted. Deadline: 2026-06-19.

## Roadmap (in progress / queued)

**Done:**
- Sharp McDiarmid for additive-independent, Doob-martingale, and homogeneous-product-measure cases ✓
- PAC-Bayes Bernstein supplied margin-proxy shell ✓
- Finite Dudley entropy-budget infrastructure ✓
- v0.1 headline endpoints (Hoeffding confidence sequence, unit-interval Dudley bridge) ✓

**Queued / open:**
- [ ] PAC-Bayes concrete margin-loss Bernstein extractor (all-real-λ or continuous-posterior)
- [ ] Sharp McDiarmid over arbitrary non-iid product spaces
- [ ] Continuous Dudley entropy-integral theorem over total-bounded classes
- [ ] Theorem-chain SVG: add PAC-Bayes Bernstein node

## Last updated

2026-06-04 by dispatch `feature/public-readme-refresh-2026-06-04`.
