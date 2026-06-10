# Release and Submission Strategy

This repo currently serves three related but distinct goals. Keep them
separate when writing docs, opening PRs, and preparing artifacts.

## 1. Research workflow submission

The workshop paper should be framed as a reproducible formalization workflow,
not just as a list of Lean theorems. The central claim is:

- Small theorem slices, explicit assumptions, cache-aware builds, full Lean
  verification, no-sorry/no-admit audits, and human review make the artifact
  inspectable and reproducible.

The paper should show:

- the cognitive research task: turning statistical learning theory proof
  sketches into checked Lean theorem statements;
- the workflow: decomposition into small proof PRs, failure handling,
  theorem-map/docs sync, CI gates, and paper-claim audits;
- reproducibility: the public repo, exact build commands, pinned commit or
  release tag, and enough process detail for another ML researcher to repeat
  the loop within a few hours;
- correctness: Lean build, example checkers, `#print axioms`, no
  `sorry`/`admit`, no custom axioms/constants, and conservative non-claims.

Do not pitch this as autonomous research or pure software engineering. The
workshop fit is the human-directed, verification-first research workflow:
the Lean kernel, CI, and human mathematical review decide what is accepted.

## 2. Public Lean repository

The public repo is the artifact reviewers and future contributors should be
able to inspect independently. Its goals are different from the paper:

- build quickly from a fresh checkout using Mathlib cache;
- expose a clean theorem spine with exact theorem names;
- separate closed theorem families from open work;
- invite small, reviewable contributions without exposing internal branch
  churn as the public story.

Before public launch:

- freeze a tag such as `v0.1.0` or `v0.1.0-rcN`;
- use the tag or commit SHA in the paper artifact paragraph;
- ensure public branch names, badges, repo description, release notes, and
  docs all match the launch snapshot;
- keep internal scratch worktrees and branch names out of the public mirror if
  using a clean-history public repo.

## 3. Later archival or full-paper venues

The longer paper should not be rushed into the workshop framing. It can absorb
new theorem families after they are closed and documented, for example more
continuous Dudley infrastructure, sharper concentration, or localized
Rademacher corollaries.

Use a separate decision gate for future venues:

- current repo builds and public release is clean;
- the workshop artifact is submitted or frozen;
- new theorem work has merged with docs and paper claims synced;
- the target venue's formatting, anonymity, deadline, and artifact policy are
  verified from the official call.

## Paper-section drafts

Each major lane keeps a paper-section draft beside its design doc, so writing
follows verification rather than racing it:

- PAC-Bayes test-time meta-theorem: `docs/pac-bayes-test-time-paper-section.md`.
- Continuous-posterior PAC-Bayes (Route B, v0.2 headline):
  `docs/route-b-paper-section-draft-2026-06-10.md`, paired with the design
  blueprint `docs/route-b-continuous-pac-bayes-blueprint-2026-06-10.md` and
  the scope in `docs/v0.2-milestone.md`.

A draft is publishable only when its `[PENDING]` rows are gone and its
verification paragraph carries real build numbers. The "What Not To Claim"
section of each draft is the honesty gate for the corresponding abstract.

## Count and claim policy

Use the CI count method when reporting Lean size:

```bash
find FormalSLT/ -name '*.lean' -exec cat {} + | wc -l
find FormalSLT/ -name '*.lean' | wc -l
```

For prose, prefer exact human-readable counts such as "19,339 Lean lines"
after rerunning the command. During active proof bursts, either omit the count
or refresh it immediately before tagging and submitting.
