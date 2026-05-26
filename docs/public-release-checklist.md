# Release Audit Checklist

Use this before cutting a release candidate tag or public artifact snapshot.

## Repository settings

- Default branch is clear, normally `main`.
- Default branch is protected before public launch:
  - require PRs before merging;
  - require CI to pass;
  - block force-pushes;
  - restrict direct pushes to maintainers if needed.
- Repository "About" description matches proved scope. Recommended text:

  > Lean 4 formalizations of statistical learning theory: ERM, Rademacher
  > symmetrization, Massart, binary VC bounds, contraction, linear predictors,
  > finite chaining, stability, PAC-Bayes, and Dudley bridge infrastructure.

- Release tag exists for the snapshot, for example `v0.1.0`.
- Stale draft PRs and local worktree branches are not part of the release
  artifact.
- CI badge branch matches the public default branch.

## Source hygiene

- `.gitignore` excludes local Lean build artifacts, editor folders, scratch
  folders, environment files, and LaTeX build outputs.
- No `.lake/`, `.claude/`, `.codex/`, local cache, or generated build output is
  staged.
- `git status --short` is clean before tagging.
- The launch branch is synced with `origin`, and `gh pr list --state open`
  shows no unexpected release-blocking PRs.

## Required checks

```bash
lake exe cache get
lake build FormalSLT
lake env lean examples/CheckShowcaseTheorems.lean
python3 scripts/generate_proof_frontier_manifest.py --check
rg -n --pcre2 '^\s*(?:by\s+)?(?:sorry|admit)\b|:=\s*(?:by\s+)?(?:sorry|admit)\b' FormalSLT examples
rg -n --pcre2 '^\s*(?:axiom|constant)\s+[A-Za-z_]' FormalSLT examples
git diff --check
```

Expected result:

- full Lean build passes;
- showcase checker prints only the standard Lean/Mathlib axioms for the public
  spine;
- proof-frontier manifest is in sync with the theorem map and source counts;
- no executable `sorry`, no executable `admit`, no custom axioms, and no custom
  constants are found;
- whitespace check passes.

In a fresh checkout or worktree, run `lake exe cache get` before the first
build. If `lake` is not on `PATH`, use `~/.elan/bin/lake`. A cold Mathlib
source build is not part of the release checklist.

## Public copy

- README theorem table renders correctly on GitHub.
- SVG theorem chain renders without overlapping text.
- "Current boundaries" is short in the README and links to the full scope doc.
- Public summaries state only checked theorem facts and explicit non-claims;
  keep internal process notes, private branches, and unverifiable attribution
  out of release copy.
- Claims about continuous Dudley, infinite classes, separability, sharp
  McDiarmid, and continuous-posterior PAC-Bayes remain future work unless the
  exact theorem is proved.
- Contributing guide mentions contribution responsibility, branch flow,
  required checks, and good first issues.
- README and paper copy use exact human-readable line counts after the count
  command has been rerun on the launch snapshot.
- External references point readers to a tag or exact commit SHA, not a moving
  branch.

## Artifact split

- If a separate manuscript or report cites the repository, keep theorem facts,
  counts, and non-claims synced with the tagged artifact.
- The repository artifact should be understandable on its own: README,
  theorem map, examples, assumptions/nonclaims, related work, and contributor
  instructions should stand on their own.
- External writing should cite the artifact by public URL plus tag or commit
  once the snapshot is frozen.
