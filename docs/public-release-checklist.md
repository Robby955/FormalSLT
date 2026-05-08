# Public Release Checklist

Use this before cutting a public showcase mirror or release candidate tag.

## Repository settings

- Default branch is clear. For the private preview repo this may be
  `release-candidate`; for a public showcase repo, prefer `main`.
- Default branch is protected before public launch:
  - require PRs before merging;
  - require CI to pass;
  - block force-pushes;
  - restrict direct pushes to maintainers if needed.
- Repository "About" description matches proved scope. Recommended text:

  > Lean 4 formalizations of statistical learning theory: ERM, Rademacher
  > symmetrization, Massart, binary VC bounds, contraction, linear predictors,
  > finite chaining, stability, PAC-Bayes, and Dudley bridge infrastructure.

- Release tag exists for the launch snapshot, for example `v0.1.0-rc2`.
- Stale draft PRs and internal worktree branches are not part of the public
  story.
- If publishing by flipping this private repository public, delete or archive
  stale internal branches first. If using a clean public mirror, push only the
  launch branch and release tags that should be part of the public artifact.
- CI badge branch matches the public default branch. Use `release-candidate`
  for the private preview repo and `main` for a clean public mirror.

## Source hygiene

- `.gitignore` excludes local Lean build artifacts, editor folders, agent
  scratch folders, environment files, and LaTeX build outputs.
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
rg -n --pcre2 '^\s*(?:by\s+)?(?:sorry|admit)\b|:=\s*(?:by\s+)?(?:sorry|admit)\b' FormalSLT examples
rg -n --pcre2 '^\s*(?:axiom|constant)\s+[A-Za-z_]' FormalSLT examples
git diff --check
```

Expected result:

- full Lean build passes;
- showcase checker prints only the standard Lean/Mathlib axioms for the public
  spine;
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
- Claims about continuous Dudley, infinite classes, separability, sharp
  McDiarmid, and continuous-posterior PAC-Bayes remain future work unless the
  exact theorem is proved.
- Contributing guide mentions AI-assisted contributions, branch flow, required
  checks, and good first issues.
- README and paper copy use exact human-readable line counts after the count
  command has been rerun on the launch snapshot.
- Paper submission notes point reviewers to a tag or exact commit SHA, not a
  moving branch.

## Paper and artifact split

- Workshop paper branches may be formatted or compressed differently from the
  public repo docs. Keep them synced on theorem facts, counts, and non-claims,
  but do not mix paper formatting changes into theorem PRs.
- The public artifact should be understandable without the paper: README,
  theorem map, examples, assumptions/nonclaims, related work, and contributor
  instructions should stand on their own.
- The paper should cite the artifact by public URL plus tag or commit once the
  launch snapshot is frozen.
