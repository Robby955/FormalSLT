# Agent Instructions

FormalSLT is a Lean 4 formalization repo. Work in small, reviewable branches
and keep public claims tied to checked theorem statements.

## First commands in a fresh checkout or worktree

Always fetch the Mathlib cache before any baseline build:

```bash
~/.elan/bin/lake exe cache get
~/.elan/bin/lake build FormalSLT
```

If `lake` is already on `PATH`, the shorter `lake exe cache get` and
`lake build FormalSLT` forms are fine. In this environment, the explicit
`~/.elan/bin/lake` path is the most reliable.

Do not cold-build Mathlib from source unless the cache command fails for a
specific reason that you report. Do not run multiple fresh Lean bootstrap or
cache-fetch steps in parallel in the same checkout; wait for the first one to
finish to avoid package-lock or index-lock conflicts.

## Branch and worktree hygiene

- Use a separate branch for every theorem or docs slice.
- Keep theorem work out of paper-only branches, and keep paper formatting work
  out of theorem branches unless the PR is explicitly a sync PR.
- Before editing, check:

  ```bash
  git status --short --branch
  git worktree list
  gh pr list --state open
  ```

- If another agent is already proving a theorem in the same module family, take
  a non-overlapping lane: docs sync, release checklist, paper consistency, or
  PR review.

## Verification before PRs

For any code or theorem PR:

```bash
~/.elan/bin/lake exe cache get
~/.elan/bin/lake build FormalSLT
for f in examples/*.lean; do echo "$f"; ~/.elan/bin/lake env lean "$f"; done
rg -n --pcre2 '^\s*(?:by\s+)?(?:sorry|admit)\b|:=\s*(?:by\s+)?(?:sorry|admit)\b' FormalSLT examples
rg -n --pcre2 '^\s*(?:axiom|constant)\s+[A-Za-z_]' FormalSLT examples
git diff --check
```

For a new public theorem, also add a `#check` / `#print axioms` entry to the
appropriate example file and confirm the public axiom set remains:

```text
[propext, Classical.choice, Quot.sound]
```

## Public claims

- Do not call the Dudley lane a full continuous Dudley theorem until a theorem
  with the required topological and measurability assumptions actually exists.
- Use human-readable line counts in prose, for example `19,339 Lean lines`,
  after rerunning the count command. Refresh the number before a release tag.
- Keep workshop-paper claims, public-repo claims, and future-venue claims
  separate. They can share the same artifact, but they should not blur what is
  proved today with what is planned next.
