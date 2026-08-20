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

  > Lean 4 formalizations of statistical learning theory and sequential
  > inference: empirical-Bernstein PAC-Bayes, adaptive trajectories,
  > finite-state stationary certification, Rademacher, VC, and stability.

- Release tag exists for the snapshot, for example `v0.2.0`.
- Stale draft PRs and local worktree branches are not part of the release
  artifact.
- CI badge branch matches the public default branch.

## Source hygiene

- `.gitignore` excludes local Lean build artifacts, editor folders, scratch
  folders, environment files, and LaTeX build outputs.
- No local config directories, local cache, or generated build output is
  staged.
- `git status --short` is clean before tagging.
- The launch branch is synced with `origin`, and `gh pr list --state open`
  shows no unexpected release-blocking PRs.

## Required checks

```bash
lake exe cache get
lake build FormalSLT
make examples
make tutorials
make api
make downstream
python3 -m pip install -r requirements-dev.txt
make python-tests
lake env lean examples/CheckShowcaseTheorems.lean
lake env lean examples/CheckSubGammaExtractor.lean
lake env lean examples/CheckUnitIntervalDudley.lean
bash scripts/check_axioms.sh
bash scripts/check_witness_quality.sh
FIDELITY_BASE_REF=origin/main bash scripts/check_statement_fidelity.sh
python3 scripts/generate_proof_frontier_manifest.py --check
python3 scripts/generate_theorem_index.py --check
python3 scripts/generate_badge_counts.py --check
python3 scripts/check_doc_anchors.py --self-test
git ls-files -z -- '*.md' '*.mdx' | \
  xargs -0 python3 scripts/check_doc_anchors.py
python3 scripts/check_no_orphan_lean_modules.py
python3 scripts/stage_docs_site.py --self-test
python3 scripts/stage_docs_site.py --check-source
lake -Kenv=dev build FormalSLT:docs
rg -n --pcre2 '^\s*(?:by\s+)?(?:sorry|admit)\b|:=\s*(?:by\s+)?(?:sorry|admit)\b' FormalSLT examples
rg -n --pcre2 '^\s*(?:axiom|constant)\s+[A-Za-z_]' FormalSLT examples
git diff --check
```

Expected result:

- full Lean build passes;
- every example, isolated stable-import checker, and tutorial type-checks;
- the 19 allowlisted v0.2 declaration types and axiom reports match their
  committed snapshot;
- the two retained v0.1 compatibility declaration types match their committed
  snapshot;
- all exact Lean examples from the annotated v0.1.0 tag compile against the
  current library;
- the independent downstream Lake package builds through all four supported
  topic imports;
- every tracked Lean module is reachable from the core umbrella or the optional
  applications umbrella, while `FormalSLT.lean` reaches no
  `FormalSLT.Applications` module;
- repository-tool Python self-tests pass;
- changed theorem statements pass the fail-closed fidelity scan against the
  exact release base;
- public theorem checker prints only the standard Lean/Mathlib axioms for the public
  spine;
- conditional sub-Gamma and unit-interval Dudley checkers print only the
  standard Lean/Mathlib axioms for their public theorem surfaces;
- proof-frontier manifest is in sync with the theorem map and source counts;
- generated proof-frontier, theorem-index, badge, and documentation-anchor
  artifacts are current;
- the static Pages source passes its self-test and source check, and the full
  documentation target builds;
- the manifest records the transitive-axiom policy and live gate command, not a
  hard-coded pass result; `scripts/check_axioms.sh` obtains `#print axioms`
  reports from Lean for every curated theorem, fails if a report is missing,
  and permits only `propext`, `Classical.choice`, and `Quot.sound`;
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
- Public summaries distinguish the checked sharp McDiarmid and
  continuous-posterior endpoints from open full continuous-Dudley,
  separability, all-real-tilt, and unrestricted stationary/mixing claims.
- Distinguish proof status (`PROVED`, `CONDITIONAL`, `OPEN`) from literature
  fidelity (`REPRODUCTION`, `SPECIALIZATION`, `DERIVED VARIANT`).
- Do not present the supplied-certificate continuous Dudley interfaces as an
  unrestricted measurable-supremum theorem.
- Do not turn the checked measurable-hypothesis empirical-Bernstein theorem
  into a continuous-observation or optional-stopping claim.
- Keep continuous-state stationary risk, post-outcome catalog construction,
  predictable or all-real tilt optimization, and general prefix-dependent
  random starts open unless an exact checked endpoint closes them.
- Contributing guide mentions contribution responsibility, branch flow,
  required checks, and good first issues.
- README and public docs use exact human-readable line counts after the count
  command has been rerun on the launch snapshot.
- External references point readers to a tag or exact commit SHA, not a moving
  branch.
- `docs/api-stability.md` names the exact supported imports and declarations;
  release notes list every deprecation or intentional signature change.

## Artifact split

- If a separate manuscript or report cites the repository, keep theorem facts,
  counts, and non-claims synced with the tagged artifact.
- The repository artifact should be understandable on its own: README,
  theorem map, examples, assumptions/nonclaims, related work, and contributor
  instructions should stand on their own.
- External writing should cite the artifact by public URL plus tag or commit
  once the snapshot is frozen.
