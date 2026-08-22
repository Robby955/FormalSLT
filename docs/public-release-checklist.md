# Release Audit Checklist

Use this before cutting a release candidate tag or public artifact snapshot.

## Repository settings

- Default branch is clear, normally `main`.
- Default branch is protected before public launch:
  - require PRs before merging;
  - require at least one approving review;
  - require CI to pass;
  - block force-pushes;
  - restrict direct pushes to maintainers if needed.
- Enable immutable releases and a tag ruleset that blocks updates and deletion
  of `v*` tags before creating `v0.2.0`. The resolver-bound smoke detects moves
  during its run, but repository governance must prevent later mutation.
- External governance status on 2026-08-20: immutable releases were disabled,
  the repository had no rulesets, and branch protection required no approving
  review. These are open publication gates; local source changes do not satisfy
  them.
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
make verify-controlled-queue-structured-ope-code-freeze
make python-tests
make verify-release-asset-packaging
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
  topic imports, and hosted CI repeats that build on Linux and macOS;
- every tracked Lean module is reachable from the core umbrella or the optional
  applications umbrella, while `FormalSLT.lean` reaches no
  `FormalSLT.Applications` module;
- repository-tool Python self-tests pass;
- deterministic release-asset packaging tests pass, including exact-commit,
  staged-source-pin, unsafe-path, symlink, overwrite, and tamper refusals;
- the controlled-queue pre-beacon gate checks the frozen protocol, all four
  prospective generator/verifier lanes, the generic Lean receipt reduction,
  and both generated-module branches without fetching a beacon or creating a
  prospective artifact; it fails if either the oracle true-kernel or fixed-range
  `PLANNED_NOT_CHECKED` arithmetic row is relabeled as a confidence certificate,
  or if its planned `1/20` allocation is reported as a checked outer-mass bound;
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

If v0.2 includes the prospective controlled-queue outcome, first bind the
protocol and code-freeze checkpoint in an immutable public registration, then
perform the single authorized generation. Run
`make verify-controlled-queue-structured-ope-prospective-receipt` afterward;
it must verify the trace, receipt, arithmetic, and generated Lean certificate
in order. Report the outcome whether or not it crosses the frozen threshold.
No local protocol or compiler fixture is a substitute for that post-beacon
gate.

The archived code-freeze binding must be version one and must not contain a
final `registration_id`, because OSF creates that GUID only when it registers
the editable draft. Save the completed registration API response and archived
binding-file metadata independently; both verifiers require their registration
IDs to agree and the metadata SHA-256 to bind the exact archived bytes.

## Post-tag installation check

Do not run the release-tag smoke as a substitute for the pre-tag checks above.
After the target tag exists on the public remote, confirm the automatically
triggered **Release tag install smoke** workflow passes for both operating
systems. The workflow also retains manual dispatch for a named existing tag.
To run the identity checks locally, use a clean checkout at the resolved commit:

```bash
python3 scripts/release_tag_identity.py resolve \
  --tag v0.2.0 \
  --output formalslt-v0.2.0-resolution.json
read -r tag_object resolved_commit < <(
  python3 -c 'import json; x=json.load(open("formalslt-v0.2.0-resolution.json")); print(x["tag_object"], x["resolved_commit"])'
)
bash scripts/check_tag_install.sh \
  v0.2.0 "$tag_object" "$resolved_commit"
python3 scripts/generate_release_receipt.py \
  --tag v0.2.0 \
  --expected-tag-object "$tag_object" \
  --expected-commit "$resolved_commit" \
  --output formalslt-v0.2.0-exact-tag.json
```

The hosted workflow first resolves one tag object and peeled commit. For an
automatic tag-push run, that commit must also equal the push event's exact
`GITHUB_SHA`, preventing a move before the resolver starts from redefining the
triggered release. Manual dispatch deliberately performs one live resolution
of the named existing tag. Both operating-system jobs checkout the resolver
commit and compare every later remote lookup and Lake installation against the
resolver outputs. The final aggregate job requires one Linux and one macOS
receipt with the same tag, object, commit, tree, Lean toolchain, and Mathlib
revision, then checks the current remote once more. Missing, malformed, moved,
or ambiguous tags; mismatched checkouts; tracked changes; unreadable
toolchains; and unpinned Mathlib revisions are hard failures. The Elan
installer URL is pinned to an exact upstream commit.

Each operating-system job uploads its JSON receipt only after the downstream
build succeeds. The receipt itself asserts only resolver-bound tag identity and
source-environment metadata; CI success is established by the hosted job, not
by a field in the receipt. Neither a receipt nor a green workflow asserts that
a GitHub Release or DOI exists.

After the aggregate receipt check passes, the same workflow builds and stages
doc-gen4 at the resolver commit. It then uploads one run-scoped Actions
artifact containing exactly:

- `formalslt-v0.2.0-source.tar.gz`, rebuilt from Git blobs at the resolved
  commit with normalized archive metadata;
- `formalslt-v0.2.0-docs.tar.gz`, containing the already-staged documentation
  with source links pinned to that commit;
- `formalslt-v0.2.0-release-assets.json`, binding the tag object, commit, tree,
  toolchain, Mathlib revision, filenames, sizes, and SHA-256 digests; and
- `SHA256SUMS`, covering the two archives and JSON manifest.

The packager rejects a dirty or mismatched checkout, unsafe paths, symlinks,
unresolved documentation source tokens, a wrong docs source pin, archive
tampering, stale extra files, and an existing output directory. The Actions
artifact is preparation for review: it does not create or modify a tag, GitHub
Release, Pages deployment, archival deposit, or DOI. Download it only from the
successful run for the exact release tag, rerun the packager's `verify` mode,
and attach those same bytes to the draft GitHub Release before publication.

## Citation and publication ordering

- If `CITATION.cff` in the tagged artifact must contain the v0.2 DOI, first
  reserve that DOI in an unpublished archival deposit. Do not publish the
  deposit yet.
- Commit the reserved DOI and version to `CITATION.cff`, review that final
  metadata commit, and rerun the exact-SHA release gates before tagging.
- Create the protected tag, require the matched Linux/macOS receipt workflow,
  then publish the GitHub Release and archival deposit. Finally verify that the
  now-public DOI resolves to the same version, tag, commit, and tree.
- Merely reserving a DOI is not a release and must not be described as minted,
  published, or resolving.
- The versioned docs tarball is the immutable documentation artifact required
  for v0.2.0. A permanent `/v0.2.0/` Pages route is useful for discovery but is
  not a release gate when the GitHub Release and archival record link the
  versioned docs archive and the deployed current docs are pinned to the same
  commit.

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
