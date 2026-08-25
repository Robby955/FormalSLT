# Release checklist

This checklist binds a FormalSLT release to one reviewed commit without
repeating expensive local builds that hosted CI has already completed for the
same source.

## 1. Prepare one release commit

- Start from current `origin/main` in a clean worktree.
- Update `README.md`, `CHANGELOG.md`, `CITATION.cff`, the API policy, and
  the versioned release notes.
- Keep theorem changes out of the release-only pull request.
- Confirm the diff contains no build output, local configuration, or generated
  prospective evidence.

## 2. Require exact-head CI

The release pull request must pass its required `build` check at the exact
head commit. If theorem source has not changed since a fully checked main
commit, do not start a second local full build merely to reproduce the hosted
run. Run the focused documentation checks locally and let CI classify the
release diff.

Focused local checks:

```bash
python3 scripts/classify_ci_scope.py --self-test
python3 scripts/generate_theorem_index.py --check
python3 scripts/stage_docs_site.py --check-source
python3 scripts/stage_docs_site.py --self-test
python3 scripts/check_doc_anchors.py --self-test
git ls-files -z -- '*.md' '*.mdx' | \
  xargs -0 python3 scripts/check_doc_anchors.py
git diff --check
```

For a release that changes Lean source, CI must run the full build, examples,
public API checks, downstream consumers, axiom checks, and repository-tool
tests. Do not substitute a partial local build for that gate.

## 3. Tag the merged commit

- Confirm immutable releases are enabled and the active version-tag rule blocks
  updates and deletions without blocking creation.
- Verify `origin/main` and the local checkout resolve to the same commit.
- Create the annotated `vX.Y.Z` tag at that commit and push only that tag.
- Do not move or reuse a published version tag.
- Wait for **Release tag install smoke** to finish.

The tag workflow:

1. resolves the tag object and peeled commit once;
2. installs and builds the tagged dependency on Linux and macOS;
3. verifies the two identity receipts agree;
4. builds documentation with source links pinned to the release commit; and
5. packages deterministic source and documentation archives, a manifest, and
   `SHA256SUMS`.

## 4. Publish the GitHub Release

- Download the asset bundle from the successful tag workflow.
- Run the packager's `verify` mode against the downloaded bytes when a local
  staged-docs tree is available.
- Create a draft GitHub Release for the existing tag.
- Attach exactly the source archive, documentation archive, identity manifest,
  and `SHA256SUMS` to the draft.
- Copy the versioned release notes and include the tag commit and tree hashes.
- Check the complete draft, then publish it. Immutable releases prevent
  changing or deleting its assets after publication.

## 5. Verify the public result

- The release page resolves and lists the intended tag and assets.
- The README install command uses that tag.
- A fresh downstream Lake project resolves the tag to the release commit.
- GitHub Pages is green and its generated source links point to the same
  release commit.
- The overview film and poster load from a versioned URL.

## Optional archival deposit

A DOI is useful but is not required to create a valid GitHub release. If an
archival deposit is published later, update `CITATION.cff` only after the DOI
exists and verify that the deposit identifies the same version and tag. Never
describe a reserved or draft identifier as a resolving DOI.

The controlled-queue prospective protocol is a separate research workflow. It
is not a release gate and v0.2.0 does not include a fresh prospective outcome.
