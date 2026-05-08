# AI4Research @ ICML 2026 — Submission Notes

This file tracks everything needed to take `paper/workshop.tex` from
the working draft in this branch to a submitted workshop paper.

## Target venue

- **Workshop:** AI4Research @ ICML 2026
  ([icml.cc/Conferences/2026/Workshops](https://icml.cc/Conferences/2026/Workshops))
- **Page limit:** 4 pages of body content + unlimited references
- **Format:** ICML 2026 style (`icml2026.sty`), single-blind unless the
  workshop announces otherwise (verify on the workshop page once the CFP
  is posted)
- **Submission system:** ICML workshops typically use OpenReview or
  CMT — confirm from the workshop CFP. Likely OpenReview.
- **Anonymity:** AI4Research has historically been single-blind
  (author-visible). Confirm from the CFP before submitting.

> **TODO before submission:** The CFP, deadline, and submission link
> were not yet final at draft time (2026-05-07). Re-check the workshop
> page and update this file with the exact deadline, submission URL,
> and any format requirements that differ from the assumptions above.

## Current status of the draft

- `paper/workshop.tex` builds with `pdflatex`/`bibtex` to a 4-page PDF
  using a self-contained `article` class with two-column ICML-style
  geometry. **No external `icml2026.sty` is required** for the working
  draft to compile, so the file is portable and reviewable in this PR
  without needing to vendor template files.
- `paper/main.tex` is the longer CPP-style draft kept as the source of
  truth for the prose; `workshop.tex` is the compressed 4-page version.
- A theorem-dependency diagram (TikZ) appears as Figure 1 in both
  drafts, summarizing the three-track spine (PAC-VC, PAC-Bayes,
  stability) and the cross-track reuse of the Azuma exposure-martingale
  tail.
- The workshop positioning is workflow-first: human-directed AI agents propose
  small formalization steps, while Lean, CI, theorem-map sync, and paper-claim
  audits decide what survives. Keep this distinct from a pure theorem-count
  paper or a public-repo launch announcement.

To rebuild:

```bash
cd paper
make workshop          # produces workshop.pdf (4 pages)
make main              # produces main.pdf  (9 pages, CPP draft)
```

### Known build warnings (benign)

The workshop draft builds clean. The `main.tex` (acmart sigplan) build
emits four expected warnings that are safe to ignore for review:

1. `Class acmart Warning: You do not have the newtxmath package
   installed.` — `acmart` prefers libertine + newtxmath fonts; without
   newtxmath it falls back to Latin Modern math, which is what the
   built PDF uses. Resolve before camera-ready by running
   `tlmgr install newtx` (or its user-mode equivalent).
2. `Class acmart Warning: ACM reference format is mandatory` and
3. `Class acmart Warning: CCS concepts are mandatory` — these fire
   because the draft anonymizes the bibstrip and skips CCS concepts
   while in `review` mode; both are mandatory only for camera-ready.
4. `Package balance Warning: You have called \balance in second
   column` — cosmetic; `balance` is invoked at end of document to
   even out the final two-column page.

## Pre-submission checklist

When the CFP is final and you are ready to submit:

- [ ] **Switch to the official ICML 2026 template.** Download
      `icml2026.sty` and the corresponding `icml2026.bst` from the ICML
      site. Replace the preamble of `workshop.tex` with the template's
      `\documentclass` and packages. The body text, `lstlisting` blocks,
      and `\bibliography{references}` line should drop in unchanged.
- [ ] **Set the camera-ready / submission flag.** Most ICML templates
      ship with `\usepackage[accepted]{icml2026}` for camera-ready and
      no option (or `[anonymous]`) for blind review. Verify from the
      template README.
- [ ] **De-anonymize / anonymize.** AI4Research is typically
      single-blind; if so, leave the author block as
      `Robby Sneiderman \\ \texttt{robbysneiderman@gmail.com}`.
      If the workshop is double-blind, replace with
      `\author{Anonymous}` and remove any first-person references that
      identify the author.
- [ ] **Confirm the public repo URL.** The draft cites
      `https://github.com/Robby955/lean-statistical-learning`. Verify
      this is the current public URL on the day of submission. If a
      release tag exists, use the tagged URL
      (e.g. `.../tree/v0.1.0`) so reviewers see a frozen artifact.
- [ ] **Pin the commit hash.** Add a sentence to the artifact
      paragraph naming the commit reviewers should `git checkout`. Run
      `git rev-parse HEAD` on `release-candidate` and paste the SHA in.
- [ ] **Build and check page count.** `make workshop` should produce a
      4-page PDF. ICML's official template has slightly tighter
      typography than the self-contained draft — expect a small
      reflow. If it overflows by a few lines, trim the introduction
      first (it has the most slack); the technical sections should
      stay intact.
- [ ] **Refresh literal repo counts.** Re-run the Lean line/module count on
      the exact artifact commit and update any literal counts in
      `workshop.tex`, `main.tex`, README, and docs before submission.
- [ ] **Re-run zero-`sorry` audit before tagging the artifact.** From
      the repo root:
      ```bash
      ~/.elan/bin/lake exe cache get
      ~/.elan/bin/lake build FormalSLT
      grep -rn "^[^-]*\bsorry\b\|^[^-]*\badmit\b\|^[^-]*\baxiom\b\|^[^-]*\bconstant\b" \
        FormalSLT/ examples/ | grep -v "^[^:]*:[^:]*:--"
      ~/.elan/bin/lake env lean examples/CheckShowcaseTheorems.lean
      ```
      The first command should succeed; the grep should return no
      executable hits; the showcase-checker should print
      `[propext, Classical.choice, Quot.sound]` for every theorem.
      If `lake` is already on `PATH`, the shorter `lake ...` form is
      fine, but the cache step should come before the first build.
- [ ] **Verify cited theorem locations.** The draft cites specific
      file:line locations for every Lean snippet. Re-run:
      ```bash
      grep -n "theorem vc_erm_excessRisk_tail\b\|theorem vc_erm_sample_complexity\b\|theorem donsker_varadhan\b\|theorem expectedFiniteGeneralizationGap_le_uniformStability_finiteProduct\b\|theorem pac_bayes_generalization\b\|theorem finiteMcAllesterGridPeeling_badEventMass_le_delta\b" \
        FormalSLT/VC/SampleComplexity.lean \
        FormalSLT/PACBayesKL.lean \
        FormalSLT/AlgorithmicStability.lean \
        FormalSLT/PACBayesBoundedLoss.lean
      ```
      and confirm the line numbers match those in the LaTeX captions.
      Update the captions if the source has shifted.
- [ ] **Spell-check and tighten.** `aspell -t -c workshop.tex` or
      similar; check abstract is ≤150 words; check that every claim in
      the paper is also stated in the repo.
- [ ] **Submit.** Upload PDF + `references.bib`-equivalent metadata
      via the workshop submission system; record the submission ID in
      this file once received.

## Open questions / decisions deferred to Rob

- **Single-author vs. acknowledgements.** The current author block is
  Robby Sneiderman alone. If anyone else contributed to the library
  (e.g. via PR review), consider an acknowledgements paragraph. Format
  is template-dependent.
- **Title.** Current: *Machine-Checked PAC-Bayes and Stability Bounds
  in Lean 4: A Finite-First Formalization of Statistical Learning
  Theory.* Alternative considered:
  *Finite-First Formalization of Statistical Learning Theory in Lean 4.*
- **Headline scope.** The 4-page version foregrounds Bousquet--Elisseeff
  + finite-grid McAllester PAC-Bayes; the PAC--VC tail is shown as one
  representative theorem rather than the full route. The full draft
  (`main.tex`) is the place that argues the spine in detail.

## Repo URL

Public artifact: <https://github.com/Robby955/lean-statistical-learning>.

The draft references a commit-pinned artifact in the abstract — set the
commit SHA in `workshop.tex` immediately before submission.

For the repo/paper split and future-venue gate, see
[`docs/release-and-submission-strategy.md`](../docs/release-and-submission-strategy.md).
