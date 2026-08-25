# One event across every sample size

This package explains one checked FormalSLT theorem in two native cuts:

- an 86-second 1920 x 1080 repository film;
- a 44-second 1080 x 1350 mobile film, composed independently rather than cropped.

The hook is concrete:

> A fixed-time guarantee assumes one fixed look. This Lean theorem controls
> every sample size `n >= 4` on one event, for bounded adapted increments that
> are conditionally centered and satisfy a conditional second-moment bound.

The result is a building block for machine-checked learning guarantees under
repeated monitoring, adaptation, and dependence. It is not a claim that an
entire trained model or deployed ML system has been verified.

## Exact theorem boundary

The film states the theorem's probability-measure model, measurability and
integrability assumptions, one-step adaptedness, almost-everywhere increment
bound, almost-everywhere conditional centering, and almost-everywhere
conditional second-moment bound. For the selected epoch `j`,

```text
4^(j+1) <= n < 4^(j+2)
B_j = log(2/delta) + log(j+1) + log(j+2)
W_n = 2 sqrt(2 sigma^2 B_j / n) + 4 b B_j / (3n).
```

The theorem produces a set `G` with complement real mass at most `delta` and
the displayed two-sided bound for every `n >= 4` on `G`. The theorem does not
assert that `G` is measurable, so the film does not rewrite this as “with
probability at least `1-delta`.”

On screen, `mu_R(G^c)` denotes Lean's `mu.real G^c`, not an unqualified event
probability.

This is an allocated polynomial fixed-tilt stitch with an
iterated-logarithm-order confidence price. It is not the sharp law of the
iterated logarithm, an empirical-variance-adaptive result, an optional-stopping
theorem, a predictable data-selected tilt, or itself an e-process. No
first-formalization or priority claim is made.

## Evidence binding

`extract_facts.py` reads every theorem and documentation anchor using `git show`
at the exact v0.2.0 commit
`e01f857d1604788be35fdc2f3dc7108851471a88`. It verifies the complete endpoint
assumptions, quantifier order, selected-epoch definition, displayed width, the
running-mean definition, checker surface, and public nonclaims. It writes:

- `facts.json`, the source-oriented extraction;
- `claim-receipt.json`, the canonical public claim and TeX surface consumed by
  both film classes.

The pinned theorem blob is unchanged from its original merge, but the public
media binds to the released commit. `verify_media.py` records source hashes,
the theorem commit, stream metadata, audio measurements, and final media hashes.

## Visual and audio contracts

All displayed mathematics is rendered by Manim `MathTex`. The fixed-tilt scene
plots the actual `a + c/n` boundary shape from the checked sub-Gamma expression.
The stitched scene evaluates the displayed `W_n` at every plotted integer
sample size under declared positive
parameters (`sigma^2 = 0.08`, `b = 0.25`, `delta = 0.05`); only its sample path
is illustrative.

The original score is synthesized deterministically without samples or
third-party audio. It uses finite mid-register swells, three restrained accents,
and deliberate silence instead of a continuous sub-bass drone. Final receipts
include peak, integrated loudness, loudness range, and true-peak measurements.

## Validate without Lean or a render

```bash
./media/stitched-lil-result-film/render.sh validate
```

This checks pinned facts and claims, Python syntax, native aspect contracts,
caption timing, soundtrack determinism, render script syntax, and receipt
logic. It neither runs a Lean umbrella build nor writes movies.

## Render

Requirements are Manim Community 0.20.1, FFmpeg/FFprobe, and a working LaTeX
installation. Render one composition at a time:

```bash
./media/stitched-lil-result-film/render.sh proof-main
./media/stitched-lil-result-film/render.sh proof-social
./media/stitched-lil-result-film/render.sh final-main
./media/stitched-lil-result-film/render.sh final-social
./media/stitched-lil-result-film/render.sh posters
```

For the bounded release pass, render both cuts and both posters sequentially,
then stage only the verified artifacts:

```bash
./media/stitched-lil-result-film/render.sh release
./media/stitched-lil-result-film/render.sh stage-delivery
```

Fresh render intermediates remain under the ignored `out/` and temporary media
directories. Final delivery files are copied into `delivery/` only after visual,
audio, and hash verification.

## Package map

- `STORYBOARD.md`: reviewed visual logic and theorem boundaries.
- `TRANSCRIPT.md`, `TRANSCRIPT-SOCIAL.md`: accessible main and mobile copy.
- `captions-main.vtt`, `captions-social.vtt`: timed caption sidecars.
- `film_config.json`: independent timing and resolution contracts.
- `extract_facts.py`, `facts.json`, `claim-receipt.json`: exact-tag claim pin.
- `stitched_lil_result.py`: both native compositions and posters.
- `compose_soundtrack.py`, `SOUNDTRACK.md`: deterministic original score.
- `render.sh`, `verify_media.py`, `stage_delivery.py`: bounded render, receipt,
  and delivery pipeline.
- `test_*.py`: source, layout, soundtrack, and receipt gates.
