# One checked event, every sample size from four onward

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

The current receipt is bound to public-main commit
`44ebbff74aea1dcd5b25592aefb561aeede51696`. Its endpoint proves that `G` is
measurable, that `mu.real(G) >= 1 - delta`, and that the displayed two-sided
bound holds for every `n >= 4` on `G`. The extractor retains the older v0.2.0
outer-mass profile only so that the tagged release remains reproducible.

This is an allocated polynomial fixed-tilt stitch with an
iterated-logarithm-order confidence price. It is not the sharp law of the
iterated logarithm, an empirical-variance-adaptive result, an optional-stopping
theorem, a predictable data-selected tilt, or itself an e-process. No
first-formalization or priority claim is made.

## Evidence binding

`extract_facts.py` reads every theorem and documentation anchor using `git show`
at the exact commit in `film_config.json`. The current pin is the measurable
endpoint merge `44ebbff74aea1dcd5b25592aefb561aeede51696`. The extractor verifies the
complete endpoint assumptions, quantifier order, selected-epoch definition,
displayed width, running-mean definition, checker surface, and public nonclaims.
It writes:

- `facts.json`, the source-oriented extraction;
- `claim-receipt.json`, the canonical public claim and TeX surface consumed by
  both film classes;
- `TRANSCRIPT.md` and `TRANSCRIPT-SOCIAL.md`, generated from checked templates.

To repin the film after a future public theorem change, fetch public main and
bind the exact new merge SHA:

```bash
git fetch origin main
./media/stitched-lil-result-film/render.sh bind-source <40-character-merge-sha>
```

The binding command refuses abbreviated SHAs, commits not reachable from the
fetched `origin/main`, commits missing the measurable theorem/checker, or any
source whose checked statement no longer matches the displayed formula. It
does not render media.

`verify_media.py` records the pinned theorem blob, render-source hashes, stream
metadata, final media hashes, and audio measurements when the selected mode has
audio.

## Visual and audio contracts

All displayed mathematics is rendered by Manim `MathTex`. The fixed-tilt scene
plots the actual `a + c/n` boundary shape from the checked sub-Gamma expression.
The stitched scene evaluates the displayed `W_n` at every plotted integer
sample size under declared positive
parameters (`sigma^2 = 0.08`, `b = 0.25`, `delta = 0.05`); only its sample path
is illustrative.

The built-in score is synthesized deterministically without samples or
third-party audio. A user-supplied Suno master may be selected only with the
absolute-path, source-hash, and rights/provenance contract in `SOUNDTRACK.md`.
Both scored modes record loudness and true peak; external mode also binds the
master, provenance, filters, and FFmpeg toolchain.

An interim silent release is available only through the explicit `--silent`
flag or `FORMALSLT_FILM_AUDIO_MODE=silent`. It produces H.264 files with no
audio streams and receipts that disclose the silent mode. It is not the final
scored film; see `SOUNDTRACK.md`.

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

For the interim silent package, append `--silent` to `release`. Both native
cuts must use the same audio mode before staging.

Fresh render intermediates remain under the ignored `out/` and temporary media
directories. Final delivery files are copied into `delivery/` only after visual,
audio, and hash verification.

## Package map

- `STORYBOARD.md`: reviewed visual logic and theorem boundaries.
- `TRANSCRIPT.md`, `TRANSCRIPT-SOCIAL.md`: accessible main and mobile copy.
- `captions-main.vtt`, `captions-social.vtt`: timed caption sidecars.
- `film_config.json`: independent timing and resolution contracts.
- `extract_facts.py`, `facts.json`, `claim-receipt.json`: exact-commit claim pin.
- `stitched_lil_result.py`: both native compositions and posters.
- `compose_soundtrack.py`, `SOUNDTRACK.md`: built-in score and external-master contract.
- `render.sh`, `verify_media.py`, `stage_delivery.py`: bounded render, receipt,
  and delivery pipeline.
- `test_*.py`: source, layout, soundtrack, and receipt gates.
