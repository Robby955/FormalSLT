# Polynomial stitched confidence-sequence film

This directory is the source package for an 86-second, caption-led FormalSLT
result film. It explains one checked theorem: a two-sided sub-Gamma confidence
sequence obtained by assigning polynomial confidence weights to factor-four
epochs and precommitting one optimized tilt per epoch.

The safe public description is:

> FormalSLT machine-checks an explicit two-sided confidence sequence for
> bounded increments revealed one step after the past and centered given that
> past. Polynomial confidence
> weights and geometric epochs produce one failure set of mass at most `delta`
> controlling every sample size `n >= 4`, with an exact
> iterated-logarithm-order budget.

This is a derived formalized composition of established sub-Gamma, Ville, and
stitching ingredients. It is not the law of the iterated logarithm, a
sharp-constant result, an optional-stopping theorem, or a countable e-process.

## Source boundary

`extract_facts.py` reads theorem, allocation, documentation, and checker text
only through `git show` at merged-main commit
`285921b60231cb45e4aa9a4fc8068f3f7c98a2fa`. It fails if the expected
declarations, statement shapes, exact formulas, checker receipts, or nonclaim
language are absent. The committed `facts.json` is the reviewable output.

The film source consumes `facts.json`; it does not copy theorem constants into
an unrelated data file. `film_config.json` is the separate editorial contract
for scene timing and compact on-screen copy.

## Lightweight validation

No renderer or Lean build is needed:

```bash
./media/stitched-lil-result-film/render.sh validate
```

That command checks the pinned facts, Python syntax and package invariants,
the deterministic short soundtrack sample, and shell syntax. It does not
import Manim or write a movie.

## Render later

Requirements:

- Python 3.13
- Manim Community 0.20.1
- FFmpeg and FFprobe
- Avenir Next and Menlo on macOS

Install into an isolated environment only when a render is authorized:

```bash
python3 -m venv .venv
source .venv/bin/activate
python3 -m pip install -r media/stitched-lil-result-film/requirements.txt
```

Then, from the repository root:

```bash
./media/stitched-lil-result-film/render.sh proof
./media/stitched-lil-result-film/render.sh final
./media/stitched-lil-result-film/render.sh poster
```

`proof` makes a low-resolution review copy. `final` makes a 1920 by 1080,
30 fps H.264 review master with the generated stereo soundtrack. A successful
movie render also writes a JSON receipt binding the theorem commit, source
asset hashes, soundtrack peak and hash, movie hash, duration, streams,
resolution, and frame rate. `poster` renders the stable title frame. All outputs remain under the ignored
`media/stitched-lil-result-film/out/` directory; this package does not publish
or replace repository-facing media.

Every scene is locked to the reviewed cue ledger. Layout checks reject text
outside the safe frame or overlapping visual groups rather than shrinking copy
until it is unreadable. The final theorem identifier is split across two lines
to remain legible on a mobile preview.

## Files

- `STORYBOARD.md`: visual direction, shot timing, and evidence anchors.
- `TRANSCRIPT.md`: accessible searchable copy for the caption-led film.
- `film_config.json`: machine-readable scene timing and copy.
- `extract_facts.py` / `facts.json`: exact-commit mathematical receipt.
- `stitched_lil_result.py`: Manim film and poster scenes.
- `SOUNDTRACK.md` / `compose_soundtrack.py`: restrained score plan and
  deterministic standard-library composer.
- `render.sh` / `manim.cfg`: isolated rendering and audio muxing.
- `verify_media.py`: fail-closed `ffprobe` and hash receipt for rendered films.
- `test_package.py`, `test_compose_soundtrack.py`, and `test_verify_media.py`:
  lightweight checks.
