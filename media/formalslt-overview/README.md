# FormalSLT overview film

This directory contains the fact-bound source for a caption-led overview of
FormalSLT. The 72-second main cut opens with the library's full mathematical
range: VC theory, Rademacher complexity, chaining, PAC-Bayes, sequential
inference, and dependent data. It then follows the shared ideas from classical
generalization to adaptive trajectories. The controlled queue appears later as
one worked case study, not as the scope of the project. A 13-second cut carries
the same broad framing for social previews.

The checked facts are extracted from the exact merged-main commit
`501fee458a539db654097dbec8933427dae9fee9`. The extractor fails if that commit
does not contain the named VC, metric-entropy, chaining, PAC-Bayes, e-process,
trajectory, and controlled-queue declarations with the expected statement
shapes. It also checks the queue cardinalities, hit-probability formula, and
exact row-TV transfer anchor.

## Render

Requirements:

- Python 3.13
- Manim Community 0.20.1
- FFmpeg
- the Avenir Next and Menlo fonts included with macOS

Each scene starts on a soundtrack cue listed in `MAIN_SCENE_STARTS` and
`SOCIAL_SCENE_STARTS`. The scene checks its own start against the renderer
clock and holds its finished composition until the next cue, so frame
rounding cannot drift the picture away from the score. Every composition also
runs frame, content-band, and pairwise overlap assertions before it animates;
a layout that collides fails the render instead of shipping.

The bound shapes burned into the classical, PAC-Bayes, anytime, and queue
scenes are copied from the pinned declarations, and the closing ledger prints
the four film anchors by their exact Lean declaration names from `facts.json`.

The mathematical inputs and scene timing are fact-bound and deterministic.
The rendered pixels are not promised to be bit-identical across platforms:
Avenir Next and Menlo are macOS system fonts, and the Python requirements do
not lock the operating system or every transitive renderer component. The
official render receipt records the renderer environment and output hashes.
Use that environment when reproducing release pixels.

Install the renderer into an isolated environment with:

```bash
python3 -m venv .venv
source .venv/bin/activate
python3 -m pip install -r media/formalslt-overview/requirements.txt
```

From the repository root:

```bash
./media/formalslt-overview/render.sh proof
./media/formalslt-overview/render.sh social-proof
./media/formalslt-overview/render.sh final
./media/formalslt-overview/render.sh social
./media/formalslt-overview/render.sh poster
./media/formalslt-overview/render.sh release
```

`proof` and `social-proof` render fast 854 by 480 review copies. `final` and
`social` render the 1920 by 1080 30 fps masters. `poster` renders the stable
click-to-play image independently of film timing. `release` refreshes both mobile
H.264 cuts with stereo AAC audio, the poster, and `render-receipt.json`. It
builds and validates that complete set in a temporary directory before
replacing the public files; a failed audio generation, mux, metadata check, or
promotion restores the prior set. Intermediate movies and WAV files are under
`media/formalslt-overview/out/` and are intentionally ignored by Git.

The films have no voiceover. Explanatory text is burned into the frames for
muted playback; the main cut also ships with a WebVTT track and a searchable
transcript.

## Soundtrack

`compose_soundtrack.py` generates an original dark-ambient score from
oscillators and a fixed pseudorandom noise sequence using only the Python
standard library. It reads no recordings, samples, or third-party audio. The
source and generated score are covered by the repository's MIT license.

The main score places restrained impacts at the nine reviewed scene
boundaries, from the field map through the closing lockup. The social score
follows its field hook, theorem spine, and close. `render.sh` reads the actual
rendered movie duration, creates a 48 kHz stereo WAV, and muxes it as 192 kbps
AAC while copying the Manim video stream. Generation stops if a cut drifts more
than half a second from its reviewed timing, forcing the cue ledger to be
retimed before release. Inspect either cue ledger without rendering:

```bash
python3 media/formalslt-overview/compose_soundtrack.py --describe main
python3 media/formalslt-overview/compose_soundtrack.py --describe social
```

Run the fast deterministic PCM checks with:

```bash
python3 media/formalslt-overview/test_compose_soundtrack.py
```

To review the audio independently, supply the intended cut duration and an
ignored output path:

```bash
python3 media/formalslt-overview/compose_soundtrack.py \
  --cut main --duration 72.0 \
  --output media/formalslt-overview/out/formalslt-overview-main-soundtrack.wav
```

The committed `facts.json` is a reviewable mathematical receipt. Every render
regenerates it from the bound Git commit and stops if a required declaration,
statement shape, cardinality, formula, or scope identity no longer matches.
`render-receipt.json` separately records source and asset hashes, video and
audio codecs, durations, soundtrack provenance, and renderer versions.

## Public delivery

- The repository poster opens the fast-start 1080p H.264 main cut directly.
- The main cut, short cut, poster, and captions live in `delivery/` so a film
  release remains independent of documentation-site generation.
- The receipt records the film's fact-bound commit separately from the later
  commit that publishes the delivery files.
- `TRANSCRIPT.md`, the WebVTT track, source, facts, and render receipt stay in
  the repository.
- A tagged release may attach the lossless archival master later; the committed
  MP4 files are delivery encodes, not the archival boundary.
