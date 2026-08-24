# Soundtrack plan

The film uses an original, restrained dark-ambient score generated entirely by
`compose_soundtrack.py`. The composer uses deterministic oscillators and a fixed
linear-congruential noise texture from the Python standard library. It reads no
samples, recordings, model output, or third-party audio.

The score should feel precise and slightly tense, not cinematic or ominous for
its own sake:

- a quiet low D/A bed keeps continuity across the 86 seconds;
- a muted tonal accent marks each mathematical transition;
- the geometric-epoch scene introduces a slow factor-four pulse;
- the allocation scene uses a light descending pair that resolves when the
  telescoping sum reaches one;
- the stitch scene opens the stereo field without increasing loudness;
- the result scene removes the tension tone and leaves a clean final fifth.

Cue ledger:

| Time | Cue |
|---:|---|
| 00:00 | fixed-time hook |
| 00:08 | process assumptions |
| 00:20 | geometric epochs |
| 00:33 | polynomial allocation |
| 00:46 | predeclared tilts |
| 01:00 | countable stitch |
| 01:14 | checked result |

The master peak must remain below `-3 dBFS`. The composer fails and removes the
WAV if the complete score violates that ceiling. It fades in and out, avoids
hard transients, and enforces a half-second maximum drift from the reviewed
86-second picture lock. The movie render retains the peak and soundtrack hash
in its JSON receipt.

Inspect the cue plan without writing audio:

```bash
python3 media/stitched-lil-result-film/compose_soundtrack.py --describe
```

Generate audio only after the picture duration has been checked:

```bash
python3 media/stitched-lil-result-film/compose_soundtrack.py \
  --duration 86.0 \
  --output media/stitched-lil-result-film/out/stitched-lil-score.wav
```
