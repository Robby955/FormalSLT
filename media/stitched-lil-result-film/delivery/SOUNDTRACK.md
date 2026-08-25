# Original score

`compose_soundtrack.py` synthesizes a sparse, slightly tense score for both
compositions. It uses deterministic oscillators and a fixed pseudorandom air
texture from the Python standard library. It contains no recordings, sample
packs, model output, or third-party audio.

The design avoids the muddy continuous drone used in an earlier overview cut:

- the lowest authored tone is 98 Hz, so the harmonic foundation survives phone
  speakers without relying on sub-bass;
- finite swells leave at least four seconds of deliberate negative space;
- exactly three restrained accents mark the mathematical turns in each cut;
- the final harmony resolves without a trailer-style impact.

## Main cues

| Time | Event |
|---:|---|
| 00:00 | fixed-look hook |
| 00:33 | telescoping allocation accent |
| 01:00 | stitched-event accent |
| 01:14 | theorem resolution |

## Mobile cues

| Time | Event |
|---:|---|
| 00:00 | fixed-look hook |
| 00:15 | geometric allocation accent |
| 00:26 | stitched-event accent |
| 00:35 | theorem resolution |

The composer is byte-deterministic and records its cut, duration, PCM format,
peak, RMS, active-duty ratio, minimum authored frequency, license, event plan,
and SHA-256 hash. Final verification additionally measures integrated loudness,
loudness range, and true peak with FFmpeg.

Inspect without writing audio:

```bash
python3 media/stitched-lil-result-film/compose_soundtrack.py --describe main
python3 media/stitched-lil-result-film/compose_soundtrack.py --describe social
```
