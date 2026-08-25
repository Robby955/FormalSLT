# Soundtrack contract

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

## External Suno master

The generated score remains the default. A final render can instead use one
user-supplied Suno master, but only when both of these environment variables
are set to absolute file paths:

```bash
export FORMALSLT_FILM_SOUNDTRACK_MASTER=/absolute/path/to/master.wav
export FORMALSLT_FILM_SOUNDTRACK_PROVENANCE=/absolute/path/to/provenance.json
```

The provenance JSON is not a license grant. It is a fail-closed record of the
user's source and rights determination:

```json
{
  "schema": "formalslt-external-soundtrack-provenance-v1",
  "source_service": "Suno",
  "source_url": "https://suno.com/song/...",
  "track_title": "...",
  "generated_at_utc": "2026-08-24T12:00:00Z",
  "license_basis": "Paid-plan commercial-use grant",
  "commercial_use_authorized": true,
  "rights_attested": true,
  "rights_attested_by": "Robert Sneiderman",
  "rights_attested_at_utc": "2026-08-24T12:05:00Z",
  "master_sha256": "64 lowercase hexadecimal characters"
}
```

Both cuts start at 0 seconds. The pipeline applies fixed 0.75-second fade-ins,
2-second fade-outs, and two-pass FFmpeg loudness normalization to -22 LUFS,
7 LU LRA, and -3.5 dBTP. It derives 48 kHz stereo PCM intermediates. Receipts
record the raw-master and provenance hashes, filter strings and hashes, FFmpeg
and FFprobe binary identities, first-pass measurements, derived measurements,
and each derived WAV hash. The delivery gate requires both cuts to bind the
same master and provenance. Raw licensed audio is never copied into delivery.

Inspect without writing audio:

```bash
python3 media/stitched-lil-result-film/compose_soundtrack.py --describe main
python3 media/stitched-lil-result-film/compose_soundtrack.py --describe social
```
