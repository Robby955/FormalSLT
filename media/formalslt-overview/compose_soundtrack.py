#!/usr/bin/env python3
"""Synthesize the original sparse score for the FormalSLT overview films.

The score uses deterministic oscillators and a fixed pseudorandom sequence. It
contains no recordings, sample packs, model output, or third-party audio. The
generated WAV is a render intermediate and inherits the repository MIT license.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
import wave
from array import array
from dataclasses import asdict, dataclass
from pathlib import Path


SOUNDTRACK_ID = "formalslt-sparse-tension-v4"
SAMPLE_RATE = 48_000
CHANNELS = 2
SAMPLE_WIDTH_BYTES = 2
BLOCK_FRAMES = 2_048
MAX_DURATION_SECONDS = 10 * 60
MASTER_GAIN = 0.78
MIN_AUTHORED_FREQUENCY_HZ = 92.5
REFERENCE_DURATIONS = {"main": 72.0, "social": 13.0}
MAX_REFERENCE_DRIFT_SECONDS = 0.50


@dataclass(frozen=True)
class Swell:
    """A finite harmonic field with audible space before the next field."""

    start: float
    end: float
    scene: str
    frequencies: tuple[float, ...]
    strength: float
    attack: float
    release: float
    pan: float


@dataclass(frozen=True)
class Accent:
    """A restrained mid-register transition tone, never a bass impact."""

    time: float
    scene: str
    frequencies: tuple[float, ...]
    strength: float
    decay: float
    pan: float


CUT_SWELLS: dict[str, tuple[Swell, ...]] = {
    "main": (
        Swell(0.0, 5.8, "thesis", (146.83, 220.00, 311.13), 0.58, 0.85, 1.85, -0.10),
        Swell(13.5, 25.2, "foundations", (110.00, 146.83, 220.00, 293.66), 0.48, 1.00, 2.20, 0.08),
        Swell(31.4, 45.8, "adaptive validity", (110.00, 155.56, 233.08, 311.13), 0.55, 0.95, 2.15, -0.08),
        Swell(49.4, 60.6, "worked case", (98.00, 146.83, 207.65, 293.66), 0.52, 0.90, 2.00, 0.10),
        Swell(65.3, 72.0, "resolution", (110.00, 146.83, 220.00, 293.66), 0.50, 0.80, 2.25, 0.00),
    ),
    "social": (
        Swell(0.0, 2.6, "hook", (146.83, 220.00, 311.13), 0.56, 0.45, 0.80, -0.08),
        Swell(4.1, 6.8, "proof stack", (110.00, 155.56, 233.08, 311.13), 0.53, 0.45, 0.85, 0.08),
        Swell(9.1, 13.0, "resolution", (110.00, 146.83, 220.00, 293.66), 0.50, 0.45, 1.20, 0.00),
    ),
}

CUT_ACCENTS: dict[str, tuple[Accent, ...]] = {
    "main": (
        Accent(32.0, "adaptive validity", (293.66, 415.30, 622.25), 0.16, 1.55, -0.18),
        Accent(50.0, "worked case", (293.66, 440.00, 659.26), 0.18, 1.35, 0.16),
        Accent(66.0, "resolution", (293.66, 440.00, 587.33, 880.00), 0.14, 1.80, 0.00),
    ),
    "social": (
        Accent(4.0, "proof stack", (293.66, 415.30, 622.25), 0.15, 1.00, -0.14),
        Accent(9.0, "resolution", (293.66, 440.00, 587.33), 0.13, 1.20, 0.12),
    ),
}


def _smoothstep(value: float) -> float:
    value = max(0.0, min(1.0, value))
    return value * value * (3.0 - 2.0 * value)


def _raised_cosine(value: float) -> float:
    value = max(0.0, min(1.0, value))
    return 0.5 - 0.5 * math.cos(math.pi * value)


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _swell_envelope(swell: Swell, time: float) -> float:
    if time < swell.start or time >= swell.end:
        return 0.0
    elapsed = time - swell.start
    remaining = swell.end - time
    return min(
        _raised_cosine(elapsed / swell.attack),
        _raised_cosine(remaining / swell.release),
    )


def _pad_sample(swell: Swell, time: float) -> tuple[float, float]:
    envelope = _swell_envelope(swell, time)
    if envelope <= 0.0:
        return (0.0, 0.0)
    note_weights = (1.0, 0.74, 0.56, 0.42)
    left = 0.0
    right = 0.0
    normalizer = 0.0
    for index, frequency in enumerate(swell.frequencies):
        weight = note_weights[index]
        phase = 0.13 + 0.19 * index
        cents = 1.8 + 0.35 * index
        left_frequency = frequency * 2.0 ** (-cents / 1200.0)
        right_frequency = frequency * 2.0 ** (cents / 1200.0)
        left += weight * (
            math.sin(math.tau * (left_frequency * time + phase))
            + 0.18 * math.sin(math.tau * (2.0 * left_frequency * time + phase * 0.7))
            + 0.05 * math.sin(math.tau * (3.0 * left_frequency * time + phase * 1.3))
        )
        right += weight * (
            math.sin(math.tau * (right_frequency * time + phase + 0.11))
            + 0.18 * math.sin(math.tau * (2.0 * right_frequency * time + phase * 0.7 + 0.08))
            + 0.05 * math.sin(math.tau * (3.0 * right_frequency * time + phase * 1.3 + 0.05))
        )
        normalizer += weight * 1.23
    left_pan = math.sqrt((1.0 - swell.pan) * 0.5)
    right_pan = math.sqrt((1.0 + swell.pan) * 0.5)
    gain = swell.strength * envelope / normalizer
    return (gain * left_pan * left, gain * right_pan * right)


def _accent_sample(accent: Accent, time: float) -> tuple[float, float]:
    elapsed = time - accent.time
    if elapsed < 0.0 or elapsed >= 3.0 * accent.decay:
        return (0.0, 0.0)
    attack = _smoothstep(elapsed / 0.022)
    envelope = attack * math.exp(-elapsed / accent.decay)
    tone = sum(
        math.sin(math.tau * (frequency * elapsed + 0.09 * index))
        / (1.0 + 0.55 * index)
        for index, frequency in enumerate(accent.frequencies)
    ) / len(accent.frequencies)
    left_pan = math.sqrt((1.0 - accent.pan) * 0.5)
    right_pan = math.sqrt((1.0 + accent.pan) * 0.5)
    signal = accent.strength * envelope * tone
    return (left_pan * signal, right_pan * signal)


def _validate_score_plan(cut: str, duration: float) -> tuple[tuple[Swell, ...], tuple[Accent, ...]]:
    if cut not in CUT_SWELLS:
        raise ValueError(f"unknown cut: {cut}")
    swells = tuple(swell for swell in CUT_SWELLS[cut] if swell.start < duration)
    accents = tuple(accent for accent in CUT_ACCENTS[cut] if accent.time < duration)
    if not swells or swells[0].start != 0.0:
        raise ValueError(f"{cut} score must begin with a finite swell at 0 seconds")
    frequencies = [
        frequency
        for event in (*swells, *accents)
        for frequency in event.frequencies
    ]
    if min(frequencies) < MIN_AUTHORED_FREQUENCY_HZ:
        raise ValueError("score plan reintroduced a sub-heavy authored frequency")
    for swell in swells:
        if not swell.start < swell.end or swell.attack <= 0.0 or swell.release <= 0.0:
            raise ValueError(f"invalid swell: {swell}")
    return swells, accents


def compose(
    output: Path,
    cut: str,
    duration: float,
    *,
    enforce_reference: bool = False,
) -> dict[str, object]:
    """Write a deterministic stereo PCM WAV and return render metadata."""

    if not math.isfinite(duration) or not 0.25 <= duration <= MAX_DURATION_SECONDS:
        raise ValueError(
            f"duration must be between 0.25 and {MAX_DURATION_SECONDS} seconds"
        )
    reference_duration = REFERENCE_DURATIONS.get(cut)
    if reference_duration is None:
        raise ValueError(f"unknown cut: {cut}")
    if enforce_reference and abs(duration - reference_duration) > MAX_REFERENCE_DRIFT_SECONDS:
        raise ValueError(
            f"{cut} duration {duration:.3f}s drifted from the reviewed "
            f"{reference_duration:.3f}s score timing; retime the score plan"
        )

    swells, accents = _validate_score_plan(cut, duration)
    frame_count = round(duration * SAMPLE_RATE)
    output.parent.mkdir(parents=True, exist_ok=True)

    # Fixed LCG seeds and two one-pole filters create a quiet 900--5500 Hz air
    # layer only while a swell is active. There is no full-band or constant bed.
    noise_left = 0x46534C54
    noise_right = 0x53434F52
    fast_left = fast_right = 0.0
    slow_left = slow_right = 0.0
    alpha_fast = 1.0 - math.exp(-math.tau * 5500.0 / SAMPLE_RATE)
    alpha_slow = 1.0 - math.exp(-math.tau * 900.0 / SAMPLE_RATE)
    peak = 0.0
    clipped_samples = 0

    with wave.open(str(output), "wb") as wav:
        wav.setnchannels(CHANNELS)
        wav.setsampwidth(SAMPLE_WIDTH_BYTES)
        wav.setframerate(SAMPLE_RATE)

        for block_start in range(0, frame_count, BLOCK_FRAMES):
            block_end = min(frame_count, block_start + BLOCK_FRAMES)
            pcm = array("h")
            for frame in range(block_start, block_end):
                time = frame / SAMPLE_RATE
                left = 0.0
                right = 0.0
                active_envelope = 0.0
                for swell in swells:
                    envelope = _swell_envelope(swell, time)
                    if envelope > 0.0:
                        swell_left, swell_right = _pad_sample(swell, time)
                        left += swell_left
                        right += swell_right
                        active_envelope = max(active_envelope, envelope)
                for accent in accents:
                    accent_left, accent_right = _accent_sample(accent, time)
                    left += accent_left
                    right += accent_right

                noise_left = (1664525 * noise_left + 1013904223) & 0xFFFFFFFF
                noise_right = (22695477 * noise_right + 1) & 0xFFFFFFFF
                raw_left = ((noise_left >> 8) / 0xFFFFFF) * 2.0 - 1.0
                raw_right = ((noise_right >> 8) / 0xFFFFFF) * 2.0 - 1.0
                fast_left += alpha_fast * (raw_left - fast_left)
                fast_right += alpha_fast * (raw_right - fast_right)
                slow_left += alpha_slow * (raw_left - slow_left)
                slow_right += alpha_slow * (raw_right - slow_right)
                left += 0.008 * active_envelope * (fast_left - slow_left)
                right += 0.008 * active_envelope * (fast_right - slow_right)

                global_fade = _smoothstep(time / 0.30) * _smoothstep(
                    (duration - time) / (0.65 if cut == "social" else 1.10)
                )
                left *= MASTER_GAIN * global_fade
                right *= MASTER_GAIN * global_fade
                if abs(left) >= 0.999 or abs(right) >= 0.999:
                    clipped_samples += 1
                left = max(-0.999, min(0.999, left))
                right = max(-0.999, min(0.999, right))
                peak = max(peak, abs(left), abs(right))
                pcm.extend((round(left * 32767), round(right * 32767)))

            if sys.byteorder != "little":
                pcm.byteswap()
            wav.writeframesraw(pcm.tobytes())

    if clipped_samples:
        raise ValueError(f"score clipped {clipped_samples} sample frames")
    peak_dbfs = 20.0 * math.log10(peak) if peak > 0.0 else float("-inf")
    active_intervals: list[list[float]] = []
    for swell in swells:
        start = swell.start
        end = min(duration, swell.end)
        if active_intervals and start <= active_intervals[-1][1]:
            active_intervals[-1][1] = max(active_intervals[-1][1], end)
        else:
            active_intervals.append([start, end])
    active_seconds = sum(end - start for start, end in active_intervals)
    return {
        "soundtrack_id": SOUNDTRACK_ID,
        "cut": cut,
        "duration_seconds": frame_count / SAMPLE_RATE,
        "reference_duration_seconds": reference_duration,
        "sample_rate": SAMPLE_RATE,
        "channels": CHANNELS,
        "sample_width_bits": SAMPLE_WIDTH_BYTES * 8,
        "frames": frame_count,
        "peak_dbfs": round(peak_dbfs, 2),
        "minimum_authored_frequency_hz": min(
            frequency
            for event in (*swells, *accents)
            for frequency in event.frequencies
        ),
        "active_duty_ratio": round(active_seconds / duration, 4),
        "third_party_audio": False,
        "license": "MIT",
        "sha256": _sha256(output),
        "swells": [asdict(swell) for swell in swells],
        "accents": [asdict(accent) for accent in accents],
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cut", choices=sorted(CUT_SWELLS))
    parser.add_argument("--duration", type=float)
    parser.add_argument("--output", type=Path)
    parser.add_argument(
        "--describe",
        choices=sorted(CUT_SWELLS),
        help="print a cut's score plan as JSON without generating audio",
    )
    parser.add_argument("--version", action="store_true")
    args = parser.parse_args()
    if args.version or args.describe:
        return args
    missing = [
        name for name in ("cut", "duration", "output") if getattr(args, name) is None
    ]
    if missing:
        parser.error("generation requires " + ", ".join(f"--{name}" for name in missing))
    return args


def main() -> None:
    args = parse_args()
    if args.version:
        print(SOUNDTRACK_ID)
        return
    if args.describe:
        swells, accents = _validate_score_plan(
            args.describe, REFERENCE_DURATIONS[args.describe]
        )
        print(
            json.dumps(
                {
                    "soundtrack_id": SOUNDTRACK_ID,
                    "cut": args.describe,
                    "sample_rate": SAMPLE_RATE,
                    "reference_duration_seconds": REFERENCE_DURATIONS[args.describe],
                    "swells": [asdict(swell) for swell in swells],
                    "accents": [asdict(accent) for accent in accents],
                },
                indent=2,
            )
        )
        return
    metadata = compose(args.output, args.cut, args.duration, enforce_reference=True)
    print(json.dumps(metadata, indent=2))


if __name__ == "__main__":
    main()
