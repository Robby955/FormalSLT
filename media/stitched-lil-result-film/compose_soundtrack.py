#!/usr/bin/env python3
"""Synthesize the original sparse score for the stitched-LIL films.

The score is deterministic and sample-free. It uses finite harmonic swells,
three restrained transition accents, and audible negative space. Generated WAV
files are render intermediates and inherit the repository MIT license.
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


PACKAGE_DIR = Path(__file__).resolve().parent
CONFIG = json.loads((PACKAGE_DIR / "film_config.json").read_text(encoding="utf-8"))

SOUNDTRACK_ID = "formalslt-stitched-lil-sparse-score-v2"
SAMPLE_RATE = 48_000
CHANNELS = 2
SAMPLE_WIDTH_BYTES = 2
BLOCK_FRAMES = 2_048
MAX_DURATION_SECONDS = 10 * 60
MASTER_GAIN = 0.78
MIN_AUTHORED_FREQUENCY_HZ = 92.5
MAX_MASTER_PEAK_DBFS = -3.0
MAX_REFERENCE_DRIFT_SECONDS = 0.50
REFERENCE_DURATIONS = {
    "main": float(CONFIG["duration_seconds"]),
    "social": float(CONFIG["social"]["duration_seconds"]),
}


@dataclass(frozen=True)
class Swell:
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
    time: float
    scene: str
    frequencies: tuple[float, ...]
    strength: float
    decay: float
    pan: float


CUT_SWELLS: dict[str, tuple[Swell, ...]] = {
    "main": (
        Swell(0.0, 6.2, "fixed look", (146.83, 220.00, 311.13), 0.58, 0.75, 1.70, -0.10),
        Swell(12.8, 26.0, "process", (110.00, 146.83, 220.00, 293.66), 0.48, 1.00, 2.10, 0.08),
        Swell(32.0, 46.0, "allocation", (116.54, 174.61, 233.08, 349.23), 0.52, 0.90, 2.20, -0.08),
        Swell(50.0, 64.0, "stitch", (98.00, 146.83, 207.65, 293.66), 0.55, 0.95, 2.25, 0.10),
        Swell(73.0, 86.0, "result", (110.00, 146.83, 220.00, 293.66), 0.50, 0.85, 2.60, 0.00),
    ),
    "social": (
        Swell(0.0, 5.5, "fixed look", (146.83, 220.00, 311.13), 0.58, 0.60, 1.30, -0.08),
        Swell(10.0, 20.0, "mechanism", (110.00, 155.56, 233.08, 311.13), 0.50, 0.80, 1.70, 0.08),
        Swell(25.0, 34.0, "stitch", (98.00, 146.83, 207.65, 293.66), 0.55, 0.75, 1.60, -0.08),
        Swell(36.0, 44.0, "result", (110.00, 146.83, 220.00, 293.66), 0.50, 0.65, 1.90, 0.00),
    ),
}

CUT_ACCENTS: dict[str, tuple[Accent, ...]] = {
    "main": (
        Accent(33.0, "allocation", (293.66, 440.00, 659.26), 0.15, 1.40, -0.14),
        Accent(60.0, "stitch", (293.66, 415.30, 622.25), 0.18, 1.45, 0.14),
        Accent(74.0, "result", (293.66, 440.00, 587.33, 880.00), 0.14, 1.85, 0.00),
    ),
    "social": (
        Accent(15.0, "mechanism", (293.66, 440.00, 659.26), 0.15, 1.20, -0.12),
        Accent(26.0, "stitch", (293.66, 415.30, 622.25), 0.18, 1.25, 0.12),
        Accent(35.0, "result", (293.66, 440.00, 587.33), 0.14, 1.55, 0.00),
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


def _write_metadata(path: Path, metadata: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


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
    weights = (1.0, 0.74, 0.56, 0.42)
    left = right = normalizer = 0.0
    for index, frequency in enumerate(swell.frequencies):
        weight = weights[index]
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
    return gain * left_pan * left, gain * right_pan * right


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
    return left_pan * signal, right_pan * signal


def _validate_score_plan(cut: str, duration: float) -> tuple[tuple[Swell, ...], tuple[Accent, ...]]:
    if cut not in CUT_SWELLS:
        raise ValueError(f"unknown cut: {cut}")
    swells = tuple(swell for swell in CUT_SWELLS[cut] if swell.start < duration)
    accents = tuple(accent for accent in CUT_ACCENTS[cut] if accent.time < duration)
    if not swells or swells[0].start != 0.0:
        raise ValueError(f"{cut} score must begin with a finite swell at zero")
    frequencies = [frequency for event in (*swells, *accents) for frequency in event.frequencies]
    if min(frequencies) < MIN_AUTHORED_FREQUENCY_HZ:
        raise ValueError("score plan reintroduced a sub-heavy authored frequency")
    for left, right in zip(swells, swells[1:], strict=False):
        if left.end > right.start:
            raise ValueError(f"overlapping score swells: {left.scene}, {right.scene}")
    return swells, accents


def compose(output: Path, cut: str, duration: float, *, enforce_reference: bool = False) -> dict[str, object]:
    if not math.isfinite(duration) or not 0.25 <= duration <= MAX_DURATION_SECONDS:
        raise ValueError(f"duration must be between 0.25 and {MAX_DURATION_SECONDS} seconds")
    if cut not in REFERENCE_DURATIONS:
        raise ValueError(f"unknown cut: {cut}")
    reference = REFERENCE_DURATIONS[cut]
    if enforce_reference and abs(duration - reference) > MAX_REFERENCE_DRIFT_SECONDS:
        raise ValueError(f"{cut} duration {duration:.3f}s drifted from {reference:.3f}s")

    swells, accents = _validate_score_plan(cut, duration)
    frame_count = round(duration * SAMPLE_RATE)
    output.parent.mkdir(parents=True, exist_ok=True)
    noise_left, noise_right = 0x46534C54, 0x53434F52
    fast_left = fast_right = slow_left = slow_right = 0.0
    alpha_fast = 1.0 - math.exp(-math.tau * 5500.0 / SAMPLE_RATE)
    alpha_slow = 1.0 - math.exp(-math.tau * 900.0 / SAMPLE_RATE)
    peak = sum_squares = 0.0
    sample_count = 0
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
                left = right = active_envelope = 0.0
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

                fade = _smoothstep(time / 0.30) * _smoothstep((duration - time) / 1.05)
                left *= MASTER_GAIN * fade
                right *= MASTER_GAIN * fade
                if abs(left) >= 0.999 or abs(right) >= 0.999:
                    clipped_samples += 1
                left = max(-0.999, min(0.999, left))
                right = max(-0.999, min(0.999, right))
                peak = max(peak, abs(left), abs(right))
                sum_squares += left * left + right * right
                sample_count += 2
                pcm.extend((round(left * 32767), round(right * 32767)))
            if sys.byteorder != "little":
                pcm.byteswap()
            wav.writeframesraw(pcm.tobytes())

    if clipped_samples:
        output.unlink(missing_ok=True)
        raise ValueError(f"score clipped {clipped_samples} sample frames")
    peak_dbfs = 20.0 * math.log10(peak) if peak > 0.0 else float("-inf")
    if peak_dbfs >= MAX_MASTER_PEAK_DBFS:
        output.unlink(missing_ok=True)
        raise ValueError(f"soundtrack peak {peak_dbfs:.2f} dBFS violates the ceiling")
    rms = math.sqrt(sum_squares / sample_count)
    active_seconds = sum(min(duration, swell.end) - swell.start for swell in swells)
    return {
        "soundtrack_id": SOUNDTRACK_ID,
        "cut": cut,
        "duration_seconds": frame_count / SAMPLE_RATE,
        "reference_duration_seconds": reference,
        "sample_rate": SAMPLE_RATE,
        "channels": CHANNELS,
        "sample_width_bits": SAMPLE_WIDTH_BYTES * 8,
        "frames": frame_count,
        "peak_dbfs": round(peak_dbfs, 2),
        "peak_ceiling_dbfs": MAX_MASTER_PEAK_DBFS,
        "rms_dbfs": round(20.0 * math.log10(max(rms, 1e-12)), 2),
        "minimum_authored_frequency_hz": min(
            frequency for event in (*swells, *accents) for frequency in event.frequencies
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
    parser.add_argument("--metadata-output", type=Path)
    parser.add_argument("--describe", choices=sorted(CUT_SWELLS))
    parser.add_argument("--version", action="store_true")
    args = parser.parse_args()
    if args.version or args.describe:
        return args
    missing = [name for name in ("cut", "duration", "output") if getattr(args, name) is None]
    if missing:
        parser.error("generation requires " + ", ".join(f"--{name}" for name in missing))
    return args


def main() -> None:
    args = parse_args()
    if args.version:
        print(SOUNDTRACK_ID)
        return
    if args.describe:
        swells, accents = _validate_score_plan(args.describe, REFERENCE_DURATIONS[args.describe])
        print(json.dumps({
            "soundtrack_id": SOUNDTRACK_ID,
            "cut": args.describe,
            "sample_rate": SAMPLE_RATE,
            "reference_duration_seconds": REFERENCE_DURATIONS[args.describe],
            "swells": [asdict(swell) for swell in swells],
            "accents": [asdict(accent) for accent in accents],
        }, indent=2))
        return
    metadata = compose(args.output, args.cut, args.duration, enforce_reference=True)
    if args.metadata_output is not None:
        _write_metadata(args.metadata_output, metadata)
    print(json.dumps(metadata, indent=2))


if __name__ == "__main__":
    main()
