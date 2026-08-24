#!/usr/bin/env python3
"""Compose the deterministic stitched-confidence-sequence film score."""

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

SOUNDTRACK_ID = "formalslt-stitched-lil-score-v1"
SAMPLE_RATE = 48_000
CHANNELS = 2
SAMPLE_WIDTH_BYTES = 2
BLOCK_FRAMES = 2_048
MAX_DURATION_SECONDS = 10 * 60
REFERENCE_DURATION_SECONDS = float(CONFIG["duration_seconds"])
MAX_REFERENCE_DRIFT_SECONDS = 0.50
MAX_MASTER_PEAK_DBFS = -3.0
MASTER_GAIN = 1.34


@dataclass(frozen=True)
class Cue:
    """Reviewed picture transition with a restrained tonal accent."""

    time: float
    scene: str
    tone_hz: float
    strength: float
    tension: float
    pan: float


_CUE_CHARACTER = {
    "hook": (73.42, 0.52, 0.28, -0.12),
    "model": (82.41, 0.55, 0.38, 0.10),
    "epochs": (98.00, 0.62, 0.54, -0.12),
    "allocation": (110.00, 0.58, 0.47, 0.14),
    "tilts": (123.47, 0.65, 0.67, -0.16),
    "stitch": (146.83, 0.70, 0.78, 0.16),
    "result": (73.42, 0.50, 0.16, 0.00),
}


def _load_cues() -> tuple[Cue, ...]:
    cues: list[Cue] = []
    for scene in CONFIG["scenes"]:
        scene_id = str(scene["id"])
        if scene_id not in _CUE_CHARACTER:
            raise ValueError(f"soundtrack has no character for scene {scene_id!r}")
        tone, strength, tension, pan = _CUE_CHARACTER[scene_id]
        cues.append(
            Cue(
                float(scene["start"]),
                scene_id,
                tone,
                strength,
                tension,
                pan,
            )
        )
    return tuple(cues)


CUES = _load_cues()


class Oscillator:
    """Small phase-accumulator oscillator with explicit local state."""

    def __init__(self, frequency: float, phase_cycles: float = 0.0) -> None:
        self.frequency = frequency
        self.phase = phase_cycles % 1.0

    def next(self, sample_rate: int) -> float:
        value = math.sin(math.tau * self.phase)
        self.phase = (self.phase + self.frequency / sample_rate) % 1.0
        return value


def _smoothstep(value: float) -> float:
    value = max(0.0, min(1.0, value))
    return value * value * (3.0 - 2.0 * value)


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


def _cue_plan(duration: float) -> tuple[Cue, ...]:
    cues = tuple(cue for cue in CUES if cue.time < duration)
    if not cues or cues[0].time != 0.0:
        raise ValueError("soundtrack must begin with a cue at zero seconds")
    return cues


def _cue_accent(cue: Cue, elapsed: float) -> tuple[float, float]:
    if elapsed < 0.0 or elapsed >= 2.6:
        return (0.0, 0.0)
    attack = _smoothstep(elapsed / 0.045)
    low_envelope = attack * math.exp(-2.45 * elapsed)
    tail_envelope = attack * math.exp(-1.20 * elapsed)
    low = math.sin(math.tau * (41.0 * elapsed - 2.6 * elapsed * elapsed))
    bell = (
        math.sin(math.tau * cue.tone_hz * elapsed)
        + 0.32 * math.sin(math.tau * cue.tone_hz * math.sqrt(2.0) * elapsed)
    )
    signal = cue.strength * (
        0.072 * low * low_envelope + 0.019 * bell * tail_envelope
    )
    left_gain = math.sqrt((1.0 - cue.pan) * 0.5)
    right_gain = math.sqrt((1.0 + cue.pan) * 0.5)
    return signal * left_gain, signal * right_gain


def _allocation_tick(time: float) -> float:
    """Four quiet descending cancellations during the allocation scene."""

    signal = 0.0
    for start, frequency in ((34.8, 146.83), (37.5, 130.81), (40.2, 116.54), (42.9, 98.00)):
        elapsed = time - start
        if 0.0 <= elapsed < 1.35:
            envelope = _smoothstep(elapsed / 0.025) * math.exp(-2.1 * elapsed)
            signal += 0.014 * envelope * math.sin(math.tau * frequency * elapsed)
    return signal


def _geometric_pulse(time: float) -> float:
    if not 20.0 <= time < 33.0:
        return 0.0
    phase = (time - 20.0) % 3.25
    envelope = _smoothstep(phase / 0.035) * math.exp(-2.8 * phase)
    return 0.014 * envelope * math.sin(math.tau * 31.0 * phase)


def compose(
    output: Path,
    duration: float,
    *,
    enforce_reference: bool = False,
) -> dict[str, object]:
    """Write a deterministic stereo PCM WAV and return render metadata."""

    if not math.isfinite(duration) or not 0.25 <= duration <= MAX_DURATION_SECONDS:
        raise ValueError(
            f"duration must be between 0.25 and {MAX_DURATION_SECONDS} seconds"
        )
    if (
        enforce_reference
        and abs(duration - REFERENCE_DURATION_SECONDS) > MAX_REFERENCE_DRIFT_SECONDS
    ):
        raise ValueError(
            f"duration {duration:.3f}s drifted from the reviewed "
            f"{REFERENCE_DURATION_SECONDS:.3f}s picture lock"
        )

    cues = _cue_plan(duration)
    frame_count = round(duration * SAMPLE_RATE)
    output.parent.mkdir(parents=True, exist_ok=True)

    # D/A foundation with a restrained E-flat tension color. Independent phases
    # make a wide field without samples, convolution, or nondeterministic effects.
    left_oscillators = (
        Oscillator(36.708, 0.00),
        Oscillator(36.846, 0.31),
        Oscillator(55.000, 0.47),
        Oscillator(73.416, 0.73),
        Oscillator(77.782, 0.13),
    )
    right_oscillators = (
        Oscillator(36.708, 0.17),
        Oscillator(36.832, 0.56),
        Oscillator(55.041, 0.81),
        Oscillator(73.361, 0.06),
        Oscillator(77.721, 0.39),
    )
    lfo = Oscillator(0.053, 0.18)

    noise_left = 0x4C494C31
    noise_right = 0x53544C54
    air_left = 0.0
    air_right = 0.0
    room_left = 0.0
    room_right = 0.0
    peak = 0.0
    cue_index = 0
    previous_tension = cues[0].tension

    with wave.open(str(output), "wb") as wav:
        wav.setnchannels(CHANNELS)
        wav.setsampwidth(SAMPLE_WIDTH_BYTES)
        wav.setframerate(SAMPLE_RATE)

        for block_start in range(0, frame_count, BLOCK_FRAMES):
            block_end = min(frame_count, block_start + BLOCK_FRAMES)
            pcm = array("h")
            for frame in range(block_start, block_end):
                time = frame / SAMPLE_RATE
                while cue_index + 1 < len(cues) and cues[cue_index + 1].time <= time:
                    previous_tension = cues[cue_index].tension
                    cue_index += 1
                cue = cues[cue_index]
                cue_elapsed = time - cue.time
                transition = _smoothstep(cue_elapsed / 1.4)
                tension = (
                    previous_tension * (1.0 - transition)
                    + cue.tension * transition
                )

                modulation = 0.94 + 0.06 * lfo.next(SAMPLE_RATE)
                # The final scene removes most of the tension oscillator.
                weights = (
                    0.118,
                    0.052,
                    0.043,
                    0.031 * (1.0 - 0.28 * tension),
                    0.010 + 0.026 * tension,
                )
                drone_left = sum(
                    weight * oscillator.next(SAMPLE_RATE)
                    for weight, oscillator in zip(weights, left_oscillators, strict=True)
                )
                drone_right = sum(
                    weight * oscillator.next(SAMPLE_RATE)
                    for weight, oscillator in zip(weights, right_oscillators, strict=True)
                )

                noise_left = (1664525 * noise_left + 1013904223) & 0xFFFFFFFF
                noise_right = (22695477 * noise_right + 1) & 0xFFFFFFFF
                raw_left = ((noise_left >> 8) / 0xFFFFFF) * 2.0 - 1.0
                raw_right = ((noise_right >> 8) / 0xFFFFFF) * 2.0 - 1.0
                room_left += 0.050 * (raw_left - room_left)
                room_right += 0.050 * (raw_right - room_right)
                air_left += 0.005 * (raw_left - air_left)
                air_right += 0.005 * (raw_right - air_right)
                texture_left = 0.011 * (room_left - air_left)
                texture_right = 0.011 * (room_right - air_right)

                accent_left, accent_right = _cue_accent(cue, cue_elapsed)
                math_pulse = _geometric_pulse(time) + _allocation_tick(time)
                # The stitch opens the field gradually without a volume jump.
                stitch_width = _smoothstep((time - 60.0) / 8.0) if 60.0 <= time < 74.0 else 0.0
                fade = _smoothstep(time / 1.8) * _smoothstep((duration - time) / 2.6)
                left = MASTER_GAIN * fade * (
                    modulation * drone_left
                    + texture_left
                    + accent_left
                    + math_pulse * (1.0 - 0.18 * stitch_width)
                )
                right = MASTER_GAIN * fade * (
                    modulation * drone_right
                    + texture_right
                    + accent_right
                    + math_pulse * (1.0 + 0.18 * stitch_width)
                )
                left = max(-0.98, min(0.98, left))
                right = max(-0.98, min(0.98, right))
                peak = max(peak, abs(left), abs(right))
                pcm.extend((round(left * 32767), round(right * 32767)))

            if sys.byteorder != "little":
                pcm.byteswap()
            wav.writeframesraw(pcm.tobytes())

    peak_dbfs = 20.0 * math.log10(peak) if peak > 0.0 else float("-inf")
    if peak_dbfs >= MAX_MASTER_PEAK_DBFS:
        output.unlink(missing_ok=True)
        raise ValueError(
            f"soundtrack peak {peak_dbfs:.2f} dBFS violates the "
            f"{MAX_MASTER_PEAK_DBFS:.2f} dBFS ceiling"
        )
    return {
        "soundtrack_id": SOUNDTRACK_ID,
        "duration_seconds": frame_count / SAMPLE_RATE,
        "reference_duration_seconds": REFERENCE_DURATION_SECONDS,
        "sample_rate": SAMPLE_RATE,
        "channels": CHANNELS,
        "sample_width_bits": SAMPLE_WIDTH_BYTES * 8,
        "frames": frame_count,
        "peak_dbfs": round(peak_dbfs, 2),
        "peak_ceiling_dbfs": MAX_MASTER_PEAK_DBFS,
        "sha256": _sha256(output),
        "cues": [asdict(cue) for cue in cues],
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--duration", type=float)
    parser.add_argument("--output", type=Path)
    parser.add_argument(
        "--metadata-output",
        type=Path,
        help="write the checked soundtrack receipt as JSON",
    )
    parser.add_argument(
        "--describe",
        action="store_true",
        help="print the reviewed cue plan without writing audio",
    )
    parser.add_argument("--version", action="store_true")
    args = parser.parse_args()
    if not args.describe and not args.version:
        missing = [name for name in ("duration", "output") if getattr(args, name) is None]
        if missing:
            parser.error("generation requires " + ", ".join(f"--{name}" for name in missing))
    return args


def main() -> None:
    args = parse_args()
    if args.version:
        print(SOUNDTRACK_ID)
        return
    if args.describe:
        print(
            json.dumps(
                {
                    "soundtrack_id": SOUNDTRACK_ID,
                    "sample_rate": SAMPLE_RATE,
                    "reference_duration_seconds": REFERENCE_DURATION_SECONDS,
                    "cues": [asdict(cue) for cue in CUES],
                },
                indent=2,
            )
        )
        return
    metadata = compose(args.output, args.duration, enforce_reference=True)
    if args.metadata_output is not None:
        _write_metadata(args.metadata_output, metadata)
    print(json.dumps(metadata, indent=2))


if __name__ == "__main__":
    main()
