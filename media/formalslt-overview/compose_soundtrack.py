#!/usr/bin/env python3
"""Synthesize the original FormalSLT dark-ambient soundtrack.

The score is generated entirely from deterministic oscillators and a fixed
pseudorandom noise sequence. It uses no recordings, sample packs, or external
audio assets. The generated WAV is an intermediate render input and inherits
the repository's MIT license.
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


SOUNDTRACK_ID = "formalslt-dark-ambient-v2"
SAMPLE_RATE = 48_000
CHANNELS = 2
SAMPLE_WIDTH_BYTES = 2
BLOCK_FRAMES = 2_048
MAX_DURATION_SECONDS = 10 * 60
MASTER_GAIN = 1.55
REFERENCE_DURATIONS = {"main": 64.228, "social": 10.366}
MAX_REFERENCE_DRIFT_SECONDS = 0.50


@dataclass(frozen=True)
class Cue:
    """A visual transition that receives a restrained tonal accent."""

    time: float
    scene: str
    tone_hz: float
    strength: float
    tension: float
    pan: float


# Boundaries are the cumulative animation durations in FormalSLTOverview and
# FormalSLTSocial at this checkpoint. Keeping the schedule here makes score
# changes reviewable without hiding timing decisions inside the film source.
CUT_CUES: dict[str, tuple[Cue, ...]] = {
    "main": (
        Cue(0.00, "title", 73.42, 0.58, 0.20, -0.15),
        Cue(4.50, "adaptive problem", 77.78, 0.76, 0.78, 0.22),
        Cue(9.60, "structured family", 73.42, 0.92, 0.88, -0.12),
        Cue(13.35, "hit statistic", 110.00, 0.78, 0.70, -0.24),
        Cue(15.40, "TV identity", 146.83, 0.84, 0.58, 0.20),
        Cue(20.30, "proof spine", 110.00, 0.66, 0.42, -0.28),
        Cue(27.55, "anytime validity", 146.83, 0.62, 0.52, 0.30),
        Cue(34.04, "adaptive trajectories", 87.31, 0.70, 0.72, -0.20),
        Cue(39.79, "stationary bridge", 98.00, 0.66, 0.48, 0.24),
        Cue(45.69, "library map", 110.00, 0.62, 0.38, -0.24),
        Cue(51.14, "declaration receipt", 82.41, 0.68, 0.56, 0.18),
        Cue(57.79, "axiom receipt", 98.00, 0.56, 0.30, -0.12),
        Cue(60.89, "source and close", 73.42, 0.54, 0.18, 0.00),
    ),
    "social": (
        Cue(0.00, "coordinate hook", 73.42, 0.82, 0.70, -0.18),
        Cue(2.60, "hit statistic", 77.78, 0.88, 0.90, 0.22),
        Cue(3.75, "TV identity", 146.83, 0.96, 0.66, -0.24),
        Cue(4.40, "scope boundary", 110.00, 0.70, 0.44, 0.20),
        Cue(7.65, "source close", 73.42, 0.62, 0.18, 0.00),
    ),
}


class Oscillator:
    """Small phase-accumulator oscillator with no mutable global state."""

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


def _cue_accent(cue: Cue, elapsed: float) -> tuple[float, float]:
    """Return a short scene-change impact with a decaying metallic tail."""

    if elapsed < 0.0 or elapsed >= 2.8:
        return (0.0, 0.0)

    attack = _smoothstep(elapsed / 0.035)
    sub_envelope = attack * math.exp(-2.25 * elapsed)
    tail_envelope = attack * math.exp(-1.05 * elapsed)
    # The falling sub tone supplies weight; the inharmonic 1.414 ratio keeps
    # the cue uneasy without becoming a melodic hook.
    chirp_cycles = 48.0 * elapsed - 4.2 * elapsed * elapsed
    sub = math.sin(math.tau * chirp_cycles) * sub_envelope
    bell = (
        math.sin(math.tau * cue.tone_hz * elapsed)
        + 0.42 * math.sin(math.tau * cue.tone_hz * math.sqrt(2.0) * elapsed)
        + 0.16 * math.sin(math.tau * cue.tone_hz * 2.731 * elapsed)
    ) * tail_envelope
    signal = cue.strength * (0.095 * sub + 0.026 * bell)
    left_gain = math.sqrt((1.0 - cue.pan) * 0.5)
    right_gain = math.sqrt((1.0 + cue.pan) * 0.5)
    return (signal * left_gain, signal * right_gain)


def _cue_plan(cut: str, duration: float) -> tuple[Cue, ...]:
    cues = tuple(cue for cue in CUT_CUES[cut] if cue.time < duration)
    if not cues or cues[0].time != 0.0:
        raise ValueError(f"{cut} soundtrack must begin with a cue at 0 seconds")
    return cues


def compose(
    output: Path,
    cut: str,
    duration: float,
    *,
    enforce_reference: bool = False,
) -> dict[str, object]:
    """Write a stereo PCM WAV and return deterministic render metadata."""

    if cut not in CUT_CUES:
        raise ValueError(f"unknown cut: {cut}")
    if not math.isfinite(duration) or not 0.25 <= duration <= MAX_DURATION_SECONDS:
        raise ValueError(
            f"duration must be between 0.25 and {MAX_DURATION_SECONDS} seconds"
        )
    reference_duration = REFERENCE_DURATIONS[cut]
    if (
        enforce_reference
        and abs(duration - reference_duration) > MAX_REFERENCE_DRIFT_SECONDS
    ):
        raise ValueError(
            f"{cut} duration {duration:.3f}s drifted from the reviewed "
            f"{reference_duration:.3f}s soundtrack timing; retime the cue ledger"
        )

    cues = _cue_plan(cut, duration)
    frame_count = round(duration * SAMPLE_RATE)
    output.parent.mkdir(parents=True, exist_ok=True)

    # D minor with a quiet E-flat tension tone. Slight detuning and different
    # starting phases make the field wide without chorus effects or plugins.
    left_oscillators = (
        Oscillator(36.708, 0.00),
        Oscillator(36.846, 0.31),
        Oscillator(43.654, 0.13),
        Oscillator(55.000, 0.47),
        Oscillator(77.782, 0.73),
    )
    right_oscillators = (
        Oscillator(36.708, 0.17),
        Oscillator(36.832, 0.56),
        Oscillator(43.612, 0.39),
        Oscillator(55.041, 0.81),
        Oscillator(77.721, 0.06),
    )
    lfo = Oscillator(0.061 if cut == "main" else 0.105, 0.18)

    # Fixed LCG seeds provide reproducible air/room texture without samples.
    noise_left = 0x4F524D41
    noise_right = 0x534C5432
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
                transition = _smoothstep(cue_elapsed / 1.2)
                tension = (
                    previous_tension * (1.0 - transition)
                    + cue.tension * transition
                )

                modulation = 0.92 + 0.08 * lfo.next(SAMPLE_RATE)
                weights = (
                    0.125,
                    0.058,
                    0.050 * (1.0 - 0.20 * tension),
                    0.045 * (1.0 - 0.35 * tension),
                    0.012 + 0.032 * tension,
                )
                drone_left = sum(
                    weight * oscillator.next(SAMPLE_RATE)
                    for weight, oscillator in zip(weights, left_oscillators)
                )
                drone_right = sum(
                    weight * oscillator.next(SAMPLE_RATE)
                    for weight, oscillator in zip(weights, right_oscillators)
                )

                noise_left = (1664525 * noise_left + 1013904223) & 0xFFFFFFFF
                noise_right = (22695477 * noise_right + 1) & 0xFFFFFFFF
                raw_left = ((noise_left >> 8) / 0xFFFFFF) * 2.0 - 1.0
                raw_right = ((noise_right >> 8) / 0xFFFFFF) * 2.0 - 1.0
                room_left += 0.055 * (raw_left - room_left)
                room_right += 0.055 * (raw_right - room_right)
                air_left += 0.006 * (raw_left - air_left)
                air_right += 0.006 * (raw_right - air_right)
                texture_left = 0.014 * (room_left - air_left)
                texture_right = 0.014 * (room_right - air_right)

                accent_left, accent_right = _cue_accent(cue, cue_elapsed)
                heartbeat_phase = time % (6.4 if cut == "main" else 3.7)
                heartbeat = (
                    0.020
                    * math.exp(-2.4 * heartbeat_phase)
                    * math.sin(math.tau * 29.0 * heartbeat_phase)
                )
                fade = _smoothstep(time / 1.6) * _smoothstep(
                    (duration - time) / (2.2 if cut == "main" else 1.0)
                )
                left = MASTER_GAIN * fade * (
                    modulation * drone_left
                    + texture_left
                    + accent_left
                    + heartbeat
                )
                right = MASTER_GAIN * fade * (
                    modulation * drone_right
                    + texture_right
                    + accent_right
                    + heartbeat
                )
                left = max(-0.98, min(0.98, left))
                right = max(-0.98, min(0.98, right))
                peak = max(peak, abs(left), abs(right))
                pcm.extend((round(left * 32767), round(right * 32767)))

            if sys.byteorder != "little":
                pcm.byteswap()
            wav.writeframesraw(pcm.tobytes())

    peak_dbfs = 20.0 * math.log10(peak) if peak > 0.0 else float("-inf")
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
        "sha256": _sha256(output),
        "cues": [asdict(cue) for cue in cues],
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cut", choices=sorted(CUT_CUES))
    parser.add_argument("--duration", type=float)
    parser.add_argument("--output", type=Path)
    parser.add_argument(
        "--describe",
        choices=sorted(CUT_CUES),
        help="print a cut's cue plan as JSON without generating audio",
    )
    parser.add_argument("--version", action="store_true")
    args = parser.parse_args()
    if args.version:
        return args
    if args.describe:
        return args
    missing = [
        name
        for name in ("cut", "duration", "output")
        if getattr(args, name) is None
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
        print(
            json.dumps(
                {
                    "soundtrack_id": SOUNDTRACK_ID,
                    "cut": args.describe,
                    "sample_rate": SAMPLE_RATE,
                    "reference_duration_seconds": REFERENCE_DURATIONS[args.describe],
                    "cues": [asdict(cue) for cue in CUT_CUES[args.describe]],
                },
                indent=2,
            )
        )
        return
    metadata = compose(
        args.output,
        args.cut,
        args.duration,
        enforce_reference=True,
    )
    print(json.dumps(metadata, indent=2))


if __name__ == "__main__":
    main()
