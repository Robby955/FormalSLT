#!/usr/bin/env python3
"""Fast deterministic checks for the stitched-LIL score."""

from __future__ import annotations

import math
import tempfile
import unittest
import wave
from array import array
from pathlib import Path

import compose_soundtrack


class SoundtrackTests(unittest.TestCase):
    def test_sparse_score_plan_is_locked_to_both_compositions(self) -> None:
        self.assertEqual(
            compose_soundtrack.SOUNDTRACK_ID,
            "formalslt-stitched-lil-sparse-score-v2",
        )
        self.assertEqual(
            compose_soundtrack.REFERENCE_DURATIONS,
            {"main": 86.0, "social": 44.0},
        )
        self.assertEqual(len(compose_soundtrack.CUT_ACCENTS["main"]), 3)
        self.assertEqual(len(compose_soundtrack.CUT_ACCENTS["social"]), 3)

    def test_all_authored_tones_are_mobile_audible(self) -> None:
        for cut in compose_soundtrack.CUT_SWELLS:
            events = (
                *compose_soundtrack.CUT_SWELLS[cut],
                *compose_soundtrack.CUT_ACCENTS[cut],
            )
            frequencies = [frequency for event in events for frequency in event.frequencies]
            self.assertGreaterEqual(
                min(frequencies),
                compose_soundtrack.MIN_AUTHORED_FREQUENCY_HZ,
                cut,
            )

    def test_both_scores_have_negative_space(self) -> None:
        for cut, duration in compose_soundtrack.REFERENCE_DURATIONS.items():
            swells = compose_soundtrack.CUT_SWELLS[cut]
            active = sum(min(duration, swell.end) - swell.start for swell in swells)
            gaps = [right.start - left.end for left, right in zip(swells, swells[1:])]
            self.assertLess(active / duration, 0.75, cut)
            self.assertGreaterEqual(max(gaps), 4.0, cut)

    def test_pcm_render_is_stereo_safe_and_byte_deterministic(self) -> None:
        with tempfile.TemporaryDirectory(prefix="stitched-lil-audio-") as temp_dir:
            first = Path(temp_dir) / "first.wav"
            second = Path(temp_dir) / "second.wav"
            first_metadata = compose_soundtrack.compose(first, "main", 2.0)
            second_metadata = compose_soundtrack.compose(second, "main", 2.0)
            self.assertEqual(first.read_bytes(), second.read_bytes())
            self.assertEqual(first_metadata["sha256"], second_metadata["sha256"])
            self.assertLess(first_metadata["peak_dbfs"], -3.0)
            self.assertGreater(first_metadata["peak_dbfs"], -30.0)
            self.assertFalse(first_metadata["third_party_audio"])
            with wave.open(str(first), "rb") as wav:
                self.assertEqual(wav.getnchannels(), compose_soundtrack.CHANNELS)
                self.assertEqual(wav.getsampwidth(), compose_soundtrack.SAMPLE_WIDTH_BYTES)
                self.assertEqual(wav.getframerate(), compose_soundtrack.SAMPLE_RATE)
                self.assertEqual(wav.getnframes(), 2 * compose_soundtrack.SAMPLE_RATE)

    def test_social_score_has_real_dynamic_spread(self) -> None:
        with tempfile.TemporaryDirectory(prefix="stitched-lil-audio-") as temp_dir:
            output = Path(temp_dir) / "social.wav"
            compose_soundtrack.compose(output, "social", 12.0)
            with wave.open(str(output), "rb") as wav:
                frame_rate = wav.getframerate()
                samples = array("h")
                samples.frombytes(wav.readframes(wav.getnframes()))
            window_samples = frame_rate * compose_soundtrack.CHANNELS
            levels = []
            for start in range(0, len(samples), window_samples):
                window = samples[start : start + window_samples]
                if len(window) < window_samples:
                    continue
                rms = math.sqrt(sum(sample * sample for sample in window) / len(window))
                levels.append(20.0 * math.log10(max(rms / 32768.0, 1e-12)))
            self.assertGreater(max(levels) - min(levels), 8.0)

    def test_reference_guard_rejects_stale_picture_lock(self) -> None:
        with tempfile.TemporaryDirectory(prefix="stitched-lil-audio-") as temp_dir:
            with self.assertRaises(ValueError):
                compose_soundtrack.compose(
                    Path(temp_dir) / "stale.wav",
                    "social",
                    40.0,
                    enforce_reference=True,
                )


if __name__ == "__main__":
    unittest.main()
