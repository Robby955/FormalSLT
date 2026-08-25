#!/usr/bin/env python3
"""Unit checks for the deterministic FormalSLT soundtrack generator."""

from __future__ import annotations

import math
import tempfile
import unittest
import wave
from pathlib import Path

import compose_soundtrack


class SoundtrackTests(unittest.TestCase):
    def test_sparse_v4_plan_is_reviewed(self) -> None:
        self.assertEqual(
            compose_soundtrack.SOUNDTRACK_ID,
            "formalslt-sparse-tension-v4",
        )
        self.assertEqual(
            compose_soundtrack.REFERENCE_DURATIONS,
            {"main": 72.0, "social": 13.0},
        )
        self.assertEqual(len(compose_soundtrack.CUT_SWELLS["main"]), 5)
        self.assertEqual(len(compose_soundtrack.CUT_ACCENTS["main"]), 3)
        self.assertEqual(len(compose_soundtrack.CUT_ACCENTS["social"]), 2)

    def test_all_authored_tones_are_mid_register_or_higher(self) -> None:
        for cut in compose_soundtrack.CUT_SWELLS:
            events = (
                *compose_soundtrack.CUT_SWELLS[cut],
                *compose_soundtrack.CUT_ACCENTS[cut],
            )
            frequencies = [
                frequency for event in events for frequency in event.frequencies
            ]
            self.assertGreaterEqual(
                min(frequencies),
                compose_soundtrack.MIN_AUTHORED_FREQUENCY_HZ,
                cut,
            )

    def test_main_score_contains_negative_space(self) -> None:
        duration = compose_soundtrack.REFERENCE_DURATIONS["main"]
        intervals = [
            (swell.start, min(duration, swell.end))
            for swell in compose_soundtrack.CUT_SWELLS["main"]
        ]
        active = sum(end - start for start, end in intervals)
        self.assertLess(active / duration, 0.75)
        scene_boundaries = {0.0, 5.0, 14.0, 23.0, 32.0, 41.0, 50.0, 59.0, 66.0}
        accent_times = {
            accent.time for accent in compose_soundtrack.CUT_ACCENTS["main"]
        }
        self.assertLess(len(accent_times), len(scene_boundaries) / 2)
        self.assertTrue(accent_times.issubset(scene_boundaries))

    def test_social_score_contains_sustained_negative_space(self) -> None:
        duration = compose_soundtrack.REFERENCE_DURATIONS["social"]
        swells = compose_soundtrack.CUT_SWELLS["social"]
        active = sum(min(duration, swell.end) - swell.start for swell in swells)
        gaps = [
            right.start - left.end
            for left, right in zip(swells, swells[1:])
        ]
        self.assertLess(active / duration, 0.75)
        self.assertGreaterEqual(max(gaps), 2.0)

    def test_pcm_render_is_stereo_and_byte_deterministic(self) -> None:
        with tempfile.TemporaryDirectory(prefix="formalslt-score-test-") as tmp:
            first = Path(tmp) / "first.wav"
            second = Path(tmp) / "second.wav"
            duration = 1.25
            first_metadata = compose_soundtrack.compose(first, "main", duration)
            second_metadata = compose_soundtrack.compose(second, "main", duration)

            self.assertEqual(first.read_bytes(), second.read_bytes())
            self.assertEqual(first_metadata["sha256"], second_metadata["sha256"])
            self.assertLess(first_metadata["peak_dbfs"], -4.0)
            self.assertGreater(first_metadata["peak_dbfs"], -24.0)
            self.assertFalse(first_metadata["third_party_audio"])
            with wave.open(str(first), "rb") as wav:
                self.assertEqual(wav.getnchannels(), compose_soundtrack.CHANNELS)
                self.assertEqual(
                    wav.getsampwidth(), compose_soundtrack.SAMPLE_WIDTH_BYTES
                )
                self.assertEqual(wav.getframerate(), compose_soundtrack.SAMPLE_RATE)
                self.assertEqual(
                    wav.getnframes(), round(duration * compose_soundtrack.SAMPLE_RATE)
                )

    def test_social_render_has_real_dynamic_spread(self) -> None:
        with tempfile.TemporaryDirectory(prefix="formalslt-score-test-") as tmp:
            output = Path(tmp) / "social.wav"
            compose_soundtrack.compose(
                output,
                "social",
                compose_soundtrack.REFERENCE_DURATIONS["social"],
                enforce_reference=True,
            )
            with wave.open(str(output), "rb") as wav:
                frame_rate = wav.getframerate()
                raw = wav.readframes(wav.getnframes())
            # One-second stereo int16 RMS windows. The range catches a return
            # to the old flat procedural bed without requiring audio plugins.
            import array

            samples = array.array("h")
            samples.frombytes(raw)
            window_samples = frame_rate * compose_soundtrack.CHANNELS
            levels = []
            for start in range(0, len(samples), window_samples):
                window = samples[start : start + window_samples]
                if len(window) < window_samples:
                    continue
                rms = math.sqrt(sum(sample * sample for sample in window) / len(window))
                levels.append(20.0 * math.log10(max(rms / 32768.0, 1e-12)))
            self.assertGreater(max(levels) - min(levels), 5.0)

    def test_invalid_duration_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory(prefix="formalslt-score-test-") as tmp:
            with self.assertRaises(ValueError):
                compose_soundtrack.compose(Path(tmp) / "bad.wav", "social", 0.10)

    def test_reference_guard_rejects_stale_scene_duration(self) -> None:
        with tempfile.TemporaryDirectory(prefix="formalslt-score-test-") as tmp:
            with self.assertRaises(ValueError):
                compose_soundtrack.compose(
                    Path(tmp) / "stale.wav",
                    "main",
                    60.35,
                    enforce_reference=True,
                )


if __name__ == "__main__":
    unittest.main()
