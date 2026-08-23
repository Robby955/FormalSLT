#!/usr/bin/env python3
"""Unit checks for the deterministic FormalSLT soundtrack generator."""

from __future__ import annotations

import tempfile
import unittest
import wave
from pathlib import Path

import compose_soundtrack


class SoundtrackTests(unittest.TestCase):
    def test_cue_ledgers_are_ordered_and_begin_at_zero(self) -> None:
        for cut, cues in compose_soundtrack.CUT_CUES.items():
            self.assertGreater(len(cues), 1, cut)
            self.assertEqual(cues[0].time, 0.0, cut)
            self.assertEqual(
                [cue.time for cue in cues],
                sorted(cue.time for cue in cues),
                cut,
            )
            self.assertEqual(len({cue.scene for cue in cues}), len(cues), cut)
            self.assertLess(cues[-1].time, compose_soundtrack.REFERENCE_DURATIONS[cut])

    def test_pcm_render_is_stereo_and_byte_deterministic(self) -> None:
        with tempfile.TemporaryDirectory(prefix="formalslt-soundtrack-test-") as tmp:
            first = Path(tmp) / "first.wav"
            second = Path(tmp) / "second.wav"
            duration = 2.0
            first_metadata = compose_soundtrack.compose(first, "main", duration)
            second_metadata = compose_soundtrack.compose(second, "main", duration)

            self.assertEqual(first.read_bytes(), second.read_bytes())
            self.assertEqual(first_metadata["sha256"], second_metadata["sha256"])
            self.assertLess(first_metadata["peak_dbfs"], -3.0)
            self.assertGreater(first_metadata["peak_dbfs"], -60.0)
            with wave.open(str(first), "rb") as wav:
                self.assertEqual(wav.getnchannels(), compose_soundtrack.CHANNELS)
                self.assertEqual(
                    wav.getsampwidth(), compose_soundtrack.SAMPLE_WIDTH_BYTES
                )
                self.assertEqual(wav.getframerate(), compose_soundtrack.SAMPLE_RATE)
                self.assertEqual(
                    wav.getnframes(), round(duration * compose_soundtrack.SAMPLE_RATE)
                )

    def test_invalid_duration_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory(prefix="formalslt-soundtrack-test-") as tmp:
            with self.assertRaises(ValueError):
                compose_soundtrack.compose(Path(tmp) / "bad.wav", "social", 0.10)

    def test_cli_timing_guard_rejects_stale_scene_duration(self) -> None:
        with tempfile.TemporaryDirectory(prefix="formalslt-soundtrack-test-") as tmp:
            with self.assertRaises(ValueError):
                compose_soundtrack.compose(
                    Path(tmp) / "stale.wav",
                    "main",
                    60.35,
                    enforce_reference=True,
                )


if __name__ == "__main__":
    unittest.main()
