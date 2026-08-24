#!/usr/bin/env python3
"""Fast deterministic checks for the stitched-result soundtrack."""

from __future__ import annotations

import tempfile
import unittest
import wave
from pathlib import Path
from unittest import mock

import compose_soundtrack


class SoundtrackTests(unittest.TestCase):
    def test_picture_lock_and_cues_match_film_config(self) -> None:
        self.assertEqual(
            compose_soundtrack.SOUNDTRACK_ID,
            "formalslt-stitched-lil-score-v1",
        )
        self.assertEqual(compose_soundtrack.REFERENCE_DURATION_SECONDS, 86.0)
        self.assertEqual(
            [cue.time for cue in compose_soundtrack.CUES],
            [0.0, 8.0, 20.0, 33.0, 46.0, 60.0, 74.0],
        )
        self.assertEqual(
            [cue.scene for cue in compose_soundtrack.CUES],
            [scene["id"] for scene in compose_soundtrack.CONFIG["scenes"]],
        )

    def test_cues_are_ordered_unique_and_inside_picture(self) -> None:
        times = [cue.time for cue in compose_soundtrack.CUES]
        self.assertEqual(times, sorted(times))
        self.assertEqual(len(times), len(set(times)))
        self.assertEqual(times[0], 0.0)
        self.assertLess(times[-1], compose_soundtrack.REFERENCE_DURATION_SECONDS)

    def test_short_pcm_render_is_stereo_safe_and_deterministic(self) -> None:
        with tempfile.TemporaryDirectory(prefix="stitched-lil-audio-") as temp_dir:
            first = Path(temp_dir) / "first.wav"
            second = Path(temp_dir) / "second.wav"
            duration = 2.0
            first_metadata = compose_soundtrack.compose(first, duration)
            second_metadata = compose_soundtrack.compose(second, duration)
            self.assertEqual(first.read_bytes(), second.read_bytes())
            self.assertEqual(first_metadata["sha256"], second_metadata["sha256"])
            self.assertLess(first_metadata["peak_dbfs"], -3.0)
            self.assertEqual(
                first_metadata["peak_ceiling_dbfs"],
                compose_soundtrack.MAX_MASTER_PEAK_DBFS,
            )
            self.assertGreater(first_metadata["peak_dbfs"], -60.0)
            with wave.open(str(first), "rb") as wav:
                self.assertEqual(wav.getnchannels(), compose_soundtrack.CHANNELS)
                self.assertEqual(wav.getsampwidth(), compose_soundtrack.SAMPLE_WIDTH_BYTES)
                self.assertEqual(wav.getframerate(), compose_soundtrack.SAMPLE_RATE)
                self.assertEqual(
                    wav.getnframes(),
                    round(duration * compose_soundtrack.SAMPLE_RATE),
                )

    def test_duration_guard_rejects_drift(self) -> None:
        with tempfile.TemporaryDirectory(prefix="stitched-lil-audio-") as temp_dir:
            with self.assertRaises(ValueError):
                compose_soundtrack.compose(
                    Path(temp_dir) / "stale.wav",
                    84.0,
                    enforce_reference=True,
                )

    def test_peak_guard_rejects_and_removes_unsafe_master(self) -> None:
        with tempfile.TemporaryDirectory(prefix="stitched-lil-audio-") as temp_dir:
            output = Path(temp_dir) / "unsafe.wav"
            with mock.patch.object(compose_soundtrack, "MASTER_GAIN", 1_000_000.0):
                with self.assertRaisesRegex(ValueError, "violates"):
                    compose_soundtrack.compose(output, 0.25)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
