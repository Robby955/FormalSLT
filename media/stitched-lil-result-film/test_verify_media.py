#!/usr/bin/env python3
"""Source-only validation tests for the final media receipt."""

from __future__ import annotations

import unittest

import verify_media


def valid_probe() -> dict[str, object]:
    return {
        "format": {"duration": "86.013"},
        "streams": [
            {
                "codec_type": "video",
                "codec_name": "h264",
                "width": 1920,
                "height": 1080,
                "avg_frame_rate": "30/1",
            },
            {
                "codec_type": "audio",
                "codec_name": "aac",
                "channels": 2,
                "sample_rate": "48000",
            },
        ],
    }


class MediaReceiptTests(unittest.TestCase):
    def test_final_probe_contract(self) -> None:
        media = verify_media.validate_probe(valid_probe(), "final")
        self.assertEqual(media["width"], 1920)
        self.assertEqual(media["height"], 1080)
        self.assertEqual(media["frame_rate"], "30")
        self.assertEqual(media["audio_codec"], "aac")

    def test_final_probe_rejects_wrong_dimensions(self) -> None:
        probe = valid_probe()
        probe["streams"][0]["width"] = 1280
        with self.assertRaisesRegex(ValueError, "dimensions"):
            verify_media.validate_probe(probe, "final")

    def test_probe_rejects_missing_audio(self) -> None:
        probe = valid_probe()
        probe["streams"] = probe["streams"][:1]
        with self.assertRaisesRegex(ValueError, "one audio stream"):
            verify_media.validate_probe(probe, "proof")

    def test_probe_rejects_picture_lock_drift(self) -> None:
        probe = valid_probe()
        probe["format"]["duration"] = "87.0"
        with self.assertRaisesRegex(ValueError, "duration"):
            verify_media.validate_probe(probe, "final")


if __name__ == "__main__":
    unittest.main()
