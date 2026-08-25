#!/usr/bin/env python3
"""Source-only validation tests for both final media receipts."""

from __future__ import annotations

import unittest

import verify_media


def valid_probe(
    composition: str = "main",
    *,
    quality: str = "final",
) -> dict[str, object]:
    contract = verify_media.composition_contract(composition)
    if quality == "final":
        width, height = contract["resolution"]
    elif composition == "main":
        width, height = 854, 480
    else:
        width, height = 432, 540
    return {
        "format": {"duration": f"{contract['duration_seconds'] + 0.013:.3f}"},
        "streams": [
            {
                "codec_type": "video",
                "codec_name": "h264",
                "width": width,
                "height": height,
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
    def test_main_final_probe_contract(self) -> None:
        media = verify_media.validate_probe(valid_probe(), "final", "main")
        self.assertEqual(media["width"], 1920)
        self.assertEqual(media["height"], 1080)
        self.assertEqual(media["frame_rate"], "30")
        self.assertEqual(media["audio_codec"], "aac")

    def test_social_final_probe_is_native_four_by_five(self) -> None:
        media = verify_media.validate_probe(
            valid_probe("social"),
            "final",
            "social",
        )
        self.assertEqual([media["width"], media["height"]], [1080, 1350])

    def test_proof_contract_preserves_each_composition_aspect(self) -> None:
        for composition in ("main", "social"):
            with self.subTest(composition=composition):
                verify_media.validate_probe(
                    valid_probe(composition, quality="proof"),
                    "proof",
                    composition,
                )

    def test_final_probe_rejects_wrong_dimensions(self) -> None:
        probe = valid_probe()
        probe["streams"][0]["width"] = 1280
        with self.assertRaisesRegex(ValueError, "dimensions"):
            verify_media.validate_probe(probe, "final", "main")

    def test_probe_rejects_missing_audio(self) -> None:
        probe = valid_probe()
        probe["streams"] = probe["streams"][:1]
        with self.assertRaisesRegex(ValueError, "one audio stream"):
            verify_media.validate_probe(probe, "proof", "main")

    def test_probe_rejects_picture_lock_drift(self) -> None:
        probe = valid_probe()
        probe["format"]["duration"] = "87.0"
        with self.assertRaisesRegex(ValueError, "duration"):
            verify_media.validate_probe(probe, "final", "main")

    def test_loudness_contract_accepts_mobile_safe_mix(self) -> None:
        measured = verify_media.validate_loudness(
            {
                "input_i": "-23.4",
                "input_tp": "-4.1",
                "input_lra": "8.2",
                "input_thresh": "-34.0",
            }
        )
        self.assertEqual(measured["integrated_lufs"], -23.4)
        self.assertEqual(measured["true_peak_dbfs"], -4.1)

    def test_loudness_contract_rejects_true_peak_violation(self) -> None:
        with self.assertRaisesRegex(ValueError, "true peak"):
            verify_media.validate_loudness(
                {
                    "input_i": "-23.4",
                    "input_tp": "-1.0",
                    "input_lra": "8.2",
                    "input_thresh": "-34.0",
                }
            )


if __name__ == "__main__":
    unittest.main()
