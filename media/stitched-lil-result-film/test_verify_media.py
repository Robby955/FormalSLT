#!/usr/bin/env python3
"""Source-only validation tests for both final media receipts."""

from __future__ import annotations

import hashlib
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

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

    def test_silent_probe_requires_zero_audio_streams(self) -> None:
        probe = valid_probe()
        probe["streams"] = probe["streams"][:1]
        media = verify_media.validate_probe(probe, "final", "main", "silent")
        self.assertEqual(media["audio_streams"], 0)
        self.assertNotIn("audio_codec", media)
        with self.assertRaisesRegex(ValueError, "zero audio streams"):
            verify_media.validate_probe(valid_probe(), "final", "main", "silent")

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

    def test_built_in_soundtrack_branch_accepts_legacy_mode_omission(self) -> None:
        with tempfile.TemporaryDirectory(prefix="stitched-lil-receipt-") as temp:
            soundtrack = Path(temp) / "score.wav"
            soundtrack.write_bytes(b"score")
            metadata = {
                "soundtrack_id": verify_media.BUILT_IN_SOUNDTRACK_ID,
                "cut": "main",
                "duration_seconds": 86.0,
                "sample_rate": 48_000,
                "channels": 2,
                "peak_dbfs": -4.0,
                "rms_dbfs": -25.0,
                "active_duty_ratio": 0.5,
                "accents": [{}, {}, {}],
                "third_party_audio": False,
                "sha256": verify_media.sha256(soundtrack),
            }
            receipt = verify_media.validate_soundtrack(metadata, soundtrack, "main")
            self.assertEqual(receipt["soundtrack_mode"], "built_in")

    def test_external_soundtrack_branch_binds_source_and_filter_hashes(self) -> None:
        with tempfile.TemporaryDirectory(prefix="stitched-lil-receipt-") as temp:
            soundtrack = Path(temp) / "derived.wav"
            soundtrack.write_bytes(b"derived-score")
            tool = Path("/bin/sh").resolve()
            tool_receipt = {
                "path": str(tool),
                "sha256": verify_media.sha256(tool),
                "version": "test tool",
            }
            measurement = {
                "input_i": -22.0,
                "input_tp": -3.6,
                "input_lra": 6.0,
                "input_thresh": -32.0,
                "output_i": -22.0,
                "output_tp": -3.6,
                "output_lra": 6.0,
                "output_thresh": -32.0,
                "target_offset": 0.0,
            }
            analysis_filter = "analysis"
            render_filter = "render"
            master_hash = "1" * 64
            metadata = {
                "soundtrack_id": verify_media.EXTERNAL_SOUNDTRACK_ID,
                "soundtrack_mode": "external_master",
                "cut": "social",
                "duration_seconds": 44.0,
                "sample_rate": 48_000,
                "channels": 2,
                "third_party_audio": True,
                "sha256": verify_media.sha256(soundtrack),
                "raw_master": {
                    "file": "master.wav",
                    "bytes": 100,
                    "sha256": master_hash,
                    "duration_seconds": 90.0,
                },
                "provenance": {
                    "file": "provenance.json",
                    "bytes": 200,
                    "sha256": "2" * 64,
                    "schema": verify_media.EXTERNAL_PROVENANCE_SCHEMA,
                    "source_service": "Suno",
                    "source_url": "https://suno.com/song/source",
                    "track_title": "Checked path",
                    "generated_at_utc": "2026-08-24T12:00:00Z",
                    "license_basis": "Paid-plan commercial-use grant",
                    "commercial_use_authorized": True,
                    "rights_attested": True,
                    "rights_attested_by": "Robert Sneiderman",
                    "rights_attested_at_utc": "2026-08-24T12:05:00Z",
                    "master_sha256": master_hash,
                },
                "derivation": {
                    "trim_start_seconds": 0.0,
                    "trim_duration_seconds": 44.0,
                    "fade_in_seconds": 0.75,
                    "fade_out_seconds": 2.0,
                    "analysis_filter": analysis_filter,
                    "analysis_filter_sha256": hashlib.sha256(
                        analysis_filter.encode()
                    ).hexdigest(),
                    "render_filter": render_filter,
                    "render_filter_sha256": hashlib.sha256(
                        render_filter.encode()
                    ).hexdigest(),
                    "ffmpeg": tool_receipt,
                    "ffprobe": tool_receipt,
                    "pass_one_measurement": measurement,
                    "derived_measurement": measurement,
                },
            }
            receipt = verify_media.validate_soundtrack(metadata, soundtrack, "social")
            self.assertEqual(receipt["soundtrack_mode"], "external_master")
            self.assertEqual(receipt["raw_master"]["sha256"], master_hash)

    def test_silent_cli_arguments_are_exclusive(self) -> None:
        path = Path("score.wav")
        verify_media.validate_audio_arguments("silent", None, None)
        with self.assertRaisesRegex(ValueError, "cannot include"):
            verify_media.validate_audio_arguments("silent", path, path)
        with self.assertRaisesRegex(ValueError, "requires both"):
            verify_media.validate_audio_arguments("built_in", None, None)

    def test_silent_receipt_has_no_audio_measurement(self) -> None:
        with tempfile.TemporaryDirectory(prefix="stitched-lil-receipt-") as temp:
            video = Path(temp) / "silent.mp4"
            video.write_bytes(b"silent-video")
            probe = valid_probe()
            probe["streams"] = probe["streams"][:1]
            with (
                patch.object(verify_media, "git_head", return_value="1" * 40),
                patch.object(verify_media, "source_asset_hashes", return_value={}),
            ):
                receipt = verify_media.build_receipt(
                    video,
                    None,
                    None,
                    probe,
                    None,
                    "final",
                    "main",
                    "silent",
                )
            self.assertEqual(
                receipt["schema"],
                "formalslt-stitched-lil-media-receipt-v2",
            )
            self.assertEqual(receipt["soundtrack"]["soundtrack_mode"], "silent")
            self.assertFalse(receipt["soundtrack"]["third_party_audio"])
            self.assertNotIn("muxed_audio_measurement", receipt)


if __name__ == "__main__":
    unittest.main()
