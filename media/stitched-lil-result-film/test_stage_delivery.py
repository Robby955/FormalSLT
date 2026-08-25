#!/usr/bin/env python3
"""Unit checks for the final delivery receipt boundary."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

import stage_delivery


class DeliveryTests(unittest.TestCase):
    def test_media_receipt_requires_exact_artifact_hash(self) -> None:
        with tempfile.TemporaryDirectory(prefix="stitched-lil-delivery-") as temp:
            video = Path(temp) / stage_delivery.CUTS["main"]["video"]
            video.write_bytes(b"checked-video-placeholder")
            receipt = {
                "schema": "formalslt-stitched-lil-media-receipt-v2",
                "quality": "final",
                "composition": "main",
                "theorem_source_commit": stage_delivery.FACTS["commit"],
                "theorem_blob_oid": stage_delivery.CLAIMS["theorem_blob_oid"],
                "render_source_commit": "1" * 40,
                "soundtrack": {
                    "soundtrack_id": stage_delivery.BUILT_IN_SOUNDTRACK_ID,
                    "soundtrack_mode": "built_in",
                    "third_party_audio": False,
                },
                "video": {
                    "file": video.name,
                    "bytes": video.stat().st_size,
                    "sha256": stage_delivery.sha256(video),
                    "width": 1920,
                    "height": 1080,
                },
            }
            self.assertEqual(
                stage_delivery.validate_media_receipt(receipt, "main", video),
                "1" * 40,
            )
            receipt["video"]["sha256"] = "0" * 64
            with self.assertRaisesRegex(ValueError, "hash"):
                stage_delivery.validate_media_receipt(receipt, "main", video)

    def test_social_receipt_cannot_claim_main_dimensions(self) -> None:
        with tempfile.TemporaryDirectory(prefix="stitched-lil-delivery-") as temp:
            video = Path(temp) / stage_delivery.CUTS["social"]["video"]
            video.write_bytes(b"checked-video-placeholder")
            receipt = {
                "schema": "formalslt-stitched-lil-media-receipt-v2",
                "quality": "final",
                "composition": "social",
                "theorem_source_commit": stage_delivery.FACTS["commit"],
                "theorem_blob_oid": stage_delivery.CLAIMS["theorem_blob_oid"],
                "render_source_commit": "2" * 40,
                "soundtrack": {
                    "soundtrack_id": stage_delivery.BUILT_IN_SOUNDTRACK_ID,
                    "soundtrack_mode": "built_in",
                    "third_party_audio": False,
                },
                "video": {
                    "file": video.name,
                    "bytes": video.stat().st_size,
                    "sha256": stage_delivery.sha256(video),
                    "width": 1920,
                    "height": 1080,
                },
            }
            with self.assertRaisesRegex(ValueError, "dimensions"):
                stage_delivery.validate_media_receipt(receipt, "social", video)

    def test_external_cuts_must_bind_one_master_and_provenance(self) -> None:
        def receipt(master_hash: str) -> dict[str, object]:
            return {
                "soundtrack": {
                    "soundtrack_mode": "external_master",
                    "raw_master": {"sha256": master_hash},
                    "provenance": {"sha256": "2" * 64},
                }
            }

        matching = {"main": receipt("1" * 64), "social": receipt("1" * 64)}
        self.assertEqual(
            stage_delivery.validate_common_soundtrack_source(matching),
            "external_master",
        )
        mismatched = {"main": receipt("1" * 64), "social": receipt("3" * 64)}
        with self.assertRaisesRegex(ValueError, "same external master"):
            stage_delivery.validate_common_soundtrack_source(mismatched)

    def test_silent_delivery_rejects_mixed_audio_modes(self) -> None:
        silent = {
            "soundtrack": {
                "soundtrack_mode": "silent",
                "third_party_audio": False,
            }
        }
        built_in = {
            "soundtrack": {
                "soundtrack_mode": "built_in",
                "third_party_audio": False,
            }
        }
        matching = {"main": silent, "social": silent}
        self.assertEqual(
            stage_delivery.validate_common_soundtrack_source(matching),
            "silent",
        )
        with self.assertRaisesRegex(ValueError, "different soundtrack modes"):
            stage_delivery.validate_common_soundtrack_source(
                {"main": silent, "social": built_in}
            )

    def test_silent_delivery_cut_omits_audio_measurement(self) -> None:
        receipt = {
            "video": {"audio_streams": 0},
            "soundtrack": {
                "soundtrack_mode": "silent",
                "third_party_audio": False,
            },
        }
        payload = stage_delivery.delivery_cut(receipt)
        self.assertNotIn("muxed_audio_measurement", payload)


if __name__ == "__main__":
    unittest.main()
