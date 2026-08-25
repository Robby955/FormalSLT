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


if __name__ == "__main__":
    unittest.main()
