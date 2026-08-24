#!/usr/bin/env python3
"""Source-only tests for the stitched-result film package."""

from __future__ import annotations

import ast
import json
import re
import subprocess
import unittest
from pathlib import Path


PACKAGE_DIR = Path(__file__).resolve().parent
ROOT = PACKAGE_DIR.parents[1]


class PackageTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.facts = json.loads((PACKAGE_DIR / "facts.json").read_text(encoding="utf-8"))
        cls.config = json.loads(
            (PACKAGE_DIR / "film_config.json").read_text(encoding="utf-8")
        )

    def test_required_source_package_is_present(self) -> None:
        expected = {
            ".gitignore",
            "README.md",
            "SOUNDTRACK.md",
            "STORYBOARD.md",
            "TRANSCRIPT.md",
            "compose_soundtrack.py",
            "extract_facts.py",
            "facts.json",
            "film_config.json",
            "manim.cfg",
            "render.sh",
            "requirements.txt",
            "stitched_lil_result.py",
            "test_compose_soundtrack.py",
            "test_package.py",
            "test_verify_media.py",
            "verify_media.py",
        }
        self.assertTrue(expected.issubset({path.name for path in PACKAGE_DIR.iterdir()}))

    def test_fact_receipt_matches_pinned_git_sources(self) -> None:
        completed = subprocess.run(
            ["python3", str(PACKAGE_DIR / "extract_facts.py")],
            cwd=ROOT,
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn(self.facts["commit"], completed.stdout)

    def test_picture_timing_is_contiguous_and_locked(self) -> None:
        self.assertEqual(self.facts["commit"], self.config["source_commit"])
        self.assertEqual(self.config["duration_seconds"], 86.0)
        self.assertEqual(self.config["frame_rate"], 30)
        self.assertEqual(self.config["resolution"], [1920, 1080])
        scenes = self.config["scenes"]
        self.assertEqual([scene["start"] for scene in scenes], [0.0, 8.0, 20.0, 33.0, 46.0, 60.0, 74.0])
        for current, following in zip(scenes, scenes[1:], strict=False):
            self.assertEqual(current["end"], following["start"])
        self.assertEqual(scenes[-1]["end"], self.config["duration_seconds"])

    def test_transcript_timestamps_match_scene_starts(self) -> None:
        transcript = (PACKAGE_DIR / "TRANSCRIPT.md").read_text(encoding="utf-8")
        matches = re.findall(r"^##\s+(\d{2}):(\d{2})\.(\d{3})\s+—", transcript, re.MULTILINE)
        seconds = [int(minutes) * 60 + int(value) + int(milliseconds) / 1000 for minutes, value, milliseconds in matches]
        self.assertEqual(seconds, [scene["start"] for scene in self.config["scenes"]])

    def test_claim_is_compact_and_does_not_assert_priority(self) -> None:
        claim = self.facts["public_claim"].lower()
        for banned in ("first", "novel", "priority", "law of the iterated logarithm"):
            self.assertNotIn(banned, claim)
        self.assertEqual(
            self.facts["classification"],
            "DERIVED VARIANT / FORMALIZED COMPOSITION",
        )
        nonclaims = "\n".join(self.facts["nonclaims"]).lower()
        self.assertIn("not the law of the iterated logarithm", nonclaims)
        self.assertIn("not itself an e-process", nonclaims)
        self.assertIn("no first-formalization or priority claim", nonclaims)

    def test_editorial_copy_remains_short(self) -> None:
        for scene in self.config["scenes"]:
            self.assertLessEqual(len(scene["title"]), 52, scene["id"])
            self.assertLessEqual(len(scene["detail"]), 82, scene["id"])

    def test_python_sources_parse_without_importing_manim(self) -> None:
        for name in (
            "compose_soundtrack.py",
            "extract_facts.py",
            "stitched_lil_result.py",
            "test_compose_soundtrack.py",
            "test_package.py",
            "test_verify_media.py",
            "verify_media.py",
        ):
            path = PACKAGE_DIR / name
            ast.parse(path.read_text(encoding="utf-8"), filename=str(path))

    def test_film_uses_fact_receipt_and_no_randomness(self) -> None:
        source = (PACKAGE_DIR / "stitched_lil_result.py").read_text(encoding="utf-8")
        self.assertIn('FACTS = json.loads((PACKAGE_DIR / "facts.json")', source)
        self.assertIn("FACTS[\"result\"][\"theorem\"]", source)
        self.assertNotRegex(source, r"\b(?:random|np\.random)\b")

    def test_increment_timing_is_stated_exactly(self) -> None:
        process_model = "\n".join(self.facts["process_model"])
        self.assertIn("F_(k+1)", process_model)
        self.assertIn("E[X_k | F_k] = 0", process_model)
        self.assertNotIn("X is adapted to F_k", process_model)

    def test_render_path_is_fresh_and_receipted(self) -> None:
        script = (PACKAGE_DIR / "render.sh").read_text(encoding="utf-8")
        self.assertIn('mktemp -d "$OUT_DIR/render.XXXXXX"', script)
        self.assertIn('--metadata-output "$soundtrack_metadata"', script)
        self.assertIn('python3 "$VERIFIER"', script)
        self.assertIn('--artifact-name "$output"', script)
        self.assertLess(script.index('python3 "$VERIFIER"'), script.index('mv -f -- "$candidate_video"'))
        self.assertNotIn('-print -quit', script)

    def test_no_rendered_media_is_committed_in_source_package(self) -> None:
        rendered = [
            path
            for path in PACKAGE_DIR.rglob("*")
            if path.is_file() and path.suffix.lower() in {".mp4", ".mov", ".wav", ".aac"}
        ]
        self.assertEqual(rendered, [])

    def test_renderer_dependency_is_pinned(self) -> None:
        requirements = (PACKAGE_DIR / "requirements.txt").read_text(encoding="utf-8")
        self.assertEqual(requirements, "manim==0.20.1\n")


if __name__ == "__main__":
    unittest.main()
