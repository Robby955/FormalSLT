#!/usr/bin/env python3
"""Source-only tests for the stitched-result film package."""

from __future__ import annotations

import ast
import configparser
import json
import re
import subprocess
import unittest
from pathlib import Path


PACKAGE_DIR = Path(__file__).resolve().parent
ROOT = PACKAGE_DIR.parents[1]
BOUND_SHA = "e01f857d1604788be35fdc2f3dc7108851471a88"


def timestamp_seconds(minutes: str, seconds: str, milliseconds: str) -> float:
    return int(minutes) * 60 + int(seconds) + int(milliseconds) / 1000


def transcript_starts(path: Path) -> list[float]:
    text = path.read_text(encoding="utf-8")
    matches = re.findall(
        r"^##\s+(\d{2}):(\d{2})\.(\d{3})\s+—",
        text,
        re.MULTILINE,
    )
    return [timestamp_seconds(*match) for match in matches]


def vtt_intervals(path: Path) -> list[tuple[float, float]]:
    text = path.read_text(encoding="utf-8")
    matches = re.findall(
        r"^(\d{2}):(\d{2})\.(\d{3}) --> (\d{2}):(\d{2})\.(\d{3})$",
        text,
        re.MULTILINE,
    )
    return [
        (timestamp_seconds(*match[:3]), timestamp_seconds(*match[3:]))
        for match in matches
    ]


class PackageTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.facts = json.loads((PACKAGE_DIR / "facts.json").read_text(encoding="utf-8"))
        cls.claims = json.loads(
            (PACKAGE_DIR / "claim-receipt.json").read_text(encoding="utf-8")
        )
        cls.config = json.loads(
            (PACKAGE_DIR / "film_config.json").read_text(encoding="utf-8")
        )

    def test_required_source_package_is_present(self) -> None:
        expected = {
            ".gitignore",
            "DELIVERY.md",
            "README.md",
            "SOUNDTRACK.md",
            "STORYBOARD.md",
            "TRANSCRIPT.md",
            "TRANSCRIPT-SOCIAL.md",
            "boundary_model.py",
            "captions-main.vtt",
            "captions-social.vtt",
            "claim-receipt.json",
            "compose_soundtrack.py",
            "extract_facts.py",
            "facts.json",
            "film_config.json",
            "manim.cfg",
            "manim-social.cfg",
            "render.sh",
            "requirements.txt",
            "stage_delivery.py",
            "stitched_lil_result.py",
            "test_boundary_model.py",
            "test_compose_soundtrack.py",
            "test_package.py",
            "test_stage_delivery.py",
            "test_verify_media.py",
            "verify_media.py",
        }
        self.assertTrue(expected.issubset({path.name for path in PACKAGE_DIR.iterdir()}))

    def test_fact_and_claim_receipts_match_pinned_git_sources(self) -> None:
        completed = subprocess.run(
            ["python3", str(PACKAGE_DIR / "extract_facts.py")],
            cwd=ROOT,
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn(BOUND_SHA, completed.stdout)
        self.assertEqual(self.facts["commit"], BOUND_SHA)
        self.assertEqual(self.claims["theorem_source_commit"], BOUND_SHA)
        self.assertEqual(self.config["source_commit"], BOUND_SHA)

    def test_picture_timing_is_contiguous_and_locked_for_both_cuts(self) -> None:
        contracts = (
            (self.config, 86.0, [1920, 1080], [0.0, 8.0, 20.0, 33.0, 46.0, 60.0, 74.0]),
            (self.config["social"], 44.0, [1080, 1350], [0.0, 7.0, 15.0, 26.0, 35.0]),
        )
        self.assertEqual(self.config["frame_rate"], 30)
        for contract, duration, resolution, starts in contracts:
            with self.subTest(resolution=resolution):
                self.assertEqual(contract["duration_seconds"], duration)
                self.assertEqual(contract["resolution"], resolution)
                scenes = contract["scenes"]
                self.assertEqual([scene["start"] for scene in scenes], starts)
                for current, following in zip(scenes, scenes[1:], strict=False):
                    self.assertEqual(current["end"], following["start"])
                self.assertEqual(scenes[-1]["end"], duration)

    def test_native_manim_geometry_matches_each_picture_lock(self) -> None:
        for config_name, contract in (
            ("manim.cfg", self.config),
            ("manim-social.cfg", self.config["social"]),
        ):
            parser = configparser.ConfigParser()
            parser.read(PACKAGE_DIR / config_name)
            cli = parser["CLI"]
            self.assertEqual(
                [int(cli["pixel_width"]), int(cli["pixel_height"])],
                contract["resolution"],
            )
            self.assertAlmostEqual(float(cli["frame_width"]), contract["frame"][0])
            self.assertAlmostEqual(float(cli["frame_height"]), contract["frame"][1])

    def test_transcripts_and_caption_sidecars_match_scene_locks(self) -> None:
        contracts = (
            (self.config, "TRANSCRIPT.md", "captions-main.vtt"),
            (self.config["social"], "TRANSCRIPT-SOCIAL.md", "captions-social.vtt"),
        )
        for contract, transcript_name, caption_name in contracts:
            scenes = contract["scenes"]
            with self.subTest(caption=caption_name):
                self.assertEqual(
                    transcript_starts(PACKAGE_DIR / transcript_name),
                    [scene["start"] for scene in scenes],
                )
                self.assertEqual(
                    vtt_intervals(PACKAGE_DIR / caption_name),
                    [(scene["start"], scene["end"]) for scene in scenes],
                )

    def test_claim_is_conservative_and_preserves_theorem_boundary(self) -> None:
        claim = self.facts["public_claim"].lower()
        for banned in ("first", "novel", "priority", "law of the iterated logarithm"):
            self.assertNotIn(banned, claim)
        self.assertEqual(
            self.facts["classification"],
            "FORMALIZED COMPOSITION; NO PRIORITY CLAIM",
        )
        self.assertEqual(self.claims["classification"], self.facts["classification"])
        assumptions = "\n".join(self.claims["assumptions"])
        self.assertIn("mu is a probability measure", assumptions)
        self.assertIn("strongly measurable with respect to F_(k+1)", assumptions)
        self.assertIn("|X_k| <= b almost everywhere", assumptions)
        self.assertIn("E[X_k | F_k] = 0 almost everywhere", assumptions)
        self.assertIn("E[X_k^2 | F_k] <= sigma^2 almost everywhere", assumptions)
        nonclaims = "\n".join(self.claims["nonclaims"]).lower()
        self.assertIn("not the law of the iterated logarithm", nonclaims)
        self.assertIn("not a sharp-constant or optimality result", nonclaims)
        self.assertIn("not an optional-stopping theorem", nonclaims)
        self.assertIn("measurability is not asserted", nonclaims)
        self.assertIn("no first-formalization or priority claim", nonclaims)

    def test_display_math_is_canonical_and_consumed_by_both_cuts(self) -> None:
        display = self.claims["display_math"]
        self.assertEqual(
            display["selector"],
            r"j=j(n),\qquad 4^{j+1}\le n<4^{j+2}",
        )
        self.assertEqual(
            display["width"],
            r"W_n=2\sqrt{\frac{2\sigma^2B_j}{n}}+\frac{4bB_j}{3n}",
        )
        self.assertEqual(
            display["failure_mass"],
            r"\mu_{\mathbb R}(G^{\mathsf c})\le\delta",
        )
        source = (PACKAGE_DIR / "stitched_lil_result.py").read_text(encoding="utf-8")
        self.assertIn('DISPLAY_MATH = CLAIMS["display_math"]', source)
        for key in (
            "selector",
            "budget",
            "width",
            "width_first_line",
            "width_second_line",
            "failure_mass",
            "event_condition",
            "event_bound",
            "event_conclusion",
        ):
            self.assertIn(f'DISPLAY_MATH["{key}"]', source, key)
        self.assertIn("MathTex(latex", source)
        self.assertNotRegex(source, r"code\(r?[\"'](?:W_|B_|\\mu|\\forall)")

    def test_fixed_tilt_plot_uses_the_exact_boundary_model(self) -> None:
        source = (PACKAGE_DIR / "stitched_lil_result.py").read_text(encoding="utf-8")
        self.assertIn("fixed_tilt_boundary_value(index, float(n))", source)
        self.assertIn("stitched_width_value(float(n))", source)
        self.assertIn("set_points_as_corners(points)", source)
        self.assertIn("for n in range(start, end)", source)
        self.assertNotIn("sub-Gamma lines", source)
        self.assertIn("PATH ILLUSTRATIVE", source)

    def test_editorial_copy_remains_bounded(self) -> None:
        for contract in (self.config, self.config["social"]):
            for scene in contract["scenes"]:
                self.assertLessEqual(len(scene["title"]), 58, scene["id"])
                self.assertLessEqual(len(scene["detail"]), 86, scene["id"])

    def test_python_sources_parse_without_importing_manim(self) -> None:
        for path in PACKAGE_DIR.glob("*.py"):
            ast.parse(path.read_text(encoding="utf-8"), filename=str(path))

    def test_no_randomness_or_stale_claim_copy(self) -> None:
        source = (PACKAGE_DIR / "stitched_lil_result.py").read_text(encoding="utf-8")
        self.assertIn('FACTS = json.loads((PACKAGE_DIR / "facts.json")', source)
        self.assertIn("FACTS[\"result\"][\"theorem\"]", source)
        self.assertNotRegex(source, r"\b(?:random|np\.random)\b")
        checked_suffixes = {".py", ".md", ".json", ".vtt", ".sh", ".cfg"}
        corpus = "\n".join(
            path.read_text(encoding="utf-8")
            for path in PACKAGE_DIR.iterdir()
            if path.is_file()
            and path.name != "test_package.py"
            and path.suffix in checked_suffixes
        )
        for stale in (
            "285921b",
            "Every time",
            "whole timeline",
            "Most guarantees",
            "Not sharp",
            "DERIVED VARIANT",
        ):
            self.assertNotIn(stale, corpus)

    def test_render_path_is_fresh_and_receipted(self) -> None:
        script = (PACKAGE_DIR / "render.sh").read_text(encoding="utf-8")
        self.assertIn('mktemp -d "$OUT_DIR/render.XXXXXX"', script)
        self.assertIn('--metadata-output "$soundtrack_metadata"', script)
        self.assertIn('python3 "$VERIFIER"', script)
        self.assertIn('--artifact-name "$output"', script)
        self.assertIn('--composition "$composition"', script)
        self.assertIn('--ffmpeg "$FFMPEG_BIN"', script)
        self.assertLess(
            script.index('python3 "$VERIFIER"'),
            script.index('mv -f -- "$candidate_video"'),
        )
        self.assertNotIn("-print -quit", script)

    def test_release_runs_both_layout_preflights_before_rendering(self) -> None:
        script = (PACKAGE_DIR / "render.sh").read_text(encoding="utf-8")
        self.assertIn("layout-check)", script)
        self.assertIn('"$MANIM_BIN" --config_file "$config_file" --dry_run', script)
        self.assertIn(
            'layout_check_composition "$PACKAGE/manim.cfg" StitchedLILResultFilm',
            script,
        )
        self.assertIn(
            'layout_check_composition "$PACKAGE/manim-social.cfg" StitchedLILResultSocial',
            script,
        )
        self.assertIn(
            'layout_check_composition "$PACKAGE/manim.cfg" StitchedLILResultPoster',
            script,
        )
        self.assertIn(
            'layout_check_composition "$PACKAGE/manim-social.cfg" StitchedLILResultSocialPoster',
            script,
        )
        release = script.split("  release)", maxsplit=1)[1].split("    ;;", maxsplit=1)[0]
        self.assertLess(release.index("layout_check_all"), release.index("render_movie"))

    def test_render_caches_are_ignored_and_untracked(self) -> None:
        for relative in (
            "media/stitched-lil-result-film/media/example",
            "media/stitched-lil-result-film/out/example",
        ):
            completed = subprocess.run(
                ["git", "-C", str(ROOT), "check-ignore", "-q", relative],
                check=False,
            )
            self.assertEqual(completed.returncode, 0, relative)
        tracked = subprocess.run(
            [
                "git",
                "-C",
                str(ROOT),
                "ls-files",
                "media/stitched-lil-result-film/media",
                "media/stitched-lil-result-film/out",
            ],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        ).stdout.strip()
        self.assertEqual(tracked, "")

    def test_renderer_dependency_is_pinned(self) -> None:
        requirements = (PACKAGE_DIR / "requirements.txt").read_text(encoding="utf-8")
        self.assertEqual(requirements, "manim==0.20.1\n")


if __name__ == "__main__":
    unittest.main()
