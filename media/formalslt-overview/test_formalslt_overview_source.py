#!/usr/bin/env python3
"""Fast source-level regressions for the FormalSLT overview film."""

from __future__ import annotations

import ast
import configparser
import unittest
from pathlib import Path


MEDIA_ROOT = Path(__file__).resolve().parent
FILM_SOURCE = MEDIA_ROOT / "formalslt_overview.py"
RENDER_SCRIPT = MEDIA_ROOT / "render.sh"
RECEIPT_WRITER = MEDIA_ROOT / "write_render_receipt.py"
MAIN_CONFIG = MEDIA_ROOT / "manim.cfg"
SOCIAL_CONFIG = MEDIA_ROOT / "manim-social.cfg"


class OverviewSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.source = FILM_SOURCE.read_text(encoding="utf-8")

    def test_source_parses(self) -> None:
        ast.parse(self.source)

    def test_equations_are_real_tex(self) -> None:
        self.assertIn("MathTex(latex", self.source)
        for expected in (
            r"\mathbb{P}",
            r"\operatorname{gap}",
            r"\mathrm{KL}",
            r"p_{\mathrm{hit}}",
            r"\left\lVert P_{\gamma}",
        ):
            self.assertIn(expected, self.source)

    def test_known_pseudo_math_never_returns(self) -> None:
        for forbidden in (
            "P[ excess risk",
            "E[ generalization gap",
            "p_hit(",
            "TV(row",
            "4√(",
            "·exp(",
            "formula_chip",
            "formula_row",
        ):
            self.assertNotIn(forbidden, self.source)

    def test_text_and_equations_do_not_cross_fade_through_each_other(self) -> None:
        tree = ast.parse(self.source)
        offenders: list[int] = []
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            if not isinstance(node.func, ast.Attribute) or node.func.attr != "play":
                continue
            animation_names = {
                child.func.id
                for child in ast.walk(node)
                if isinstance(child, ast.Call) and isinstance(child.func, ast.Name)
            }
            if {"FadeIn", "FadeOut"} <= animation_names:
                offenders.append(node.lineno)
        self.assertEqual(
            offenders,
            [],
            f"split FadeOut/FadeIn into sequential plays at lines {offenders}",
        )

    def test_delivery_requires_sparse_original_soundtrack(self) -> None:
        render_source = RENDER_SCRIPT.read_text(encoding="utf-8")
        receipt_source = RECEIPT_WRITER.read_text(encoding="utf-8")
        self.assertIn("compose_soundtrack.py", render_source)
        self.assertIn("loudnorm=I=-22:LRA=7:TP=-3.5", render_source)
        self.assertIn("-map 0:v:0 -map 0:a:0", render_source)
        self.assertIn("exactly one AAC soundtrack", receipt_source)
        self.assertIn("ebur128=peak=true", receipt_source)
        self.assertIn("((6.0, 10.0) if role == \"main\" else (5.0, 9.0))", receipt_source)

    def test_social_cut_is_authored_and_rendered_natively_at_four_by_five(self) -> None:
        parser = configparser.ConfigParser()
        parser.read(SOCIAL_CONFIG)
        cli = parser["CLI"]
        self.assertEqual(cli.getint("pixel_width"), 1080)
        self.assertEqual(cli.getint("pixel_height"), 1350)
        self.assertEqual(cli.getfloat("frame_width"), 6.4)
        self.assertEqual(cli.getfloat("frame_height"), 8.0)
        render_source = RENDER_SCRIPT.read_text(encoding="utf-8")
        receipt_source = RECEIPT_WRITER.read_text(encoding="utf-8")
        self.assertIn("manim-social.cfg", render_source)
        self.assertIn("1080,1350", render_source)
        self.assertIn('(1080, 1350)', receipt_source)
        social_source = self.source.split("class FormalSLTSocial", 1)[1].split(
            "class FormalSLTPoster", 1
        )[0]
        self.assertIn("assert_social_geometry()", social_source)
        self.assertNotIn(r"p_{\mathrm{hit}}", social_source)

    def test_render_caches_stay_inside_ignored_media_directories(self) -> None:
        for config_path in (MAIN_CONFIG, SOCIAL_CONFIG):
            parser = configparser.ConfigParser()
            parser.read(config_path)
            cli = parser["CLI"]
            self.assertEqual(cli["tex_dir"], "{media_dir}/Tex")
            self.assertEqual(cli["text_dir"], "{media_dir}/texts")


if __name__ == "__main__":
    unittest.main()
