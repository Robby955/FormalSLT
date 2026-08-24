from __future__ import annotations

import json
from pathlib import Path

import numpy as np
from manim import (
    AnimationGroup,
    Arrow,
    Axes,
    Circle,
    Create,
    DashedLine,
    Dot,
    DOWN,
    FadeIn,
    FadeOut,
    GrowFromCenter,
    LaggedStart,
    LEFT,
    Line,
    MoveAlongPath,
    Polygon,
    Rectangle,
    RIGHT,
    RoundedRectangle,
    Scene,
    Text,
    Transform,
    UP,
    VGroup,
    VMobject,
    config,
    linear,
)


ROOT = Path(__file__).resolve().parents[2]
FACTS = json.loads((Path(__file__).with_name("facts.json")).read_text())

BG = "#08111E"
IVORY = "#F4F1E8"
CYAN = "#64D8D2"
SOFT_CYAN = "#9FD9D5"
MUTED = "#A7B3C2"
DEEP = "#172539"
AMBER = "#F0B35A"
RED = "#EF6A68"

FRAME_LEFT = -6.75
FRAME_RIGHT = 6.75
FRAME_TOP = 3.72
FRAME_BOTTOM = -3.72
CONTENT_TOP = 1.72
CONTENT_BOTTOM = -2.08

SCENE_TITLE_SIZE = 46
SCENE_DETAIL_SIZE = 29
BODY_SIZE = 28
LABEL_SIZE = 28
SMALL_SIZE = 24
FORMULA_SIZE = 24

DISPLAY_FONT = "Avenir Next"
CODE_FONT = "Menlo"

# Scene start times in seconds. compose_soundtrack.py places its impacts on
# these boundaries; the render fails if a scene drifts off its cue.
MAIN_SCENE_STARTS = {
    "intro": 0.0,
    "field_map": 5.0,
    "classical_spine": 14.0,
    "pac_bayes": 23.0,
    "anytime": 32.0,
    "dependent_path": 41.0,
    "structured_case_study": 50.0,
    "proof_map": 59.0,
    "close": 66.0,
    "end": 72.0,
}
SOCIAL_SCENE_STARTS = {
    "social_hook": 0.0,
    "social_spine": 4.0,
    "social_close": 9.0,
    "end": 13.0,
}
SCENE_CLOCK_TOLERANCE = 0.05
CLEAR_RUN_TIME = 0.55
MIN_READING_HOLD = 0.5

config.background_color = BG


def label(
    text: str,
    size: float,
    color: str = IVORY,
    weight: str = "MEDIUM",
    font: str = DISPLAY_FONT,
) -> Text:
    return Text(
        text,
        font=font,
        font_size=size,
        color=color,
        weight=weight,
        disable_ligatures=True,
    )


def code(text: str, size: float = FORMULA_SIZE, color: str = SOFT_CYAN) -> Text:
    return label(text, size, color, "BOLD", CODE_FONT)


def eyebrow(text: str) -> Text:
    item = label(text.upper(), SMALL_SIZE, CYAN, "BOLD")
    item.set_opacity(0.95)
    return item


def caption(title: str, body: str) -> VGroup:
    heading = label(title, SCENE_TITLE_SIZE, IVORY, "BOLD")
    detail = label(body, SCENE_DETAIL_SIZE, MUTED, "MEDIUM")
    if heading.width > 12.0 or detail.width > 12.0:
        raise ValueError(
            "Scene copy exceeds the 12-unit safe width; wrap or shorten it "
            "instead of shrinking the font."
        )
    group = VGroup(heading, detail).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
    group.to_edge(LEFT, buff=0.72).to_edge(UP, buff=0.55)
    return group


def text_lines(
    lines: list[str],
    size: float,
    color: str = IVORY,
    weight: str = "MEDIUM",
    font: str = DISPLAY_FONT,
    buff: float = 0.08,
) -> VGroup:
    """Build an explicit text block; never shrink prose to hide overflow."""
    block = VGroup(
        *[label(line, size, color, weight, font) for line in lines]
    ).arrange(DOWN, aligned_edge=LEFT, buff=buff)
    if block.width > 12.0:
        raise ValueError("Text block exceeds the film safe width.")
    return block


def assert_in_frame(item, name: str, margin: float = 0.12) -> None:
    if (
        item.get_left()[0] < FRAME_LEFT + margin
        or item.get_right()[0] > FRAME_RIGHT - margin
        or item.get_top()[1] > FRAME_TOP - margin
        or item.get_bottom()[1] < FRAME_BOTTOM + margin
    ):
        raise ValueError(
            f"{name} leaves the render-safe frame: "
            f"left={item.get_left()[0]:.3f}, right={item.get_right()[0]:.3f}, "
            f"top={item.get_top()[1]:.3f}, bottom={item.get_bottom()[1]:.3f}"
        )


def assert_in_content(item, name: str) -> None:
    if item.get_top()[1] > CONTENT_TOP or item.get_bottom()[1] < CONTENT_BOTTOM:
        raise ValueError(
            f"{name} leaves the caption-safe content band: "
            f"top={item.get_top()[1]:.3f}, bottom={item.get_bottom()[1]:.3f}, "
            f"allowed=[{CONTENT_BOTTOM:.3f}, {CONTENT_TOP:.3f}]"
        )


def assert_horizontal_gap(left_item, right_item, name: str, gap: float = 0.35) -> None:
    if left_item.get_right()[0] + gap > right_item.get_left()[0]:
        raise ValueError(
            f"{name} columns overlap: left right={left_item.get_right()[0]:.3f}, "
            f"right left={right_item.get_left()[0]:.3f}, required gap={gap:.3f}"
        )


def assert_no_overlap(first, second, name: str, gap: float = 0.08) -> None:
    separated = (
        first.get_right()[0] + gap <= second.get_left()[0]
        or second.get_right()[0] + gap <= first.get_left()[0]
        or first.get_top()[1] + gap <= second.get_bottom()[1]
        or second.get_top()[1] + gap <= first.get_bottom()[1]
    )
    if not separated:
        raise ValueError(f"{name} overlap; revise the composition instead of shrinking text")


def path_curve(points: list[np.ndarray], color: str = CYAN, width: float = 4) -> VMobject:
    curve = VMobject(
        stroke_color=color,
        stroke_width=width,
        fill_color=color,
        fill_opacity=0,
    )
    curve.set_points_smoothly(points)
    curve.set_fill(opacity=0)
    return curve


def band_motif(width: float = 11.0, height: float = 0.75, opacity: float = 0.22) -> VGroup:
    """Faint shrinking confidence band; a quiet visual signature for the lockups."""
    xs = np.linspace(0.0, 1.0, 40)
    half = width / 2
    upper = path_curve(
        [np.array([-half + width * x, height / np.sqrt(1 + 9 * x), 0]) for x in xs],
        CYAN,
        2.2,
    )
    lower = path_curve(
        [np.array([-half + width * x, -height / np.sqrt(1 + 9 * x), 0]) for x in xs],
        CYAN,
        2.2,
    )
    trace = path_curve(
        [
            np.array([-half + width * x, 0.45 * height * np.sin(9 * x) / np.sqrt(1 + 9 * x), 0])
            for x in xs
        ],
        IVORY,
        2.0,
    )
    group = VGroup(upper, lower, trace)
    group.set_stroke(opacity=opacity)
    return group


def coordinate_panel(width: float = 4.6, height: float = 3.15) -> VGroup:
    """Six visible macro-bins per axis, each standing for eight observations."""
    frame = Rectangle(
        width=width,
        height=height,
        color=CYAN,
        stroke_width=2.2,
        fill_color="#10233A",
        fill_opacity=0.72,
    )
    lines = VGroup()
    for index in range(8, 48, 8):
        x = -width / 2 + width * index / 48
        y = -height / 2 + height * index / 48
        lines.add(
            Line(
                np.array([x, -height / 2, 0]),
                np.array([x, height / 2, 0]),
                color=CYAN,
                stroke_width=1.5,
                stroke_opacity=0.48,
            ),
            Line(
                np.array([-width / 2, y, 0]),
                np.array([width / 2, y, 0]),
                color=CYAN,
                stroke_width=1.5,
                stroke_opacity=0.48,
            ),
        )
    return VGroup(frame, lines)


def topic_card(text: str, *, active: bool = False, width: float = 3.5) -> VGroup:
    box = RoundedRectangle(
        width=width,
        height=0.95,
        corner_radius=0.12,
        color=CYAN if active else DEEP,
        stroke_width=2.2,
        fill_color="#0B1625",
        fill_opacity=0.98,
    )
    copy_size = 24 if width < 3.5 and len(text) >= 12 else 28
    copy = label(text, copy_size, IVORY, "BOLD")
    if copy.width > width - 0.22:
        raise ValueError(f"Topic label does not fit its card: {text!r}")
    copy.move_to(box)
    return VGroup(box, copy)


def formula_chip(text: str, size: float = FORMULA_SIZE, color: str = SOFT_CYAN) -> VGroup:
    copy = code(text, size, color)
    box = RoundedRectangle(
        width=copy.width + 0.44,
        height=copy.height + 0.24,
        corner_radius=0.10,
        color=DEEP,
        stroke_width=1.8,
        fill_color="#0B1625",
        fill_opacity=0.96,
    )
    copy.move_to(box)
    return VGroup(box, copy)


def formula_row(name: str, formula: str, size: float = FORMULA_SIZE) -> VGroup:
    """A muted route name followed by the checked bound shape in code font."""
    tag = label(name, 23, MUTED, "BOLD")
    chip = formula_chip(formula, size)
    row = VGroup(tag, chip).arrange(RIGHT, buff=0.30)
    if row.width > 12.0:
        raise ValueError(f"Formula row exceeds the film safe width: {name!r}")
    return row


def play_mark(radius: float = 0.52) -> VGroup:
    ring = Circle(
        radius=radius,
        color=IVORY,
        stroke_width=2.4,
        fill_color=BG,
        fill_opacity=0.75,
    )
    triangle = Polygon(
        np.array([-0.14, -0.22, 0]),
        np.array([-0.14, 0.22, 0]),
        np.array([0.23, 0, 0]),
        color=CYAN,
        fill_color=CYAN,
        fill_opacity=1,
        stroke_width=0,
    ).shift(RIGHT * 0.04)
    return VGroup(ring, triangle)


def brand_mark() -> VGroup:
    return VGroup(
        Line(LEFT * 0.38, RIGHT * 0.38, color=CYAN, stroke_width=5),
        Dot(radius=0.07, color=CYAN).shift(LEFT * 0.38),
        Dot(radius=0.07, color=CYAN).shift(RIGHT * 0.38),
    )


class FormalSLTOverview(Scene):
    scene_starts = MAIN_SCENE_STARTS

    def construct(self) -> None:
        self.intro()
        self.field_map()
        self.classical_spine()
        self.pac_bayes()
        self.anytime()
        self.dependent_path()
        self.structured_case_study()
        self.proof_map()
        self.close()

    def on_cue(self, scene_name: str) -> None:
        """Fail the render if a scene starts off its soundtrack cue."""
        expected = self.scene_starts[scene_name]
        actual = float(self.renderer.time)
        if abs(actual - expected) > SCENE_CLOCK_TOLERANCE:
            raise ValueError(
                f"scene {scene_name!r} starts at {actual:.3f}s, expected "
                f"{expected:.3f}s; retime the scene or the cue ledger"
            )

    def hold_until(self, next_scene: str, clear: float = CLEAR_RUN_TIME) -> None:
        """Hold the finished composition until the next cue, absorbing frame rounding."""
        target = self.scene_starts[next_scene] - clear
        remaining = target - float(self.renderer.time)
        if remaining < MIN_READING_HOLD:
            raise ValueError(
                f"only {remaining:.3f}s of reading hold remain before {next_scene!r}; "
                f"shorten the scene's animations instead of the hold"
            )
        self.wait(remaining)

    def clear_for_next(self, *keep) -> None:
        protected = set(keep)
        targets = [mob for mob in self.mobjects if mob not in protected]
        if targets:
            self.play(
                AnimationGroup(
                    *[FadeOut(mob, shift=UP * 0.08) for mob in targets],
                    lag_ratio=0,
                ),
                run_time=CLEAR_RUN_TIME,
            )

    def intro(self) -> None:
        self.on_cue("intro")
        mark = brand_mark().shift(UP * 1.55)
        title = label("FormalSLT", 75, IVORY, "BOLD")
        title.next_to(mark, DOWN, buff=0.36)
        subtitle = label(
            "Machine-checked statistical learning in Lean.",
            34,
            IVORY,
            "MEDIUM",
        )
        subtitle.next_to(title, DOWN, buff=0.22)
        scope = label(
            "VC · Rademacher · chaining · PAC-Bayes · sequential · dependent data",
            24,
            CYAN,
            "MEDIUM",
        )
        scope.next_to(subtitle, DOWN, buff=0.36)
        band = band_motif().move_to(DOWN * 2.25)
        stamp = label(
            f"SOURCE  {FACTS['short_commit']}",
            18,
            MUTED,
            "BOLD",
            CODE_FONT,
        ).to_edge(DOWN, buff=0.42)
        assert_in_frame(VGroup(mark, title, subtitle, scope, band, stamp), "intro")
        assert_no_overlap(scope, band, "intro band")
        assert_no_overlap(band, stamp, "intro stamp")

        self.play(Create(mark), Create(band), run_time=0.8)
        self.play(FadeIn(title, shift=UP * 0.08), FadeIn(subtitle, shift=UP * 0.12), run_time=0.75)
        self.play(FadeIn(scope), FadeIn(stamp), run_time=0.55)
        self.hold_until("field_map")
        self.clear_for_next()

    def field_map(self) -> None:
        self.on_cue("field_map")
        head = caption(
            "One library across the field",
            "Classical generalization and modern sequential inference.",
        )
        self.play(FadeIn(head), run_time=0.6)

        names = [
            "VC theory",
            "Rademacher",
            "Chaining",
            "PAC-Bayes",
            "Sequential",
            "Dependent data",
        ]
        topics = VGroup(*[
            topic_card(name, active=index in (0, 3), width=3.55)
            for index, name in enumerate(names)
        ]).arrange_in_grid(rows=2, cols=3, buff=(0.42, 0.34)).shift(UP * 0.12)
        top_row = VGroup(*topics[:3])
        bottom_row = VGroup(*topics[3:])
        links = VGroup(
            *[
                Line(
                    topics[index][0].get_bottom(),
                    topics[index + 3][0].get_top(),
                    color=DEEP,
                    stroke_width=2.6,
                )
                for index in range(3)
            ],
            Line(
                topics[0][0].get_right(),
                topics[1][0].get_left(),
                color=DEEP,
                stroke_width=2.6,
            ),
            Line(
                topics[1][0].get_right(),
                topics[2][0].get_left(),
                color=DEEP,
                stroke_width=2.6,
            ),
            Line(
                topics[3][0].get_right(),
                topics[4][0].get_left(),
                color=DEEP,
                stroke_width=2.6,
            ),
            Line(
                topics[4][0].get_right(),
                topics[5][0].get_left(),
                color=DEEP,
                stroke_width=2.6,
            ),
        )
        center = Dot(radius=0.10, color=CYAN).move_to(topics[0])
        route = VMobject().set_points_as_corners(
            [topics[index].get_center() for index in (0, 1, 2, 5, 4, 3)]
        )
        thesis = label(
            "Capacity  ·  complexity  ·  selection  ·  time  ·  dependence",
            28,
            CYAN,
            "BOLD",
        ).next_to(topics, DOWN, buff=0.42)
        assert_in_content(VGroup(topics, thesis), "field map")
        assert_in_frame(VGroup(topics, thesis), "field map")

        self.play(
            LaggedStart(*[FadeIn(card, shift=UP * 0.1) for card in top_row], lag_ratio=0.12),
            run_time=0.8,
        )
        self.play(
            LaggedStart(*[FadeIn(card, shift=UP * 0.1) for card in bottom_row], lag_ratio=0.12),
            run_time=0.8,
        )
        self.play(Create(links), run_time=0.8)
        self.add(center)
        self.play(MoveAlongPath(center, route, rate_func=linear), run_time=1.6)
        self.play(FadeOut(center), FadeIn(thesis, shift=UP * 0.08), run_time=0.7)
        self.hold_until("classical_spine")
        self.clear_for_next()

    def classical_spine(self) -> None:
        self.on_cue("classical_spine")
        head = caption(
            "From capacity to generalization",
            "VC growth and metric entropy meet at complexity bounds.",
        )
        self.play(FadeIn(head), run_time=0.6)

        top = VGroup(*[
            topic_card(name, active=index in (0, 3), width=2.55)
            for index, name in enumerate(
                ["VC dimension", "Growth bound", "Rademacher", "Risk bound"]
            )
        ]).arrange(RIGHT, buff=0.48).move_to(UP * 1.05)
        lower = VGroup(
            topic_card("Covering numbers", width=3.25),
            topic_card("Chaining", active=True, width=2.65),
        ).arrange(RIGHT, buff=0.72).move_to(DOWN * 0.22 + LEFT * 0.85)

        top_arrows = VGroup(*[
            Arrow(
                top[index][0].get_right(),
                top[index + 1][0].get_left(),
                buff=0.08,
                color=MUTED,
                stroke_width=2.5,
                stroke_opacity=0.65,
                max_tip_length_to_length_ratio=0.18,
            )
            for index in range(len(top) - 1)
        ])
        lower_arrow = Arrow(
            lower[0][0].get_right(),
            lower[1][0].get_left(),
            buff=0.08,
            color=MUTED,
            stroke_width=2.5,
            max_tip_length_to_length_ratio=0.18,
        )
        join = Arrow(
            lower[1][0].get_top(),
            top[2][0].get_bottom(),
            buff=0.10,
            color=CYAN,
            stroke_width=2.8,
            max_tip_length_to_length_ratio=0.18,
        )
        pulse = Dot(top[0].get_center(), radius=0.09, color=CYAN)
        top_route = VMobject().set_points_as_corners(
            [card.get_center() for card in top]
        )
        lower_pulse = Dot(lower[0].get_center(), radius=0.09, color=CYAN)
        lower_route = VMobject().set_points_as_corners(
            [lower[0].get_center(), lower[1].get_center(), top[2].get_center()]
        )

        # Bound shapes copied from the pinned declarations; the extractor
        # checks the leading constants 2 and 8 and the sqrt / exp forms.
        vc_route = formula_row(
            "VC route",
            "P[ excess risk ≥ 4√(2d·log(en/d)/n) + 2ε ] ≤ 2·exp(−ε²n/8)",
            20,
        )
        entropy_route = formula_row(
            "Entropy route",
            "E[ generalization gap ] ≤ 8·√(2/n) · ∫ √(log N(ε)) dε",
            20,
        )
        routes = VGroup(vc_route, entropy_route).arrange(
            DOWN, aligned_edge=LEFT, buff=0.14
        )
        routes.move_to(DOWN * 1.46)
        assert_in_content(VGroup(top, lower, routes), "classical learning routes")
        assert_in_frame(VGroup(top, lower, routes), "classical learning routes")
        assert_no_overlap(lower, routes, "classical routes vs formulas")

        self.play(
            LaggedStart(
                *[FadeIn(node, shift=UP * 0.1) for node in VGroup(*top, *lower)],
                lag_ratio=0.10,
            ),
            run_time=1.1,
        )
        self.play(Create(top_arrows), Create(lower_arrow), Create(join), run_time=0.8)
        self.add(pulse)
        self.play(MoveAlongPath(pulse, top_route, rate_func=linear), run_time=1.0)
        self.add(lower_pulse)
        self.play(
            FadeOut(pulse),
            MoveAlongPath(lower_pulse, lower_route, rate_func=linear),
            run_time=1.0,
        )
        self.play(
            top[2][0].animate.set_stroke(CYAN, width=3, opacity=1),
            top[3][0].animate.set_stroke(CYAN, width=3, opacity=1),
            FadeOut(lower_pulse),
            run_time=0.7,
        )
        self.play(FadeIn(vc_route, shift=UP * 0.08), run_time=0.5)
        self.play(FadeIn(entropy_route, shift=UP * 0.08), run_time=0.5)
        self.hold_until("pac_bayes")
        self.clear_for_next()

    def pac_bayes(self) -> None:
        self.on_cue("pac_bayes")
        head = caption(
            "Choose after seeing the data",
            "PAC-Bayes prices posterior selection with relative entropy.",
        )
        self.play(FadeIn(head), run_time=0.6)

        row_y = 1.05
        prior = topic_card("prior  π", active=True, width=2.5).move_to(LEFT * 4.5 + UP * row_y)
        data = VGroup(
            *[
                Dot(radius=0.08, color=IVORY if index < 5 else CYAN)
                for index in range(8)
            ]
        ).arrange(RIGHT, buff=0.24).move_to(UP * (row_y + 0.12))
        data_label = label("observed data", 26, MUTED, "BOLD").next_to(
            data, DOWN, buff=0.20
        )
        posterior = topic_card("posterior  ρ", active=True, width=2.9).move_to(
            RIGHT * 4.35 + UP * row_y
        )
        arrows = VGroup(
            Arrow(prior[0].get_right(), data.get_left(), buff=0.18, color=MUTED),
            Arrow(data.get_right(), posterior[0].get_left(), buff=0.18, color=CYAN),
        )
        posterior_choices = VGroup(*[
            Dot(radius=0.07, color=CYAN if index == 2 else MUTED)
            for index in range(5)
        ]).arrange(RIGHT, buff=0.20).next_to(posterior, DOWN, buff=0.22)
        choices_label = label("every allowed ρ", 22, MUTED, "BOLD").next_to(
            posterior_choices, DOWN, buff=0.10
        )
        kl = formula_chip("selection cost:  KL(ρ ‖ π)", 28, CYAN)
        kl.move_to(DOWN * 0.38 + LEFT * 0.45)
        guarantee = label(
            "One event covers every allowed posterior.",
            30,
            IVORY,
            "BOLD",
        ).next_to(kl, DOWN, buff=0.24).set_x(0)
        delta = formula_row(
            "Checked",
            "P[ the bound fails for some allowed ρ ] ≤ δ",
            20,
        ).next_to(guarantee, DOWN, buff=0.18).set_x(0)
        scene = VGroup(
            prior, data, data_label, posterior, posterior_choices, choices_label,
            kl, guarantee, delta,
        )
        assert_in_content(scene, "PAC-Bayes scene")
        assert_in_frame(scene, "PAC-Bayes scene")
        assert_no_overlap(kl, prior, "PAC-Bayes cost vs prior")
        assert_no_overlap(kl, data_label, "PAC-Bayes cost vs data label")
        assert_no_overlap(kl, choices_label, "PAC-Bayes cost vs choices")

        self.play(FadeIn(prior, shift=RIGHT * 0.1), run_time=0.8)
        self.play(LaggedStart(*[GrowFromCenter(dot) for dot in data], lag_ratio=0.08), FadeIn(data_label), run_time=0.6)
        self.play(FadeIn(posterior, shift=LEFT * 0.1), Create(arrows), run_time=0.8)
        self.play(FadeIn(kl, shift=UP * 0.08), run_time=0.7)
        self.play(FadeIn(guarantee, shift=UP * 0.08), run_time=0.8)
        self.play(
            LaggedStart(*[GrowFromCenter(dot) for dot in posterior_choices], lag_ratio=0.15),
            FadeIn(choices_label),
            run_time=1.2,
        )
        self.play(FadeIn(delta, shift=UP * 0.08), run_time=0.5)
        self.hold_until("anytime")
        self.clear_for_next()

    def anytime(self) -> None:
        self.on_cue("anytime")
        head = caption(
            "Keep looking. Keep the guarantee.",
            "Confidence sequences and e-processes cover repeated looks.",
        )
        self.play(FadeIn(head), run_time=0.6)

        axes = Axes(
            x_range=[0, 10, 2],
            y_range=[-1.2, 1.2, 0.6],
            x_length=10.2,
            y_length=2.2,
            axis_config={"color": DEEP, "stroke_width": 2, "include_ticks": False},
            tips=False,
        ).shift(UP * 0.30)
        band_fn = lambda x: 0.95 / np.sqrt(x + 0.55)
        trace_fn = lambda x: 0.42 * np.sin(1.7 * x) / np.sqrt(x + 0.7)
        upper = axes.plot(band_fn, x_range=[0.25, 10], color=CYAN, stroke_width=3)
        lower = axes.plot(lambda x: -band_fn(x), x_range=[0.25, 10], color=CYAN, stroke_width=3)
        trace = axes.plot(trace_fn, x_range=[0.25, 10], color=IVORY, stroke_width=3.5)
        band_label = label("confidence sequence", 20, CYAN, "BOLD")
        band_label.next_to(axes.c2p(7.7, -band_fn(7.7)), DOWN, buff=0.12)
        looks = [0.7, 3.2, 6.2, 9.2]
        scan = DashedLine(
            axes.c2p(looks[0], -1.0), axes.c2p(looks[0], 1.0),
            color=AMBER, stroke_width=2.2, dash_length=0.08,
        )
        scan_label = label("look", SMALL_SIZE, AMBER, "BOLD").next_to(scan, UP, buff=0.12)
        for x in looks:
            probe = DashedLine(axes.c2p(x, -1.0), axes.c2p(x, 1.0))
            probe_label = label("look", SMALL_SIZE, AMBER, "BOLD").next_to(probe, UP, buff=0.12)
            assert_no_overlap(band_label, probe, f"anytime band label vs look at {x}")
            assert_no_overlap(band_label, probe_label, f"anytime band label vs look label at {x}")

        eprocess = formula_row("E-process", "P[ max E_k ≥ 1/α ] ≤ α", 20)
        eprocess.move_to(DOWN * 1.30)
        quantifier = VGroup(
            label("ONE EVENT", LABEL_SIZE, CYAN, "BOLD"),
            label("EVERY TIME", LABEL_SIZE, IVORY, "BOLD"),
            label("EVERY DECLARED CHOICE", LABEL_SIZE, IVORY, "BOLD"),
        ).arrange(RIGHT, buff=0.9).move_to(DOWN * 1.88)
        assert_in_content(VGroup(axes, band_label, eprocess, quantifier), "anytime scene")
        assert_no_overlap(axes, eprocess, "anytime axes vs e-process")
        assert_no_overlap(band_label, eprocess, "anytime band label vs e-process")
        assert_no_overlap(eprocess, quantifier, "anytime e-process vs quantifier")

        self.play(Create(axes), run_time=0.7)
        self.play(Create(upper), Create(lower), Create(trace), FadeIn(band_label), run_time=1.3)
        self.play(FadeIn(scan), FadeIn(scan_label), run_time=0.4)
        for x in looks[1:]:
            target = DashedLine(
                axes.c2p(x, -1.0), axes.c2p(x, 1.0),
                color=AMBER, stroke_width=2.2, dash_length=0.08,
            )
            look_dot = Dot(axes.c2p(x, trace_fn(x)), radius=0.09, color=AMBER)
            self.play(
                Transform(scan, target),
                scan_label.animate.next_to(target, UP, buff=0.12),
                GrowFromCenter(look_dot),
                run_time=0.48,
            )
        self.play(FadeIn(eprocess, shift=UP * 0.08), run_time=0.5)
        self.play(LaggedStart(*[FadeIn(x, shift=UP * 0.08) for x in quantifier], lag_ratio=0.12), run_time=0.8)
        self.hold_until("dependent_path")
        self.clear_for_next()

    def dependent_path(self) -> None:
        self.on_cue("dependent_path")
        head = caption(
            "Learning along a path",
            "Choose from the prefix. Score before the next state.",
        )
        self.play(FadeIn(head), run_time=0.6)

        base_y = 0.30
        centers = [
            np.array([-6.05, base_y + 0.00, 0]),
            np.array([-5.05, base_y + 0.50, 0]),
            np.array([-4.05, base_y - 0.28, 0]),
            np.array([-3.00, base_y + 0.36, 0]),
            np.array([-1.90, base_y - 0.18, 0]),
        ]
        nodes = VGroup(*[Circle(radius=0.24, color=IVORY, stroke_width=2.6).move_to(p) for p in centers])
        arrows = VGroup(*[
            Arrow(centers[i], centers[i + 1], buff=0.28, color=MUTED, stroke_width=2.5, max_tip_length_to_length_ratio=0.12)
            for i in range(len(centers) - 1)
        ])
        memory = VGroup()
        for index in [2, 3, 4]:
            arc = path_curve([
                centers[0] + UP * 0.23,
                centers[0] + UP * (0.42 + 0.10 * index),
                centers[index] + UP * (0.42 + 0.10 * index),
                centers[index] + UP * 0.23,
            ], CYAN, 1.8)
            arc.set_stroke(opacity=0.3 + index * 0.1)
            memory.add(arc)

        history = label("OBSERVED PREFIX", 24, CYAN, "BOLD")
        history.next_to(memory, UP, buff=0.06)
        choice = VGroup(
            label("posterior + tilt", 24, CYAN, "BOLD"),
            label("chosen from the prefix", 27, IVORY, "BOLD"),
        ).arrange(DOWN, buff=0.08).next_to(nodes, DOWN, buff=0.40)

        bridge = Arrow(
            LEFT * 1.15 + UP * base_y,
            RIGHT * 1.25 + UP * base_y,
            color=CYAN,
            stroke_width=4,
            buff=0.05,
        )
        bridge_label = label("Poisson correction", 25, CYAN, "BOLD")
        bridge_label.next_to(bridge, UP, buff=0.18)

        ring_center = RIGHT * 4.35 + UP * base_y
        orbit = Circle(radius=1.12, color=DEEP, stroke_width=3).move_to(ring_center)
        orbit_nodes = VGroup(*[
            Dot(ring_center + 1.12 * np.array([np.cos(a), np.sin(a), 0]), radius=0.08, color=CYAN)
            for a in np.linspace(0, 2 * np.pi, 9)[:-1]
        ])
        pi = label("π", 40, IVORY, "BOLD", CODE_FONT).move_to(ring_center)
        stationary_title = label("stationary risk", 27, MUTED, "BOLD")
        stationary_title.next_to(orbit, DOWN, buff=0.16)

        result = label(
            "trajectory evidence  →  long-run target",
            28,
            IVORY,
            "BOLD",
        ).move_to(DOWN * 1.86 + RIGHT * 1.3)
        scene = VGroup(
            memory,
            history,
            nodes,
            choice,
            bridge,
            bridge_label,
            orbit,
            orbit_nodes,
            pi,
            stationary_title,
            result,
        )
        assert_in_content(scene, "dependent path scene")
        assert_in_frame(scene, "dependent path scene")
        assert_no_overlap(stationary_title, bridge_label, "dependent path labels")
        assert_no_overlap(bridge_label, memory, "dependent path bridge vs prefix arcs")
        assert_no_overlap(choice, result, "dependent path choice vs result")
        assert_no_overlap(stationary_title, result, "dependent path stationary vs result")
        self.play(LaggedStart(*[GrowFromCenter(n) for n in nodes], lag_ratio=0.09), run_time=0.9)
        self.play(Create(arrows), run_time=0.8)
        self.play(LaggedStart(*[Create(a) for a in memory], lag_ratio=0.12), run_time=1.0)
        self.play(FadeIn(history), FadeIn(choice, shift=UP * 0.1), run_time=0.8)
        self.play(Create(bridge), FadeIn(bridge_label), run_time=0.7)
        self.play(
            Create(orbit),
            LaggedStart(*[GrowFromCenter(x) for x in orbit_nodes], lag_ratio=0.06),
            FadeIn(pi),
            FadeIn(stationary_title),
            run_time=0.9,
        )
        self.play(FadeIn(result, shift=UP * 0.08), run_time=0.6)
        self.hold_until("structured_case_study")
        self.clear_for_next()

    def structured_case_study(self) -> None:
        self.on_cue("structured_case_study")
        queue = FACTS["controlled_queue"]
        head = caption(
            "One worked case study",
            "Controlled queue · declared one-parameter refresh family.",
        )
        self.play(FadeIn(head), run_time=0.55)

        grid = coordinate_panel(width=3.3, height=1.7).move_to(LEFT * 3.9 + UP * 0.35)
        generic_count = VGroup(
            code(f"{queue['transition_coordinates']:,}", 30, IVORY),
            label("generic coordinates", 23, MUTED, "BOLD"),
        ).arrange(RIGHT, buff=0.18).next_to(grid, UP, buff=0.14)
        hit = VGroup(
            Circle(radius=0.62, color=CYAN, stroke_width=3.2),
            code("hit", 31, CYAN),
        ).move_to(RIGHT * 3.9 + UP * 0.35)
        hit[1].move_to(hit[0])
        scalar_count = VGroup(
            code("1", 30, IVORY),
            label("hit rate", 23, MUTED, "BOLD"),
        ).arrange(RIGHT, buff=0.18).next_to(hit, UP, buff=0.18)
        collapse = Arrow(
            grid.get_right() + RIGHT * 0.12,
            hit.get_left() + LEFT * 0.12,
            buff=0.05,
            color=CYAN,
            stroke_width=5,
            max_tip_length_to_length_ratio=0.20,
        )
        collapse_label = label("one parameter", 23, MUTED, "BOLD").next_to(collapse, UP, buff=0.12)
        identity = VGroup(
            label("row TV = hit-rate gap", 34, IVORY, "BOLD"),
            label("EXACT FOR EVERY PHYSICAL ROW", 22, CYAN, "BOLD"),
        ).arrange(RIGHT, buff=0.40).move_to(DOWN * 0.85)
        formulas = VGroup(
            code("p_hit(γ) = (1 + 23γ) / 24", 24),
            code("TV(row γ, row γ′) = |p_γ − p_γ′|", 24),
        ).arrange(RIGHT, buff=0.70).move_to(DOWN * 1.40)
        scope = label(
            "Declared refresh family  ·  not a membership test",
            24,
            AMBER,
            "BOLD",
        ).move_to(DOWN * 1.88)
        scene = VGroup(
            grid,
            generic_count,
            hit,
            scalar_count,
            collapse,
            collapse_label,
            identity,
            formulas,
            scope,
        )
        assert_in_content(scene, "queue case study")
        assert_in_frame(scene, "queue case study")
        assert_no_overlap(scalar_count, hit, "queue scalar label", gap=0.10)
        assert_no_overlap(grid, identity, "queue grid vs identity")
        assert_no_overlap(identity, formulas, "queue identity vs formulas")
        assert_no_overlap(formulas, scope, "queue formulas vs scope")
        assert_no_overlap(collapse_label, generic_count, "queue arrow label vs count")
        assert_no_overlap(collapse_label, scalar_count, "queue arrow label vs scalar")

        ghost = grid.copy()
        self.play(FadeIn(grid), FadeIn(generic_count), run_time=0.8)
        self.add(ghost)
        self.play(
            Transform(ghost, hit[0]),
            Create(collapse),
            FadeIn(collapse_label),
            FadeIn(scalar_count),
            run_time=1.0,
        )
        self.remove(ghost)
        self.add(hit)
        self.play(FadeIn(identity, shift=UP * 0.08), run_time=0.7)
        self.play(FadeIn(formulas, shift=UP * 0.06), run_time=0.5)
        self.play(FadeIn(scope), run_time=0.45)
        self.hold_until("proof_map")
        self.clear_for_next()

    def proof_map(self) -> None:
        self.on_cue("proof_map")
        head = caption(
            "Reusable results across the field",
            "Four checked declarations. The queue is one application.",
        )
        self.play(FadeIn(head), run_time=0.6)

        anchors = FACTS["film_anchors"]
        rows = VGroup()
        rails = VGroup()
        names = VGroup()
        for index, anchor in enumerate(anchors):
            number = code(f"{index + 1:02d}", 20, CYAN)
            title = label(anchor["label"].replace("-", "–", 1), 26, IVORY, "BOLD")
            name = code(anchor["name"], 20, MUTED)
            if name.width > 11.45:
                raise ValueError(f"Declaration name does not fit the ledger: {anchor['name']}")
            body = VGroup(title, name).arrange(DOWN, aligned_edge=LEFT, buff=0.07)
            number.next_to(body, LEFT, buff=0.28).align_to(title, UP)
            row = VGroup(number, body)
            rows.add(row)
            names.add(name)
        rows.arrange(DOWN, aligned_edge=LEFT, buff=0.22)
        rows.move_to(DOWN * 0.18)
        for index, row in enumerate(rows):
            active = index in (0, 3)
            rail = Line(
                row.get_top() + LEFT * 0.0,
                row.get_bottom(),
                color=CYAN if active else DEEP,
                stroke_width=4 if active else 2.5,
            ).next_to(row, LEFT, buff=0.22)
            rails.add(rail)
        source_stamp = label(
            f"DECLARATIONS AND FILES PINNED AT  {FACTS['short_commit']}  ·  media/formalslt-overview/facts.json",
            18,
            MUTED,
            "BOLD",
            CODE_FONT,
        ).to_edge(DOWN, buff=0.50)
        if rows.width + 0.35 > 12.6:
            raise ValueError("Proof ledger exceeds the film safe width")
        assert_in_content(rows, "proof ledger")
        assert_in_frame(VGroup(rows, rails, source_stamp), "proof map")
        assert_no_overlap(rows, source_stamp, "proof ledger vs stamp")

        self.play(
            LaggedStart(
                *[FadeIn(VGroup(row[0], row[1][0]), shift=UP * 0.1) for row in rows],
                lag_ratio=0.12,
            ),
            run_time=0.9,
        )
        self.play(
            LaggedStart(*[FadeIn(name, shift=RIGHT * 0.08) for name in names], lag_ratio=0.15),
            run_time=0.7,
        )
        self.play(Create(rails), run_time=0.8)
        self.play(FadeIn(source_stamp), run_time=0.6)
        self.hold_until("close")
        self.clear_for_next()

    def close(self) -> None:
        self.on_cue("close")
        mark = brand_mark().shift(UP * 1.62)
        final = label("FormalSLT", 70, IVORY, "BOLD")
        final.next_to(mark, DOWN, buff=0.34)
        line = label(
            "A Lean foundation for statistical learning",
            31,
            CYAN,
            "MEDIUM",
        )
        line.next_to(final, DOWN, buff=0.22)
        second_line = label(
            "and modern finite-sample inference.",
            31,
            CYAN,
            "MEDIUM",
        ).next_to(line, DOWN, buff=0.08)
        url = label("github.com/Robby955/FormalSLT", 23, MUTED, "MEDIUM", CODE_FONT)
        url.next_to(second_line, DOWN, buff=0.35)
        band = band_motif(opacity=0.18).move_to(DOWN * 2.55)
        lockup = VGroup(mark, final, line, second_line, url)
        assert_in_frame(VGroup(lockup, band), "closing lockup")
        assert_no_overlap(url, band, "closing band")
        self.play(FadeIn(mark), FadeIn(final, shift=UP * 0.12), Create(band), run_time=0.8)
        self.play(FadeIn(line), FadeIn(second_line), run_time=0.7)
        self.play(FadeIn(url), run_time=0.55)
        self.hold_until("end", clear=0.0)


class FormalSLTSocial(FormalSLTOverview):
    """Short cut with all explanatory text burned into the frame."""

    scene_starts = SOCIAL_SCENE_STARTS

    def construct(self) -> None:
        self.social_hook()
        self.social_spine()
        self.social_close()

    def social_hook(self) -> None:
        self.on_cue("social_hook")
        brand = eyebrow("FORMALSLT")
        brand.to_edge(LEFT, buff=0.72).to_edge(UP, buff=0.48)
        title = text_lines(
            ["Machine-checked", "statistical learning"],
            48,
            IVORY,
            "BOLD",
            buff=0.04,
        )
        title.to_edge(LEFT, buff=0.72).shift(UP * 0.28)
        sub = label("Built in Lean", 31, CYAN, "BOLD")
        sub.next_to(title, DOWN, aligned_edge=LEFT, buff=0.34)
        topics = VGroup(*[
            topic_card(name, active=index in (0, 3), width=2.75)
            for index, name in enumerate(
                ["VC", "Rademacher", "Chaining", "PAC-Bayes", "Anytime", "Dependent data"]
            )
        ]).arrange_in_grid(rows=3, cols=2, buff=(0.32, 0.25)).move_to(RIGHT * 3.50)
        left_column = VGroup(brand, title, sub)
        assert_horizontal_gap(left_column, topics, "social hook", gap=0.35)
        assert_in_frame(VGroup(left_column, topics), "social hook")
        self.play(
            FadeIn(brand),
            FadeIn(title, shift=UP * 0.12),
            run_time=0.7,
        )
        self.play(
            FadeIn(sub),
            LaggedStart(*[FadeIn(topic, shift=UP * 0.08) for topic in topics], lag_ratio=0.08),
            run_time=0.8,
        )
        self.hold_until("social_spine")
        self.clear_for_next()

    def social_spine(self) -> None:
        self.on_cue("social_spine")
        head = caption(
            "From classical theory to adaptive data",
            "Capacity bounds meet sequential inference.",
        )
        self.play(FadeIn(head), run_time=0.5)
        names = ["VC", "Rad", "PAC", "Seq", "Path"]
        roles = ["capacity", "complexity", "selection", "time", "dependence"]
        nodes = VGroup(*[
            VGroup(
                Circle(radius=0.55, color=CYAN if index in (0, 4) else DEEP, stroke_width=3.0),
                label(name, 30, IVORY, "BOLD"),
            )
            for index, name in enumerate(names)
        ]).arrange(RIGHT, buff=1.05).shift(UP * 0.30)
        for node in nodes:
            node[1].move_to(node[0])
        role_labels = VGroup(*[
            label(role, 23, MUTED, "BOLD").next_to(node, DOWN, buff=0.18)
            for role, node in zip(roles, nodes)
        ])
        arrows = VGroup(*[
            Arrow(
                nodes[index][0].get_right(),
                nodes[index + 1][0].get_left(),
                buff=0.10,
                color=MUTED,
                stroke_width=2.3,
                max_tip_length_to_length_ratio=0.18,
            )
            for index in range(len(nodes) - 1)
        ])
        line = label(
            "generalization  ·  selection  ·  repeated looks  ·  dependence",
            27,
            CYAN,
            "BOLD",
        ).next_to(role_labels, DOWN, buff=0.55)
        assert_in_content(VGroup(nodes, role_labels, line), "social theorem spine")
        assert_in_frame(VGroup(nodes, role_labels, line), "social theorem spine")
        for first, second in zip(role_labels[:-1], role_labels[1:]):
            assert_no_overlap(first, second, "social role labels")
        self.play(LaggedStart(*[GrowFromCenter(node) for node in nodes], lag_ratio=0.10), run_time=0.7)
        self.play(Create(arrows), FadeIn(role_labels), run_time=0.8)
        self.play(FadeIn(line, shift=UP * 0.08), run_time=0.7)
        self.hold_until("social_close")
        self.clear_for_next()

    def social_close(self) -> None:
        self.on_cue("social_close")
        mark = play_mark(radius=0.42).shift(UP * 1.55)
        title = label("FormalSLT", 70, IVORY, "BOLD")
        title.next_to(mark, DOWN, buff=0.32)
        line = label("Statistical learning theory, checked in Lean", 31, CYAN, "MEDIUM")
        line.next_to(title, DOWN, buff=0.2)
        url = label(
            "github.com/Robby955/FormalSLT",
            24,
            IVORY,
            "BOLD",
            CODE_FONT,
        ).next_to(line, DOWN, buff=0.38)
        band = band_motif(opacity=0.18).move_to(DOWN * 2.55)
        assert_no_overlap(url, band, "social closing band")
        self.play(FadeIn(mark), FadeIn(title), Create(band), run_time=0.75)
        self.play(FadeIn(line), run_time=0.55)
        self.play(FadeIn(url), run_time=0.45)
        self.hold_until("end", clear=0.0)


class FormalSLTPoster(Scene):
    """Stable click-to-play poster; independent of scene timing and counts."""

    def construct(self) -> None:
        brand = label("FORMALSLT", 29, CYAN, "BOLD")
        title = text_lines(
            ["Machine-checked", "statistical learning", "in Lean."],
            50,
            IVORY,
            "BOLD",
            buff=0.04,
        )
        body = text_lines(
            [
                "Classical generalization",
                "through adaptive data",
            ],
            31,
            MUTED,
            "MEDIUM",
            buff=0.08,
        )
        play = play_mark(radius=0.5)
        watch = label("WATCH THE FILM", 28, IVORY, "BOLD", CODE_FONT)
        cta = VGroup(play, watch).arrange(RIGHT, buff=0.3)
        left_column = VGroup(brand, title, body, cta).arrange(
            DOWN,
            aligned_edge=LEFT,
            buff=0.42,
        )
        left_column.to_edge(LEFT, buff=0.72).shift(UP * 0.18)

        topics = VGroup(*[
            topic_card(name, active=index in (0, 3), width=2.85)
            for index, name in enumerate(
                ["VC theory", "Rademacher", "Chaining", "PAC-Bayes", "Anytime", "Dependent data"]
            )
        ]).arrange_in_grid(rows=3, cols=2, buff=(0.32, 0.25)).move_to(RIGHT * 3.50)
        spine = Line(
            [topics.get_center()[0], topics.get_top()[1] + 0.18, 0],
            [topics.get_center()[0], topics.get_bottom()[1] - 0.18, 0],
            color=CYAN,
            stroke_width=3,
            stroke_opacity=0.35,
        )
        right_column = VGroup(spine, topics)

        assert_horizontal_gap(left_column, right_column, "poster", gap=0.42)
        assert_in_frame(left_column, "poster left column")
        assert_in_frame(right_column, "poster right column")

        self.add(left_column, right_column)
