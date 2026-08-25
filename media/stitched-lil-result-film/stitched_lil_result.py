from __future__ import annotations

import json
from pathlib import Path

import numpy as np
from boundary_model import (
    ILLUSTRATIVE_B,
    ILLUSTRATIVE_DELTA,
    ILLUSTRATIVE_SIGMA2,
    fixed_tilt_boundary_value,
    log_time_x,
    stitched_width_value,
)
from manim import (
    AnimationGroup,
    Create,
    DashedLine,
    Dot,
    DOWN,
    FadeIn,
    FadeOut,
    LEFT,
    Line,
    MathTex,
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
)


PACKAGE_DIR = Path(__file__).resolve().parent
FACTS = json.loads((PACKAGE_DIR / "facts.json").read_text(encoding="utf-8"))
CLAIMS = json.loads(
    (PACKAGE_DIR / "claim-receipt.json").read_text(encoding="utf-8")
)
FILM = json.loads((PACKAGE_DIR / "film_config.json").read_text(encoding="utf-8"))

if not (
    FACTS["commit"]
    == CLAIMS["theorem_source_commit"]
    == FILM["source_commit"]
):
    raise ValueError("film timing and mathematical fact receipts bind different commits")
DISPLAY_MATH = CLAIMS["display_math"]
ILLUSTRATIVE_PARAMETER_TEX = (
    rf"\sigma^2={ILLUSTRATIVE_SIGMA2:.2f},\quad "
    rf"b={ILLUSTRATIVE_B:.2f},\quad\delta={ILLUSTRATIVE_DELTA:.2f}"
)

PALETTE = FILM["palette"]
BG = PALETTE["background"]
IVORY = PALETTE["ivory"]
CYAN = PALETTE["cyan"]
MUTED = PALETTE["muted"]
DEEP = PALETTE["deep"]
AMBER = PALETTE["amber"]
RED = PALETTE["red"]
SOFT_CYAN = "#9FD9D5"

DISPLAY_FONT = "Avenir Next"
CODE_FONT = "Menlo"

FRAME_LEFT = -6.75
FRAME_RIGHT = 6.75
FRAME_TOP = 3.72
FRAME_BOTTOM = -3.72
CONTENT_TOP = 1.68
CONTENT_BOTTOM = -2.05

TITLE_SIZE = 46
DETAIL_SIZE = 29
BODY_SIZE = 30
LABEL_SIZE = 28
SMALL_SIZE = 23
FORMULA_SIZE = 27

SOCIAL_FRAME_LEFT = -2.95
SOCIAL_FRAME_RIGHT = 2.95
SOCIAL_FRAME_TOP = 3.72
SOCIAL_FRAME_BOTTOM = -3.72
SOCIAL_TITLE_SIZE = 39
SOCIAL_BODY_SIZE = 25
SOCIAL_FORMULA_SIZE = 30

CLEAR_RUN_TIME = 0.55
SCENE_CLOCK_TOLERANCE = 0.05
MIN_READING_HOLD = 0.65

SCENE_STARTS = {scene["id"]: float(scene["start"]) for scene in FILM["scenes"]}
SCENE_STARTS["end"] = float(FILM["duration_seconds"])
SCENE_COPY = {scene["id"]: scene for scene in FILM["scenes"]}
SOCIAL_FILM = FILM["social"]
SOCIAL_SCENE_STARTS = {
    scene["id"]: float(scene["start"]) for scene in SOCIAL_FILM["scenes"]
}
SOCIAL_SCENE_STARTS["end"] = float(SOCIAL_FILM["duration_seconds"])
SOCIAL_SCENE_COPY = {scene["id"]: scene for scene in SOCIAL_FILM["scenes"]}

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


def math_display(
    latex: str,
    size: float = 34,
    color: str = SOFT_CYAN,
    *,
    max_width: float = 11.85,
) -> MathTex:
    """Typeset display mathematics with TeX and reject unreadable overflow."""
    item = MathTex(latex, font_size=size, color=color)
    if item.width > max_width:
        raise ValueError(
            f"MathTex display exceeds safe width ({item.width:.3f} > {max_width:.3f}); "
            "split the equation instead of shrinking it"
        )
    return item


def caption(scene_id: str) -> VGroup:
    scene = SCENE_COPY[scene_id]
    heading = text_lines(
        wrap_copy(scene["title"], 40, 11.85, "BOLD"),
        40,
        IVORY,
        "BOLD",
        buff=0.04,
    )
    detail = text_lines(
        wrap_copy(scene["detail"], 22, 11.85),
        22,
        MUTED,
        buff=0.04,
    )
    group = VGroup(heading, detail).arrange(DOWN, aligned_edge=LEFT, buff=0.16)
    group.to_edge(LEFT, buff=0.72).to_edge(UP, buff=0.54)
    if group.get_bottom()[1] < 1.78:
        raise ValueError(f"{scene_id} caption leaves insufficient content clearance")
    return group


def text_lines(
    lines: list[str],
    size: float,
    color: str = IVORY,
    weight: str = "MEDIUM",
    font: str = DISPLAY_FONT,
    buff: float = 0.09,
) -> VGroup:
    group = VGroup(
        *[label(line, size, color, weight, font) for line in lines]
    ).arrange(DOWN, aligned_edge=LEFT, buff=buff)
    if group.width > 12.0:
        raise ValueError("text block exceeds the 12-unit safe width")
    return group


def wrap_copy(
    text: str,
    size: float,
    max_width: float,
    weight: str = "MEDIUM",
) -> list[str]:
    """Wrap human copy by measured font width; never shrink a full sentence."""
    words = text.split()
    if not words:
        raise ValueError("cannot wrap empty copy")
    lines: list[str] = []
    current = words[0]
    for word in words[1:]:
        candidate = f"{current} {word}"
        if label(candidate, size, IVORY, weight).width <= max_width:
            current = candidate
        else:
            lines.append(current)
            current = word
    lines.append(current)
    if any(label(line, size, IVORY, weight).width > max_width for line in lines):
        raise ValueError(f"one copy token exceeds the safe width: {text!r}")
    return lines


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
            f"top={item.get_top()[1]:.3f}, bottom={item.get_bottom()[1]:.3f}"
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


def assert_contains(container, item, name: str, margin: float = 0.06) -> None:
    if (
        item.get_left()[0] < container.get_left()[0] + margin
        or item.get_right()[0] > container.get_right()[0] - margin
        or item.get_top()[1] > container.get_top()[1] - margin
        or item.get_bottom()[1] < container.get_bottom()[1] + margin
    ):
        raise ValueError(f"{name} is not contained by its panel")


def path_curve(points: list[np.ndarray], color: str, width: float = 4.0) -> VMobject:
    curve = VMobject(
        stroke_color=color,
        stroke_width=width,
        fill_color=color,
        fill_opacity=0,
    )
    curve.set_points_smoothly(points)
    curve.set_fill(opacity=0)
    return curve


def polyline_curve(
    points: list[np.ndarray],
    color: str,
    width: float = 4.0,
) -> VMobject:
    """Join evaluated boundary points without spline overshoot."""
    curve = VMobject(
        stroke_color=color,
        stroke_width=width,
        fill_color=color,
        fill_opacity=0,
    )
    curve.set_points_as_corners(points)
    curve.set_fill(opacity=0)
    return curve


STITCHED_EPOCHS = ((4, 16), (16, 64), (64, 256), (256, 1024))


def stitched_envelope_segments(
    x_left: float,
    x_right: float,
    *,
    center_y: float,
    scale: float,
    width: float,
) -> tuple[VGroup, VGroup]:
    """Draw exact W_n values at integer n, split at every epoch jump."""
    upper = VGroup()
    lower = VGroup()
    for start, end in STITCHED_EPOCHS:
        upper_points = [
            np.array(
                [
                    log_time_x(float(n), x_left, x_right),
                    center_y + scale * stitched_width_value(float(n)),
                    0,
                ]
            )
            for n in range(start, end)
        ]
        lower_points = [
            np.array([point[0], 2.0 * center_y - point[1], 0])
            for point in upper_points
        ]
        upper.add(polyline_curve(upper_points, CYAN, width))
        lower.add(polyline_curve(lower_points, CYAN, width))
    return upper, lower


def math_chip(
    latex: str,
    *,
    width: float | None = None,
    color: str = SOFT_CYAN,
    size: float = FORMULA_SIZE,
) -> VGroup:
    copy = math_display(latex, size, color, max_width=11.85)
    box_width = copy.width + 0.48 if width is None else width
    if copy.width > box_width - 0.30:
        raise ValueError(f"formula does not fit chip: {latex!r}")
    box = RoundedRectangle(
        width=box_width,
        height=max(0.72, copy.height + 0.28),
        corner_radius=0.11,
        color=DEEP,
        stroke_width=1.8,
        fill_color="#0B1625",
        fill_opacity=0.97,
    )
    copy.move_to(box)
    return VGroup(box, copy)


def prose_chip(
    text: str,
    *,
    width: float,
    color: str = IVORY,
    size: float = 25,
) -> VGroup:
    copy = label(text, size, color, "BOLD")
    if copy.width > width - 0.30:
        raise ValueError(f"prose does not fit chip: {text!r}")
    box = RoundedRectangle(
        width=width,
        height=max(0.72, copy.height + 0.28),
        corner_radius=0.11,
        color=DEEP,
        stroke_width=1.8,
        fill_color="#0B1625",
        fill_opacity=0.97,
    )
    copy.move_to(box)
    return VGroup(box, copy)


def assumption_card(latex: str, plain: str, math_size: float = 31) -> VGroup:
    box = RoundedRectangle(
        width=5.3,
        height=1.18,
        corner_radius=0.12,
        color=DEEP,
        stroke_width=2.0,
        fill_color="#0B1625",
        fill_opacity=0.98,
    )
    mathematical = math_display(latex, math_size, CYAN, max_width=4.75)
    description = label(plain, 23, MUTED, "MEDIUM")
    copy = VGroup(mathematical, description).arrange(
        DOWN,
        aligned_edge=LEFT,
        buff=0.08,
    )
    if copy.width > box.width - 0.42:
        raise ValueError(f"assumption copy does not fit: {latex!r}")
    copy.move_to(box)
    return VGroup(box, copy)


def source_stamp() -> Text:
    return label(
        f"SOURCE  {FACTS['short_commit']}",
        18,
        MUTED,
        "BOLD",
        CODE_FONT,
    )


def assert_social_geometry() -> None:
    expected_width, expected_height = SOCIAL_FILM["frame"]
    expected_pixels = SOCIAL_FILM["resolution"]
    if (
        abs(float(config.frame_width) - float(expected_width)) > 0.01
        or abs(float(config.frame_height) - float(expected_height)) > 0.01
        or abs(
            float(config.pixel_width) / float(config.pixel_height)
            - float(expected_pixels[0]) / float(expected_pixels[1])
        ) > 0.001
    ):
        raise ValueError(
            "StitchedLILResultSocial requires the native 4:5 configuration: "
            f"frame={config.frame_width}x{config.frame_height}, "
            f"pixels={config.pixel_width}x{config.pixel_height}"
        )


def assert_in_social_frame(item, name: str, margin: float = 0.08) -> None:
    if (
        item.get_left()[0] < SOCIAL_FRAME_LEFT + margin
        or item.get_right()[0] > SOCIAL_FRAME_RIGHT - margin
        or item.get_top()[1] > SOCIAL_FRAME_TOP - margin
        or item.get_bottom()[1] < SOCIAL_FRAME_BOTTOM + margin
    ):
        raise ValueError(
            f"{name} leaves the social-safe frame: "
            f"left={item.get_left()[0]:.3f}, right={item.get_right()[0]:.3f}, "
            f"top={item.get_top()[1]:.3f}, bottom={item.get_bottom()[1]:.3f}"
        )


def social_header(scene_id: str) -> VGroup:
    scene = SOCIAL_SCENE_COPY[scene_id]
    heading = text_lines(
        wrap_copy(scene["title"], 30, 5.35, "BOLD"),
        30,
        IVORY,
        "BOLD",
        DISPLAY_FONT,
        buff=0.04,
    )
    detail = text_lines(
        wrap_copy(scene["detail"], 16, 5.35),
        16,
        MUTED,
        "MEDIUM",
        DISPLAY_FONT,
        buff=0.03,
    )
    header_gap = 0.12 if scene_id == "social_result" else 0.18
    group = VGroup(heading, detail).arrange(
        DOWN,
        aligned_edge=LEFT,
        buff=header_gap,
    )
    group.to_edge(LEFT, buff=0.35).to_edge(UP, buff=0.40)
    if group.get_bottom()[1] < 1.98:
        raise ValueError(f"{scene_id} social header leaves insufficient content clearance")
    assert_in_social_frame(group, f"{scene_id} header")
    return group


def social_assumption_card(
    latex: str,
    plain: str,
    math_size: float = 27,
) -> VGroup:
    box = RoundedRectangle(
        width=5.35,
        height=0.88,
        corner_radius=0.10,
        color=DEEP,
        stroke_width=1.8,
        fill_color="#0B1625",
        fill_opacity=0.98,
    )
    formula = math_display(latex, math_size, CYAN, max_width=3.0)
    explanation = label(plain, 19, MUTED, "MEDIUM")
    copy = VGroup(formula, explanation).arrange(RIGHT, buff=0.24)
    if copy.width > box.width - 0.30:
        raise ValueError(f"social assumption does not fit: {latex!r}")
    copy.move_to(box)
    return VGroup(box, copy)


class StitchedLILResultFilm(Scene):
    def construct(self) -> None:
        self.hook()
        self.model()
        self.epochs()
        self.allocation()
        self.tilts()
        self.stitch()
        self.result()

    def on_cue(self, scene_id: str) -> None:
        expected = SCENE_STARTS[scene_id]
        actual = float(self.renderer.time)
        if abs(actual - expected) > SCENE_CLOCK_TOLERANCE:
            raise ValueError(
                f"scene {scene_id!r} starts at {actual:.3f}s, expected "
                f"{expected:.3f}s"
            )

    def hold_until(self, next_scene: str, *, clear: bool = True) -> None:
        clear_time = CLEAR_RUN_TIME if clear else 0.0
        target = SCENE_STARTS[next_scene] - clear_time
        remaining = target - float(self.renderer.time)
        if remaining < MIN_READING_HOLD:
            raise ValueError(
                f"only {remaining:.3f}s reading hold remains before {next_scene!r}"
            )
        self.wait(remaining)
        if clear:
            targets = list(self.mobjects)
            if targets:
                self.play(
                    AnimationGroup(
                        *[FadeOut(item, shift=UP * 0.06) for item in targets],
                        lag_ratio=0,
                    ),
                    run_time=CLEAR_RUN_TIME,
                )

    def hook(self) -> None:
        self.on_cue("hook")
        head = caption("hook")
        stamp = source_stamp().to_edge(DOWN, buff=0.42).to_edge(RIGHT, buff=0.72)

        x_left, x_right, axis_y = -5.75, 5.75, -0.45
        axis = Line(
            np.array([x_left, axis_y, 0]),
            np.array([x_right, axis_y, 0]),
            color=DEEP,
            stroke_width=3.0,
        )
        xs = np.linspace(x_left, x_right, 48)
        trace = path_curve(
            [
                np.array(
                    [
                        x,
                        axis_y
                        + 0.50 * np.sin(1.65 * x + 0.6) / np.sqrt(1.0 + 0.16 * (x - x_left)),
                        0,
                    ]
                )
                for x in xs
            ],
            IVORY,
            3.0,
        )
        slice_x = -0.65
        fixed_slice = Line(
            np.array([slice_x, axis_y - 0.72, 0]),
            np.array([slice_x, axis_y + 0.72, 0]),
            color=CYAN,
            stroke_width=7.0,
        )
        cap_top = Line(
            np.array([slice_x - 0.18, axis_y + 0.72, 0]),
            np.array([slice_x + 0.18, axis_y + 0.72, 0]),
            color=CYAN,
            stroke_width=5.0,
        )
        cap_bottom = cap_top.copy().shift(DOWN * 1.44)
        fixed_label = label("one fixed look", 23, CYAN, "BOLD").next_to(
            fixed_slice, DOWN, buff=0.22
        )
        question = label(
            "What remains valid after the next sample arrives?",
            31,
            IVORY,
            "MEDIUM",
        ).move_to(DOWN * 2.18)

        content = VGroup(axis, trace, fixed_slice, cap_top, cap_bottom, fixed_label)
        assert_in_content(content, "hook plot")
        assert_in_frame(VGroup(head, content, question, stamp), "hook")
        assert_no_overlap(content, question, "hook plot and question")

        self.play(FadeIn(head), FadeIn(stamp), run_time=0.65)
        self.play(Create(axis), Create(trace), run_time=1.65)
        self.play(
            Create(fixed_slice),
            Create(cap_top),
            Create(cap_bottom),
            FadeIn(fixed_label),
            run_time=0.75,
        )
        self.play(FadeIn(question, shift=UP * 0.08), run_time=0.55)
        self.hold_until("model")

    def model(self) -> None:
        self.on_cue("model")
        head = caption("model")
        spine_math = math_display(r"X_0,\ X_1,\ X_2,\ldots", 38, IVORY)
        spine_plain = label(
            "μ is a probability measure · increments are measurable and integrable",
            21,
            MUTED,
        )
        spine = VGroup(spine_math, spine_plain).arrange(DOWN, buff=0.09).move_to(
            UP * 1.25
        )
        cards = VGroup(
            assumption_card(
                r"X_k\text{ is }\mathcal F_{k+1}\text{-strongly measurable}",
                "one-step reveal",
                22,
            ),
            assumption_card(r"\lvert X_k\rvert \le b", "bounded a.e."),
            assumption_card(
                r"\mathbb E[X_k\mid\mathcal F_k]=0",
                "conditionally centered a.e.",
            ),
            assumption_card(
                r"\mathbb E[X_k^2\mid\mathcal F_k]\le\sigma^2",
                "second moment bounded a.e.",
            ),
        ).arrange_in_grid(rows=2, cols=2, buff=(0.45, 0.34))
        cards.move_to(DOWN * 0.60)
        scope = math_display(
            r"0<\delta\le 1\,,\qquad b>0\,,\qquad \sigma^2>0",
            31,
            AMBER,
        ).move_to(DOWN * 2.42)

        assert_in_content(VGroup(spine, cards), "model content")
        assert_in_frame(VGroup(head, spine, cards, scope), "model")
        assert_no_overlap(spine, cards, "model spine and cards", gap=0.10)
        assert_no_overlap(cards, scope, "model cards and scope")

        self.play(FadeIn(head), FadeIn(spine), run_time=0.65)
        self.play(
            AnimationGroup(
                *[FadeIn(card, shift=UP * 0.08) for card in cards],
                lag_ratio=0.12,
            ),
            run_time=1.55,
        )
        self.play(FadeIn(scope), run_time=0.5)
        self.hold_until("epochs")

    def epochs(self) -> None:
        self.on_cue("epochs")
        head = caption("epochs")
        floor_formula = math_display(r"N_j=4^{j+1}", 39, AMBER).move_to(UP * 1.15)
        axis_y = -0.55
        boundaries = [-5.60, -2.80, 0.00, 2.80, 5.60]
        interval_text = FACTS["epochs"]["examples"]
        if len(interval_text) != 4:
            raise ValueError("the epoch scene requires exactly four checked examples")
        segments = VGroup()
        boundary_marks = VGroup()
        interval_labels = VGroup()
        epoch_labels = VGroup()
        for index in range(4):
            left, right = boundaries[index], boundaries[index + 1]
            box = Rectangle(
                width=right - left - 0.06,
                height=0.92,
                color=CYAN if index % 2 == 0 else SOFT_CYAN,
                stroke_width=2.0,
                fill_color="#10233A",
                fill_opacity=0.76 if index % 2 == 0 else 0.52,
            ).move_to(np.array([(left + right) / 2, axis_y, 0]))
            segments.add(box)
            boundary_marks.add(Dot(np.array([left, axis_y, 0]), radius=0.07, color=AMBER))
            interval_labels.add(
                math_display(
                    interval_text[index].replace("[", r"[").replace(")", r")"),
                    28,
                    IVORY,
                ).move_to(
                    np.array([(left + right) / 2, axis_y, 0])
                )
            )
            epoch_labels.add(
                math_display(rf"j={index}", 27, AMBER).move_to(
                    np.array([(left + right) / 2, axis_y + 0.78, 0])
                )
            )
        boundary_marks.add(Dot(np.array([boundaries[-1], axis_y, 0]), radius=0.07, color=AMBER))
        selector = label(
            "The checked selector places every eligible sample size inside its epoch.",
            27,
            IVORY,
        ).move_to(DOWN * 1.78)

        content = VGroup(
            floor_formula,
            segments,
            boundary_marks,
            interval_labels,
            epoch_labels,
            selector,
        )
        assert_in_content(content, "epochs content")
        assert_in_frame(VGroup(head, content), "epochs")

        self.play(FadeIn(head), FadeIn(floor_formula), run_time=0.65)
        self.play(
            AnimationGroup(
                *[FadeIn(segment) for segment in segments],
                lag_ratio=0.14,
            ),
            AnimationGroup(
                *[FadeIn(item) for item in boundary_marks],
                lag_ratio=0.10,
            ),
            run_time=1.35,
        )
        self.play(FadeIn(interval_labels), FadeIn(epoch_labels), run_time=0.60)
        self.play(FadeIn(selector, shift=UP * 0.06), run_time=0.45)
        self.hold_until("allocation")

    def allocation(self) -> None:
        self.on_cue("allocation")
        head = caption("allocation")
        weight_formula = math_display(
            r"w_j=\frac{1}{(j+1)(j+2)}",
            39,
            AMBER,
        ).move_to(UP * 1.20)
        weights = VGroup(
            math_chip(r"\frac12", width=1.65, color=AMBER, size=32),
            math_chip(r"\frac16", width=1.65, color=AMBER, size=32),
            math_chip(r"\frac1{12}", width=1.65, color=AMBER, size=32),
            math_chip(r"\frac1{20}", width=1.65, color=AMBER, size=32),
            math_chip(r"\cdots", width=1.65, color=MUTED, size=32),
        ).arrange(RIGHT, buff=0.22).move_to(UP * 0.15)
        telescope = math_display(
            r"w_j=\frac1{j+1}-\frac1{j+2}",
            38,
            SOFT_CYAN,
        ).move_to(DOWN * 0.90)
        total = math_chip(
            r"\sum_{j=0}^{\infty} w_j=1",
            width=4.15,
            color=CYAN,
            size=30,
        ).move_to(DOWN * 2.10)

        content = VGroup(weight_formula, weights, telescope, total)
        assert_in_frame(VGroup(head, content), "allocation")
        assert_no_overlap(weight_formula, weights, "allocation formula and weights", gap=0.10)
        assert_no_overlap(weights, telescope, "allocation weights and telescope", gap=0.10)
        assert_no_overlap(telescope, total, "allocation formulas", gap=0.16)

        self.play(FadeIn(head), FadeIn(weight_formula), run_time=0.65)
        self.play(
            AnimationGroup(
                *[FadeIn(item, shift=UP * 0.05) for item in weights],
                lag_ratio=0.16,
            ),
            run_time=1.25,
        )
        self.play(FadeIn(telescope), run_time=0.55)
        telescope_copy = telescope.copy()
        self.add(telescope_copy)
        self.play(Transform(telescope_copy, total), run_time=0.75)
        self.remove(telescope_copy)
        self.add(total)
        self.hold_until("tilts")

    def tilts(self) -> None:
        self.on_cue("tilts")
        head = caption("tilts")
        axis_y = -0.72
        x_left, x_right = -5.45, 5.47
        axis = Line(
            np.array([x_left, axis_y, 0]),
            np.array([x_right, axis_y, 0]),
            color=DEEP,
            stroke_width=3.0,
        )
        tick_values = (4, 16, 64, 256, 1024)
        boundaries = [log_time_x(float(n), x_left, x_right) for n in tick_values]
        tick_marks = VGroup()
        tick_labels = VGroup()
        for n, x in zip(tick_values, boundaries, strict=True):
            tick_marks.add(
                Line(
                    np.array([x, axis_y - 0.08, 0]),
                    np.array([x, axis_y + 0.08, 0]),
                    color=DEEP,
                    stroke_width=2.0,
                )
            )
            tick_labels.add(
                math_display(str(n), 20, MUTED).move_to(np.array([x, axis_y - 0.28, 0]))
            )
        axis_label = VGroup(
            math_display(r"n", 24, MUTED),
            label("log scale", 17, MUTED),
        ).arrange(RIGHT, buff=0.10).move_to(np.array([4.95, axis_y - 0.55, 0]))
        faint_curves = VGroup()
        active_segments = VGroup()
        floor_dots = VGroup()
        for index in range(4):
            floor = float(4 ** (index + 1))
            horizon = float(4 ** (index + 2))
            tail_n = np.geomspace(floor, 1024.0, 72)
            tail_points = [
                np.array(
                    [
                        log_time_x(float(n), x_left, x_right),
                        axis_y + 2.20 * fixed_tilt_boundary_value(index, float(n)),
                        0,
                    ]
                )
                for n in tail_n
            ]
            faint_curve = polyline_curve(tail_points, SOFT_CYAN, 2.0)
            faint_curve.set_stroke(opacity=0.22)
            faint_curves.add(faint_curve)
            active_n = np.geomspace(floor, horizon, 36, endpoint=False)
            active_points = [
                np.array(
                    [
                        log_time_x(float(n), x_left, x_right),
                        axis_y + 2.20 * fixed_tilt_boundary_value(index, float(n)),
                        0,
                    ]
                )
                for n in active_n
            ]
            active_segments.add(polyline_curve(active_points, CYAN, 5.0))
            floor_dots.add(
                Dot(
                    active_points[0],
                    radius=0.075,
                    color=AMBER,
                )
            )
        boundary_formula = math_display(
            r"g_{\lambda_j}(n)="
            r"\frac{\operatorname{subGammaCgf}(\sigma^2,b,\lambda_j)}{\lambda_j}"
            r"+\frac{B_j}{n\lambda_j}",
            21,
            SOFT_CYAN,
        )
        boundary_parameters = math_display(
            ILLUSTRATIVE_PARAMETER_TEX,
            20,
            MUTED,
        )
        boundary_shape = VGroup(boundary_formula, boundary_parameters).arrange(
            DOWN, buff=0.07
        ).move_to(UP * 1.42 + LEFT * 2.52)

        epoch_index = math_display(
            DISPLAY_MATH["selector"],
            27,
            MUTED,
        )
        budget_formula = math_display(
            DISPLAY_MATH["budget"],
            29,
            AMBER,
        )
        budget = VGroup(epoch_index, budget_formula).arrange(
            DOWN, aligned_edge=LEFT, buff=0.10
        ).move_to(UP * 1.05 + RIGHT * 3.55)
        precommit = prose_chip(
            "one fixed tilt per epoch",
            width=4.55,
            color=IVORY,
            size=25,
        ).move_to(DOWN * 1.60 + LEFT * 2.55)
        receipt = math_display(
            r"\delta=\tfrac12,\ j=0\quad\Longrightarrow\quad B_0=\log 8",
            28,
            MUTED,
        ).move_to(
            DOWN * 1.60 + RIGHT * 2.85
        )

        plot = VGroup(
            axis,
            tick_marks,
            tick_labels,
            axis_label,
            faint_curves,
            active_segments,
            floor_dots,
        )
        assert_in_frame(VGroup(head, plot, budget, boundary_shape, precommit, receipt), "tilts")
        assert_no_overlap(boundary_shape, plot, "tilt formula and plot", gap=0.10)
        assert_no_overlap(budget, plot, "tilt budget and plot", gap=0.03)
        assert_no_overlap(precommit, receipt, "tilt footer", gap=0.18)

        self.play(FadeIn(head), FadeIn(budget), FadeIn(boundary_shape), run_time=0.70)
        self.play(
            Create(axis),
            FadeIn(tick_marks),
            FadeIn(tick_labels),
            FadeIn(axis_label),
            Create(faint_curves),
            run_time=1.00,
        )
        self.play(
            AnimationGroup(
                *[Create(segment) for segment in active_segments],
                lag_ratio=0.16,
            ),
            AnimationGroup(
                *[FadeIn(dot) for dot in floor_dots],
                lag_ratio=0.16,
            ),
            run_time=1.40,
        )
        self.play(FadeIn(precommit), FadeIn(receipt), run_time=0.55)
        self.hold_until("stitch")

    def stitch(self) -> None:
        self.on_cue("stitch")
        head = caption("stitch")
        x_left, x_right = -5.55, 3.45
        upper, lower = stitched_envelope_segments(
            x_left,
            x_right,
            center_y=-0.12,
            scale=1.08,
            width=4.6,
        )
        n_values = np.geomspace(4.0, 1023.0, 128)
        trace_points = [
            np.array(
                [
                    log_time_x(float(n), x_left, x_right),
                    -0.12
                    + 0.46
                    * stitched_width_value(float(n))
                    * np.sin(2.10 * np.log(float(n))),
                    0,
                ]
            )
            for n in n_values
        ]
        trace = path_curve(trace_points, IVORY, 2.8)
        epoch_cuts = VGroup(
            *[
                DashedLine(
                    np.array([x, -1.65, 0]),
                    np.array([x, 1.65, 0]),
                    color=DEEP,
                    stroke_width=1.5,
                    dash_length=0.09,
                )
                for x in (
                    log_time_x(16.0, x_left, x_right),
                    log_time_x(64.0, x_left, x_right),
                    log_time_x(256.0, x_left, x_right),
                )
            ]
        )
        plot = VGroup(upper, lower, trace, epoch_cuts).shift(LEFT * 1.05 + DOWN * 0.25)
        plot_note = VGroup(
            label("CHECKED INTEGER VALUES", 17, CYAN, "BOLD"),
            math_display(
                ILLUSTRATIVE_PARAMETER_TEX,
                22,
                MUTED,
            ),
            label("PATH ILLUSTRATIVE", 17, MUTED, "BOLD"),
        ).arrange(RIGHT, buff=0.16).move_to(UP * 1.48 + LEFT * 1.10)

        ledger_box = RoundedRectangle(
            width=3.90,
            height=2.65,
            corner_radius=0.14,
            color=DEEP,
            stroke_width=2.0,
            fill_color="#0B1625",
            fill_opacity=0.98,
        ).move_to(RIGHT * 4.66 + DOWN * 0.25)
        ledger = math_display(
            r"\delta w_0+\delta w_1+\delta w_2+\cdots=\delta",
            29,
            AMBER,
        ).move_to(ledger_box)
        failure = math_chip(
            DISPLAY_MATH["failure_mass"],
            width=4.10,
            color=RED,
            size=33,
        ).move_to(DOWN * 2.08 + RIGHT * 3.88)
        scope = text_lines(
            ["Countable subadditivity.", "Not a countable e-process."],
            24,
            IVORY,
            "BOLD",
            DISPLAY_FONT,
            buff=0.04,
        ).move_to(DOWN * 2.10 + LEFT * 3.25)

        assert_in_content(VGroup(plot, plot_note, ledger_box, ledger), "stitch content")
        assert_in_frame(VGroup(head, plot, plot_note, ledger_box, ledger, failure, scope), "stitch")
        assert_contains(ledger_box, ledger, "stitch ledger", margin=0.18)
        assert_no_overlap(plot, ledger_box, "stitch plot and ledger", gap=0.18)
        assert_no_overlap(ledger_box, failure, "stitch ledger and failure", gap=0.12)
        assert_no_overlap(scope, failure, "stitch scope and failure", gap=0.18)

        self.play(FadeIn(head), FadeIn(epoch_cuts), FadeIn(plot_note), run_time=0.65)
        self.play(Create(trace), run_time=1.15)
        self.play(
            AnimationGroup(*[Create(segment) for segment in upper], lag_ratio=0.05),
            AnimationGroup(*[Create(segment) for segment in lower], lag_ratio=0.05),
            run_time=1.55,
        )
        self.play(FadeIn(ledger_box), FadeIn(ledger), run_time=0.60)
        self.play(FadeIn(failure), FadeIn(scope), run_time=0.55)
        self.hold_until("result")

    def result(self) -> None:
        self.on_cue("result")
        head = caption("result")
        budget = math_display(
            DISPLAY_MATH["budget"],
            27,
            AMBER,
        )
        width = math_display(
            DISPLAY_MATH["width"],
            29,
            SOFT_CYAN,
        )
        event_condition = math_display(
            DISPLAY_MATH["event_condition"],
            24,
            IVORY,
        )
        failure = math_display(DISPLAY_MATH["failure_mass"], 27, RED)
        event_bound = math_display(
            DISPLAY_MATH["event_bound"],
            26,
            IVORY,
        )
        event_intro = VGroup(failure, event_condition).arrange(RIGHT, buff=0.55)
        epoch_index = math_display(
            DISPLAY_MATH["selector"],
            24,
            MUTED,
        )
        theorem_card = VGroup(epoch_index, budget, width, event_intro, event_bound).arrange(
            DOWN,
            aligned_edge=LEFT,
            buff=0.10,
        )
        theorem_box = RoundedRectangle(
            width=11.80,
            height=3.40,
            corner_radius=0.15,
            color=CYAN,
            stroke_width=2.2,
            fill_color="#0B1625",
            fill_opacity=0.98,
        )
        if theorem_card.width > theorem_box.width - 0.55:
            raise ValueError("result formula card is too wide")
        theorem_card.move_to(theorem_box)
        result_group = VGroup(theorem_box, theorem_card).move_to(DOWN * 0.05)

        module_name = code("AnytimeValid.PolynomialStitchedLIL", 20, MUTED)
        theorem_name = code(FACTS["result"]["theorem"], 20, MUTED)
        receipt = VGroup(module_name, theorem_name).arrange(
            DOWN,
            aligned_edge=LEFT,
            buff=0.06,
        ).move_to(DOWN * 2.25 + LEFT * 2.72)
        commit = code(f"SOURCE {FACTS['short_commit']}", 20, CYAN).move_to(
            DOWN * 2.25 + RIGHT * 4.85
        )
        boundary = label(
            "Not the LIL law. No sharp-constant claim. Not itself an e-process.",
            24,
            AMBER,
            "BOLD",
        ).move_to(DOWN * 3.05)

        assert_in_content(result_group, "result theorem card")
        assert_in_frame(VGroup(head, result_group, receipt, commit, boundary), "result")
        assert_contains(theorem_box, theorem_card, "result theorem card", margin=0.12)
        assert_no_overlap(result_group, receipt, "result formula and receipt", gap=0.18)
        assert_no_overlap(result_group, commit, "result formula and source", gap=0.18)
        assert_no_overlap(receipt, boundary, "result receipt and boundary", gap=0.14)

        self.play(FadeIn(head), run_time=0.60)
        self.play(FadeIn(theorem_box), FadeIn(theorem_card), run_time=1.10)
        self.play(FadeIn(receipt), FadeIn(commit), run_time=0.60)
        self.play(FadeIn(boundary), run_time=0.45)
        self.hold_until("end", clear=False)
        self.on_cue("end")


class StitchedLILResultPoster(Scene):
    def construct(self) -> None:
        title = text_lines(
            ["One checked event.", "Every sample size from four onward."],
            48,
            IVORY,
            "BOLD",
            DISPLAY_FONT,
            buff=0.05,
        ).move_to(UP * 2.78)
        subtitle = label(
            "A machine-checked log-log confidence sequence in Lean.",
            32,
            MUTED,
        ).next_to(title, DOWN, buff=0.18)

        definitions = VGroup(
            math_display(DISPLAY_MATH["selector"], 22, MUTED),
            math_display(DISPLAY_MATH["budget"], 25, AMBER),
            math_display(DISPLAY_MATH["width"], 27, SOFT_CYAN),
        ).arrange(DOWN, buff=0.08).move_to(UP * 0.52)
        failure = math_display(DISPLAY_MATH["failure_mass"], 34, RED)
        event = math_display(DISPLAY_MATH["event_conclusion"], 31, IVORY)
        guarantee_copy = VGroup(failure, event).arrange(DOWN, buff=0.15)
        guarantee_box = RoundedRectangle(
            width=11.35,
            height=1.64,
            corner_radius=0.13,
            color=CYAN,
            stroke_width=2.0,
            fill_color="#0B1625",
            fill_opacity=0.98,
        )
        guarantee_copy.move_to(guarantee_box)
        result = VGroup(guarantee_box, guarantee_copy).move_to(DOWN * 1.32)
        stamp = source_stamp().move_to(DOWN * 2.82)

        composition = VGroup(title, subtitle, definitions, result, stamp)
        assert_in_frame(composition, "poster")
        assert_contains(guarantee_box, guarantee_copy, "poster guarantee")
        assert_no_overlap(subtitle, definitions, "poster subtitle and definitions", gap=0.16)
        assert_no_overlap(definitions, result, "poster definitions and result", gap=0.18)
        self.add(composition)


class StitchedLILResultSocial(Scene):
    """Native 4:5 theorem-first composition; never rendered as a crop."""

    def construct(self) -> None:
        assert_social_geometry()
        self.hook()
        self.model()
        self.mechanism()
        self.stitch()
        self.result()

    def on_cue(self, scene_id: str) -> None:
        expected = SOCIAL_SCENE_STARTS[scene_id]
        actual = float(self.renderer.time)
        if abs(actual - expected) > SCENE_CLOCK_TOLERANCE:
            raise ValueError(
                f"social scene {scene_id!r} starts at {actual:.3f}s, "
                f"expected {expected:.3f}s"
            )

    def hold_until(self, next_scene: str, *, clear: bool = True) -> None:
        clear_time = CLEAR_RUN_TIME if clear else 0.0
        target = SOCIAL_SCENE_STARTS[next_scene] - clear_time
        remaining = target - float(self.renderer.time)
        if remaining < MIN_READING_HOLD:
            raise ValueError(
                f"only {remaining:.3f}s reading hold remains before {next_scene!r}"
            )
        self.wait(remaining)
        if clear:
            targets = list(self.mobjects)
            if targets:
                self.play(
                    AnimationGroup(
                        *[FadeOut(item, shift=UP * 0.04) for item in targets],
                        lag_ratio=0,
                    ),
                    run_time=CLEAR_RUN_TIME,
                )

    def hook(self) -> None:
        self.on_cue("social_hook")
        head = social_header("social_hook")
        axis_y = -0.10
        axis = Line(LEFT * 2.52 + UP * axis_y, RIGHT * 2.52 + UP * axis_y, color=DEEP)
        xs = np.linspace(-2.52, 2.52, 48)
        trace = path_curve(
            [
                np.array(
                    [
                        x,
                        axis_y + 0.46 * np.sin(2.7 * (x + 2.52))
                        / np.sqrt(1.0 + 0.34 * (x + 2.52)),
                        0,
                    ]
                )
                for x in xs
            ],
            IVORY,
            3.0,
        )
        fixed = Line(
            np.array([-0.45, axis_y - 0.67, 0]),
            np.array([-0.45, axis_y + 0.67, 0]),
            color=AMBER,
            stroke_width=6.0,
        )
        fixed_copy = label("one fixed look", 20, AMBER, "BOLD").next_to(
            fixed, DOWN, buff=0.18
        )
        promise = VGroup(
            label("ONE EVENT", 20, CYAN, "BOLD"),
            math_display(r"\forall n\ge4", 43, IVORY, max_width=4.8),
        ).arrange(DOWN, buff=0.10).move_to(DOWN * 2.25)
        stamp = source_stamp().scale(0.88).move_to(DOWN * 3.42)
        composition = VGroup(head, axis, trace, fixed, fixed_copy, promise, stamp)
        assert_in_social_frame(composition, "social hook")
        assert_no_overlap(VGroup(axis, trace, fixed, fixed_copy), promise, "social hook plot and promise")

        self.play(FadeIn(head), FadeIn(stamp), run_time=0.55)
        self.play(Create(axis), Create(trace), run_time=1.25)
        self.play(Create(fixed), FadeIn(fixed_copy), run_time=0.55)
        self.play(FadeIn(promise, shift=UP * 0.06), run_time=0.50)
        self.hold_until("social_model")

    def model(self) -> None:
        self.on_cue("social_model")
        head = social_header("social_model")
        cards = VGroup(
            social_assumption_card(
                r"X_k\text{ is }\mathcal F_{k+1}\text{-strongly measurable}",
                "one-step reveal",
                18,
            ),
            social_assumption_card(r"\lvert X_k\rvert\le b", "bounded a.e."),
            social_assumption_card(
                r"\mathbb E[X_k\mid\mathcal F_k]=0",
                "centered a.e.",
            ),
            social_assumption_card(
                r"\mathbb E[X_k^2\mid\mathcal F_k]\le\sigma^2",
                "fixed proxy a.e.",
            ),
        ).arrange(DOWN, buff=0.13).move_to(DOWN * 0.20)
        scope = math_display(
            r"0<\delta\le1,\qquad b>0,\qquad\sigma^2>0",
            27,
            AMBER,
            max_width=5.4,
        ).move_to(DOWN * 2.58)
        foot = VGroup(
            label("μ is a probability measure.", 19, IVORY, "BOLD"),
            label("Relations are a.e.; no independence assumption.", 19, MUTED),
        ).arrange(DOWN, buff=0.04).move_to(DOWN * 3.14)
        composition = VGroup(head, cards, scope, foot)
        assert_in_social_frame(composition, "social model")
        assert_no_overlap(cards, scope, "social model cards and scope")

        self.play(FadeIn(head), run_time=0.45)
        self.play(
            AnimationGroup(
                *[FadeIn(card, shift=UP * 0.05) for card in cards],
                lag_ratio=0.12,
            ),
            run_time=1.25,
        )
        self.play(FadeIn(scope), FadeIn(foot), run_time=0.45)
        self.hold_until("social_mechanism")

    def mechanism(self) -> None:
        self.on_cue("social_mechanism")
        head = social_header("social_mechanism")
        interval_latex = (r"[4,16)", r"[16,64)", r"[64,256)", r"[256,1024)")
        weight_latex = (r"w_0=\frac12", r"w_1=\frac16", r"w_2=\frac1{12}", r"w_3=\frac1{20}")
        rows = VGroup()
        for index, (interval, weight) in enumerate(zip(interval_latex, weight_latex, strict=True)):
            box = RoundedRectangle(
                width=5.30,
                height=0.60,
                corner_radius=0.08,
                color=CYAN if index % 2 == 0 else DEEP,
                stroke_width=1.6,
                fill_color="#0B1625",
                fill_opacity=0.98,
            )
            left_math = math_display(interval, 27, IVORY, max_width=2.1)
            right_math = math_display(weight, 27, AMBER, max_width=2.1)
            row_copy = VGroup(left_math, right_math).arrange(RIGHT, buff=1.02)
            row_copy.move_to(box)
            rows.add(VGroup(box, row_copy))
        rows.arrange(DOWN, buff=0.10).move_to(UP * 0.30)
        total = math_display(
            r"\sum_{j=0}^{\infty}w_j=1",
            28,
            CYAN,
            max_width=3.45,
        ).move_to(DOWN * 1.55)
        epoch_index = math_display(
            DISPLAY_MATH["selector"],
            23,
            MUTED,
            max_width=5.30,
        )
        budget_formula = math_display(
            DISPLAY_MATH["budget"],
            25,
            AMBER,
            max_width=5.30,
        )
        budget = VGroup(epoch_index, budget_formula).arrange(
            DOWN, buff=0.08
        ).move_to(DOWN * 2.50)
        foot = label("One fixed tilt per epoch, chosen in advance.", 20, MUTED).move_to(
            DOWN * 3.18
        )
        composition = VGroup(head, rows, total, budget, foot)
        assert_in_social_frame(composition, "social mechanism")
        assert_no_overlap(rows, total, "social mechanism rows and total")
        assert_no_overlap(total, budget, "social mechanism total and budget")
        assert_no_overlap(budget, foot, "social mechanism budget and foot")

        self.play(FadeIn(head), run_time=0.45)
        self.play(
            AnimationGroup(*[FadeIn(row) for row in rows], lag_ratio=0.15),
            run_time=1.25,
        )
        self.play(FadeIn(total), run_time=0.50)
        self.play(FadeIn(budget), FadeIn(foot), run_time=0.50)
        self.hold_until("social_stitch")

    def stitch(self) -> None:
        self.on_cue("social_stitch")
        head = social_header("social_stitch")
        x_left, x_right = -2.50, 2.50
        upper, lower = stitched_envelope_segments(
            x_left,
            x_right,
            center_y=-0.05,
            scale=1.05,
            width=4.2,
        )
        n_values = np.geomspace(4.0, 1023.0, 112)
        trace_points = [
            np.array(
                [
                    log_time_x(float(n), x_left, x_right),
                    -0.05
                    + 0.44
                    * stitched_width_value(float(n))
                    * np.sin(2.15 * np.log(float(n))),
                    0,
                ]
            )
            for n in n_values
        ]
        plot = VGroup(
            upper,
            lower,
            path_curve(trace_points, IVORY, 2.8),
        ).move_to(UP * 0.10)
        cuts = VGroup(
            *[
                DashedLine(
                    np.array([x, -1.38, 0]),
                    np.array([x, 1.55, 0]),
                    color=DEEP,
                    stroke_width=1.4,
                    dash_length=0.07,
                )
                for x in (
                    log_time_x(16.0, x_left, x_right),
                    log_time_x(64.0, x_left, x_right),
                    log_time_x(256.0, x_left, x_right),
                )
            ]
        )
        plot_note = VGroup(
            label("CHECKED INTEGER VALUES", 15, CYAN, "BOLD"),
            math_display(
                ILLUSTRATIVE_PARAMETER_TEX,
                18,
                MUTED,
                max_width=3.55,
            ),
            label("PATH ILLUSTRATIVE", 15, MUTED, "BOLD"),
        ).arrange(DOWN, buff=0.03).move_to(UP * 1.48)
        ledger = math_display(
            r"\sum_{j\ge0}\delta w_j=\delta",
            35,
            AMBER,
            max_width=4.6,
        ).move_to(DOWN * 1.86)
        guarantee = math_chip(
            DISPLAY_MATH["failure_mass"],
            width=3.65,
            color=RED,
            size=36,
        ).move_to(DOWN * 2.70)
        foot = label("One event controls every running mean.", 21, IVORY, "BOLD").move_to(
            DOWN * 3.30
        )
        composition = VGroup(head, plot, cuts, plot_note, ledger, guarantee, foot)
        assert_in_social_frame(composition, "social stitch")
        assert_no_overlap(plot, ledger, "social stitch plot and ledger")

        self.play(FadeIn(head), FadeIn(cuts), FadeIn(plot_note), run_time=0.45)
        self.play(Create(plot[2]), run_time=0.85)
        self.play(
            AnimationGroup(*[Create(segment) for segment in upper], lag_ratio=0.04),
            AnimationGroup(*[Create(segment) for segment in lower], lag_ratio=0.04),
            run_time=1.05,
        )
        self.play(FadeIn(ledger), FadeIn(guarantee), FadeIn(foot), run_time=0.55)
        self.hold_until("social_result")

    def result(self) -> None:
        self.on_cue("social_result")
        head = social_header("social_result")
        budget_top = math_display(
            DISPLAY_MATH["budget"],
            27,
            AMBER,
            max_width=5.15,
        )
        width_top = math_display(
            DISPLAY_MATH["width_first_line"],
            33,
            SOFT_CYAN,
            max_width=5.15,
        )
        width_bottom = math_display(
            DISPLAY_MATH["width_second_line"],
            33,
            SOFT_CYAN,
            max_width=5.15,
        )
        event_condition = math_display(
            DISPLAY_MATH["event_condition"],
            24,
            IVORY,
            max_width=5.15,
        )
        event_bound = math_display(
            DISPLAY_MATH["event_bound"],
            25,
            IVORY,
            max_width=5.15,
        )
        failure = math_display(DISPLAY_MATH["failure_mass"], 33, RED, max_width=3.2)
        epoch_index = math_display(
            DISPLAY_MATH["selector"],
            24,
            MUTED,
            max_width=5.15,
        )
        equations = VGroup(
            epoch_index,
            budget_top,
            width_top,
            width_bottom,
            failure,
            event_condition,
            event_bound,
        ).arrange(DOWN, buff=0.06).move_to(DOWN * 0.24)
        box = RoundedRectangle(
            width=5.55,
            height=4.24,
            corner_radius=0.14,
            color=CYAN,
            stroke_width=2.0,
            fill_color="#0B1625",
            fill_opacity=0.98,
        ).move_to(equations)
        receipt = VGroup(
            code(FACTS["result"]["theorem"], 14, MUTED),
            code(f"SOURCE {FACTS['short_commit']}", 15, CYAN),
        ).arrange(DOWN, buff=0.04).move_to(DOWN * 2.72)
        boundary = text_lines(
            ["Allocated fixed-tilt stitch.", "No sharp-constant claim. Not itself an e-process."],
            18,
            AMBER,
            "BOLD",
            DISPLAY_FONT,
            buff=0.05,
        ).move_to(DOWN * 3.34)
        composition = VGroup(head, box, equations, receipt, boundary)
        assert_in_social_frame(composition, "social result")
        assert_contains(box, equations, "social result equations")
        assert_no_overlap(head, box, "social result header and equations", gap=0.12)
        assert_no_overlap(box, receipt, "social result equations and receipt")
        assert_no_overlap(receipt, boundary, "social result receipt and boundary")

        self.play(FadeIn(head), run_time=0.45)
        self.play(FadeIn(box), FadeIn(equations), run_time=1.10)
        self.play(FadeIn(receipt), FadeIn(boundary), run_time=0.55)
        self.hold_until("end", clear=False)
        self.on_cue("end")


class StitchedLILResultSocialPoster(Scene):
    def construct(self) -> None:
        assert_social_geometry()
        title = text_lines(
            ["ONE CHECKED EVENT", "EVERY SAMPLE SIZE", "FROM FOUR ONWARD"],
            36,
            IVORY,
            "BOLD",
            DISPLAY_FONT,
            buff=0.10,
        ).move_to(UP * 2.78)
        definitions = VGroup(
            math_display(DISPLAY_MATH["selector"], 18, MUTED, max_width=5.1),
            math_display(DISPLAY_MATH["budget"], 19, AMBER, max_width=5.1),
            math_display(DISPLAY_MATH["width_first_line"], 23, SOFT_CYAN, max_width=5.1),
            math_display(DISPLAY_MATH["width_second_line"], 23, SOFT_CYAN, max_width=5.1),
        ).arrange(DOWN, buff=0.04).move_to(UP * 1.13)
        upper, lower = stitched_envelope_segments(
            -2.45,
            2.45,
            center_y=0.0,
            scale=0.32,
            width=4.2,
        )
        motif = VGroup(upper, lower).move_to(DOWN * 0.25)
        failure = math_display(DISPLAY_MATH["failure_mass"], 28, RED, max_width=4.8)
        event_top = math_display(
            DISPLAY_MATH["event_condition"],
            23,
            IVORY,
            max_width=4.9,
        )
        event_bottom = math_display(
            DISPLAY_MATH["event_bound"],
            26,
            IVORY,
            max_width=4.9,
        )
        guarantee_copy = VGroup(failure, event_top, event_bottom).arrange(DOWN, buff=0.10)
        guarantee_box = RoundedRectangle(
            width=5.35,
            height=1.75,
            corner_radius=0.12,
            color=CYAN,
            stroke_width=1.9,
            fill_color="#0B1625",
            fill_opacity=0.98,
        )
        guarantee_copy.move_to(guarantee_box)
        result = VGroup(guarantee_box, guarantee_copy).move_to(DOWN * 1.59)
        subtitle = text_lines(
            ["MACHINE-CHECKED IN LEAN", "FORMALSLT"],
            23,
            MUTED,
            "BOLD",
            DISPLAY_FONT,
            buff=0.08,
        ).move_to(DOWN * 2.83)
        stamp = source_stamp().scale(0.88).move_to(DOWN * 3.48)
        composition = VGroup(title, definitions, motif, result, subtitle, stamp)
        assert_in_social_frame(composition, "social poster")
        assert_contains(guarantee_box, guarantee_copy, "social poster guarantee")
        assert_no_overlap(title, definitions, "social poster title and definitions")
        assert_no_overlap(definitions, motif, "social poster definitions and motif")
        assert_no_overlap(motif, result, "social poster motif and result")
        assert_no_overlap(result, subtitle, "social poster result and subtitle")
        self.add(composition)
