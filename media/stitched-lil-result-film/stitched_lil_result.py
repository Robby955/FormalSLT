from __future__ import annotations

import json
from pathlib import Path

import numpy as np
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
FILM = json.loads((PACKAGE_DIR / "film_config.json").read_text(encoding="utf-8"))

if FACTS["commit"] != FILM["source_commit"]:
    raise ValueError("film timing and mathematical fact receipts bind different commits")

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

CLEAR_RUN_TIME = 0.55
SCENE_CLOCK_TOLERANCE = 0.05
MIN_READING_HOLD = 0.65

SCENE_STARTS = {scene["id"]: float(scene["start"]) for scene in FILM["scenes"]}
SCENE_STARTS["end"] = float(FILM["duration_seconds"])
SCENE_COPY = {scene["id"]: scene for scene in FILM["scenes"]}

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


def caption(scene_id: str) -> VGroup:
    scene = SCENE_COPY[scene_id]
    heading = label(scene["title"], TITLE_SIZE, IVORY, "BOLD")
    detail = label(scene["detail"], DETAIL_SIZE, MUTED)
    if heading.width > 12.0 or detail.width > 12.0:
        raise ValueError(f"{scene_id} caption exceeds the 12-unit safe width")
    group = VGroup(heading, detail).arrange(DOWN, aligned_edge=LEFT, buff=0.16)
    group.to_edge(LEFT, buff=0.72).to_edge(UP, buff=0.54)
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


def formula_chip(
    text: str,
    *,
    width: float | None = None,
    color: str = SOFT_CYAN,
    size: float = FORMULA_SIZE,
) -> VGroup:
    copy = code(text, size, color)
    box_width = copy.width + 0.48 if width is None else width
    if copy.width > box_width - 0.30:
        raise ValueError(f"formula does not fit chip: {text!r}")
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


def assumption_card(formula: str, plain: str) -> VGroup:
    box = RoundedRectangle(
        width=5.3,
        height=1.18,
        corner_radius=0.12,
        color=DEEP,
        stroke_width=2.0,
        fill_color="#0B1625",
        fill_opacity=0.98,
    )
    mathematical = code(formula, 27, CYAN)
    description = label(plain, 23, MUTED, "MEDIUM")
    copy = VGroup(mathematical, description).arrange(
        DOWN,
        aligned_edge=LEFT,
        buff=0.08,
    )
    if copy.width > box.width - 0.42:
        raise ValueError(f"assumption copy does not fit: {formula!r}")
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
        stamp = source_stamp().to_edge(DOWN, buff=0.38).to_edge(RIGHT, buff=0.72)

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
        fixed_label = code("one fixed n", 24, CYAN).next_to(fixed_slice, DOWN, buff=0.22)
        question = label(
            "What remains valid when the timeline keeps moving?",
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
        spine = code(
            "measurable, integrable X_0, X_1, X_2, ...",
            29,
            IVORY,
        ).move_to(UP * 1.18)
        cards = VGroup(
            assumption_card("X_k revealed at k+1", "one step after the past"),
            assumption_card("|X_k| <= b", "bounded increments"),
            assumption_card("E[X_k | F_k] = 0", "conditional centering"),
            assumption_card("E[X_k^2 | F_k] <= sigma^2", "fixed variance proxy"),
        ).arrange_in_grid(rows=2, cols=2, buff=(0.45, 0.34))
        cards.move_to(DOWN * 0.45)
        scope = label(
            "0 < delta <= 1   |   b > 0   |   sigma^2 > 0",
            25,
            AMBER,
            "BOLD",
        ).move_to(DOWN * 2.20)

        assert_in_content(VGroup(spine, cards), "model content")
        assert_in_frame(VGroup(head, spine, cards, scope), "model")
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
        floor_formula = code("N_j = 4^(j+1)", 31, AMBER).move_to(UP * 1.15)
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
                code(interval_text[index], 22, IVORY).move_to(
                    np.array([(left + right) / 2, axis_y, 0])
                )
            )
            epoch_labels.add(
                code(f"j = {index}", 22, AMBER).move_to(
                    np.array([(left + right) / 2, axis_y + 0.78, 0])
                )
            )
        boundary_marks.add(Dot(np.array([boundaries[-1], axis_y, 0]), radius=0.07, color=AMBER))
        selector = label(
            "The checked selector places every n >= 4 inside its epoch.",
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
        weight_formula = code(
            f"w_j = {FACTS['allocation']['weight']}",
            31,
            AMBER,
        ).move_to(UP * 1.16)
        weights = VGroup(
            formula_chip("1/2", width=1.65, color=AMBER),
            formula_chip("1/6", width=1.65, color=AMBER),
            formula_chip("1/12", width=1.65, color=AMBER),
            formula_chip("1/20", width=1.65, color=AMBER),
            formula_chip("...", width=1.65, color=MUTED),
        ).arrange(RIGHT, buff=0.22).move_to(UP * 0.22)
        telescope = code(
            "1/(j+1) - 1/(j+2)",
            30,
            SOFT_CYAN,
        ).move_to(DOWN * 0.82)
        total = formula_chip(
            "sum_j w_j = 1",
            width=4.15,
            color=CYAN,
            size=31,
        ).move_to(DOWN * 1.63)

        content = VGroup(weight_formula, weights, telescope, total)
        assert_in_content(content, "allocation content")
        assert_in_frame(VGroup(head, content), "allocation")
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
        axis = Line(
            np.array([-5.65, axis_y, 0]),
            np.array([5.65, axis_y, 0]),
            color=DEEP,
            stroke_width=3.0,
        )
        boundaries = [-5.45, -2.72, 0.01, 2.74, 5.47]
        faint_lines = VGroup()
        active_segments = VGroup()
        floor_dots = VGroup()
        for index in range(4):
            slope = -0.07 - 0.025 * index
            y_offset = 0.82 + 0.24 * index
            start = np.array([-5.45, axis_y + y_offset, 0])
            end = np.array([5.47, axis_y + y_offset + slope * 10.92, 0])
            faint_lines.add(
                Line(
                    start,
                    end,
                    color=SOFT_CYAN,
                    stroke_width=2.0,
                    stroke_opacity=0.18,
                )
            )
            x0, x1 = boundaries[index], boundaries[index + 1]
            y0 = axis_y + y_offset + slope * (x0 + 5.45)
            y1 = axis_y + y_offset + slope * (x1 + 5.45)
            active_segments.add(
                Line(
                    np.array([x0, y0, 0]),
                    np.array([x1, y1, 0]),
                    color=CYAN,
                    stroke_width=5.0,
                )
            )
            floor_dots.add(Dot(np.array([x0, y0, 0]), radius=0.075, color=AMBER))

        budget = text_lines(
            [
                "B_j = log(2/delta)",
                "      + log(j+1) + log(j+2)",
            ],
            27,
            AMBER,
            "BOLD",
            CODE_FONT,
            buff=0.06,
        ).move_to(UP * 1.12 + RIGHT * 3.55)
        precommit = formula_chip(
            "one fixed tilt per epoch",
            width=4.55,
            color=IVORY,
            size=25,
        ).move_to(DOWN * 1.60 + LEFT * 2.55)
        receipt = code("delta=1/2, j=0  ->  B_0=log 8", 23, MUTED).move_to(
            DOWN * 1.60 + RIGHT * 2.85
        )

        plot = VGroup(axis, faint_lines, active_segments, floor_dots)
        assert_in_content(VGroup(plot, budget, precommit, receipt), "tilt content")
        assert_in_frame(VGroup(head, plot, budget, precommit, receipt), "tilts")
        assert_no_overlap(precommit, receipt, "tilt footer", gap=0.18)

        self.play(FadeIn(head), FadeIn(budget), run_time=0.70)
        self.play(Create(axis), Create(faint_lines), run_time=1.00)
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
        x_values = np.linspace(-5.55, 3.45, 64)
        upper_points = [
            np.array([x, 0.12 + 1.35 / np.sqrt(1.0 + 0.78 * (x + 5.55)), 0])
            for x in x_values
        ]
        lower_points = [np.array([x, -point[1] - 0.28, 0]) for x, point in zip(x_values, upper_points)]
        trace_points = [
            np.array(
                [
                    x,
                    -0.08
                    + 0.55 * np.sin(1.95 * (x + 5.55))
                    / np.sqrt(1.0 + 0.84 * (x + 5.55)),
                    0,
                ]
            )
            for x in x_values
        ]
        upper = path_curve(upper_points, CYAN, 4.6)
        lower = path_curve(lower_points, CYAN, 4.6)
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
                for x in (-3.30, -1.05, 1.20)
            ]
        )
        plot = VGroup(upper, lower, trace, epoch_cuts).shift(LEFT * 1.05 + DOWN * 0.25)

        ledger_box = RoundedRectangle(
            width=3.25,
            height=2.65,
            corner_radius=0.14,
            color=DEEP,
            stroke_width=2.0,
            fill_color="#0B1625",
            fill_opacity=0.98,
        ).move_to(RIGHT * 4.65 + DOWN * 0.25)
        ledger = text_lines(
            [
                "delta w_0",
                "+ delta w_1",
                "+ delta w_2 + ...",
                "= delta",
            ],
            24,
            AMBER,
            "BOLD",
            CODE_FONT,
            buff=0.14,
        ).move_to(ledger_box)
        failure = formula_chip(
            "failure mass <= delta",
            width=3.65,
            color=RED,
            size=23,
        ).move_to(DOWN * 2.08 + RIGHT * 3.88)
        scope = label(
            "Countable subadditivity, not a countable e-process.",
            26,
            IVORY,
            "BOLD",
        ).move_to(DOWN * 2.35 + LEFT * 1.65)

        assert_in_content(VGroup(plot, ledger_box, ledger), "stitch content")
        assert_in_frame(VGroup(head, plot, ledger_box, ledger, failure, scope), "stitch")
        assert_no_overlap(plot, ledger_box, "stitch plot and ledger", gap=0.18)
        assert_no_overlap(ledger_box, failure, "stitch ledger and failure", gap=0.12)

        self.play(FadeIn(head), FadeIn(epoch_cuts), run_time=0.65)
        self.play(Create(trace), run_time=1.15)
        self.play(Create(upper), Create(lower), run_time=1.55)
        self.play(FadeIn(ledger_box), FadeIn(ledger), run_time=0.60)
        self.play(FadeIn(failure), FadeIn(scope), run_time=0.55)
        self.hold_until("result")

    def result(self) -> None:
        self.on_cue("result")
        head = caption("result")
        budget = code(
            "B_j = log(2/delta) + log(j+1) + log(j+2)",
            25,
            AMBER,
        )
        width = code(
            "W_n = 2 sqrt(2 sigma^2 B_j / n) + 4 b B_j / (3n)",
            25,
            SOFT_CYAN,
        )
        conclusion = code(
            "|runningMean X n| < W_n     for every n >= 4",
            27,
            IVORY,
        )
        failure = code("failure mass <= delta", 25, RED)
        theorem_card = VGroup(budget, width, conclusion, failure).arrange(
            DOWN,
            aligned_edge=LEFT,
            buff=0.23,
        )
        theorem_box = RoundedRectangle(
            width=11.80,
            height=2.62,
            corner_radius=0.15,
            color=CYAN,
            stroke_width=2.2,
            fill_color="#0B1625",
            fill_opacity=0.98,
        )
        if theorem_card.width > theorem_box.width - 0.55:
            raise ValueError("result formula card is too wide")
        theorem_card.move_to(theorem_box)
        result_group = VGroup(theorem_box, theorem_card).move_to(UP * 0.12)

        module_name = code("AnytimeValid.PolynomialStitchedLIL", 20, MUTED)
        theorem_name = code(FACTS["result"]["theorem"], 20, MUTED)
        receipt = VGroup(module_name, theorem_name).arrange(
            DOWN,
            aligned_edge=LEFT,
            buff=0.06,
        ).move_to(DOWN * 1.70 + LEFT * 2.72)
        commit = code(f"SOURCE {FACTS['short_commit']}", 20, CYAN).move_to(
            DOWN * 1.70 + RIGHT * 4.85
        )
        boundary = label(
            "Not the LIL law. Not sharp. Not itself an e-process.",
            24,
            AMBER,
            "BOLD",
        ).move_to(DOWN * 2.42)

        assert_in_content(result_group, "result theorem card")
        assert_in_frame(VGroup(head, result_group, receipt, commit, boundary), "result")
        assert_no_overlap(result_group, receipt, "result formula and receipt", gap=0.18)
        assert_no_overlap(receipt, boundary, "result receipt and boundary", gap=0.14)

        self.play(FadeIn(head), run_time=0.60)
        self.play(FadeIn(theorem_box), FadeIn(theorem_card), run_time=1.10)
        self.play(FadeIn(receipt), FadeIn(commit), run_time=0.60)
        self.play(FadeIn(boundary), run_time=0.45)
        self.hold_until("end", clear=False)
        self.on_cue("end")


class StitchedLILResultPoster(Scene):
    def construct(self) -> None:
        title = label(FILM["title"], 60, IVORY, "BOLD")
        title.move_to(UP * 1.85)
        subtitle = label(
            "A machine-checked log-log confidence sequence in Lean.",
            32,
            MUTED,
        ).next_to(title, DOWN, buff=0.23)

        xs = np.linspace(-5.5, 5.5, 64)
        upper = path_curve(
            [np.array([x, 0.82 / np.sqrt(1.0 + 0.62 * (x + 5.5)), 0]) for x in xs],
            CYAN,
            4.5,
        )
        lower = path_curve(
            [np.array([x, -0.82 / np.sqrt(1.0 + 0.62 * (x + 5.5)), 0]) for x in xs],
            CYAN,
            4.5,
        )
        trace = path_curve(
            [
                np.array(
                    [
                        x,
                        0.44 * np.sin(1.8 * (x + 5.5)) / np.sqrt(1.0 + 0.65 * (x + 5.5)),
                        0,
                    ]
                )
                for x in xs
            ],
            IVORY,
            2.8,
        )
        motif = VGroup(upper, lower, trace).move_to(DOWN * 0.32)
        result = formula_chip(
            "every n >= 4   |   failure mass <= delta",
            width=8.35,
            color=AMBER,
            size=26,
        ).move_to(DOWN * 1.93)
        stamp = source_stamp().move_to(DOWN * 2.72)

        composition = VGroup(title, subtitle, motif, result, stamp)
        assert_in_frame(composition, "poster")
        assert_no_overlap(subtitle, motif, "poster subtitle and motif", gap=0.18)
        assert_no_overlap(motif, result, "poster motif and result", gap=0.18)
        self.add(composition)
