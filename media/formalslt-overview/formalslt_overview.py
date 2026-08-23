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
LABEL_SIZE = 26
SMALL_SIZE = 22

DISPLAY_FONT = "Avenir Next"
CODE_FONT = "Menlo"

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


def split_code_identifier(name: str, max_chars: int = 42) -> list[str]:
    """Wrap a Lean identifier at visible boundaries without dropping characters."""
    lines: list[str] = []
    remaining = name
    while len(remaining) > max_chars:
        candidates = [
            index + 1
            for index, character in enumerate(remaining[:max_chars])
            if character == "_"
        ]
        candidates.extend(
            index
            for index in range(1, min(len(remaining), max_chars + 1))
            if remaining[index].isupper() and remaining[index - 1].islower()
        )
        split_at = max(candidates, default=max_chars)
        lines.append(remaining[:split_at])
        remaining = remaining[split_at:]
    lines.append(remaining)
    return lines


def declaration_focus_card(item: dict[str, str]) -> VGroup:
    stage = label(item["stage"].upper(), SMALL_SIZE, CYAN, "BOLD")
    name = text_lines(
        split_code_identifier(item["name"], max_chars=36),
        29,
        IVORY,
        "MEDIUM",
        CODE_FONT,
        buff=0.04,
    )
    source = label(Path(item["file"]).name, 21, MUTED, "MEDIUM", CODE_FONT)
    return VGroup(stage, name, source).arrange(DOWN, aligned_edge=LEFT, buff=0.18)


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


class FormalSLTOverview(Scene):
    def construct(self) -> None:
        self.intro()
        self.problem()
        self.structured_reduction(section="03")
        self.proof_spine()
        self.anytime(section="04")
        self.trajectories(section="05")
        self.stationary_layer(section="06")
        self.theorem_graph()
        self.close()

    def clear_for_next(self, *keep) -> None:
        protected = set(keep)
        targets = [mob for mob in self.mobjects if mob not in protected]
        if targets:
            self.play(
                AnimationGroup(
                    *[FadeOut(mob, shift=UP * 0.08) for mob in targets],
                    lag_ratio=0,
                ),
                run_time=0.55,
            )

    def intro(self) -> None:
        mark = VGroup(
            Line(LEFT * 0.38, RIGHT * 0.38, color=CYAN, stroke_width=5),
            Dot(radius=0.07, color=CYAN).shift(LEFT * 0.38),
            Dot(radius=0.07, color=CYAN).shift(RIGHT * 0.38),
        )
        mark.shift(UP * 1.4)
        title = label("FormalSLT", 75, IVORY, "BOLD")
        title.next_to(mark, DOWN, buff=0.4)
        subtitle = label("Learning guarantees that survive adaptation.", 34, IVORY, "MEDIUM")
        subtitle.next_to(title, DOWN, buff=0.22)
        scope = label(
            "PAC-Bayes  ·  anytime inference  ·  dependent paths",
            26,
            CYAN,
            "MEDIUM",
        )
        scope.next_to(subtitle, DOWN, buff=0.36)
        stamp = label(
            f"FACTS CHECKED AT  {FACTS['short_commit']}",
            19,
            MUTED,
            "BOLD",
            CODE_FONT,
        ).to_edge(DOWN, buff=0.38)

        self.play(Create(mark), run_time=0.8)
        self.play(FadeIn(title, shift=UP * 0.08), FadeIn(subtitle, shift=UP * 0.12), run_time=0.75)
        self.play(FadeIn(scope), FadeIn(stamp), run_time=0.55)
        self.wait(1.85)
        self.clear_for_next()

    def problem(self) -> None:
        head = caption(
            "When the data are not IID",
            "The next observation can depend on everything seen so far.",
        )
        self.play(FadeIn(head), run_time=0.6)

        xs = np.linspace(-5.3, 5.0, 12)
        ys = [0.0, 0.15, -0.08, 0.25, 0.5, 0.1, -0.5, -0.15, -0.75, -0.35, 0.3, 0.7]
        dots = VGroup(*[
            Dot(np.array([x, y - 0.35, 0]), radius=0.08, color=IVORY)
            for x, y in zip(xs, ys)
        ])
        links = VGroup(*[
            Line(dots[i].get_center(), dots[i + 1].get_center(), color=MUTED, stroke_width=2)
            for i in range(len(dots) - 1)
        ])
        path = VGroup(links, dots)

        iid = label("independent samples", LABEL_SIZE, MUTED).next_to(path, DOWN, buff=0.42)
        self.play(LaggedStart(*[GrowFromCenter(d) for d in dots], lag_ratio=0.06), run_time=0.9)
        self.play(Create(links), FadeIn(iid), run_time=0.7)

        feedback = VGroup()
        for left, right, lift in [(2, 6, 0.85), (5, 9, 1.15), (7, 11, 0.75)]:
            start = dots[left].get_center() + UP * 0.06
            end = dots[right].get_center() + UP * 0.06
            arc = path_curve([start, start + UP * lift, end + UP * lift, end], RED, 2.5)
            feedback.add(arc)

        adaptive = label("adaptive or dependent path", LABEL_SIZE, RED, "BOLD")
        adaptive.move_to(iid)
        self.play(FadeOut(iid), FadeIn(adaptive), Create(feedback), run_time=0.75)

        warning = VGroup(
            label("data-selected model", 25, IVORY, "BOLD"),
            label("dependent data", 25, IVORY, "BOLD"),
            label("repeated looks", 25, IVORY, "BOLD"),
        ).arrange(RIGHT, buff=1.0).next_to(path, DOWN, buff=0.45)
        assert_in_content(VGroup(path, warning), "problem scene")
        assert_horizontal_gap(warning[0], warning[1], "problem labels", gap=0.3)
        assert_horizontal_gap(warning[1], warning[2], "problem labels", gap=0.3)
        self.play(FadeOut(adaptive), run_time=0.20)
        self.play(
            LaggedStart(
                *[FadeIn(w, shift=UP * 0.1) for w in warning], lag_ratio=0.15
            ),
            run_time=0.60,
        )
        self.wait(0.8)
        self.clear_for_next()

    def proof_spine(self) -> None:
        head = caption(
            "Four mechanisms, checked in Lean",
            "From exponential processes to guarantees along a path.",
        )
        self.play(FadeIn(head), run_time=0.6)

        stages = [
            ("EXP", "e-process"),
            ("KL", "change of measure\n+ PAC-Bayes"),
            ("∀t", "every time"),
            ("PATH", "dependent\npath"),
        ]
        nodes = VGroup()
        for symbol, text in stages:
            ring = Circle(radius=0.44, color=CYAN, stroke_width=3, stroke_opacity=0.48)
            symbol_size = 25 if len(symbol) > 3 else 27 if len(symbol) > 2 else 29
            glyph = label(symbol, symbol_size, CYAN, "BOLD", CODE_FONT)
            glyph.move_to(ring)
            name = label(text, 22, MUTED, "MEDIUM")
            name.next_to(ring, DOWN, buff=0.22)
            nodes.add(VGroup(ring, glyph, name))
        nodes.arrange(RIGHT, buff=1.05).shift(DOWN * 0.15)

        arrows = VGroup(*[
            Arrow(
                nodes[i][0].get_right(),
                nodes[i + 1][0].get_left(),
                buff=0.12,
                color=MUTED,
                stroke_width=2.5,
                stroke_opacity=0.65,
                max_tip_length_to_length_ratio=0.18,
            )
            for i in range(len(nodes) - 1)
        ])
        pulse = Dot(nodes[0][0].get_center(), radius=0.08, color=CYAN)

        self.play(LaggedStart(*[FadeIn(n, shift=UP * 0.12) for n in nodes], lag_ratio=0.12), run_time=1.2)
        self.play(Create(arrows), run_time=0.8)
        route = VMobject().set_points_as_corners([n[0].get_center() for n in nodes])
        self.add(pulse)
        self.play(MoveAlongPath(pulse, route, rate_func=linear), run_time=1.8)
        self.play(
            *[n[0].animate.set_stroke(CYAN, width=3, opacity=1) for n in nodes],
            FadeOut(pulse),
            run_time=0.7,
        )

        receipt = label(
            "Every displayed result is tied to the pinned Lean source.",
            BODY_SIZE,
            IVORY,
            "BOLD",
        )
        receipt.next_to(nodes, DOWN, buff=0.62)
        assert_in_content(VGroup(nodes, receipt), "mechanism route")
        self.play(FadeIn(receipt, shift=UP * 0.1), run_time=0.7)
        self.wait(0.9)
        self.clear_for_next()

    def structured_reduction(self, section: str = "06") -> None:
        queue = FACTS["controlled_queue"]
        head = caption(
            "One family, one checked reduction",
            "4,608 transition coordinates become one hit rate.",
        )
        self.play(FadeIn(head), run_time=0.55)

        grid = coordinate_panel(width=4.0, height=2.55).move_to(LEFT * 3.55 + DOWN * 0.12)
        coordinate_count = label(
            f"{queue['observations']} × {queue['observations']} × "
            f"{queue['transition_coordinate_sides']} = "
            f"{queue['transition_coordinates']:,}",
            32,
            IVORY,
            "BOLD",
            CODE_FONT,
        ).next_to(grid, UP, buff=0.16)
        dimensions = text_lines(
            ["48 current × 48 next × 2 orientations"],
            SMALL_SIZE,
            MUTED,
            "BOLD",
            buff=0.04,
        ).next_to(grid, DOWN, buff=0.15)

        row_nodes = VGroup(*[
            Dot(
                radius=0.11 if index != 15 else 0.16,
                color=CYAN if index == 15 else MUTED,
            )
            for index in range(queue["physical_states"])
        ]).arrange_in_grid(rows=3, cols=8, buff=(0.34, 0.35)).move_to(RIGHT * 3.5)
        step_ring = Circle(radius=0.22, color=CYAN, stroke_width=2.6).move_to(row_nodes[15])
        row_title = text_lines(
            ["Each row is a uniform refresh", "+ extra mass on one known step"],
            25,
            IVORY,
            "BOLD",
            buff=0.06,
        ).next_to(row_nodes, UP, buff=0.3)
        mixture = text_lines(
            ["(1 − γ) · Uniform24", "+ γ · δ(step)"],
            24,
            CYAN,
            "BOLD",
            CODE_FONT,
            buff=0.04,
        ).next_to(row_nodes, DOWN, aligned_edge=LEFT, buff=0.25)
        first_beat = VGroup(grid, coordinate_count, dimensions, row_nodes, step_ring, row_title, mixture)
        assert_in_content(first_beat, "structured family overview")
        assert_in_frame(first_beat, "structured family overview")

        self.play(FadeIn(grid), FadeIn(coordinate_count), FadeIn(dimensions), run_time=0.7)
        self.play(
            LaggedStart(*[GrowFromCenter(node) for node in row_nodes], lag_ratio=0.025),
            FadeIn(row_title),
            run_time=0.85,
        )
        self.play(Create(step_ring), FadeIn(mixture), run_time=0.55)
        self.wait(0.65)

        self.play(FadeOut(first_beat, shift=LEFT * 0.12), run_time=0.45)

        hit = VGroup(
            Circle(radius=0.62, color=CYAN, stroke_width=3),
            label("hit", 29, CYAN, "BOLD", CODE_FONT),
        ).move_to(LEFT * 4.9 + UP * 0.35)
        hit[1].move_to(hit[0])
        hit_definition = text_lines(
            ["hit = 1 when the next state", "is the known deterministic step"],
            28,
            IVORY,
            "BOLD",
            buff=0.05,
        ).next_to(hit, RIGHT, buff=0.48)
        hit_mean = label(
            f"pγ = E[hit | past] = {queue['hit_probability']}",
            28,
            CYAN,
            "BOLD",
            CODE_FONT,
        ).next_to(hit_definition, DOWN, aligned_edge=LEFT, buff=0.27)
        hit_beat = VGroup(hit, hit_definition, hit_mean)
        hit_beat.shift(LEFT * 0.12)
        assert_in_content(hit_beat, "structured hit definition")
        assert_in_frame(hit_beat, "structured hit definition")
        identity = label(
            "TV(row γ, row γ′) = |pγ − pγ′|",
            34,
            IVORY,
            "BOLD",
            CODE_FONT,
        ).move_to(RIGHT * 1.25 + UP * 0.42)
        exact = label("EXACT FOR EVERY PHYSICAL ROW", 24, CYAN, "BOLD")
        exact.next_to(identity, DOWN, aligned_edge=LEFT, buff=0.18)
        scope_copy = text_lines(
            [
                "Assumes the predeclared refresh family.",
                "Does not test whether the data belong to it.",
            ],
            24,
            AMBER,
            "BOLD",
            buff=0.05,
        )
        scope_box = RoundedRectangle(
            width=scope_copy.width + 0.48,
            height=scope_copy.height + 0.32,
            corner_radius=0.1,
            color=AMBER,
            stroke_width=1.8,
            fill_color="#241B12",
            fill_opacity=0.72,
        ).move_to(scope_copy)
        scope = VGroup(scope_box, scope_copy)
        scope.next_to(exact, DOWN, aligned_edge=LEFT, buff=0.18)
        result_beat = VGroup(hit, identity, exact, scope)
        assert_in_content(result_beat, "structured reduction result")
        assert_in_frame(result_beat, "structured reduction result")

        self.play(GrowFromCenter(hit), FadeIn(hit_definition), run_time=0.55)
        self.play(FadeIn(hit_mean, shift=UP * 0.08), run_time=0.5)
        self.wait(0.6)
        self.play(FadeOut(hit_definition), FadeOut(hit_mean), run_time=0.4)
        self.play(FadeIn(identity, shift=UP * 0.08), FadeIn(exact), run_time=0.65)
        self.play(FadeIn(scope), run_time=0.45)
        self.wait(3.25)
        self.clear_for_next()

    def anytime(self, section: str = "03") -> None:
        head = caption(
            "One guarantee, valid at every time",
            "The same event covers every allowed posterior.",
        )
        self.play(FadeIn(head), run_time=0.6)

        axes = Axes(
            x_range=[0, 10, 2],
            y_range=[-1.2, 1.2, 0.6],
            x_length=10.2,
            y_length=3.3,
            axis_config={"color": DEEP, "stroke_width": 2, "include_ticks": False},
            tips=False,
        ).shift(DOWN * 0.35)
        upper = axes.plot(lambda x: 0.95 / np.sqrt(x + 0.55), x_range=[0.25, 10], color=CYAN, stroke_width=3)
        lower = axes.plot(lambda x: -0.95 / np.sqrt(x + 0.55), x_range=[0.25, 10], color=CYAN, stroke_width=3)
        trace = axes.plot(
            lambda x: 0.42 * np.sin(1.7 * x) / np.sqrt(x + 0.7),
            x_range=[0.25, 10],
            color=IVORY,
            stroke_width=3.5,
        )
        scan = DashedLine(
            axes.c2p(0.7, -1.0), axes.c2p(0.7, 1.0),
            color=AMBER, stroke_width=2.2, dash_length=0.08,
        )
        scan_label = label("look", SMALL_SIZE, AMBER, "BOLD").next_to(scan, UP, buff=0.12)

        self.play(Create(axes), run_time=0.7)
        self.play(Create(upper), Create(lower), Create(trace), run_time=1.3)
        self.play(FadeIn(scan), FadeIn(scan_label), run_time=0.4)
        for x in [3.2, 6.2, 9.2]:
            target = DashedLine(
                axes.c2p(x, -1.0), axes.c2p(x, 1.0),
                color=AMBER, stroke_width=2.2, dash_length=0.08,
            )
            self.play(Transform(scan, target), scan_label.animate.next_to(target, UP, buff=0.12), run_time=0.48)

        quantifier = VGroup(
            label("ONE EVENT", LABEL_SIZE, CYAN, "BOLD"),
            label("EVERY TIME", LABEL_SIZE, IVORY, "BOLD"),
            label("EVERY ALLOWED POSTERIOR", LABEL_SIZE, IVORY, "BOLD"),
        ).arrange(RIGHT, buff=0.9).move_to(DOWN * 1.9)
        assert_in_content(VGroup(axes, quantifier), "anytime scene")
        self.play(LaggedStart(*[FadeIn(x, shift=UP * 0.08) for x in quantifier], lag_ratio=0.12), run_time=0.8)
        self.wait(0.7)
        self.clear_for_next()

    def trajectories(self, section: str = "04") -> None:
        head = caption(
            "The next prediction may use the path",
            "Choose from the past. Score before the next state arrives.",
        )
        self.play(FadeIn(head), run_time=0.6)

        centers = [
            np.array([-5.3, -0.2, 0]), np.array([-3.7, 0.65, 0]),
            np.array([-2.1, -0.55, 0]), np.array([-0.3, 0.4, 0]),
            np.array([1.5, -0.35, 0]), np.array([3.3, 0.55, 0]),
            np.array([5.15, -0.1, 0]),
        ]
        nodes = VGroup(*[Circle(radius=0.24, color=IVORY, stroke_width=2.6).move_to(p) for p in centers])
        arrows = VGroup(*[
            Arrow(centers[i], centers[i + 1], buff=0.28, color=MUTED, stroke_width=2.5, max_tip_length_to_length_ratio=0.12)
            for i in range(len(centers) - 1)
        ])
        memory = VGroup()
        for i in [2, 3, 4, 5]:
            arc = path_curve([
                centers[0] + UP * 0.23,
                centers[0] + UP * (0.45 + 0.10 * i),
                centers[i] + UP * (0.45 + 0.10 * i),
                centers[i] + UP * 0.23,
            ], CYAN, 1.8)
            arc.set_stroke(opacity=0.3 + i * 0.1)
            memory.add(arc)

        self.play(LaggedStart(*[GrowFromCenter(n) for n in nodes], lag_ratio=0.09), run_time=0.9)
        self.play(Create(arrows), run_time=0.8)
        self.play(LaggedStart(*[Create(a) for a in memory], lag_ratio=0.12), run_time=1.1)

        history = label("OBSERVED PREFIX", SMALL_SIZE, CYAN, "BOLD")
        history.next_to(memory, UP, buff=0.05)
        choice = VGroup(
            VGroup(
                label("POSTERIOR + TILT", 21, CYAN, "BOLD"),
                label("chosen from the observed prefix", 26, IVORY, "BOLD"),
            ).arrange(DOWN, buff=0.08),
            VGroup(
                label("NEXT-STEP SCORE", 21, CYAN, "BOLD"),
                label("fixed before the next state", 26, IVORY, "BOLD"),
            ).arrange(DOWN, buff=0.08),
        ).arrange(RIGHT, buff=1.25).next_to(nodes, DOWN, buff=0.5)
        assert_in_content(VGroup(memory, nodes, choice), "trajectory scene")
        self.play(FadeIn(history), LaggedStart(*[FadeIn(x, shift=UP * 0.1) for x in choice], lag_ratio=0.1), run_time=0.9)
        self.wait(0.9)
        self.clear_for_next()

    def stationary_layer(self, section: str = "05") -> None:
        head = caption(
            "From one path to long-run risk",
            "For finite-state kernels, a Poisson correction makes the bridge.",
        )
        self.play(FadeIn(head), run_time=0.6)

        left_center = LEFT * 4.15 + DOWN * 0.2
        path_nodes = VGroup(*[
            Dot(left_center + RIGHT * i * 0.72 + UP * (0.28 * np.sin(i * 1.7)), radius=0.07, color=IVORY)
            for i in range(8)
        ])
        path_links = VGroup(*[
            Line(path_nodes[i].get_center(), path_nodes[i + 1].get_center(), color=MUTED, stroke_width=2.2)
            for i in range(7)
        ])
        path_title = label("observed path", LABEL_SIZE, MUTED).next_to(path_nodes, DOWN, buff=0.32)

        bridge = Arrow(RIGHT * 1.0 + DOWN * 0.2, RIGHT * 2.72 + DOWN * 0.2, color=CYAN, stroke_width=4, buff=0.05)
        bridge_label = label("Poisson\ncorrection", LABEL_SIZE, CYAN, "BOLD")
        bridge_label.next_to(bridge, UP, buff=0.22)

        ring_center = RIGHT * 4.1 + DOWN * 0.2
        orbit = Circle(radius=1.2, color=DEEP, stroke_width=3).move_to(ring_center)
        orbit_nodes = VGroup(*[
            Dot(ring_center + 1.2 * np.array([np.cos(a), np.sin(a), 0]), radius=0.08, color=CYAN)
            for a in np.linspace(0, 2 * np.pi, 9)[:-1]
        ])
        pi = label("π", 40, IVORY, "BOLD", CODE_FONT).move_to(ring_center)
        stationary_title = label("stationary target", 22, MUTED, "BOLD")
        stationary_title.next_to(orbit, UP, buff=0.16)

        self.play(Create(path_links), LaggedStart(*[GrowFromCenter(x) for x in path_nodes], lag_ratio=0.07), FadeIn(path_title), run_time=1.0)
        self.play(Create(bridge), FadeIn(bridge_label), run_time=0.75)
        self.play(Create(orbit), LaggedStart(*[GrowFromCenter(x) for x in orbit_nodes], lag_ratio=0.06), FadeIn(pi), FadeIn(stationary_title), run_time=1.0)

        routes = VGroup(
            label("KNOWN KERNEL", 23, IVORY, "BOLD"),
            label("PREDECLARED KERNEL CATALOG", 23, CYAN, "BOLD"),
        ).arrange(RIGHT, buff=1.4).move_to(DOWN * 1.95)
        assert_in_content(VGroup(path_nodes, bridge, orbit, routes), "stationary scene")
        assert_no_overlap(stationary_title, bridge_label, "stationary labels")
        assert_no_overlap(orbit, routes, "stationary target and route labels")
        self.play(FadeIn(routes, shift=UP * 0.1), run_time=0.7)
        self.play(orbit.animate.set_stroke(CYAN, width=3.4), run_time=0.5)
        self.wait(0.8)
        self.clear_for_next()

    def theorem_graph(self) -> None:
        head = caption(
            "One library, four mathematical layers",
            "PAC-Bayes, sequential inference, dynamics, and VC theory.",
        )
        self.play(FadeIn(head), run_time=0.6)

        topic_names = ["PAC-Bayes", "Sequential", "Dynamics", "VC theory"]
        topics = VGroup()
        for index, name in enumerate(topic_names):
            box = RoundedRectangle(
                width=4.3,
                height=1.15,
                corner_radius=0.12,
                color=CYAN if index in (0, 2) else DEEP,
                stroke_width=2.2,
                fill_color="#0B1625",
                fill_opacity=0.96,
            )
            text = label(name, 28, IVORY, "BOLD")
            text.move_to(box)
            topics.add(VGroup(box, text))
        topics.arrange_in_grid(rows=2, cols=2, buff=(0.48, 0.38)).move_to(UP * 0.12)
        topic_links = VGroup(*[
            Line(
                topics[index][0].get_right(),
                topics[index + 1][0].get_left(),
                color=DEEP,
                stroke_width=3,
            )
            for index in (0, 2)
        ])

        self.play(LaggedStart(*[FadeIn(topic, shift=UP * 0.1) for topic in topics], lag_ratio=0.12), run_time=0.9)
        self.play(Create(topic_links), run_time=0.7)

        receipt = label(
            "Reusable statements, explicit assumptions, exact source.",
            BODY_SIZE,
            CYAN,
            "MEDIUM",
        ).next_to(topics, DOWN, buff=0.22)
        assert_in_content(VGroup(topics, receipt), "library layers")
        self.play(FadeIn(receipt, shift=UP * 0.08), run_time=0.7)
        self.wait(2.0)
        self.clear_for_next()

    def close(self) -> None:
        ey = eyebrow("EXACT LEAN RECEIPT")
        ey.to_edge(LEFT, buff=0.72).to_edge(UP, buff=0.55)
        title = label("Two declarations used in the film", 46, IVORY, "BOLD")
        title.next_to(ey, DOWN, aligned_edge=LEFT, buff=0.24)
        self.play(FadeIn(ey), FadeIn(title, shift=UP * 0.1), run_time=0.7)

        declarations = FACTS["proof_spine"]
        first_page = declaration_focus_card(declarations[0])
        second_page = declaration_focus_card(declarations[-1])
        panel = RoundedRectangle(
            width=12.5,
            height=3.65,
            corner_radius=0.12,
            color=DEEP,
            stroke_width=1.5,
            fill_color="#0B1625",
            fill_opacity=1,
        ).move_to(DOWN * 0.15)
        for page in (first_page, second_page):
            page.move_to(panel).align_to(panel, LEFT).shift(RIGHT * 0.52)
        assert_in_content(panel, "declaration receipt panel")
        self.play(
            FadeIn(panel),
            FadeIn(first_page, shift=RIGHT * 0.12),
            run_time=0.7,
        )
        self.wait(2.35)
        self.play(
            FadeOut(first_page, shift=LEFT * 0.12),
            FadeIn(second_page, shift=LEFT * 0.12),
            run_time=0.55,
        )
        self.wait(2.35)

        axiom_card = VGroup(
            label("No project-specific axioms", 38, IVORY, "BOLD"),
            label(
                "Audited primitives: propext · Classical.choice · Quot.sound",
                24,
                MUTED,
                "MEDIUM",
                CODE_FONT,
            ),
            label(
                f"FACTS CHECKED AT  {FACTS['short_commit']}",
                21,
                CYAN,
                "BOLD",
                CODE_FONT,
            ),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.25)
        axiom_card.move_to(panel).align_to(panel, LEFT).shift(RIGHT * 0.55)
        self.play(FadeOut(second_page), FadeIn(axiom_card, shift=UP * 0.08), run_time=0.65)
        self.wait(1.8)

        self.play(FadeOut(VGroup(ey, title, panel, axiom_card)), run_time=0.65)
        final = label("FormalSLT", 70, IVORY, "BOLD")
        line = label("Checked learning theory for data that adapt.", 30, CYAN, "MEDIUM")
        url = label("github.com/Robby955/FormalSLT", 23, MUTED, "MEDIUM", CODE_FONT)
        lockup = VGroup(final, line, url).arrange(DOWN, buff=0.24)
        self.play(FadeIn(lockup, shift=UP * 0.15), run_time=0.8)
        self.wait(2.2)


class FormalSLTSocial(FormalSLTOverview):
    """Short cut with all explanatory text burned into the frame."""

    def construct(self) -> None:
        self.social_hook()
        self.social_reduction()
        self.social_close()

    def social_hook(self) -> None:
        grid = coordinate_panel(width=4.4, height=3.05).move_to(RIGHT * 3.75 + DOWN * 0.15)
        brand = eyebrow("FORMALSLT")
        brand.to_edge(LEFT, buff=0.72).to_edge(UP, buff=0.48)
        title = text_lines(
            ["4,608 transition", "coordinates"],
            48,
            IVORY,
            "BOLD",
            buff=0.04,
        )
        title.to_edge(LEFT, buff=0.72).shift(UP * 0.28)
        sub = label("One checked reduction", 30, CYAN, "BOLD")
        sub.next_to(title, DOWN, aligned_edge=LEFT, buff=0.34)
        scope = label(
            "Inside a predeclared refresh family",
            26,
            AMBER,
            "BOLD",
        ).next_to(sub, DOWN, aligned_edge=LEFT, buff=0.45)
        left_column = VGroup(brand, title, sub, scope)
        assert_horizontal_gap(left_column, grid, "social hook")
        assert_in_frame(VGroup(left_column, grid), "social hook")
        self.play(
            FadeIn(brand),
            FadeIn(grid),
            FadeIn(title, shift=UP * 0.12),
            run_time=0.7,
        )
        self.play(FadeIn(sub), FadeIn(scope), run_time=0.6)
        self.wait(0.75)
        self.clear_for_next()

    def social_reduction(self) -> None:
        queue = FACTS["controlled_queue"]
        head = caption(
            "4,608 coordinates become one hit rate",
            "The transfer is exact inside the declared family.",
        )
        hit = VGroup(
            Circle(radius=0.72, color=CYAN, stroke_width=3.2),
            label("hit", 32, CYAN, "BOLD", CODE_FONT),
        ).move_to(LEFT * 4.85 + UP * 0.2)
        hit[1].move_to(hit[0])
        definition = text_lines(
            ["hit = 1 on the known step", f"pγ = {queue['hit_probability']}"],
            29,
            IVORY,
            "BOLD",
            buff=0.15,
        ).next_to(hit, RIGHT, buff=0.52)
        definition[1].set_color(CYAN)
        identity = label(
            "TV(row γ, row γ′) = |pγ − pγ′|",
            37,
            IVORY,
            "BOLD",
            CODE_FONT,
        ).next_to(definition, DOWN, aligned_edge=LEFT, buff=0.42)
        scope = label(
            "Assumes the family. Does not test membership.",
            27,
            AMBER,
            "BOLD",
        ).next_to(identity, DOWN, aligned_edge=LEFT, buff=0.38)
        result = VGroup(hit, definition, identity, scope)
        assert_in_content(result, "social reduction")
        assert_in_frame(result, "social reduction")

        self.play(FadeIn(head), run_time=0.5)
        self.play(GrowFromCenter(hit), FadeIn(definition), run_time=0.65)
        self.play(FadeIn(identity, shift=UP * 0.08), run_time=0.65)
        self.play(FadeIn(scope), run_time=0.4)
        self.wait(2.3)
        self.clear_for_next()

    def social_close(self) -> None:
        mark = play_mark(radius=0.42).shift(UP * 1.55)
        title = label("FormalSLT", 70, IVORY, "BOLD")
        title.next_to(mark, DOWN, buff=0.32)
        line = label("Checked learning theory for data that adapt", 31, CYAN, "MEDIUM")
        line.next_to(title, DOWN, buff=0.2)
        detail = label(
            "The theorem, assumptions, and exact source are linked below.",
            25,
            MUTED,
            "MEDIUM",
        ).next_to(line, DOWN, buff=0.42)
        url = label(
            "github.com/Robby955/FormalSLT",
            22,
            IVORY,
            "BOLD",
            CODE_FONT,
        ).next_to(detail, DOWN, buff=0.2)
        self.play(FadeIn(mark), FadeIn(title), FadeIn(line), run_time=0.75)
        self.play(FadeIn(detail), FadeIn(url), run_time=0.55)
        self.wait(1.35)


class FormalSLTPoster(Scene):
    """Stable click-to-play poster; independent of scene timing and counts."""

    def construct(self) -> None:
        brand = eyebrow("FORMALSLT")
        title = text_lines(
            ["Learning guarantees", "that survive", "adaptation."],
            49,
            IVORY,
            "BOLD",
            buff=0.04,
        )
        body = text_lines(
            [
                "PAC-Bayes · anytime inference",
                "dependent paths · stationary risk",
            ],
            30,
            MUTED,
            "MEDIUM",
            buff=0.08,
        )
        play = play_mark(radius=0.5)
        watch = label("WATCH THE FILM", 24, IVORY, "BOLD", CODE_FONT)
        cta = VGroup(play, watch).arrange(RIGHT, buff=0.3)
        left_column = VGroup(brand, title, body, cta).arrange(
            DOWN,
            aligned_edge=LEFT,
            buff=0.42,
        )
        left_column.to_edge(LEFT, buff=0.72).shift(UP * 0.18)

        grid = coordinate_panel(width=3.55, height=2.55).move_to(RIGHT * 4.70 + UP * 0.05)
        grid.set_opacity(0.88)
        scalar = VGroup(
            Circle(radius=0.64, color=CYAN, stroke_width=3),
            label("hit", 28, CYAN, "BOLD", CODE_FONT),
        ).move_to(RIGHT * 1.45 + UP * 0.05)
        scalar[1].move_to(scalar[0])
        collapse = Arrow(
            grid.get_left() + LEFT * 0.12,
            scalar.get_right() + RIGHT * 0.12,
            color=CYAN,
            stroke_width=5,
            buff=0.02,
            max_tip_length_to_length_ratio=0.24,
        )
        if collapse.get_length() < 0.5:
            raise ValueError("Poster reduction arrow is too short to read.")
        grid_count = VGroup(
            label("4,608", 39, IVORY, "BOLD", CODE_FONT),
            label("GENERIC COORDINATES", 21, MUTED, "BOLD", CODE_FONT),
        ).arrange(DOWN, buff=0.03).next_to(grid, UP, buff=0.18)
        scalar_count = VGroup(
            label("1", 39, IVORY, "BOLD", CODE_FONT),
            label("HIT RATE", 21, MUTED, "BOLD", CODE_FONT),
        ).arrange(DOWN, buff=0.03).next_to(scalar, UP, buff=0.40)
        scope = text_lines(
            ["Inside one predeclared family", "Not a membership test"],
            25,
            AMBER,
            "BOLD",
            buff=0.04,
        ).move_to(RIGHT * 3.45 + DOWN * 1.82)
        right_column = VGroup(grid, scalar, collapse, grid_count, scalar_count, scope)

        assert_horizontal_gap(left_column, right_column, "poster", gap=0.42)
        assert_no_overlap(scalar_count, scalar, "poster scalar count", gap=0.2)
        assert_no_overlap(scalar_count, grid, "poster count and grid", gap=0.16)
        assert_in_frame(left_column, "poster left column")
        assert_in_frame(right_column, "poster right column")

        self.add(left_column, right_column)
