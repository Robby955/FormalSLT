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
    ORIGIN,
    Rectangle,
    ReplacementTransform,
    RIGHT,
    RoundedRectangle,
    Scene,
    Square,
    Text,
    Transform,
    UP,
    VGroup,
    VMobject,
    Write,
    config,
    linear,
)


ROOT = Path(__file__).resolve().parents[2]
FACTS = json.loads((Path(__file__).with_name("facts.json")).read_text())

BG = "#08111E"
IVORY = "#F4F1E8"
CYAN = "#64D8D2"
MUTED = "#8C9BAB"
DEEP = "#172539"
AMBER = "#F0B35A"
RED = "#EF6A68"

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
    item = label(text.upper(), 19, CYAN, "BOLD")
    item.set_opacity(0.95)
    return item


def caption(title: str, body: str) -> VGroup:
    heading = label(title, 39, IVORY, "BOLD")
    detail = label(body, 22, MUTED, "MEDIUM")
    group = VGroup(heading, detail).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
    group.to_edge(LEFT, buff=0.72).to_edge(UP, buff=0.55)
    return group


def footer(section: str) -> VGroup:
    rule = Line(LEFT * 6.55, RIGHT * 6.55, stroke_width=1.2, color=DEEP)
    text = label(section.upper(), 14, MUTED, "BOLD")
    text.next_to(rule, DOWN, buff=0.12).align_to(rule, LEFT)
    return VGroup(rule, text).to_edge(DOWN, buff=0.28)


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


class FormalSLTOverview(Scene):
    def construct(self) -> None:
        self.intro()
        self.problem()
        self.proof_spine()
        self.anytime()
        self.trajectories()
        self.stationary_layer()
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
        subtitle = label("Machine-checked learning theory", 28, MUTED)
        subtitle.next_to(title, DOWN, buff=0.22)
        scope = label("adaptive data  ·  dependent paths  ·  stationary risk", 19, CYAN)
        scope.next_to(subtitle, DOWN, buff=0.55)
        stamp = label(
            f"MERGED MAIN  /  {FACTS['short_commit']}",
            14,
            MUTED,
            "BOLD",
            CODE_FONT,
        ).to_edge(DOWN, buff=0.38)

        self.play(Create(mark), run_time=0.8)
        self.play(Write(title), FadeIn(subtitle, shift=UP * 0.12), run_time=1.0)
        self.play(FadeIn(scope), FadeIn(stamp), run_time=0.7)
        self.wait(1.1)
        self.clear_for_next()

    def problem(self) -> None:
        head = caption(
            "The hard case is not IID.",
            "The data-generating process can react to its own history.",
        )
        foot = footer("01  /  THE PROBLEM")
        self.play(FadeIn(head), FadeIn(foot), run_time=0.6)

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

        iid = label("independent samples", 17, MUTED).next_to(path, DOWN, buff=0.45)
        self.play(LaggedStart(*[GrowFromCenter(d) for d in dots], lag_ratio=0.06), run_time=0.9)
        self.play(Create(links), FadeIn(iid), run_time=0.7)

        feedback = VGroup()
        for left, right, lift in [(2, 6, 0.85), (5, 9, 1.15), (7, 11, 0.75)]:
            start = dots[right].get_center() + UP * 0.06
            end = dots[left].get_center() + UP * 0.06
            arc = path_curve([start, start + UP * lift, end + UP * lift, end], RED, 2.5)
            feedback.add(arc)

        adaptive = label("adaptive / dependent path", 17, RED, "BOLD")
        adaptive.move_to(iid)
        self.play(ReplacementTransform(iid, adaptive), Create(feedback), run_time=1.0)

        warning = VGroup(
            label("selection", 18, IVORY, "BOLD"),
            label("dependence", 18, IVORY, "BOLD"),
            label("time", 18, IVORY, "BOLD"),
        ).arrange(RIGHT, buff=1.55).next_to(path, DOWN, buff=0.88)
        self.play(LaggedStart(*[FadeIn(w, shift=UP * 0.1) for w in warning], lag_ratio=0.15), run_time=0.8)
        self.wait(0.8)
        self.clear_for_next()

    def proof_spine(self) -> None:
        head = caption(
            "One checked proof spine.",
            "Each layer feeds the next; assumptions stay visible.",
        )
        foot = footer("02  /  THE CONSTRUCTION")
        self.play(FadeIn(head), FadeIn(foot), run_time=0.6)

        stages = [
            ("EXP", "exponential\nprocesses"),
            ("KL", "change of\nmeasure"),
            ("PB", "PAC-Bayes"),
            ("∀t", "anytime\nvalidity"),
            ("PATH", "adaptive\ntrajectories"),
            ("STAT", "stationary /\nkernel layer"),
        ]
        nodes = VGroup()
        for symbol, text in stages:
            ring = Circle(radius=0.39, color=DEEP, stroke_width=3)
            symbol_size = 15 if len(symbol) > 3 else 18 if len(symbol) > 2 else 25
            glyph = label(symbol, symbol_size, CYAN, "BOLD", CODE_FONT)
            glyph.move_to(ring)
            name = label(text, 16, MUTED, "MEDIUM")
            name.next_to(ring, DOWN, buff=0.22)
            nodes.add(VGroup(ring, glyph, name))
        nodes.arrange(RIGHT, buff=0.72).shift(DOWN * 0.2)

        arrows = VGroup(*[
            Arrow(
                nodes[i][0].get_right(),
                nodes[i + 1][0].get_left(),
                buff=0.12,
                color=DEEP,
                stroke_width=2.5,
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
            *[n[0].animate.set_stroke(CYAN, width=3) for n in nodes],
            FadeOut(pulse),
            run_time=0.7,
        )

        receipt = label("Lean checks the composition, not just the endpoints.", 21, IVORY, "BOLD")
        receipt.next_to(nodes, DOWN, buff=0.78)
        self.play(FadeIn(receipt, shift=UP * 0.1), run_time=0.7)
        self.wait(0.9)
        self.clear_for_next()

    def anytime(self) -> None:
        head = caption(
            "Validity that survives looking again.",
            "A common event can cover every time and every admissible posterior.",
        )
        foot = footer("03  /  ANYTIME PAC-BAYES")
        self.play(FadeIn(head), FadeIn(foot), run_time=0.6)

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
        scan_label = label("observe", 15, AMBER, "BOLD").next_to(scan, UP, buff=0.12)

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
            label("ONE EVENT", 17, CYAN, "BOLD"),
            label("EVERY TIME", 17, IVORY, "BOLD"),
            label("EVERY POSTERIOR", 17, IVORY, "BOLD"),
        ).arrange(RIGHT, buff=1.3).next_to(axes, DOWN, buff=0.36)
        self.play(LaggedStart(*[FadeIn(x, shift=UP * 0.08) for x in quantifier], lag_ratio=0.12), run_time=0.8)
        self.wait(0.7)
        self.clear_for_next()

    def trajectories(self) -> None:
        head = caption(
            "The path can choose what happens next.",
            "Scores, dynamics, and posteriors may depend on the observed prefix.",
        )
        foot = footer("04  /  ADAPTIVE TRAJECTORIES")
        self.play(FadeIn(head), FadeIn(foot), run_time=0.6)

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
                centers[i] + UP * 0.23,
                centers[i] + UP * (0.65 + 0.14 * i),
                centers[0] + UP * (0.65 + 0.14 * i),
                centers[0] + UP * 0.23,
            ], CYAN, 1.8)
            arc.set_stroke(opacity=0.3 + i * 0.1)
            memory.add(arc)

        self.play(LaggedStart(*[GrowFromCenter(n) for n in nodes], lag_ratio=0.09), run_time=0.9)
        self.play(Create(arrows), run_time=0.8)
        self.play(LaggedStart(*[Create(a) for a in memory], lag_ratio=0.12), run_time=1.1)

        history = label("full observed prefix", 17, CYAN, "BOLD")
        history.next_to(memory, UP, buff=0.05)
        choice = VGroup(
            label("posterior(path, n)", 19, IVORY, "BOLD", CODE_FONT),
            label("tilt(path, n)", 19, IVORY, "BOLD", CODE_FONT),
            label("score s(prefix, next)", 19, IVORY, "BOLD", CODE_FONT),
        ).arrange(RIGHT, buff=0.85).next_to(nodes, DOWN, buff=0.8)
        self.play(FadeIn(history), LaggedStart(*[FadeIn(x, shift=UP * 0.1) for x in choice], lag_ratio=0.1), run_time=0.9)
        self.wait(0.9)
        self.clear_for_next()

    def stationary_layer(self) -> None:
        head = caption(
            "From one path to long-run risk.",
            "Poisson corrections bridge prequential evidence to stationary targets.",
        )
        foot = footer("05  /  STOCHASTIC DYNAMICS")
        self.play(FadeIn(head), FadeIn(foot), run_time=0.6)

        left_center = LEFT * 4.15 + DOWN * 0.2
        path_nodes = VGroup(*[
            Dot(left_center + RIGHT * i * 0.72 + UP * (0.28 * np.sin(i * 1.7)), radius=0.07, color=IVORY)
            for i in range(8)
        ])
        path_links = VGroup(*[
            Line(path_nodes[i].get_center(), path_nodes[i + 1].get_center(), color=MUTED, stroke_width=2.2)
            for i in range(7)
        ])
        path_title = label("observed path", 18, MUTED).next_to(path_nodes, DOWN, buff=0.35)

        bridge = Arrow(LEFT * 0.9 + DOWN * 0.2, RIGHT * 1.05 + DOWN * 0.2, color=CYAN, stroke_width=4, buff=0.05)
        bridge_label = label("Poisson\ncorrection", 16, CYAN, "BOLD")
        bridge_label.next_to(bridge, UP, buff=0.22)

        ring_center = RIGHT * 4.1 + DOWN * 0.2
        orbit = Circle(radius=1.2, color=DEEP, stroke_width=3).move_to(ring_center)
        orbit_nodes = VGroup(*[
            Dot(ring_center + 1.2 * np.array([np.cos(a), np.sin(a), 0]), radius=0.08, color=CYAN)
            for a in np.linspace(0, 2 * np.pi, 9)[:-1]
        ])
        pi = label("π", 40, IVORY, "BOLD", CODE_FONT).move_to(ring_center)
        stationary_title = label("stationary target", 18, MUTED).next_to(orbit, DOWN, buff=0.3)

        self.play(Create(path_links), LaggedStart(*[GrowFromCenter(x) for x in path_nodes], lag_ratio=0.07), FadeIn(path_title), run_time=1.0)
        self.play(Create(bridge), FadeIn(bridge_label), run_time=0.75)
        self.play(Create(orbit), LaggedStart(*[GrowFromCenter(x) for x in orbit_nodes], lag_ratio=0.06), FadeIn(pi), FadeIn(stationary_title), run_time=1.0)

        routes = VGroup(
            label("KNOWN KERNEL", 16, IVORY, "BOLD"),
            label("PREDECLARED KERNEL CATALOG", 16, CYAN, "BOLD"),
        ).arrange(RIGHT, buff=1.8).to_edge(DOWN, buff=0.95)
        self.play(FadeIn(routes, shift=UP * 0.1), run_time=0.7)
        self.play(orbit.animate.set_stroke(CYAN, width=3.4), run_time=0.5)
        self.wait(0.8)
        self.clear_for_next()

    def theorem_graph(self) -> None:
        head = caption(
            "A library, not a one-off proof.",
            "The library spans probability, sequential inference, dynamics, and VC theory.",
        )
        foot = footer("06  /  THE LIBRARY")
        self.play(FadeIn(head), FadeIn(foot), run_time=0.6)

        positions = [
            (-4.9, 0.6), (-3.6, -0.7), (-2.2, 0.2), (-0.9, -0.9),
            (0.2, 0.75), (1.4, -0.2), (2.7, 0.85), (3.7, -0.65), (5.0, 0.3),
            (-4.3, -1.5), (-1.8, 1.35), (0.7, -1.55), (3.0, -1.45), (4.6, 1.45),
        ]
        graph_nodes = VGroup(*[
            Dot(np.array([x, y - 0.15, 0]), radius=0.1 if i in [0, 2, 4, 6, 8] else 0.065, color=CYAN if i in [0, 2, 4, 6, 8] else MUTED)
            for i, (x, y) in enumerate(positions)
        ])
        edges_idx = [
            (0, 2), (2, 4), (4, 6), (6, 8), (0, 1), (1, 2), (2, 3),
            (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (1, 9), (2, 10),
            (3, 11), (5, 11), (6, 12), (7, 12), (8, 13), (10, 4), (13, 6),
        ]
        graph_edges = VGroup(*[
            Line(graph_nodes[a].get_center(), graph_nodes[b].get_center(), color=DEEP, stroke_width=1.7)
            for a, b in edges_idx
        ])
        spine = path_curve([graph_nodes[i].get_center() for i in [0, 2, 4, 6, 8]], CYAN, 4)

        topics = VGroup(*[
            label(name, 15, IVORY if i != 2 else CYAN, "BOLD", CODE_FONT)
            for i, name in enumerate(FACTS["library"]["stable_topic_imports"])
        ]).arrange(RIGHT, buff=0.75).to_edge(DOWN, buff=0.86)

        self.play(Create(graph_edges), run_time=0.8)
        self.play(LaggedStart(*[GrowFromCenter(n) for n in graph_nodes], lag_ratio=0.035), Create(spine), run_time=1.0)
        self.play(FadeIn(topics, shift=UP * 0.08), run_time=0.7)

        counts = VGroup(
            label(f"{FACTS['library']['modules']}", 43, IVORY, "BOLD", CODE_FONT),
            label("MODULES", 14, MUTED, "BOLD"),
            label(f"{FACTS['library']['theorems_and_lemmas']:,}", 43, IVORY, "BOLD", CODE_FONT),
            label("THEOREMS + LEMMAS", 14, MUTED, "BOLD"),
        )
        counts[1].next_to(counts[0], DOWN, buff=0.08)
        counts[2].next_to(counts[0], RIGHT, buff=1.2)
        counts[3].next_to(counts[2], DOWN, buff=0.08)
        counts.move_to(UP * 1.25)
        panel = RoundedRectangle(width=5.3, height=1.45, corner_radius=0.12, color=DEEP, stroke_width=1.5, fill_color=BG, fill_opacity=0.92).move_to(counts)
        self.play(FadeIn(panel), FadeIn(counts), run_time=0.8)
        self.wait(1.0)
        self.clear_for_next()

    def close(self) -> None:
        ey = eyebrow("SOURCE, STATEMENT, ASSUMPTIONS")
        ey.to_edge(LEFT, buff=0.72).to_edge(UP, buff=0.55)
        title = label("The theorem is the artifact.", 45, IVORY, "BOLD")
        title.next_to(ey, DOWN, aligned_edge=LEFT, buff=0.24)
        self.play(FadeIn(ey), FadeIn(title, shift=UP * 0.1), run_time=0.7)

        declarations = [
            "exists_forwardEmpiricalBernsteinLowerTiltCatalog_event",
            "timeUniformPACBayes_tiltMixture_allPosteriors_bound",
            "exists_trajectoryCountable...allTime_vanishing_event",
            "exists_empiricalStationaryCatalog_event",
        ]
        code_lines = VGroup()
        for i, item in enumerate(declarations):
            keyword = label("theorem", 18, CYAN, "BOLD", CODE_FONT)
            name = label(item, 18, IVORY, "MEDIUM", CODE_FONT)
            line = VGroup(keyword, name).arrange(RIGHT, buff=0.28)
            code_lines.add(line)
        code_lines.arrange(DOWN, aligned_edge=LEFT, buff=0.32)
        panel = RoundedRectangle(
            width=12.2,
            height=3.4,
            corner_radius=0.12,
            color=DEEP,
            stroke_width=1.5,
            fill_color="#0B1625",
            fill_opacity=1,
        ).move_to(DOWN * 0.15)
        code_lines.move_to(panel).align_to(panel, LEFT).shift(RIGHT * 0.36)
        self.play(FadeIn(panel), LaggedStart(*[FadeIn(line, shift=RIGHT * 0.12) for line in code_lines], lag_ratio=0.14), run_time=1.3)

        axiom = label("public axiom surface: propext · Classical.choice · Quot.sound", 15, MUTED, "MEDIUM", CODE_FONT)
        axiom.next_to(panel, DOWN, buff=0.28).align_to(panel, LEFT).shift(RIGHT * 0.12)
        commit = label(f"CHECKED AT  {FACTS['short_commit']}  /  MERGED MAIN", 15, CYAN, "BOLD", CODE_FONT)
        commit.next_to(axiom, DOWN, buff=0.18).align_to(panel, LEFT)
        self.play(FadeIn(axiom), FadeIn(commit), run_time=0.65)
        self.wait(1.2)

        self.play(FadeOut(VGroup(ey, title, panel, code_lines, axiom, commit)), run_time=0.65)
        final = label("FormalSLT", 64, IVORY, "BOLD")
        line = label("A checked foundation for statistical learning.", 26, CYAN, "MEDIUM")
        url = label("github.com/Robby955/FormalSLT", 17, MUTED, "MEDIUM", CODE_FONT)
        lockup = VGroup(final, line, url).arrange(DOWN, buff=0.24)
        self.play(FadeIn(lockup, shift=UP * 0.15), run_time=0.8)
        self.wait(1.8)
