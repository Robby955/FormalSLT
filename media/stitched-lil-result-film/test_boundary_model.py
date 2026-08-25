#!/usr/bin/env python3
"""Regression tests for the exact numerical boundary drawings."""

from __future__ import annotations

import math
import unittest

from boundary_model import (
    fixed_tilt_boundary_value,
    log_time_x,
    optimized_tilt_value,
    selected_epoch_value,
    stitched_width_value,
)


class BoundaryModelTests(unittest.TestCase):
    def test_selected_epoch_matches_checked_factor_four_buckets(self) -> None:
        expected = {
            4: 0,
            15: 0,
            16: 1,
            63: 1,
            64: 2,
            255: 2,
            256: 3,
            1023: 3,
            1024: 4,
        }
        self.assertEqual(
            {n: selected_epoch_value(float(n)) for n in expected},
            expected,
        )

    def test_selector_rejects_theorem_outside_domain(self) -> None:
        for value in (0.0, 3.999, float("nan"), float("inf")):
            with self.subTest(value=value), self.assertRaises(ValueError):
                selected_epoch_value(value)

    def test_fixed_tilt_boundaries_have_a_plus_c_over_n_shape(self) -> None:
        for epoch in range(4):
            floor = float(4 ** (epoch + 1))
            middle = 2.0 * floor
            horizon = 4.0 * floor
            first = fixed_tilt_boundary_value(epoch, floor)
            second = fixed_tilt_boundary_value(epoch, middle)
            third = fixed_tilt_boundary_value(epoch, horizon)
            self.assertGreater(first, second)
            self.assertGreater(second, third)
            # For a + c/n, the first drop is exactly twice the second drop.
            self.assertAlmostEqual(first - second, 2.0 * (second - third), places=12)
            self.assertGreater(optimized_tilt_value(epoch), 0.0)

    def test_stitched_width_is_positive_and_finite(self) -> None:
        for n in (4.0, 15.0, 16.0, 63.0, 64.0, 1024.0):
            width = stitched_width_value(n)
            self.assertTrue(math.isfinite(width))
            self.assertGreater(width, 0.0)

    def test_log_time_axis_places_factor_four_ticks_evenly(self) -> None:
        coordinates = [log_time_x(float(n), -5.0, 5.0) for n in (4, 16, 64, 256, 1024)]
        gaps = [right - left for left, right in zip(coordinates, coordinates[1:])]
        for gap in gaps:
            self.assertAlmostEqual(gap, 2.5, places=12)


if __name__ == "__main__":
    unittest.main()
