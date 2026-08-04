/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Rademacher.Symmetrization

/-!
# Compatibility import: Rademacher symmetrization

The implementation lives in `FormalSLT.Rademacher.Symmetrization`. This module
preserves the earlier verbose namespace and import path without duplicating the
proof.
-/

namespace FormalSLT.Rademacher.RademacherSymmetrization

alias expected_genGap_le_two_expected_empiricalRademacherComplexity :=
  FormalSLT.Rademacher.Symmetrization.expected_genGap_le_two_expected_empiricalRademacherComplexity

end FormalSLT.Rademacher.RademacherSymmetrization
