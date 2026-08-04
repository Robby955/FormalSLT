/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Rademacher.LinearPredictor

/-!
# Compatibility import: linear-predictor Rademacher bounds

The implementation lives in `FormalSLT.Rademacher.LinearPredictor`. These
aliases preserve the earlier verbose namespace and import path.
-/

namespace FormalSLT.Rademacher.LinearPredictorRademacher

alias signProduct_same := FormalSLT.Rademacher.LinearPredictor.signProduct_same
alias sum_signProduct := FormalSLT.Rademacher.LinearPredictor.sum_signProduct
alias avg_signProduct := FormalSLT.Rademacher.LinearPredictor.avg_signProduct
alias sum_sign_norm_sq := FormalSLT.Rademacher.LinearPredictor.sum_sign_norm_sq
alias sup_inner_le := FormalSLT.Rademacher.LinearPredictor.sup_inner_le
alias sign_avg_norm_le_sqrt := FormalSLT.Rademacher.LinearPredictor.sign_avg_norm_le_sqrt
alias linearPredictor_rademacher :=
  FormalSLT.Rademacher.LinearPredictor.linearPredictor_rademacher
alias linearPredictor_rademacher_uniform :=
  FormalSLT.Rademacher.LinearPredictor.linearPredictor_rademacher_uniform
alias linearPredictor_rademacher_finiteDim :=
  FormalSLT.Rademacher.LinearPredictor.linearPredictor_rademacher_finiteDim
alias linearPredictor_rademacher_uniform_finiteDim :=
  FormalSLT.Rademacher.LinearPredictor.linearPredictor_rademacher_uniform_finiteDim

end FormalSLT.Rademacher.LinearPredictorRademacher
