import FormalSLT.Covering.DudleySumToIntegral
import FormalSLT.Covering.TwoPointDudleyIntegral

/-!
# Finite Dudley entropy-integral endpoint

This module is the canonical import surface for the finite G3 Dudley endpoint.
It re-exports the q087 sum-to-integral theorem, the lower-friction q087
wrappers, and the rooted two-point integral example.

The statements remain finite-scale. They do not assert a measurable supremum
theorem, separability theorem, or continuous limiting theorem.
-/

namespace FormalSLT.Covering.DudleyEntropyIntegral

export FormalSLT.Covering.DudleySumToIntegral
  (coveringNumber_entropy_antitone
   coveringNumber_entropy_integrable_of_antitone
   coveringNumber_entropy_integrable
   dyadic_sum_le_entropy_integral
   dudley_entropy_integral_of_antitone_coveringNumber
   dudley_entropy_integral)

export FormalSLT.Covering.TwoPointDudleyIntegral
  (twoPointRootNet
   twoPointTerminalNet
   twoPointRootedNet
   twoPointIntegralCoverProfile
   twoPointIntegralCoverProfile_antitone
   twoPointIntegralCoverProfile_pos
   twoPointRademacher_centered_dudley_entropy_integral)

end FormalSLT.Covering.DudleyEntropyIntegral
