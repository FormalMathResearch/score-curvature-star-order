import Mathlib

namespace ScoreCurvatureStarOrder

/-- Abstract two-point score kernel. -/
def twoPointKernel (S Sprime : ℝ → ℝ) (a x t : ℝ) : ℝ :=
  Sprime (a + x) * (t - x) * S (a + t) - S (a + x) * (S (a + t) - S (a + x))

end ScoreCurvatureStarOrder
