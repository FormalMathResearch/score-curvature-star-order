import Mathlib

namespace ScoreCurvatureStarOrder

open Set Filter

/-- A derivative known only within the closed positive half-line is an ordinary
(two-sided) derivative at every strictly positive interior point. At the
boundary point `0` we intentionally keep the weaker `HasDerivWithinAt`
statement, matching one-sided regularity on `[0, ∞)`. -/
theorem hasDerivAt_of_pos_of_hasDerivWithinAt_Ici
    {f : ℝ → ℝ} {f' x : ℝ}
    (hx : 0 < x)
    (h : HasDerivWithinAt f f' (Set.Ici (0 : ℝ)) x) :
    HasDerivAt f f' x := by
  exact h.hasDerivAt (Ici_mem_nhds hx)

/-- Pointwise differentiability within `[0, ∞)` implies continuity on that
closed half-line, including the one-sided boundary continuity at `0`. -/
theorem continuousOn_Ici_of_hasDerivWithinAt
    {f f' : ℝ → ℝ}
    (h : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt f (f' x) (Set.Ici (0 : ℝ)) x) :
    ContinuousOn f (Set.Ici (0 : ℝ)) := by
  intro x hx
  exact (h x hx).continuousWithinAt

end ScoreCurvatureStarOrder
