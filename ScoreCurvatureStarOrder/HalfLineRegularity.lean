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

/-- If `f` is differentiable within `[0, ∞)` and `a ≥ 0`, then the shifted
function `x ↦ f (a + x)` is continuous on `[0, ∞)`.  This is the correct
boundary-continuity statement for shifted kernels when `a = 0`. -/
theorem continuousOn_shift_Ici_of_hasDerivWithinAt
    {f f' : ℝ → ℝ} {a : ℝ}
    (ha : 0 ≤ a)
    (h : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt f (f' z) (Set.Ici (0 : ℝ)) z) :
    ContinuousOn (fun x : ℝ => f (a + x)) (Set.Ici (0 : ℝ)) := by
  have hf : ContinuousOn f (Set.Ici (0 : ℝ)) :=
    continuousOn_Ici_of_hasDerivWithinAt h
  refine hf.comp' (by fun_prop) ?_
  intro x hx
  exact add_nonneg ha hx

/-- At a point whose shifted argument is strictly positive, a within-derivative
on `[0, ∞)` gives the ordinary derivative of the shifted function. -/
theorem hasDerivAt_shift_of_pos_of_hasDerivWithinAt_Ici
    {f f' : ℝ → ℝ} {a x : ℝ}
    (hax : 0 < a + x)
    (h : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt f (f' z) (Set.Ici (0 : ℝ)) z) :
    HasDerivAt (fun y : ℝ => f (a + y)) (f' (a + x)) x := by
  exact
    (hasDerivAt_of_pos_of_hasDerivWithinAt_Ici hax (h (a + x) hax.le)).comp_const_add a x

end ScoreCurvatureStarOrder
