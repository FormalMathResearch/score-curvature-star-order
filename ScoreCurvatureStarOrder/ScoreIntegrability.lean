import Mathlib
import ScoreCurvatureStarOrder.Moments
import ScoreCurvatureStarOrder.Boundary

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- Derivative of the integration-by-parts boundary product on the positive half-line. -/
theorem powerWeightedShift_product_deriv
    {theta S : ℝ → ℝ} {a p x : ℝ}
    (hx : 0 < x) (hax : 0 ≤ a + x)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z) :
    HasDerivAt (fun y : ℝ => y ^ (p + 1) * theta (a + y))
      ((p + 1) * x ^ p * theta (a + x) -
        x ^ (p + 1) * S (a + x) * theta (a + x)) x := by
  have hrpow :
      HasDerivAt (fun y : ℝ => y ^ (p + 1)) ((p + 1) * x ^ p) x := by
    have h := Real.hasDerivAt_rpow_const (x := x) (p := p + 1) (Or.inl hx.ne')
    convert h using 1 <;> ring
  have hshift : HasDerivAt (fun y : ℝ => a + y) 1 x := by
    simpa using (hasDerivAt_const x a).add (hasDerivAt_id x)
  have htheta_shift :
      HasDerivAt (fun y : ℝ => theta (a + y)) (-S (a + x) * theta (a + x)) x := by
    simpa using (htheta_deriv (a + x) hax).comp x hshift
  convert hrpow.mul htheta_shift using 1 <;> ring

end ScoreCurvatureStarOrder
