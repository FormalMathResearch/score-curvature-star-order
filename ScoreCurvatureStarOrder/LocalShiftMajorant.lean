import Mathlib
import ScoreCurvatureStarOrder.ShiftDerivativeMajorant

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- On compact ranges in both the shift and integration variables, the absolute
`a`-derivative of the shifted kernel is uniformly bounded. -/
theorem exists_shifted_thetaDeriv_local_majorant
    {theta S Sprime : ℝ → ℝ} {A T : ℝ}
    (hA : 0 ≤ A) (hT : 0 ≤ T)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a x : ℝ,
      a ∈ Set.Icc 0 A → x ∈ Set.Icc 0 T →
        |(-S (a + x) * theta (a + x))| ≤ C := by
  have hAT : 0 ≤ A + T := add_nonneg hA hT
  have hcont : ContinuousOn (fun z : ℝ => |S z * theta z|) (Set.Icc 0 (A + T)) := by
    intro z hz
    have hz0 : z ∈ Set.Ici (0 : ℝ) := hz.1
    exact (((hS z hz0).continuousAt.mul
      (htheta_deriv z hz0).continuousAt).abs).continuousWithinAt
  rcases isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hAT) hcont with
    ⟨z, hz, hmax⟩
  refine ⟨|S z * theta z|, abs_nonneg _, ?_⟩
  intro a x ha hx
  have hax : a + x ∈ Set.Icc 0 (A + T) := by
    constructor
    · exact add_nonneg ha.1 hx.1
    · exact add_le_add ha.2 hx.2
  simpa [abs_mul] using hmax hax

end ScoreCurvatureStarOrder
