import Mathlib
import ScoreCurvatureStarOrder.ShiftDerivativeMajorant
import ScoreCurvatureStarOrder.HalfLineRegularity

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- On compact ranges in both the shift and integration variables, the absolute
`a`-derivative of the shifted kernel is uniformly bounded.  Only one-sided
boundary differentiability on `[0, ∞)` is required. -/
theorem exists_shifted_thetaDeriv_local_majorant_within
    {theta S Sprime : ℝ → ℝ} {A T : ℝ}
    (hA : 0 ≤ A) (hT : 0 ≤ T)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a x : ℝ,
      a ∈ Set.Icc 0 A → x ∈ Set.Icc 0 T →
        |(-S (a + x) * theta (a + x))| ≤ C := by
  have hAT : 0 ≤ A + T := add_nonneg hA hT
  have hS_Ici : ContinuousOn S (Set.Ici (0 : ℝ)) :=
    continuousOn_Ici_of_hasDerivWithinAt hS
  have htheta_Ici : ContinuousOn theta (Set.Ici (0 : ℝ)) :=
    continuousOn_Ici_of_hasDerivWithinAt htheta_deriv
  have hIcc_sub : Set.Icc (0 : ℝ) (A + T) ⊆ Set.Ici (0 : ℝ) := by
    intro z hz
    exact hz.1
  have hcont : ContinuousOn (fun z : ℝ => |S z * theta z|) (Set.Icc 0 (A + T)) :=
    ((hS_Ici.mono hIcc_sub).mul (htheta_Ici.mono hIcc_sub)).abs
  rcases isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hAT) hcont with
    ⟨z, hz, hmax⟩
  refine ⟨|S z * theta z|, abs_nonneg _, ?_⟩
  intro a x ha hx
  have hax : a + x ∈ Set.Icc 0 (A + T) := by
    constructor
    · exact add_nonneg ha.1 hx.1
    · exact add_le_add ha.2 hx.2
  simpa [abs_mul] using hmax hax

/-- Backward-compatible wrapper for the former two-sided assumptions. -/
theorem exists_shifted_thetaDeriv_local_majorant
    {theta S Sprime : ℝ → ℝ} {A T : ℝ}
    (hA : 0 ≤ A) (hT : 0 ≤ T)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a x : ℝ,
      a ∈ Set.Icc 0 A → x ∈ Set.Icc 0 T →
        |(-S (a + x) * theta (a + x))| ≤ C := by
  exact exists_shifted_thetaDeriv_local_majorant_within
    hA hT
    (fun z hz => (htheta_deriv z hz).hasDerivWithinAt)
    (fun z hz => (hS z hz).hasDerivWithinAt)

end ScoreCurvatureStarOrder
