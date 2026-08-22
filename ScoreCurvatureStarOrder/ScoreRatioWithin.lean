import Mathlib
import ScoreCurvatureStarOrder.ScoreRatio
import ScoreCurvatureStarOrder.HalfLineRegularity

namespace ScoreCurvatureStarOrder

open Set

/-- Half-line version of score-ratio monotonicity.

If `S` and `S'` are differentiable only within `[0, ∞)`, then on every later
half-line `[R, ∞)` with `R ≥ 0`, the curvature inequality
`S'' S - (S')² ≤ 0` still makes `S'/S` antitone wherever `S` does not vanish.
No two-sided derivative at the boundary `R` is used. -/
theorem scoreRatio_antitoneOn_Ici_within
    {S Sprime Ssecond : ℝ → ℝ} {R : ℝ}
    (hR : 0 ≤ R)
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt Sprime (Ssecond z) (Set.Ici (0 : ℝ)) z)
    (hSnz : ∀ z ∈ Set.Ici R, S z ≠ 0)
    (hcurv : ∀ z ∈ Set.Ici R,
      Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    AntitoneOn (fun z => Sprime z / S z) (Set.Ici R) := by
  have hsubset : Set.Ici R ⊆ Set.Ici (0 : ℝ) := by
    intro z hz
    exact hR.trans hz
  have hcont : ContinuousOn (fun z => Sprime z / S z) (Set.Ici R) := by
    intro z hz
    have hSp : ContinuousWithinAt Sprime (Set.Ici R) z :=
      (hSprime z (hsubset hz)).continuousWithinAt.mono hsubset
    have hSc : ContinuousWithinAt S (Set.Ici R) z :=
      (hS z (hsubset hz)).continuousWithinAt.mono hsubset
    exact hSp.div hSc (hSnz z hz)
  have hinterior_subset : interior (Set.Ici R) ⊆ Set.Ici (0 : ℝ) := by
    intro z hz
    exact hsubset (interior_subset hz)
  have hder :
      ∀ z ∈ interior (Set.Ici R),
        HasDerivWithinAt (fun y => Sprime y / S y)
          ((Ssecond z * S z - Sprime z * Sprime z) / S z ^ 2)
          (interior (Set.Ici R)) z := by
    intro z hz
    have hzR : z ∈ Set.Ici R := interior_subset hz
    have hSp := (hSprime z (hsubset hzR)).mono hinterior_subset
    have hSd := (hS z (hsubset hzR)).mono hinterior_subset
    exact hSp.div hSd (hSnz z hzR)
  have hnonpos :
      ∀ z ∈ interior (Set.Ici R),
        (Ssecond z * S z - Sprime z * Sprime z) / S z ^ 2 ≤ 0 := by
    intro z hz
    have hzR : z ∈ Set.Ici R := interior_subset hz
    have hnum : Ssecond z * S z - Sprime z * Sprime z ≤ 0 := by
      simpa [pow_two] using hcurv z hzR
    exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg (S z))
  exact antitoneOn_of_hasDerivWithinAt_nonpos
    (convex_Ici R) hcont hder hnonpos

end ScoreCurvatureStarOrder
