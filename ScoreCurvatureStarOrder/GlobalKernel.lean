import Mathlib
import ScoreCurvatureStarOrder.ScoreRatio

namespace ScoreCurvatureStarOrder

/-- Global nonnegativity of the two-point kernel under score curvature on `[0, ∞)`. -/
theorem twoPointKernel_nonneg
    {S Sprime Ssecond : ℝ → ℝ} {a x t : ℝ}
    (ha : 0 ≤ a) (hx0 : 0 ≤ x) (ht0 : 0 ≤ t)
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt Sprime (Ssecond z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ),
      Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    0 ≤ twoPointKernel S Sprime a x t := by
  have hax : a + x ∈ Set.Ici (0 : ℝ) := by
    exact add_nonneg ha hx0
  have hat : a + t ∈ Set.Ici (0 : ℝ) := by
    exact add_nonneg ha ht0
  have hcont : ContinuousOn S (Set.Ici (0 : ℝ)) := by
    intro z hz
    exact (hS z hz).continuousAt.continuousWithinAt
  have hder :
      ∀ z ∈ interior (Set.Ici (0 : ℝ)),
        HasDerivWithinAt S (Sprime z) (interior (Set.Ici (0 : ℝ))) z := by
    intro z hz
    exact (hS z (interior_subset hz)).hasDerivWithinAt
  have hmono : MonotoneOn S (Set.Ici (0 : ℝ)) := by
    exact monotoneOn_of_hasDerivWithinAt_nonneg
      (convex_Ici (0 : ℝ)) hcont hder
      (fun z hz => (hSprime_pos z (interior_subset hz)).le)
  have hSpx : 0 ≤ Sprime (a + x) :=
    (hSprime_pos (a + x) hax).le

  by_cases hsx0 : S (a + x) = 0
  · exact twoPointKernel_nonneg_of_left_zero ha hx0 ht0 hmono hSpx hsx0
  by_cases hst0 : S (a + t) = 0
  · exact twoPointKernel_nonneg_of_right_zero hst0

  rcases lt_or_gt_of_ne hsx0 with hsxneg | hsxpos
  · rcases lt_or_gt_of_ne hst0 with hstneg | hstpos
    · rcases le_total x t with hxt | htx
      · let D : Set ℝ := Set.Icc (a + x) (a + t)
        have hD : Convex ℝ D := by
          dsimp [D]
          exact convex_Icc _ _
        have hsub : D ⊆ Set.Ici (0 : ℝ) := by
          intro z hz
          dsimp [D] at hz
          exact hax.trans hz.1
        have haxD : a + x ∈ D := by
          dsimp [D]
          exact ⟨le_rfl, by linarith⟩
        have hatD : a + t ∈ D := by
          dsimp [D]
          exact ⟨by linarith, le_rfl⟩
        have hSnzD : ∀ z ∈ D, S z ≠ 0 := by
          intro z hz
          have hzI : z ∈ Set.Ici (0 : ℝ) := hsub hz
          have hz' : z ≤ a + t := by
            exact hz.2
          have hm : S z ≤ S (a + t) := hmono hzI hat hz'
          exact ne_of_lt (lt_of_le_of_lt hm hstneg)
        exact twoPointKernel_nonneg_of_curvature_on
          hD
          (fun z hz => hS z (hsub hz))
          (fun z hz => hSprime z (hsub hz))
          hSnzD
          (fun z hz => hcurv z (hsub hz))
          haxD hatD
          (div_pos_of_neg_of_neg hstneg hsxneg)
      · let D : Set ℝ := Set.Icc (a + t) (a + x)
        have hD : Convex ℝ D := by
          dsimp [D]
          exact convex_Icc _ _
        have hsub : D ⊆ Set.Ici (0 : ℝ) := by
          intro z hz
          dsimp [D] at hz
          exact hat.trans hz.1
        have haxD : a + x ∈ D := by
          dsimp [D]
          exact ⟨by linarith, le_rfl⟩
        have hatD : a + t ∈ D := by
          dsimp [D]
          exact ⟨le_rfl, by linarith⟩
        have hSnzD : ∀ z ∈ D, S z ≠ 0 := by
          intro z hz
          have hzI : z ∈ Set.Ici (0 : ℝ) := hsub hz
          have hz' : z ≤ a + x := by
            exact hz.2
          have hm : S z ≤ S (a + x) := hmono hzI hax hz'
          exact ne_of_lt (lt_of_le_of_lt hm hsxneg)
        exact twoPointKernel_nonneg_of_curvature_on
          hD
          (fun z hz => hS z (hsub hz))
          (fun z hz => hSprime z (hsub hz))
          hSnzD
          (fun z hz => hcurv z (hsub hz))
          haxD hatD
          (div_pos_of_neg_of_neg hstneg hsxneg)
    · have hxt : x ≤ t := by
        by_contra hnot
        have htx : t < x := lt_of_not_ge hnot
        have hm : S (a + t) ≤ S (a + x) :=
          hmono hat hax (by linarith)
        linarith
      exact twoPointKernel_nonneg_of_left_nonpos_right_nonneg
        hSpx hxt hsxneg.le hstpos.le
  · rcases lt_or_gt_of_ne hst0 with hstneg | hstpos
    · have htx : t ≤ x := by
        by_contra hnot
        have hxt : x < t := lt_of_not_ge hnot
        have hm : S (a + x) ≤ S (a + t) :=
          hmono hax hat (by linarith)
        linarith
      exact twoPointKernel_nonneg_of_left_nonneg_right_nonpos
        hSpx htx hsxpos.le hstneg.le
    · rcases le_total x t with hxt | htx
      · let D : Set ℝ := Set.Icc (a + x) (a + t)
        have hD : Convex ℝ D := by
          dsimp [D]
          exact convex_Icc _ _
        have hsub : D ⊆ Set.Ici (0 : ℝ) := by
          intro z hz
          dsimp [D] at hz
          exact hax.trans hz.1
        have haxD : a + x ∈ D := by
          dsimp [D]
          exact ⟨le_rfl, by linarith⟩
        have hatD : a + t ∈ D := by
          dsimp [D]
          exact ⟨by linarith, le_rfl⟩
        have hSnzD : ∀ z ∈ D, S z ≠ 0 := by
          intro z hz
          have hzI : z ∈ Set.Ici (0 : ℝ) := hsub hz
          have hz' : a + x ≤ z := by
            exact hz.1
          have hm : S (a + x) ≤ S z := hmono hax hzI hz'
          exact ne_of_gt (lt_of_lt_of_le hsxpos hm)
        exact twoPointKernel_nonneg_of_curvature_on
          hD
          (fun z hz => hS z (hsub hz))
          (fun z hz => hSprime z (hsub hz))
          hSnzD
          (fun z hz => hcurv z (hsub hz))
          haxD hatD
          (div_pos hstpos hsxpos)
      · let D : Set ℝ := Set.Icc (a + t) (a + x)
        have hD : Convex ℝ D := by
          dsimp [D]
          exact convex_Icc _ _
        have hsub : D ⊆ Set.Ici (0 : ℝ) := by
          intro z hz
          dsimp [D] at hz
          exact hat.trans hz.1
        have haxD : a + x ∈ D := by
          dsimp [D]
          exact ⟨by linarith, le_rfl⟩
        have hatD : a + t ∈ D := by
          dsimp [D]
          exact ⟨le_rfl, by linarith⟩
        have hSnzD : ∀ z ∈ D, S z ≠ 0 := by
          intro z hz
          have hzI : z ∈ Set.Ici (0 : ℝ) := hsub hz
          have hz' : a + t ≤ z := by
            exact hz.1
          have hm : S (a + t) ≤ S z := hmono hat hzI hz'
          exact ne_of_gt (lt_of_lt_of_le hstpos hm)
        exact twoPointKernel_nonneg_of_curvature_on
          hD
          (fun z hz => hS z (hsub hz))
          (fun z hz => hSprime z (hsub hz))
          hSnzD
          (fun z hz => hcurv z (hsub hz))
          haxD hatD
          (div_pos hstpos hsxpos)

end ScoreCurvatureStarOrder
