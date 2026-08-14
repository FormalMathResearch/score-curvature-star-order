import Mathlib
import ScoreCurvatureStarOrder.GlobalKernel
import ScoreCurvatureStarOrder.HalfLineRegularity

namespace ScoreCurvatureStarOrder

/-- Global nonnegativity of the two-point kernel at strictly positive radial
arguments, assuming only one-sided differentiability on `[0, ∞)`.

The strict positivity of `x` and `t` is exactly what is needed in the later
kernel expectation, whose integration domain is `(0, ∞)`.  It ensures that any
ordinary two-sided derivative used on the finite interval between `a+x` and
`a+t` is taken at a strictly positive argument; no two-sided derivative at the
boundary `0` is introduced. -/
theorem twoPointKernel_nonneg_of_pos_within
    {S Sprime Ssecond : ℝ → ℝ} {a x t : ℝ}
    (ha : 0 ≤ a) (hx : 0 < x) (ht : 0 < t)
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt Sprime (Ssecond z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ),
      Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    0 ≤ twoPointKernel S Sprime a x t := by
  have haxpos : 0 < a + x := add_pos_of_nonneg_of_pos ha hx
  have hatpos : 0 < a + t := add_pos_of_nonneg_of_pos ha ht
  have hax : a + x ∈ Set.Ici (0 : ℝ) := haxpos.le
  have hat : a + t ∈ Set.Ici (0 : ℝ) := hatpos.le
  have hcont : ContinuousOn S (Set.Ici (0 : ℝ)) :=
    continuousOn_Ici_of_hasDerivWithinAt hS
  have hder :
      ∀ z ∈ interior (Set.Ici (0 : ℝ)),
        HasDerivWithinAt S (Sprime z) (interior (Set.Ici (0 : ℝ))) z := by
    intro z hz
    exact (hS z (interior_subset hz)).mono interior_subset
  have hmono : MonotoneOn S (Set.Ici (0 : ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg
      (convex_Ici (0 : ℝ)) hcont hder
      (fun z hz => (hSprime_pos z (interior_subset hz)).le)
  have hSpx : 0 ≤ Sprime (a + x) := (hSprime_pos (a + x) hax).le

  by_cases hsx0 : S (a + x) = 0
  · exact twoPointKernel_nonneg_of_left_zero ha hx.le ht.le hmono hSpx hsx0
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
        have hposD : ∀ z ∈ D, 0 < z := by
          intro z hz
          dsimp [D] at hz
          exact haxpos.trans_le hz.1
        have hSD : ∀ z ∈ D, HasDerivAt S (Sprime z) z := by
          intro z hz
          have hzpos := hposD z hz
          exact hasDerivAt_of_pos_of_hasDerivWithinAt_Ici hzpos (hS z hzpos.le)
        have hSprimeD : ∀ z ∈ D, HasDerivAt Sprime (Ssecond z) z := by
          intro z hz
          have hzpos := hposD z hz
          exact hasDerivAt_of_pos_of_hasDerivWithinAt_Ici hzpos (hSprime z hzpos.le)
        have haxD : a + x ∈ D := by
          dsimp [D]
          exact ⟨le_rfl, by linarith⟩
        have hatD : a + t ∈ D := by
          dsimp [D]
          exact ⟨by linarith, le_rfl⟩
        have hSnzD : ∀ z ∈ D, S z ≠ 0 := by
          intro z hz
          have hzI : z ∈ Set.Ici (0 : ℝ) := hsub hz
          have hm : S z ≤ S (a + t) := hmono hzI hat hz.2
          exact ne_of_lt (lt_of_le_of_lt hm hstneg)
        exact twoPointKernel_nonneg_of_curvature_on
          hD hSD hSprimeD hSnzD
          (fun z hz => hcurv z (hsub hz)) haxD hatD
          (div_pos_of_neg_of_neg hstneg hsxneg)
      · let D : Set ℝ := Set.Icc (a + t) (a + x)
        have hD : Convex ℝ D := by
          dsimp [D]
          exact convex_Icc _ _
        have hsub : D ⊆ Set.Ici (0 : ℝ) := by
          intro z hz
          dsimp [D] at hz
          exact hat.trans hz.1
        have hposD : ∀ z ∈ D, 0 < z := by
          intro z hz
          dsimp [D] at hz
          exact hatpos.trans_le hz.1
        have hSD : ∀ z ∈ D, HasDerivAt S (Sprime z) z := by
          intro z hz
          have hzpos := hposD z hz
          exact hasDerivAt_of_pos_of_hasDerivWithinAt_Ici hzpos (hS z hzpos.le)
        have hSprimeD : ∀ z ∈ D, HasDerivAt Sprime (Ssecond z) z := by
          intro z hz
          have hzpos := hposD z hz
          exact hasDerivAt_of_pos_of_hasDerivWithinAt_Ici hzpos (hSprime z hzpos.le)
        have haxD : a + x ∈ D := by
          dsimp [D]
          exact ⟨by linarith, le_rfl⟩
        have hatD : a + t ∈ D := by
          dsimp [D]
          exact ⟨le_rfl, by linarith⟩
        have hSnzD : ∀ z ∈ D, S z ≠ 0 := by
          intro z hz
          have hzI : z ∈ Set.Ici (0 : ℝ) := hsub hz
          have hm : S z ≤ S (a + x) := hmono hzI hax hz.2
          exact ne_of_lt (lt_of_le_of_lt hm hsxneg)
        exact twoPointKernel_nonneg_of_curvature_on
          hD hSD hSprimeD hSnzD
          (fun z hz => hcurv z (hsub hz)) haxD hatD
          (div_pos_of_neg_of_neg hstneg hsxneg)
    · have hxt : x ≤ t := by
        by_contra hnot
        have htx : t < x := lt_of_not_ge hnot
        have hm : S (a + t) ≤ S (a + x) := hmono hat hax (by linarith)
        linarith
      exact twoPointKernel_nonneg_of_left_nonpos_right_nonneg
        hSpx hxt hsxneg.le hstpos.le
  · rcases lt_or_gt_of_ne hst0 with hstneg | hstpos
    · have htx : t ≤ x := by
        by_contra hnot
        have hxt : x < t := lt_of_not_ge hnot
        have hm : S (a + x) ≤ S (a + t) := hmono hax hat (by linarith)
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
        have hposD : ∀ z ∈ D, 0 < z := by
          intro z hz
          dsimp [D] at hz
          exact haxpos.trans_le hz.1
        have hSD : ∀ z ∈ D, HasDerivAt S (Sprime z) z := by
          intro z hz
          have hzpos := hposD z hz
          exact hasDerivAt_of_pos_of_hasDerivWithinAt_Ici hzpos (hS z hzpos.le)
        have hSprimeD : ∀ z ∈ D, HasDerivAt Sprime (Ssecond z) z := by
          intro z hz
          have hzpos := hposD z hz
          exact hasDerivAt_of_pos_of_hasDerivWithinAt_Ici hzpos (hSprime z hzpos.le)
        have haxD : a + x ∈ D := by
          dsimp [D]
          exact ⟨le_rfl, by linarith⟩
        have hatD : a + t ∈ D := by
          dsimp [D]
          exact ⟨by linarith, le_rfl⟩
        have hSnzD : ∀ z ∈ D, S z ≠ 0 := by
          intro z hz
          have hzI : z ∈ Set.Ici (0 : ℝ) := hsub hz
          have hm : S (a + x) ≤ S z := hmono hax hzI hz.1
          exact ne_of_gt (lt_of_lt_of_le hsxpos hm)
        exact twoPointKernel_nonneg_of_curvature_on
          hD hSD hSprimeD hSnzD
          (fun z hz => hcurv z (hsub hz)) haxD hatD
          (div_pos hstpos hsxpos)
      · let D : Set ℝ := Set.Icc (a + t) (a + x)
        have hD : Convex ℝ D := by
          dsimp [D]
          exact convex_Icc _ _
        have hsub : D ⊆ Set.Ici (0 : ℝ) := by
          intro z hz
          dsimp [D] at hz
          exact hat.trans hz.1
        have hposD : ∀ z ∈ D, 0 < z := by
          intro z hz
          dsimp [D] at hz
          exact hatpos.trans_le hz.1
        have hSD : ∀ z ∈ D, HasDerivAt S (Sprime z) z := by
          intro z hz
          have hzpos := hposD z hz
          exact hasDerivAt_of_pos_of_hasDerivWithinAt_Ici hzpos (hS z hzpos.le)
        have hSprimeD : ∀ z ∈ D, HasDerivAt Sprime (Ssecond z) z := by
          intro z hz
          have hzpos := hposD z hz
          exact hasDerivAt_of_pos_of_hasDerivWithinAt_Ici hzpos (hSprime z hzpos.le)
        have haxD : a + x ∈ D := by
          dsimp [D]
          exact ⟨by linarith, le_rfl⟩
        have hatD : a + t ∈ D := by
          dsimp [D]
          exact ⟨le_rfl, by linarith⟩
        have hSnzD : ∀ z ∈ D, S z ≠ 0 := by
          intro z hz
          have hzI : z ∈ Set.Ici (0 : ℝ) := hsub hz
          have hm : S (a + t) ≤ S z := hmono hat hzI hz.1
          exact ne_of_gt (lt_of_lt_of_le hstpos hm)
        exact twoPointKernel_nonneg_of_curvature_on
          hD hSD hSprimeD hSnzD
          (fun z hz => hcurv z (hsub hz)) haxD hatD
          (div_pos hstpos hsxpos)

end ScoreCurvatureStarOrder
