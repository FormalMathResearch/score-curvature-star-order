import Mathlib
import ScoreCurvatureStarOrder.Entropy

namespace ScoreCurvatureStarOrder

noncomputable def twoPointKernel (S : ℝ → ℝ) (a x t : ℝ) : ℝ :=
  deriv S (a + x) * (t - x) * S (a + t) -
    S (a + x) * (S (a + t) - S (a + x))

theorem twoPointKernel_nonneg_of_log_ratio {S : ℝ → ℝ} {a x t : ℝ}
    (hx : S (a + x) ≠ 0)
    (hr : 0 < S (a + t) / S (a + x))
    (hlog :
      Real.log (S (a + t) / S (a + x)) ≤
        (deriv S (a + x) / S (a + x)) * (t - x)) :
    0 ≤ twoPointKernel S a x t := by
  let r : ℝ := S (a + t) / S (a + x)
  have hent : 0 ≤ 1 - r + r * Real.log r := by
    exact entropy_nonneg (by simpa [r] using hr)
  have hratio : r - 1 ≤ r * Real.log r := by
    linarith
  have hmul :
      r * Real.log r ≤
        r * ((deriv S (a + x) / S (a + x)) * (t - x)) := by
    apply mul_le_mul_of_nonneg_left
    · simpa [r] using hlog
    · exact (by simpa [r] using hr.le)
  have hnorm :
      r - 1 ≤ r * ((deriv S (a + x) / S (a + x)) * (t - x)) :=
    hratio.trans hmul
  have hnonneg :
      0 ≤ (S (a + x)) ^ 2 *
        (r * ((deriv S (a + x) / S (a + x)) * (t - x)) - (r - 1)) := by
    exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hnorm)
  have hid :
      (S (a + x)) ^ 2 *
          (r * ((deriv S (a + x) / S (a + x)) * (t - x)) - (r - 1)) =
        twoPointKernel S a x t := by
    dsimp [r, twoPointKernel]
    field_simp [hx]
    <;> ring
  rw [← hid]
  exact hnonneg

theorem twoPointKernel_nonneg_of_right_zero {S : ℝ → ℝ} {a x t : ℝ}
    (ht : S (a + t) = 0) :
    0 ≤ twoPointKernel S a x t := by
  simpa [twoPointKernel, ht, pow_two] using sq_nonneg (S (a + x))

theorem twoPointKernel_nonneg_of_left_zero {S : ℝ → ℝ} {a x t : ℝ}
    (ha : 0 ≤ a) (hx0 : 0 ≤ x) (ht0 : 0 ≤ t)
    (hmono : MonotoneOn S (Set.Ici 0))
    (hderiv : 0 ≤ deriv S (a + x))
    (hx : S (a + x) = 0) :
    0 ≤ twoPointKernel S a x t := by
  have hax : a + x ∈ Set.Ici (0 : ℝ) := by
    exact add_nonneg ha hx0
  have hat : a + t ∈ Set.Ici (0 : ℝ) := by
    exact add_nonneg ha ht0
  have hprod : 0 ≤ (t - x) * S (a + t) := by
    rcases le_total x t with hxt | htx
    · have hs : 0 ≤ S (a + t) := by
        have hm := hmono hax hat (by linarith : a + x ≤ a + t)
        simpa [hx] using hm
      exact mul_nonneg (sub_nonneg.mpr hxt) hs
    · have hs : S (a + t) ≤ 0 := by
        have hm := hmono hat hax (by linarith : a + t ≤ a + x)
        simpa [hx] using hm
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr htx) hs
  have hmain : 0 ≤ deriv S (a + x) * ((t - x) * S (a + t)) :=
    mul_nonneg hderiv hprod
  simpa [twoPointKernel, hx, mul_assoc] using hmain

theorem twoPointKernel_nonneg_of_left_nonpos_right_nonneg
    {S : ℝ → ℝ} {a x t : ℝ}
    (hderiv : 0 ≤ deriv S (a + x))
    (hxt : x ≤ t)
    (hsx : S (a + x) ≤ 0)
    (hst : 0 ≤ S (a + t)) :
    0 ≤ twoPointKernel S a x t := by
  have hfirst : 0 ≤ deriv S (a + x) * (t - x) * S (a + t) :=
    mul_nonneg (mul_nonneg hderiv (sub_nonneg.mpr hxt)) hst
  have hdiff : 0 ≤ S (a + t) - S (a + x) := by
    linarith
  have hsecond : S (a + x) * (S (a + t) - S (a + x)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hsx hdiff
  unfold twoPointKernel
  linarith

theorem twoPointKernel_nonneg_of_left_nonneg_right_nonpos
    {S : ℝ → ℝ} {a x t : ℝ}
    (hderiv : 0 ≤ deriv S (a + x))
    (htx : t ≤ x)
    (hsx : 0 ≤ S (a + x))
    (hst : S (a + t) ≤ 0) :
    0 ≤ twoPointKernel S a x t := by
  have hpair : deriv S (a + x) * (t - x) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hderiv (sub_nonpos.mpr htx)
  have hfirst : 0 ≤ deriv S (a + x) * (t - x) * S (a + t) :=
    mul_nonneg_of_nonpos_of_nonpos hpair hst
  have hdiff : S (a + t) - S (a + x) ≤ 0 := by
    linarith
  have hsecond : S (a + x) * (S (a + t) - S (a + x)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hsx hdiff
  unfold twoPointKernel
  linarith

end ScoreCurvatureStarOrder
