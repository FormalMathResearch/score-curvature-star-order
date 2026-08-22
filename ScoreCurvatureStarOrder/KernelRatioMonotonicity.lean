import Mathlib
import ScoreCurvatureStarOrder.HalfLineRegularity

namespace ScoreCurvatureStarOrder

open Set

/-- First spatial step in manuscript Theorem 5.4.

For two ordered nonnegative shifts `a₁ < a₂`, the kernel ratio

`x ↦ theta (a₂ + x) / theta (a₁ + x)`

is strictly decreasing on `(0,∞)` whenever the score `S` has strictly positive
derivative on the positive half-line.

The proof keeps the one-sided half-line regularity used throughout the project.
First `S' > 0` gives strict monotonicity of `S` on `[0,∞)`.  Differentiating
the ratio at `x > 0` gives

`r'(x) = r(x) * (S (a₁+x) - S (a₂+x)) < 0`,

because the kernel ratio is positive and `S (a₁+x) < S (a₂+x)`. -/
theorem powerWeightedShift_thetaRatio_strictAntiOn_Ioi_within
    {theta S Sprime : ℝ → ℝ} {a₁ a₂ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₁₂ : a₁ < a₂)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    StrictAntiOn
      (fun x : ℝ => theta (a₂ + x) / theta (a₁ + x))
      (Set.Ioi (0 : ℝ)) := by
  have ha₂ : 0 ≤ a₂ := ha₁.trans ha₁₂.le

  have hSmono : StrictMonoOn S (Set.Ici (0 : ℝ)) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (f' := Sprime)
      (convex_Ici (0 : ℝ))
      (continuousOn_Ici_of_hasDerivWithinAt hS) ?_ ?_
    · intro z hz
      exact (hS z (interior_subset hz)).mono interior_subset
    · intro z hz
      exact hSprime_pos z (interior_subset hz)

  have hIoi_subset : Set.Ioi (0 : ℝ) ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    change 0 < x at hx
    exact hx.le

  have htheta₁_cont :
      ContinuousOn (fun x : ℝ => theta (a₁ + x)) (Set.Ioi (0 : ℝ)) := by
    exact
      (continuousOn_shift_Ici_of_hasDerivWithinAt ha₁ htheta_deriv).mono
        hIoi_subset
  have htheta₂_cont :
      ContinuousOn (fun x : ℝ => theta (a₂ + x)) (Set.Ioi (0 : ℝ)) := by
    exact
      (continuousOn_shift_Ici_of_hasDerivWithinAt ha₂ htheta_deriv).mono
        hIoi_subset

  have hratio_cont :
      ContinuousOn
        (fun x : ℝ => theta (a₂ + x) / theta (a₁ + x))
        (Set.Ioi (0 : ℝ)) := by
    refine htheta₂_cont.div htheta₁_cont ?_
    intro x hx
    have hax₁ : 0 ≤ a₁ + x := add_nonneg ha₁ hx.le
    exact (htheta_pos (a₁ + x) hax₁).ne'

  have hratio_deriv :
      ∀ x ∈ interior (Set.Ioi (0 : ℝ)),
        HasDerivWithinAt
          (fun y : ℝ => theta (a₂ + y) / theta (a₁ + y))
          (((-S (a₂ + x) * theta (a₂ + x)) * theta (a₁ + x) -
              theta (a₂ + x) * (-S (a₁ + x) * theta (a₁ + x))) /
            theta (a₁ + x) ^ 2)
          (interior (Set.Ioi (0 : ℝ))) x := by
    intro x hx
    have hxpos : 0 < x := by
      exact (interior_subset hx : x ∈ Set.Ioi (0 : ℝ))
    have hax₁ : 0 < a₁ + x := add_pos_of_nonneg_of_pos ha₁ hxpos
    have hax₂ : 0 < a₂ + x := add_pos_of_nonneg_of_pos ha₂ hxpos
    have hd₁ :=
      hasDerivAt_shift_of_pos_of_hasDerivWithinAt_Ici
        (f := theta) (f' := fun z => -S z * theta z)
        (a := a₁) (x := x) hax₁ htheta_deriv
    have hd₂ :=
      hasDerivAt_shift_of_pos_of_hasDerivWithinAt_Ici
        (f := theta) (f' := fun z => -S z * theta z)
        (a := a₂) (x := x) hax₂ htheta_deriv
    have ht₁ : 0 < theta (a₁ + x) := htheta_pos (a₁ + x) hax₁.le
    exact (hd₂.div hd₁ ht₁.ne').hasDerivWithinAt

  have hratio_deriv_neg :
      ∀ x ∈ interior (Set.Ioi (0 : ℝ)),
        (((-S (a₂ + x) * theta (a₂ + x)) * theta (a₁ + x) -
              theta (a₂ + x) * (-S (a₁ + x) * theta (a₁ + x))) /
            theta (a₁ + x) ^ 2) < 0 := by
    intro x hx
    have hxpos : 0 < x := by
      exact (interior_subset hx : x ∈ Set.Ioi (0 : ℝ))
    have hax₁_nonneg : 0 ≤ a₁ + x := add_nonneg ha₁ hxpos.le
    have hax₂_nonneg : 0 ≤ a₂ + x := add_nonneg ha₂ hxpos.le
    have harg_lt : a₁ + x < a₂ + x := by linarith
    have hSlt : S (a₁ + x) < S (a₂ + x) :=
      hSmono hax₁_nonneg hax₂_nonneg harg_lt
    have ht₁ : 0 < theta (a₁ + x) :=
      htheta_pos (a₁ + x) hax₁_nonneg
    have ht₂ : 0 < theta (a₂ + x) :=
      htheta_pos (a₂ + x) hax₂_nonneg
    have hnum_eq :
        (-S (a₂ + x) * theta (a₂ + x)) * theta (a₁ + x) -
            theta (a₂ + x) * (-S (a₁ + x) * theta (a₁ + x)) =
          (theta (a₂ + x) * theta (a₁ + x)) *
            (S (a₁ + x) - S (a₂ + x)) := by
      ring
    rw [hnum_eq]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg
        (mul_pos ht₂ ht₁)
        (sub_neg.mpr hSlt))
      (pow_pos ht₁ 2)

  exact strictAntiOn_of_hasDerivWithinAt_neg
    (convex_Ioi (0 : ℝ)) hratio_cont hratio_deriv hratio_deriv_neg

end ScoreCurvatureStarOrder
