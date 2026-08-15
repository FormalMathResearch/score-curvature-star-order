import Mathlib
import ScoreCurvatureStarOrder.Density

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- Second step in manuscript Theorem 5.4: the ratio of normalization moments is
an expectation of the spatial kernel ratio under the earlier shifted density.

For `0 ≤ a₁ < a₂` and `p > -1`,

`M_p(a₂) / M_p(a₁) = E_{p,a₁}[theta(a₂+X) / theta(a₁+X)]`.

The proof is purely algebraic.  On `(0,∞)` the positive factor
`theta (a₁ + x)` cancels against the same factor in the normalized density;
then the constant `M_p(a₁)⁻¹` is pulled out of the integral. -/
theorem powerWeightedShift_momentRatio_eq_thetaRatio_expectation_within
    {theta S Sprime : ℝ → ℝ} {a₁ a₂ p : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₁₂ : a₁ < a₂) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    powerWeightedShiftMoment theta a₂ p /
        powerWeightedShiftMoment theta a₁ p =
      ∫ x : ℝ in Set.Ioi 0,
        (theta (a₂ + x) / theta (a₁ + x)) *
          powerWeightedShiftDensity theta a₁ p x := by
  have hM₁pos : 0 < powerWeightedShiftMoment theta a₁ p :=
    powerWeightedShiftMoment_pos_within
      ha₁ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hM₁ne : powerWeightedShiftMoment theta a₁ p ≠ 0 := hM₁pos.ne'

  have hexpectation :
      (∫ x : ℝ in Set.Ioi 0,
          (theta (a₂ + x) / theta (a₁ + x)) *
            powerWeightedShiftDensity theta a₁ p x) =
        powerWeightedShiftMoment theta a₂ p /
          powerWeightedShiftMoment theta a₁ p := by
    calc
      (∫ x : ℝ in Set.Ioi 0,
          (theta (a₂ + x) / theta (a₁ + x)) *
            powerWeightedShiftDensity theta a₁ p x) =
          ∫ x : ℝ in Set.Ioi 0,
            (powerWeightedShiftMoment theta a₁ p)⁻¹ *
              (x ^ p * theta (a₂ + x)) := by
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro x hx
        change 0 < x at hx
        have hax₁ : 0 ≤ a₁ + x := add_nonneg ha₁ hx.le
        have ht₁ : theta (a₁ + x) ≠ 0 :=
          (htheta_pos (a₁ + x) hax₁).ne'
        dsimp [powerWeightedShiftDensity]
        field_simp [ht₁, hM₁ne]
        <;> ring
      _ = (powerWeightedShiftMoment theta a₁ p)⁻¹ *
          ∫ x : ℝ in Set.Ioi 0, x ^ p * theta (a₂ + x) := by
        rw [integral_const_mul]
      _ = (powerWeightedShiftMoment theta a₁ p)⁻¹ *
          powerWeightedShiftMoment theta a₂ p := by
        rfl
      _ = powerWeightedShiftMoment theta a₂ p /
          powerWeightedShiftMoment theta a₁ p := by
        rw [div_eq_mul_inv]
        ring

  exact hexpectation.symm

end ScoreCurvatureStarOrder
