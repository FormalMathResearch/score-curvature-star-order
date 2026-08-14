import Mathlib
import ScoreCurvatureStarOrder.Moments

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- The normalized density of the power-weighted shifted kernel. -/
noncomputable def powerWeightedShiftDensity (theta : ℝ → ℝ) (a p x : ℝ) : ℝ :=
  x ^ p * theta (a + x) / powerWeightedShiftMoment theta a p

/-- The normalized power-weighted shifted kernel integrates to one on the positive half-line. -/
theorem powerWeightedShiftDensity_integral_eq_one
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    (∫ x : ℝ in Set.Ioi 0, powerWeightedShiftDensity theta a p x) = 1 := by
  have hMpos : 0 < powerWeightedShiftMoment theta a p :=
    powerWeightedShiftMoment_pos
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hMne : powerWeightedShiftMoment theta a p ≠ 0 := hMpos.ne'
  calc
    (∫ x : ℝ in Set.Ioi 0, powerWeightedShiftDensity theta a p x) =
        ∫ x : ℝ in Set.Ioi 0,
          (powerWeightedShiftMoment theta a p)⁻¹ * (x ^ p * theta (a + x)) := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro x hx
      dsimp [powerWeightedShiftDensity]
      rw [div_eq_mul_inv]
      ring
    _ = (powerWeightedShiftMoment theta a p)⁻¹ *
        ∫ x : ℝ in Set.Ioi 0, x ^ p * theta (a + x) := by
      rw [integral_const_mul]
    _ = (powerWeightedShiftMoment theta a p)⁻¹ *
        powerWeightedShiftMoment theta a p := by
      rw [powerWeightedShiftMoment]
    _ = 1 := inv_mul_cancel₀ hMne

end ScoreCurvatureStarOrder
