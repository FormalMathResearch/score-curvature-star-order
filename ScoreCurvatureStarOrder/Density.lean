import Mathlib
import ScoreCurvatureStarOrder.Moments

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- The normalized density of the power-weighted shifted kernel. -/
noncomputable def powerWeightedShiftDensity (theta : ℝ → ℝ) (a p x : ℝ) : ℝ :=
  x ^ p * theta (a + x) / powerWeightedShiftMoment theta a p

/-- The normalized power-weighted shifted density is integrable on the positive
half-line under the mathematically natural one-sided regularity assumptions. -/
theorem powerWeightedShiftDensity_integrableOn_Ioi_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    IntegrableOn (powerWeightedShiftDensity theta a p) (Set.Ioi (0 : ℝ)) := by
  have hraw :
      IntegrableOn (fun x : ℝ => x ^ p * theta (a + x)) (Set.Ioi (0 : ℝ)) :=
    powerWeightedShift_integrableOn_Ioi_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hscaled := hraw.const_mul (powerWeightedShiftMoment theta a p)⁻¹
  refine IntegrableOn.congr_fun hscaled ?_ measurableSet_Ioi
  intro x hx
  dsimp [powerWeightedShiftDensity]
  rw [div_eq_mul_inv]
  ring

/-- Backward-compatible integrability wrapper for the former two-sided assumptions. -/
theorem powerWeightedShiftDensity_integrableOn_Ioi
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    IntegrableOn (powerWeightedShiftDensity theta a p) (Set.Ioi (0 : ℝ)) := by
  exact powerWeightedShiftDensity_integrableOn_Ioi_within
    ha hp htheta_pos
    (fun z hz => (htheta_deriv z hz).hasDerivWithinAt)
    htheta_int
    (fun z hz => (hS z hz).hasDerivWithinAt)
    hSprime_pos

/-- The normalized power-weighted shifted kernel integrates to one on the positive
half-line under one-sided differentiability at the boundary. -/
theorem powerWeightedShiftDensity_integral_eq_one_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    (∫ x : ℝ in Set.Ioi 0, powerWeightedShiftDensity theta a p x) = 1 := by
  have hMpos : 0 < powerWeightedShiftMoment theta a p :=
    powerWeightedShiftMoment_pos_within
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

/-- Backward-compatible wrapper for the former two-sided assumptions. -/
theorem powerWeightedShiftDensity_integral_eq_one
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    (∫ x : ℝ in Set.Ioi 0, powerWeightedShiftDensity theta a p x) = 1 := by
  exact powerWeightedShiftDensity_integral_eq_one_within
    ha hp htheta_pos
    (fun z hz => (htheta_deriv z hz).hasDerivWithinAt)
    htheta_int
    (fun z hz => (hS z hz).hasDerivWithinAt)
    hSprime_pos

end ScoreCurvatureStarOrder
