import Mathlib
import ScoreCurvatureStarOrder.Density
import ScoreCurvatureStarOrder.PowerLogMoments

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- The logarithm is integrable against the normalized power-weighted shifted
density.  This is the normalized-density form of the already verified first
logarithmic power moment and is the endpoint-control interface needed for
quantile transport. -/
theorem powerWeightedShift_log_density_integrableOn_Ioi_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    IntegrableOn
      (fun x : ℝ => Real.log x * powerWeightedShiftDensity theta a p x)
      (Set.Ioi (0 : ℝ)) := by
  have hraw := powerWeightedShift_log_integrableOn_Ioi_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p)
    ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hscaled := hraw.const_mul (powerWeightedShiftMoment theta a p)⁻¹
  refine IntegrableOn.congr_fun hscaled ?_ measurableSet_Ioi
  intro x hx
  dsimp [powerWeightedShiftDensity]
  rw [div_eq_mul_inv]
  ring

/-- The squared logarithm is integrable against the normalized power-weighted
shifted density.  This is the normalized-density form of the already verified
second logarithmic power moment. -/
theorem powerWeightedShift_log_sq_density_integrableOn_Ioi_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    IntegrableOn
      (fun x : ℝ => (Real.log x) ^ 2 * powerWeightedShiftDensity theta a p x)
      (Set.Ioi (0 : ℝ)) := by
  have hraw := powerWeightedShift_log_sq_integrableOn_Ioi_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p)
    ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hscaled := hraw.const_mul (powerWeightedShiftMoment theta a p)⁻¹
  refine IntegrableOn.congr_fun hscaled ?_ measurableSet_Ioi
  intro x hx
  dsimp [powerWeightedShiftDensity]
  rw [div_eq_mul_inv]
  ring

end ScoreCurvatureStarOrder
