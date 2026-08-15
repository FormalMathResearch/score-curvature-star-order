import Mathlib
import ScoreCurvatureStarOrder.LogDensityIntegrability

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Topology

/-- As the upper cutoff tends to `+∞`, the finite interval integral of `log x`
against the normalized power-weighted shifted density converges to the full
half-line log moment.  This is a direct improper-integral consequence of the
already verified normalized-density integrability. -/
theorem powerWeightedShift_log_density_intervalIntegral_tendsto_Ioi_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    Tendsto
      (fun R : ℝ => ∫ x : ℝ in 0..R,
        Real.log x * powerWeightedShiftDensity theta a p x)
      atTop
      (𝓝 (∫ x : ℝ in Set.Ioi 0,
        Real.log x * powerWeightedShiftDensity theta a p x)) := by
  have hint := powerWeightedShift_log_density_integrableOn_Ioi_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p)
    ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  simpa using
    (MeasureTheory.intervalIntegral_tendsto_integral_Ioi
      (μ := volume)
      (f := fun x : ℝ =>
        Real.log x * powerWeightedShiftDensity theta a p x)
      (a := (0 : ℝ)) hint tendsto_id)

/-- The squared-log analogue of
`powerWeightedShift_log_density_intervalIntegral_tendsto_Ioi_within`. -/
theorem powerWeightedShift_log_sq_density_intervalIntegral_tendsto_Ioi_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    Tendsto
      (fun R : ℝ => ∫ x : ℝ in 0..R,
        (Real.log x) ^ 2 * powerWeightedShiftDensity theta a p x)
      atTop
      (𝓝 (∫ x : ℝ in Set.Ioi 0,
        (Real.log x) ^ 2 * powerWeightedShiftDensity theta a p x)) := by
  have hint := powerWeightedShift_log_sq_density_integrableOn_Ioi_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p)
    ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  simpa using
    (MeasureTheory.intervalIntegral_tendsto_integral_Ioi
      (μ := volume)
      (f := fun x : ℝ =>
        (Real.log x) ^ 2 * powerWeightedShiftDensity theta a p x)
      (a := (0 : ℝ)) hint tendsto_id)

end ScoreCurvatureStarOrder
