import Mathlib
import ScoreCurvatureStarOrder.Density
import ScoreCurvatureStarOrder.IntegrationByParts

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- The score observable is integrable under the normalized power-weighted shifted
density, assuming differentiability only within the closed positive half-line. -/
theorem powerWeightedShift_score_expectation_integrableOn_Ioi_within
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
      (fun x : ℝ => (x * S (a + x)) * powerWeightedShiftDensity theta a p x)
      (Set.Ioi (0 : ℝ)) := by
  have hscore :
      IntegrableOn
        (fun x : ℝ => x ^ (p + 1) * S (a + x) * theta (a + x))
        (Set.Ioi (0 : ℝ)) :=
    powerWeightedShift_score_integrableOn_Ioi_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hscaled := hscore.const_mul (powerWeightedShiftMoment theta a p)⁻¹
  refine IntegrableOn.congr_fun hscaled ?_ measurableSet_Ioi
  intro x hx
  have hrpow_add : x ^ (p + 1) = x ^ p * x := by
    simpa using Real.rpow_add hx p 1
  dsimp [powerWeightedShiftDensity]
  rw [hrpow_add, div_eq_mul_inv]
  ring

/-- Backward-compatible wrapper for the former two-sided assumptions. -/
theorem powerWeightedShift_score_expectation_integrableOn_Ioi
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    IntegrableOn
      (fun x : ℝ => (x * S (a + x)) * powerWeightedShiftDensity theta a p x)
      (Set.Ioi (0 : ℝ)) := by
  exact powerWeightedShift_score_expectation_integrableOn_Ioi_within
    ha hp htheta_pos
    (fun z hz => (htheta_deriv z hz).hasDerivWithinAt)
    htheta_int
    (fun z hz => (hS z hz).hasDerivWithinAt)
    hSprime_pos

/-- Under the normalized power-weighted shifted density,
`E[X S(a+X)] = p+1`, with only one-sided boundary differentiability. -/
theorem powerWeightedShift_score_expectation_identity_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    (∫ x : ℝ in Set.Ioi 0,
        (x * S (a + x)) * powerWeightedShiftDensity theta a p x) = p + 1 := by
  have hMpos : 0 < powerWeightedShiftMoment theta a p :=
    powerWeightedShiftMoment_pos_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hMne : powerWeightedShiftMoment theta a p ≠ 0 := hMpos.ne'
  have hscore := powerWeightedShift_score_moment_identity_within
    (theta := theta) (S := S) (Sprime := Sprime) (a := a) (p := p)
    ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  calc
    (∫ x : ℝ in Set.Ioi 0,
        (x * S (a + x)) * powerWeightedShiftDensity theta a p x) =
        ∫ x : ℝ in Set.Ioi 0,
          (powerWeightedShiftMoment theta a p)⁻¹ *
            (x ^ (p + 1) * S (a + x) * theta (a + x)) := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro x hx
      have hrpow_add : x ^ (p + 1) = x ^ p * x := by
        simpa using Real.rpow_add hx p 1
      dsimp [powerWeightedShiftDensity]
      rw [hrpow_add, div_eq_mul_inv]
      ring
    _ = (powerWeightedShiftMoment theta a p)⁻¹ *
        ∫ x : ℝ in Set.Ioi 0,
          x ^ (p + 1) * S (a + x) * theta (a + x) := by
      rw [integral_const_mul]
    _ = (powerWeightedShiftMoment theta a p)⁻¹ *
        ((p + 1) * ∫ x : ℝ in Set.Ioi 0, x ^ p * theta (a + x)) := by
      rw [hscore]
    _ = (powerWeightedShiftMoment theta a p)⁻¹ *
        ((p + 1) * powerWeightedShiftMoment theta a p) := by
      rw [powerWeightedShiftMoment]
    _ = p + 1 := by
      calc
        (powerWeightedShiftMoment theta a p)⁻¹ *
            ((p + 1) * powerWeightedShiftMoment theta a p) =
            ((powerWeightedShiftMoment theta a p)⁻¹ *
              powerWeightedShiftMoment theta a p) * (p + 1) := by ring
        _ = p + 1 := by rw [inv_mul_cancel₀ hMne, one_mul]

/-- Backward-compatible wrapper for the former two-sided assumptions. -/
theorem powerWeightedShift_score_expectation_identity
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    (∫ x : ℝ in Set.Ioi 0,
        (x * S (a + x)) * powerWeightedShiftDensity theta a p x) = p + 1 := by
  exact powerWeightedShift_score_expectation_identity_within
    ha hp htheta_pos
    (fun z hz => (htheta_deriv z hz).hasDerivWithinAt)
    htheta_int
    (fun z hz => (hS z hz).hasDerivWithinAt)
    hSprime_pos

end ScoreCurvatureStarOrder
