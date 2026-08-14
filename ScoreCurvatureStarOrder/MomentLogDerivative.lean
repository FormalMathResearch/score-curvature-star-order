import Mathlib
import ScoreCurvatureStarOrder.Density
import ScoreCurvatureStarOrder.MomentShiftDerivative

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- At every interior shift `a > 0`, the logarithmic derivative of the normalization
moment is minus the score mean under the normalized shifted density. -/
theorem powerWeightedShiftMoment_log_hasDerivAt
    {theta S Sprime Ssecond : ℝ → ℝ} {a p : ℝ}
    (ha : 0 < a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt Sprime (Ssecond z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ), Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    HasDerivAt
      (fun b : ℝ => Real.log (powerWeightedShiftMoment theta b p))
      (-(∫ x : ℝ in Set.Ioi 0,
        S (a + x) * powerWeightedShiftDensity theta a p x)) a := by
  have hMderiv := powerWeightedShiftMoment_hasDerivAt
    (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
    (a := a) (p := p) ha hp htheta_pos htheta_deriv htheta_int hS hSprime
    hSprime_pos hcurv
  have hMpos : 0 < powerWeightedShiftMoment theta a p :=
    powerWeightedShiftMoment_pos
      ha.le hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hlog := hMderiv.log hMpos.ne'
  have hcoef :
      (∫ x : ℝ in Set.Ioi 0,
        x ^ p * (-S (a + x) * theta (a + x))) /
          powerWeightedShiftMoment theta a p =
      -(∫ x : ℝ in Set.Ioi 0,
        S (a + x) * powerWeightedShiftDensity theta a p x) := by
    calc
      (∫ x : ℝ in Set.Ioi 0,
          x ^ p * (-S (a + x) * theta (a + x))) /
            powerWeightedShiftMoment theta a p =
          (powerWeightedShiftMoment theta a p)⁻¹ *
            ∫ x : ℝ in Set.Ioi 0,
              x ^ p * (-S (a + x) * theta (a + x)) := by
        rw [div_eq_mul_inv]
        ring
      _ = ∫ x : ℝ in Set.Ioi 0,
          (powerWeightedShiftMoment theta a p)⁻¹ *
            (x ^ p * (-S (a + x) * theta (a + x))) := by
        rw [integral_const_mul]
      _ = ∫ x : ℝ in Set.Ioi 0,
          -(S (a + x) * powerWeightedShiftDensity theta a p x) := by
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro x hx
        dsimp [powerWeightedShiftDensity]
        rw [div_eq_mul_inv]
        ring
      _ = -(∫ x : ℝ in Set.Ioi 0,
          S (a + x) * powerWeightedShiftDensity theta a p x) := by
        rw [integral_neg]
  rw [hcoef] at hlog
  exact hlog

end ScoreCurvatureStarOrder
