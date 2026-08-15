import Mathlib
import ScoreCurvatureStarOrder.Density
import ScoreCurvatureStarOrder.PowerMomentLogSecondDerivative

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- The variance of `log X` under the normalized power-weighted shifted density.
This is the manuscript quantity `Var_{p,a}(log X)`, written directly in terms
of the already verified density rather than by introducing a second probability
measure representation. -/
noncomputable def powerWeightedShiftLogVariance
    (theta : ℝ → ℝ) (a p : ℝ) : ℝ :=
  (∫ x : ℝ in Set.Ioi 0,
      (Real.log x) ^ 2 * powerWeightedShiftDensity theta a p x) -
    (∫ x : ℝ in Set.Ioi 0,
      Real.log x * powerWeightedShiftDensity theta a p x) ^ 2

/-- Under the project hypotheses, the log-variance under the normalized density
is exactly the quadratic moment expression appearing in the second power
derivative of `log M_p(a)`:

`Var_{p,a}(log X) = (Q_p(a) M_p(a) - L_p(a)^2) / M_p(a)^2`.

Here `L_p(a) = ∫ x^p log(x) theta(a+x) dx` and
`Q_p(a) = ∫ x^p (log x)^2 theta(a+x) dx`. -/
theorem powerWeightedShift_logVariance_eq_moment_formula_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    powerWeightedShiftLogVariance theta a p =
      (((∫ x : ℝ in Set.Ioi 0,
          x ^ p * (Real.log x) ^ 2 * theta (a + x)) *
          powerWeightedShiftMoment theta a p -
        (∫ x : ℝ in Set.Ioi 0,
          x ^ p * Real.log x * theta (a + x)) ^ 2) /
        (powerWeightedShiftMoment theta a p) ^ 2) := by
  have hMpos : 0 < powerWeightedShiftMoment theta a p :=
    powerWeightedShiftMoment_pos_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hMne : powerWeightedShiftMoment theta a p ≠ 0 := hMpos.ne'

  have hmean :
      (∫ x : ℝ in Set.Ioi 0,
          Real.log x * powerWeightedShiftDensity theta a p x) =
        (∫ x : ℝ in Set.Ioi 0,
          x ^ p * Real.log x * theta (a + x)) /
          powerWeightedShiftMoment theta a p := by
    calc
      (∫ x : ℝ in Set.Ioi 0,
          Real.log x * powerWeightedShiftDensity theta a p x) =
          ∫ x : ℝ in Set.Ioi 0,
            (powerWeightedShiftMoment theta a p)⁻¹ *
              (x ^ p * Real.log x * theta (a + x)) := by
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro x hx
        dsimp [powerWeightedShiftDensity]
        rw [div_eq_mul_inv]
        ring
      _ = (powerWeightedShiftMoment theta a p)⁻¹ *
          ∫ x : ℝ in Set.Ioi 0,
            x ^ p * Real.log x * theta (a + x) := by
        rw [integral_const_mul]
      _ = (∫ x : ℝ in Set.Ioi 0,
          x ^ p * Real.log x * theta (a + x)) /
          powerWeightedShiftMoment theta a p := by
        rw [div_eq_mul_inv]
        ring

  have hsecond :
      (∫ x : ℝ in Set.Ioi 0,
          (Real.log x) ^ 2 * powerWeightedShiftDensity theta a p x) =
        (∫ x : ℝ in Set.Ioi 0,
          x ^ p * (Real.log x) ^ 2 * theta (a + x)) /
          powerWeightedShiftMoment theta a p := by
    calc
      (∫ x : ℝ in Set.Ioi 0,
          (Real.log x) ^ 2 * powerWeightedShiftDensity theta a p x) =
          ∫ x : ℝ in Set.Ioi 0,
            (powerWeightedShiftMoment theta a p)⁻¹ *
              (x ^ p * (Real.log x) ^ 2 * theta (a + x)) := by
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro x hx
        dsimp [powerWeightedShiftDensity]
        rw [div_eq_mul_inv]
        ring
      _ = (powerWeightedShiftMoment theta a p)⁻¹ *
          ∫ x : ℝ in Set.Ioi 0,
            x ^ p * (Real.log x) ^ 2 * theta (a + x) := by
        rw [integral_const_mul]
      _ = (∫ x : ℝ in Set.Ioi 0,
          x ^ p * (Real.log x) ^ 2 * theta (a + x)) /
          powerWeightedShiftMoment theta a p := by
        rw [div_eq_mul_inv]
        ring

  unfold powerWeightedShiftLogVariance
  rw [hmean, hsecond]
  field_simp [hMne]
  ring

end ScoreCurvatureStarOrder
