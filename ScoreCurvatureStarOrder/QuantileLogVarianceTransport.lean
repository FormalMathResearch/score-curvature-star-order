import Mathlib
import ScoreCurvatureStarOrder.GlobalQuantileLogTransport
import ScoreCurvatureStarOrder.LogVariance

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- Variance of the logarithm of the canonical quantile on the uniform
probability interval `(0,1)`.

This is the quantile-side representation used in the star-order proof of
monotonicity of `Var_{p,a}(log X)` with respect to the shift. -/
noncomputable def powerWeightedShiftLogQuantileVariance
    (theta : ℝ → ℝ) (a p : ℝ) : ℝ :=
  (∫ u : ℝ in Set.Ioo (0 : ℝ) 1,
      (Real.log (powerWeightedShiftQuantile theta a p u)) ^ 2) -
    (∫ u : ℝ in Set.Ioo (0 : ℝ) 1,
      Real.log (powerWeightedShiftQuantile theta a p u)) ^ 2

/-- The variance of `log X` under the normalized power-weighted shifted density
is exactly the variance of the logarithm of its canonical quantile on `(0,1)`.

This is the global transport bridge needed before applying the manuscript's
monotone-covariance argument. -/
theorem powerWeightedShift_logQuantileVariance_eq_logVariance_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    powerWeightedShiftLogQuantileVariance theta a p =
      powerWeightedShiftLogVariance theta a p := by
  have hfirst :=
    powerWeightedShift_logQuantile_integral_Ioo_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p)
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hsecond :=
    powerWeightedShift_logQuantile_sq_integral_Ioo_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p)
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  unfold powerWeightedShiftLogQuantileVariance powerWeightedShiftLogVariance
  rw [hfirst, hsecond]

end ScoreCurvatureStarOrder
