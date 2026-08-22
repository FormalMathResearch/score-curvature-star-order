import Mathlib
import ScoreCurvatureStarOrder.PowerMomentDerivative

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- For every nonnegative shift and every `p > -1`, the logarithm of the
normalization moment is differentiable with respect to the power parameter:

`∂ₚ log M_p(a) = (∫ x^p log(x) theta(a+x) dx) / M_p(a)`.

This is a direct consequence of the verified power-parameter derivative of
`M_p(a)` and strict positivity of the normalization moment. -/
theorem powerWeightedShiftMoment_log_hasDerivAt_power_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    HasDerivAt
      (fun q : ℝ => Real.log (powerWeightedShiftMoment theta a q))
      ((∫ x : ℝ in Set.Ioi 0,
          x ^ p * Real.log x * theta (a + x)) /
        powerWeightedShiftMoment theta a p) p := by
  have hMderiv := powerWeightedShiftMoment_hasDerivAt_power_within
    (theta := theta) (S := S) (Sprime := Sprime) (a := a) (p := p)
    ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hMpos : 0 < powerWeightedShiftMoment theta a p :=
    powerWeightedShiftMoment_pos_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  exact hMderiv.log hMpos.ne'

end ScoreCurvatureStarOrder
