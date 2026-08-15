import Mathlib
import ScoreCurvatureStarOrder.PowerMomentLogDerivative
import ScoreCurvatureStarOrder.PowerLogMomentDerivative

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- For every nonnegative shift and every `p > -1`, the first power derivative
of `log M_p(a)` is itself differentiable in the power parameter.  Writing

`L_p(a) = ∫ x^p log(x) theta(a+x) dx`
and
`Q_p(a) = ∫ x^p (log x)^2 theta(a+x) dx`,

the derivative of `L_p(a) / M_p(a)` is

`(Q_p(a) M_p(a) - L_p(a)^2) / M_p(a)^2`.

Together with `powerWeightedShiftMoment_log_hasDerivAt_power_within`, this is
the analytic second-derivative formula for `log M_p(a)`.  No new interchange
of derivative and integral is used here: the proof is the quotient rule applied
to the already verified derivatives of `M_p(a)` and `L_p(a)`, with strict
positivity of `M_p(a)` supplying the nonzero denominator. -/
theorem powerWeightedShiftMoment_logDerivative_hasDerivAt_power_within
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
      (fun q : ℝ =>
        (∫ x : ℝ in Set.Ioi 0,
          x ^ q * Real.log x * theta (a + x)) /
        powerWeightedShiftMoment theta a q)
      (((∫ x : ℝ in Set.Ioi 0,
          x ^ p * (Real.log x) ^ 2 * theta (a + x)) *
          powerWeightedShiftMoment theta a p -
        (∫ x : ℝ in Set.Ioi 0,
          x ^ p * Real.log x * theta (a + x)) ^ 2) /
        (powerWeightedShiftMoment theta a p) ^ 2) p := by
  have hL := powerWeightedShift_logMoment_hasDerivAt_power_within
    (theta := theta) (S := S) (Sprime := Sprime) (a := a) (p := p)
    ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hM := powerWeightedShiftMoment_hasDerivAt_power_within
    (theta := theta) (S := S) (Sprime := Sprime) (a := a) (p := p)
    ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hMpos : 0 < powerWeightedShiftMoment theta a p :=
    powerWeightedShiftMoment_pos_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hquot := hL.div hM hMpos.ne'
  simpa [Pi.div_apply, pow_two] using hquot

end ScoreCurvatureStarOrder
