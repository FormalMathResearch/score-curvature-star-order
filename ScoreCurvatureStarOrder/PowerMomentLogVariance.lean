import Mathlib
import ScoreCurvatureStarOrder.LogVariance

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- The derivative of the first power derivative of `log M_p(a)` is the
variance of `log X` under the normalized power-weighted shifted density.

This is the second identity in manuscript Lemma 5.2:

`∂ₚ² log M_p(a) = Var_{p,a}(log X)`.

The function being differentiated is the already verified first derivative
`L_p(a) / M_p(a)`, written using pointwise function division to match Lean's
quotient-rule interface. -/
theorem powerWeightedShiftMoment_logDerivative_hasDerivAt_logVariance_within
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
      ((fun q : ℝ =>
          ∫ x : ℝ in Set.Ioi 0,
            x ^ q * Real.log x * theta (a + x)) /
        (fun q : ℝ => powerWeightedShiftMoment theta a q))
      (powerWeightedShiftLogVariance theta a p) p := by
  have hsecond :=
    powerWeightedShiftMoment_logDerivative_hasDerivAt_power_within
      (theta := theta) (S := S) (Sprime := Sprime) (a := a) (p := p)
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hvar :=
    powerWeightedShift_logVariance_eq_moment_formula_within
      (theta := theta) (S := S) (Sprime := Sprime) (a := a) (p := p)
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  rw [hvar]
  exact hsecond

/-- Manuscript-oriented wrapper for Lemma 5.2.  Under the one-sided half-line
hypotheses used throughout the project, both power-parameter identities hold:

`∂ₚ log M_p(a) = E_{p,a}[log X]`
and
`∂ₚ² log M_p(a) = Var_{p,a}(log X)`.

The first expectation is represented by its normalized moment ratio, while the
second is the project definition `powerWeightedShiftLogVariance`. -/
theorem powerWeightedShiftMoment_log_power_derivatives_within
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
          powerWeightedShiftMoment theta a p) p ∧
      HasDerivAt
        ((fun q : ℝ =>
            ∫ x : ℝ in Set.Ioi 0,
              x ^ q * Real.log x * theta (a + x)) /
          (fun q : ℝ => powerWeightedShiftMoment theta a q))
        (powerWeightedShiftLogVariance theta a p) p := by
  constructor
  · exact powerWeightedShiftMoment_log_hasDerivAt_power_within
      (theta := theta) (S := S) (Sprime := Sprime) (a := a) (p := p)
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  · exact powerWeightedShiftMoment_logDerivative_hasDerivAt_logVariance_within
      (theta := theta) (S := S) (Sprime := Sprime) (a := a) (p := p)
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos

end ScoreCurvatureStarOrder
