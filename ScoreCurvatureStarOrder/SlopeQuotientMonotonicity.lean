import Mathlib
import ScoreCurvatureStarOrder.KernelExpectation

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- Under the score-curvature hypotheses, the derivative of the reduced slope
quotient is nonpositive at every strictly positive point where its denominator
is nonzero.  This combines the exact quotient derivative formula with the
verified nonnegativity of the scalar kernel `K_{p,a}`. -/
theorem powerWeightedShiftSlopeQuotient_deriv_nonpos_within
    {theta S Sprime Ssecond : ℝ → ℝ} {a p x : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p) (hx : 0 < x)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt Sprime (Ssecond z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ),
      Ssecond z * S z - (Sprime z) ^ 2 ≤ 0)
    (hden : p + 1 - x * S (a + x) ≠ 0) :
    deriv (fun y : ℝ => powerWeightedShiftSlopeQuotient theta S a p y) x ≤ 0 := by
  have hq := powerWeightedShiftSlopeQuotient_hasDerivAt_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p) (x := x) ha hx hS hden
  rw [hq.deriv]
  have hK : 0 ≤ powerWeightedShiftSlopeKernel theta S Sprime a p x :=
    powerWeightedShiftSlopeKernel_nonneg_within
      ha hp hx htheta_pos htheta_deriv htheta_int hS hSprime hSprime_pos hcurv
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hK) (sq_nonneg _)

end ScoreCurvatureStarOrder
