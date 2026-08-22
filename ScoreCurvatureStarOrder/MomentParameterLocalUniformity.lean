import Mathlib
import ScoreCurvatureStarOrder.CompactParameterLogMajorants
import ScoreCurvatureStarOrder.CompactParameterLogSqMajorants
import ScoreCurvatureStarOrder.CompactParameterThetaDerivMajorants
import ScoreCurvatureStarOrder.PowerMomentDerivative
import ScoreCurvatureStarOrder.PowerLogMomentDerivative
import ScoreCurvatureStarOrder.MomentShiftBoundaryDerivative

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- The shift derivative of the normalization moment on the natural parameter
half-line, including the right derivative at `a = 0` and the ordinary derivative
at every `a > 0`, expressed uniformly as a derivative within `[0,∞)`. -/
theorem powerWeightedShiftMoment_hasDerivWithinAt_shift_within
    {theta S Sprime Ssecond : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
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
      Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    HasDerivWithinAt
      (fun b : ℝ => powerWeightedShiftMoment theta b p)
      (∫ x : ℝ in Set.Ioi 0,
        x ^ p * (-S (a + x) * theta (a + x)))
      (Set.Ici (0 : ℝ)) a := by
  by_cases h0 : a = 0
  · subst a
    simpa using
      (powerWeightedShiftMoment_hasDerivWithinAt_zero_within
        (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
        (p := p) hp htheta_pos htheta_deriv htheta_int hS hSprime
        hSprime_pos hcurv)
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
    exact
      (powerWeightedShiftMoment_hasDerivAt_within
        (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
        (a := a) (p := p) ha_pos hp htheta_pos htheta_deriv htheta_int
        hS hSprime hSprime_pos hcurv).hasDerivWithinAt

/-- **Proposition 2.4, local-uniform differentiation data.**

At every admissible parameter point `(p,a) ∈ (-1,∞) × [0,∞)`, there is a
compact parameter rectangle containing the point in its relative interior and
three integrable functions on `(0,∞)` which dominate, simultaneously for every
`(q,b)` in that rectangle, the first and second power-derivative integrands and
the shift-derivative integrand.

This is the precise domination statement behind the manuscript phrase that the
parameter derivatives may be taken under the integral sign locally uniformly
on the joint parameter domain. -/
theorem exists_powerWeightedShift_parameterDerivative_local_majorants_within
    {theta S Sprime Ssecond : ℝ → ℝ} {p a : ℝ}
    (hp : -1 < p) (ha : 0 ≤ a)
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
      Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    ∃ p₀ p₁ A : ℝ, ∃ boundP boundPP boundA : ℝ → ℝ,
      -1 < p₀ ∧ p₀ < p ∧ p < p₁ ∧ 0 ≤ A ∧ a < A ∧
      IntegrableOn boundP (Set.Ioi (0 : ℝ)) ∧
      IntegrableOn boundPP (Set.Ioi (0 : ℝ)) ∧
      IntegrableOn boundA (Set.Ioi (0 : ℝ)) ∧
      (∀ q ∈ Set.Icc p₀ p₁, ∀ b ∈ Set.Icc (0 : ℝ) A,
        ∀ x ∈ Set.Ioi (0 : ℝ),
          ‖x ^ q * Real.log x * theta (b + x)‖ ≤ boundP x) ∧
      (∀ q ∈ Set.Icc p₀ p₁, ∀ b ∈ Set.Icc (0 : ℝ) A,
        ∀ x ∈ Set.Ioi (0 : ℝ),
          ‖x ^ q * (Real.log x) ^ 2 * theta (b + x)‖ ≤ boundPP x) ∧
      (∀ q ∈ Set.Icc p₀ p₁, ∀ b ∈ Set.Icc (0 : ℝ) A,
        ∀ x ∈ Set.Ioi (0 : ℝ),
          x ^ q * |(-S (b + x) * theta (b + x))| ≤ boundA x) := by
  let p₀ : ℝ := (p - 1) / 2
  let p₁ : ℝ := p + 1
  let A : ℝ := a + 1
  have hp₀ : -1 < p₀ := by
    dsimp [p₀]
    linarith
  have hp₀p : p₀ < p := by
    dsimp [p₀]
    linarith
  have hpp₁ : p < p₁ := by
    dsimp [p₁]
    linarith
  have hp₀₁ : p₀ ≤ p₁ := hp₀p.le.trans hpp₁.le
  have hA : 0 ≤ A := by
    dsimp [A]
    linarith
  have haA : a < A := by
    dsimp [A]
    linarith

  rcases exists_powerWeightedShift_log_compact_majorant_within
      (theta := theta) (S := S) (Sprime := Sprime)
      hp₀ hp₀₁ hA htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨boundP, hboundP_int, hboundP⟩
  rcases exists_powerWeightedShift_log_sq_compact_majorant_within
      (theta := theta) (S := S) (Sprime := Sprime)
      hp₀ hp₀₁ hA htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨boundPP, hboundPP_int, hboundPP⟩
  rcases exists_powerWeightedShift_thetaDeriv_compact_majorant_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      hp₀ hp₀₁ hA htheta_pos htheta_deriv htheta_int hS hSprime
      hSprime_pos hcurv with
    ⟨boundA, hboundA_int, hboundA⟩

  exact ⟨p₀, p₁, A, boundP, boundPP, boundA,
    hp₀, hp₀p, hpp₁, hA, haA,
    hboundP_int, hboundPP_int, hboundA_int,
    hboundP, hboundPP, hboundA⟩

end ScoreCurvatureStarOrder
