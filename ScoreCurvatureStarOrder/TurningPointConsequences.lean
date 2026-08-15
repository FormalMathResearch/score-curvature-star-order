import Mathlib
import ScoreCurvatureStarOrder.TurningPoint
import ScoreCurvatureStarOrder.RadialDensity
import ScoreCurvatureStarOrder.SlopeQuotientMonotonicity

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- The unique turning point simultaneously controls the sign of the radial-density
derivative and separates the reduced slope quotient into its two pole-free antitone
components.

All boundary differentiability assumptions remain one-sided on `[0, ∞)`.  The
strict positivity of the normalized density on `(0,∞)` is proved inside the
argument from positivity of the kernel and of the normalization moment. -/
theorem powerWeightedShift_turningPoint_deriv_sign_and_slope_antitone_within
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
    ∃ x0 : ℝ,
      0 < x0 ∧
      x0 * S (a + x0) = p + 1 ∧
      (∀ x : ℝ, 0 < x → x < x0 →
        0 < deriv (fun y : ℝ => powerWeightedShiftRadialDensity theta a p y) x) ∧
      (∀ x : ℝ, x0 < x →
        deriv (fun y : ℝ => powerWeightedShiftRadialDensity theta a p y) x < 0) ∧
      AntitoneOn
        (fun x : ℝ => powerWeightedShiftSlopeQuotient theta S a p x)
        (Set.Ioo (0 : ℝ) x0) ∧
      AntitoneOn
        (fun x : ℝ => powerWeightedShiftSlopeQuotient theta S a p x)
        (Set.Ioi x0) := by
  rcases powerWeightedShift_exists_turningPoint_with_sign_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨x0, hx0, hroot, hleft, hright, _hzero⟩

  have hMpos : 0 < powerWeightedShiftMoment theta a p :=
    powerWeightedShiftMoment_pos_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos

  have hdensity_pos :
      ∀ x : ℝ, 0 < x → 0 < powerWeightedShiftDensity theta a p x := by
    intro x hx
    have hax0 : 0 ≤ a + x := by linarith
    dsimp [powerWeightedShiftDensity]
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos hx p) (htheta_pos (a + x) hax0)) hMpos

  have hDleft :
      ∀ x : ℝ, 0 < x → x < x0 →
        0 < deriv (fun y : ℝ => powerWeightedShiftRadialDensity theta a p y) x := by
    intro x hx hxx0
    have hD := powerWeightedShiftRadialDensity_hasDerivAt_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (x := x)
      ha hp hx htheta_pos htheta_deriv htheta_int hS hSprime_pos
    rw [hD.deriv]
    exact mul_pos (hdensity_pos x hx) (hleft x hx hxx0)

  have hDright :
      ∀ x : ℝ, x0 < x →
        deriv (fun y : ℝ => powerWeightedShiftRadialDensity theta a p y) x < 0 := by
    intro x hx0x
    have hx : 0 < x := hx0.trans hx0x
    have hD := powerWeightedShiftRadialDensity_hasDerivAt_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (x := x)
      ha hp hx htheta_pos htheta_deriv htheta_int hS hSprime_pos
    rw [hD.deriv]
    exact mul_neg_of_pos_of_neg (hdensity_pos x hx) (hright x hx0x)

  have hqleft :
      AntitoneOn
        (fun x : ℝ => powerWeightedShiftSlopeQuotient theta S a p x)
        (Set.Ioo (0 : ℝ) x0) := by
    apply powerWeightedShiftSlopeQuotient_antitoneOn_convex_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (a := a) (p := p)
      ha hp (convex_Ioo (0 : ℝ) x0)
      (by
        intro x hx
        exact hx.1)
      htheta_pos htheta_deriv htheta_int hS hSprime hSprime_pos hcurv
    intro x hx
    exact (hleft x hx.1 hx.2).ne'

  have hqright :
      AntitoneOn
        (fun x : ℝ => powerWeightedShiftSlopeQuotient theta S a p x)
        (Set.Ioi x0) := by
    apply powerWeightedShiftSlopeQuotient_antitoneOn_convex_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (a := a) (p := p)
      ha hp (convex_Ioi x0)
      (by
        intro x hx
        exact hx0.trans hx)
      htheta_pos htheta_deriv htheta_int hS hSprime hSprime_pos hcurv
    intro x hx
    exact (hright x hx).ne

  exact ⟨x0, hx0, hroot, hDleft, hDright, hqleft, hqright⟩

end ScoreCurvatureStarOrder
