import Mathlib
import ScoreCurvatureStarOrder.CumulativeRadialRatio
import ScoreCurvatureStarOrder.TurningPoint
import ScoreCurvatureStarOrder.LeftCumulativeRadialRatio
import ScoreCurvatureStarOrder.RightCumulativeRadialRatio

namespace ScoreCurvatureStarOrder

open Set MeasureTheory
open scoped Topology

/-- The cumulative-radial ratio `R=A/D` is antitone on the whole positive
half-line under the one-sided score-curvature hypotheses.

The left and right monotonicity theorems produce positive turning points; the
previously proved uniqueness theorem identifies them.  The ratio `R` itself is
regular at that turning point because its denominator `D` is strictly positive
there.  Hence the left antitonicity extends from `(0,x₀)` to `(0,x₀]`, the right
antitonicity extends from `(x₀,∞)` to `[x₀,∞)`, and the two closed components can
be glued through the common value `R(x₀)`.  The singular slope quotient `q` is
never evaluated at the turning point. -/
theorem powerWeightedShift_cumulativeRadialRatio_antitoneOn_Ioi_within
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
    AntitoneOn
      (fun x : ℝ => powerWeightedShiftCumulativeRadialRatio theta S a p x)
      (Set.Ioi (0 : ℝ)) := by
  rcases powerWeightedShift_left_cumulativeRadialRatio_monotonicity_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (a := a) (p := p)
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime hSprime_pos hcurv with
    ⟨x0, hx0, hroot, _hqRleft, hRderiv_left, _hRanti_left_open⟩
  rcases powerWeightedShift_right_cumulativeRadialRatio_monotonicity_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (a := a) (p := p)
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime hSprime_pos hcurv with
    ⟨y0, hy0, hyroot, _hRqright, hRderiv_right_y0, _hRanti_right_open⟩

  rcases powerWeightedShift_turningPoint_exists_unique_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p)
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨z0, _hz0, huniq⟩
  have hx0z0 : x0 = z0 := huniq x0 ⟨hx0, hroot⟩
  have hy0z0 : y0 = z0 := huniq y0 ⟨hy0, hyroot⟩
  have hy0x0 : y0 = x0 := hy0z0.trans hx0z0.symm
  subst y0

  let R : ℝ → ℝ := fun x =>
    powerWeightedShiftCumulativeRadialRatio theta S a p x

  have hRdiff_pos : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ R x := by
    intro x hx
    have hRx := powerWeightedShiftCumulativeRadialRatio_hasDerivAt_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (x := x)
      ha hp hx htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [R] using hRx.differentiableAt

  have hRcont_left : ContinuousOn R (Set.Ioc (0 : ℝ) x0) := by
    intro x hx
    exact (hRdiff_pos x hx.1).continuousAt.continuousWithinAt
  have hRdiff_left : DifferentiableOn ℝ R (interior (Set.Ioc (0 : ℝ) x0)) := by
    intro x hxInt
    have hxI : x ∈ Set.Ioc (0 : ℝ) x0 := interior_subset hxInt
    exact (hRdiff_pos x hxI.1).differentiableWithinAt
  have hRderiv_left_closed :
      ∀ x ∈ interior (Set.Ioc (0 : ℝ) x0), deriv R x ≤ 0 := by
    intro x hxInt
    rw [interior_Ioc] at hxInt
    simpa [R] using hRderiv_left x hxInt.1 hxInt.2
  have hRanti_left : AntitoneOn R (Set.Ioc (0 : ℝ) x0) := by
    exact antitoneOn_of_deriv_nonpos
      (convex_Ioc (0 : ℝ) x0) hRcont_left hRdiff_left hRderiv_left_closed

  have hRcont_right : ContinuousOn R (Set.Ici x0) := by
    intro x hx
    have hxpos : 0 < x := hx0.trans_le hx
    exact (hRdiff_pos x hxpos).continuousAt.continuousWithinAt
  have hRdiff_right : DifferentiableOn ℝ R (interior (Set.Ici x0)) := by
    intro x hxInt
    have hxI : x ∈ Set.Ici x0 := interior_subset hxInt
    have hxpos : 0 < x := hx0.trans_le hxI
    exact (hRdiff_pos x hxpos).differentiableWithinAt
  have hRderiv_right_closed :
      ∀ x ∈ interior (Set.Ici x0), deriv R x ≤ 0 := by
    intro x hxInt
    rw [interior_Ici] at hxInt
    change x0 < x at hxInt
    simpa [R] using hRderiv_right_y0 x hxInt
  have hRanti_right : AntitoneOn R (Set.Ici x0) := by
    exact antitoneOn_of_deriv_nonpos
      (convex_Ici x0) hRcont_right hRdiff_right hRderiv_right_closed

  have hRanti_global : AntitoneOn R (Set.Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    by_cases hy_left : y ≤ x0
    · have hx_left : x ≤ x0 := hxy.trans hy_left
      exact hRanti_left
        ⟨hx, hx_left⟩ ⟨hy, hy_left⟩ hxy
    · have hx0y : x0 < y := lt_of_not_ge hy_left
      by_cases hx_right : x0 ≤ x
      · exact hRanti_right
          hx_right hx0y.le hxy
      · have hxx0 : x < x0 := lt_of_not_ge hx_right
        have hleft_bridge : R x0 ≤ R x :=
          hRanti_left
            ⟨hx, hxx0.le⟩ ⟨hx0, le_rfl⟩ hxx0.le
        have hright_bridge : R y ≤ R x0 :=
          hRanti_right
            le_rfl hx0y.le hx0y.le
        exact hright_bridge.trans hleft_bridge

  simpa [R] using hRanti_global

end ScoreCurvatureStarOrder
