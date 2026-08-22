import Mathlib
import ScoreCurvatureStarOrder.QuantileShiftDerivative
import ScoreCurvatureStarOrder.CumulativeRadialRatio

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- For an interior shift `a>0` and level `u∈(0,1)`, the logarithmic shift
derivative of the canonical quantile is exactly minus the global cumulative
radial ratio evaluated at that quantile:

`∂ₐ log Q_{p,a}(u) = -R_{p,a}(Q_{p,a}(u))`.

This is the bridge from the implicit quantile derivative to the already
verified global antitonicity theorem for `R`. -/
theorem powerWeightedShift_logQuantile_hasDerivAt_shift_within
    {theta S Sprime Ssecond : ℝ → ℝ} {a p u : ℝ}
    (ha : 0 < a) (hp : -1 < p) (hu0 : 0 < u) (hu1 : u < 1)
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
    HasDerivAt
      (fun b : ℝ => Real.log (powerWeightedShiftQuantile theta b p u))
      (-powerWeightedShiftCumulativeRadialRatio theta S a p
        (powerWeightedShiftQuantile theta a p u)) a := by
  let q : ℝ := powerWeightedShiftQuantile theta a p u
  let A : ℝ := powerWeightedShiftCumulativeShiftNumerator theta S a p q
  let f : ℝ := powerWeightedShiftDensity theta a p q

  have hQ := powerWeightedShiftQuantile_pos_and_CDF_eq_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p) (u := u)
    ha.le hp hu0 hu1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hqpos : 0 < q := by simpa [q] using hQ.1
  have hfpos : 0 < f := by
    dsimp [f]
    exact powerWeightedShiftDensity_pos_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (x := q)
      ha.le hp hqpos htheta_pos htheta_deriv htheta_int hS hSprime_pos

  have hQderiv := powerWeightedShiftQuantile_hasDerivAt_shift_within
    (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
    (a := a) (p := p) (u := u)
    ha hp hu0 hu1 htheta_pos htheta_deriv htheta_int hS hSprime
    hSprime_pos hcurv
  have hlog := hQderiv.log hqpos.ne'

  have hD : powerWeightedShiftRadialDensity theta a p q = q * f := by
    simpa [f] using
      (powerWeightedShiftRadialDensity_eq_mul_density
        (theta := theta) (a := a) (p := p) (x := q) hqpos)
  have hcoef :
      ((-A / f) / q) =
        -powerWeightedShiftCumulativeRadialRatio theta S a p q := by
    dsimp [powerWeightedShiftCumulativeRadialRatio, A]
    rw [hD]
    field_simp [hqpos.ne', hfpos.ne']

  change HasDerivAt
    (fun b : ℝ => Real.log (powerWeightedShiftQuantile theta b p u))
    (-powerWeightedShiftCumulativeRadialRatio theta S a p q) a
  rw [← hcoef]
  simpa [q, A, f] using hlog

end ScoreCurvatureStarOrder
