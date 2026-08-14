import Mathlib
import ScoreCurvatureStarOrder.Density
import ScoreCurvatureStarOrder.ScoreIntegrability

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- The radial density `D(x) = x f_{p,a}(x)`, written in the equivalent
power-product form that is regular at the lower endpoint when `p > -1`. -/
noncomputable def powerWeightedShiftRadialDensity
    (theta : ℝ → ℝ) (a p x : ℝ) : ℝ :=
  x ^ (p + 1) * theta (a + x) / powerWeightedShiftMoment theta a p

/-- On the positive half-line, the power-product definition of the radial density equals
`x` times the normalized density. -/
theorem powerWeightedShiftRadialDensity_eq_mul_density
    {theta : ℝ → ℝ} {a p x : ℝ} (hx : 0 < x) :
    powerWeightedShiftRadialDensity theta a p x =
      x * powerWeightedShiftDensity theta a p x := by
  have hrpow_add : x ^ (p + 1) = x ^ p * x := by
    simpa using Real.rpow_add hx p 1
  dsimp [powerWeightedShiftRadialDensity, powerWeightedShiftDensity]
  rw [hrpow_add]
  ring

/-- For `x > 0`, the radial density satisfies
`D'(x) = f_{p,a}(x) (p+1 - x S(a+x))`. -/
theorem powerWeightedShiftRadialDensity_hasDerivAt
    {theta S Sprime : ℝ → ℝ} {a p x : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p) (hx : 0 < x)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    HasDerivAt
      (fun y : ℝ => powerWeightedShiftRadialDensity theta a p y)
      (powerWeightedShiftDensity theta a p x *
        (p + 1 - x * S (a + x))) x := by
  have hMpos : 0 < powerWeightedShiftMoment theta a p :=
    powerWeightedShiftMoment_pos
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hMne : powerWeightedShiftMoment theta a p ≠ 0 := hMpos.ne'
  have hax0 : 0 ≤ a + x := add_nonneg ha hx.le
  have hprod := powerWeightedShift_product_deriv
    (theta := theta) (S := S) (a := a) (p := p) (x := x)
    hx hax0 htheta_deriv
  have hscaled := hprod.mul_const (powerWeightedShiftMoment theta a p)⁻¹
  have hrpow_add : x ^ (p + 1) = x ^ p * x := by
    simpa using Real.rpow_add hx p 1
  have hcoef :
      (((p + 1) * x ^ p * theta (a + x) -
          x ^ (p + 1) * S (a + x) * theta (a + x)) *
          (powerWeightedShiftMoment theta a p)⁻¹) =
        powerWeightedShiftDensity theta a p x *
          (p + 1 - x * S (a + x)) := by
    dsimp [powerWeightedShiftDensity]
    rw [hrpow_add, div_eq_mul_inv]
    ring
  change HasDerivAt
    (fun y : ℝ =>
      y ^ (p + 1) * theta (a + y) / powerWeightedShiftMoment theta a p)
    (powerWeightedShiftDensity theta a p x *
      (p + 1 - x * S (a + x))) x
  rw [← hcoef]
  simpa [div_eq_mul_inv] using hscaled

end ScoreCurvatureStarOrder
