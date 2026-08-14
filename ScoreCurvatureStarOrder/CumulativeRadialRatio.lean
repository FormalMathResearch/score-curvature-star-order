import Mathlib
import ScoreCurvatureStarOrder.RadialDensity
import ScoreCurvatureStarOrder.CumulativeShiftNumerator

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- The ratio `R=A/D` used in the monotone-l'Hospital step.  It is only used
on the strictly positive half-line, where the radial density is positive. -/
noncomputable def powerWeightedShiftCumulativeRadialRatio
    (theta S : ℝ → ℝ) (a p x : ℝ) : ℝ :=
  powerWeightedShiftCumulativeShiftNumerator theta S a p x /
    powerWeightedShiftRadialDensity theta a p x

/-- The radial density is strictly positive at every positive point under the
one-sided half-line assumptions. -/
theorem powerWeightedShiftRadialDensity_pos_within
    {theta S Sprime : ℝ → ℝ} {a p x : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p) (hx : 0 < x)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    0 < powerWeightedShiftRadialDensity theta a p x := by
  have hMpos : 0 < powerWeightedShiftMoment theta a p :=
    powerWeightedShiftMoment_pos_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hax : a + x ∈ Set.Ici (0 : ℝ) := by
    exact add_nonneg ha hx.le
  have hxpow : 0 < x ^ (p + 1) := Real.rpow_pos_of_pos hx _
  exact div_pos (mul_pos hxpow (htheta_pos (a + x) hax)) hMpos

/-- Hence the denominator of `R=A/D` is nonzero on `(0,∞)`. -/
theorem powerWeightedShiftRadialDensity_ne_zero_within
    {theta S Sprime : ℝ → ℝ} {a p x : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p) (hx : 0 < x)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    powerWeightedShiftRadialDensity theta a p x ≠ 0 :=
  (powerWeightedShiftRadialDensity_pos_within
    ha hp hx htheta_pos htheta_deriv htheta_int hS hSprime_pos).ne'

/-- The cumulative numerator has the exact left endpoint value `A(0)=0`. -/
theorem powerWeightedShiftCumulativeShiftNumerator_zero
    {theta S : ℝ → ℝ} {a p : ℝ} :
    powerWeightedShiftCumulativeShiftNumerator theta S a p 0 = 0 := by
  simp [powerWeightedShiftCumulativeShiftNumerator]

/-- For `p>-1`, the regular power-product form gives the exact endpoint value
`D(0)=0`. -/
theorem powerWeightedShiftRadialDensity_zero
    {theta : ℝ → ℝ} {a p : ℝ} (hp : -1 < p) :
    powerWeightedShiftRadialDensity theta a p 0 = 0 := by
  have hp1 : p + 1 ≠ 0 := by linarith
  simp [powerWeightedShiftRadialDensity, hp1]

/-- On `(0,∞)`, `R=A/D` has the ordinary quotient derivative under the same
one-sided half-line hypotheses used for `A'` and `D'`.  No turning-point or
curvature assumption is needed for this algebraic quotient rule. -/
theorem powerWeightedShiftCumulativeRadialRatio_hasDerivAt_within
    {theta S Sprime : ℝ → ℝ} {a p x : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p) (hx : 0 < x)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    HasDerivAt
      (fun y : ℝ => powerWeightedShiftCumulativeRadialRatio theta S a p y)
      ((powerWeightedShiftDensity theta a p x *
          (powerWeightedShiftScoreMean theta S a p - S (a + x))) *
          powerWeightedShiftRadialDensity theta a p x -
        powerWeightedShiftCumulativeShiftNumerator theta S a p x *
          (powerWeightedShiftDensity theta a p x *
            (p + 1 - x * S (a + x)))) /
        (powerWeightedShiftRadialDensity theta a p x) ^ 2) x := by
  have hA := powerWeightedShiftCumulativeShiftNumerator_hasDerivAt_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p) (x := x) ha hp hx htheta_deriv hS
  have hD := powerWeightedShiftRadialDensity_hasDerivAt_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p) (x := x)
    ha hp hx htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hDne : powerWeightedShiftRadialDensity theta a p x ≠ 0 :=
    powerWeightedShiftRadialDensity_ne_zero_within
      ha hp hx htheta_pos htheta_deriv htheta_int hS hSprime_pos
  simpa [powerWeightedShiftCumulativeRadialRatio] using hA.div hD hDne

end ScoreCurvatureStarOrder
