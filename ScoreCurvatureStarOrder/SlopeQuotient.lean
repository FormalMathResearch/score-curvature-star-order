import Mathlib
import ScoreCurvatureStarOrder.CumulativeShiftNumerator
import ScoreCurvatureStarOrder.RadialDensity

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- The reduced quotient `q = A'/D'` used in the star-order argument. -/
noncomputable def powerWeightedShiftSlopeQuotient
    (theta S : ℝ → ℝ) (a p x : ℝ) : ℝ :=
  (powerWeightedShiftScoreMean theta S a p - S (a + x)) /
    (p + 1 - x * S (a + x))

/-- The scalar kernel appearing in the derivative of the reduced quotient. -/
noncomputable def powerWeightedShiftSlopeKernel
    (theta S Sprime : ℝ → ℝ) (a p x : ℝ) : ℝ :=
  (p + 1 - x * powerWeightedShiftScoreMean theta S a p) * Sprime (a + x) +
    S (a + x) ^ 2 -
      powerWeightedShiftScoreMean theta S a p * S (a + x)

/-- Wherever `D'(x) ≠ 0`, the ratio of the already verified derivative formulas for
`A` and `D` reduces to the manuscript quotient `q`. -/
theorem powerWeightedShift_APrime_div_DPrime_eq_slopeQuotient
    {theta S Sprime : ℝ → ℝ} {a p x : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p) (hx : 0 < x)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z)
    (hden : p + 1 - x * S (a + x) ≠ 0) :
    deriv (fun y : ℝ =>
      powerWeightedShiftCumulativeShiftNumerator theta S a p y) x /
      deriv (fun y : ℝ => powerWeightedShiftRadialDensity theta a p y) x =
        powerWeightedShiftSlopeQuotient theta S a p x := by
  have hA := powerWeightedShiftCumulativeShiftNumerator_hasDerivAt
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p) (x := x) ha hp hx htheta_deriv hS
  have hD := powerWeightedShiftRadialDensity_hasDerivAt
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p) (x := x) ha hp hx htheta_pos htheta_deriv htheta_int hS
    hSprime_pos
  have hMpos : 0 < powerWeightedShiftMoment theta a p :=
    powerWeightedShiftMoment_pos
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hax0 : 0 ≤ a + x := add_nonneg ha hx.le
  have hrpow_pos : 0 < x ^ p := Real.rpow_pos_of_pos hx p
  have hdensity_pos : 0 < powerWeightedShiftDensity theta a p x := by
    dsimp [powerWeightedShiftDensity]
    exact div_pos (mul_pos hrpow_pos (htheta_pos (a + x) hax0)) hMpos
  have hdensity_ne : powerWeightedShiftDensity theta a p x ≠ 0 := hdensity_pos.ne'
  rw [hA.deriv, hD.deriv]
  dsimp [powerWeightedShiftSlopeQuotient]
  field_simp [hdensity_ne, hden]

/-- The manuscript quotient satisfies
`q'(x) = -K(x) / (p+1-x S(a+x))^2` wherever its denominator is nonzero. -/
theorem powerWeightedShiftSlopeQuotient_hasDerivAt
    {theta S Sprime : ℝ → ℝ} {a p x : ℝ}
    (ha : 0 ≤ a) (hx : 0 ≤ x)
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hden : p + 1 - x * S (a + x) ≠ 0) :
    HasDerivAt
      (fun y : ℝ => powerWeightedShiftSlopeQuotient theta S a p y)
      (-powerWeightedShiftSlopeKernel theta S Sprime a p x /
        (p + 1 - x * S (a + x)) ^ 2) x := by
  let G : ℝ := powerWeightedShiftScoreMean theta S a p
  let sx : ℝ := S (a + x)
  let spx : ℝ := Sprime (a + x)
  have hax0 : 0 ≤ a + x := add_nonneg ha hx
  have hSxa : HasDerivAt S spx (x + a) := by
    simpa [spx, add_comm] using hS (a + x) hax0
  have hSshift0 : HasDerivAt (fun y : ℝ => S (y + a)) spx x :=
    hSxa.comp_add_const x a
  have hSshift : HasDerivAt (fun y : ℝ => S (a + y)) spx x := by
    simpa only [add_comm] using hSshift0
  have hnum0 := (hasDerivAt_const x G).sub hSshift
  have hnum_fun :
      ((fun _ : ℝ => G) - (fun y : ℝ => S (a + y))) =
        (fun y : ℝ => G - S (a + y)) := by
    funext y
    rfl
  have hnum : HasDerivAt (fun y : ℝ => G - S (a + y)) (-spx) x := by
    rw [← hnum_fun]
    simpa only [zero_sub] using hnum0
  have hprod0 := (hasDerivAt_id x).mul hSshift
  have hprod_fun :
      (id * (fun y : ℝ => S (a + y))) =
        (fun y : ℝ => y * S (a + y)) := by
    funext y
    rfl
  have hprod :
      HasDerivAt (fun y : ℝ => y * S (a + y)) (sx + x * spx) x := by
    rw [← hprod_fun]
    simpa only [sx] using hprod0
  have hden0 := (hasDerivAt_const x (p + 1)).sub hprod
  have hden_fun :
      ((fun _ : ℝ => p + 1) - (fun y : ℝ => y * S (a + y))) =
        (fun y : ℝ => p + 1 - y * S (a + y)) := by
    funext y
    rfl
  have hdenDer :
      HasDerivAt (fun y : ℝ => p + 1 - y * S (a + y)) (-(sx + x * spx)) x := by
    rw [← hden_fun]
    simpa only [zero_sub] using hden0
  have hquot := hnum.fun_div hdenDer hden
  have hcoef :
      ((-spx) * (p + 1 - x * sx) -
          (G - sx) * (-(sx + x * spx))) /
          (p + 1 - x * sx) ^ 2 =
        -powerWeightedShiftSlopeKernel theta S Sprime a p x /
          (p + 1 - x * sx) ^ 2 := by
    dsimp [powerWeightedShiftSlopeKernel, G, sx, spx]
    ring
  change HasDerivAt
    (fun y : ℝ => (G - S (a + y)) / (p + 1 - y * S (a + y)))
    (-powerWeightedShiftSlopeKernel theta S Sprime a p x /
      (p + 1 - x * S (a + x)) ^ 2) x
  rw [← hcoef]
  simpa [G, sx] using hquot

end ScoreCurvatureStarOrder
