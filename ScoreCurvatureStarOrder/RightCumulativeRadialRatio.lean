import Mathlib
import ScoreCurvatureStarOrder.CumulativeRadialRatio
import ScoreCurvatureStarOrder.TurningPointConsequences
import ScoreCurvatureStarOrder.RightEndpointLimits

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Topology

/-- On the right side of the unique turning point, the cumulative-radial ratio
`R=A/D` lies below the reduced slope quotient `q`, has nonpositive derivative,
and is antitone.

For a fixed `x>x₀`, define `F(y)=A(y)-q(x)D(y)`.  Since `q` is antitone and
`D'<0` on the right component, `F'≥0` on `[x,∞)`.  The verified endpoint
limits `A(y)→0` and `D(y)→0` imply `F(y)→0`, hence monotonicity gives
`F(x)≤0`, i.e. `R(x)≤q(x)`.  This argument never crosses the pole at `x₀`
and uses the correct right endpoint rather than the left endpoint identities. -/
theorem powerWeightedShift_right_cumulativeRadialRatio_monotonicity_within
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
      (∀ x : ℝ, x0 < x →
        powerWeightedShiftCumulativeRadialRatio theta S a p x ≤
          powerWeightedShiftSlopeQuotient theta S a p x) ∧
      (∀ x : ℝ, x0 < x →
        deriv (fun y : ℝ =>
          powerWeightedShiftCumulativeRadialRatio theta S a p y) x ≤ 0) ∧
      AntitoneOn
        (fun x : ℝ => powerWeightedShiftCumulativeRadialRatio theta S a p x)
        (Set.Ioi x0) := by
  rcases powerWeightedShift_turningPoint_deriv_sign_and_slope_antitone_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (a := a) (p := p)
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime hSprime_pos hcurv with
    ⟨x0, hx0, hroot, _hDleft, hDright, _hqleft, hqright⟩
  rcases powerWeightedShift_turningPoint_sign_within
      ha hp hx0 hroot hS hSprime_pos with
    ⟨_hdenleft, hdenright⟩
  have hlimits :=
    powerWeightedShift_cumulative_and_radial_tendsto_atTop_zero_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (a := a) (p := p)
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime hSprime_pos hcurv

  let A : ℝ → ℝ := fun y =>
    powerWeightedShiftCumulativeShiftNumerator theta S a p y
  let D : ℝ → ℝ := fun y => powerWeightedShiftRadialDensity theta a p y
  let q : ℝ → ℝ := fun y => powerWeightedShiftSlopeQuotient theta S a p y
  let R : ℝ → ℝ := fun y => powerWeightedShiftCumulativeRadialRatio theta S a p y

  have hAlim : Tendsto A atTop (𝓝 0) := by
    simpa [A] using hlimits.1
  have hDlim : Tendsto D atTop (𝓝 0) := by
    simpa [D] using hlimits.2

  have hMpos : 0 < powerWeightedShiftMoment theta a p :=
    powerWeightedShiftMoment_pos_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hdensity_pos : ∀ y : ℝ, 0 < y →
      0 < powerWeightedShiftDensity theta a p y := by
    intro y hy
    have hay : 0 ≤ a + y := by linarith
    dsimp [powerWeightedShiftDensity]
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos hy p) (htheta_pos (a + y) hay)) hMpos

  have hR_le_q : ∀ x : ℝ, x0 < x → R x ≤ q x := by
    intro x hx0x
    have hx : 0 < x := hx0.trans hx0x
    let qx : ℝ := q x
    let F : ℝ → ℝ := fun y => A y - qx * D y
    let F' : ℝ → ℝ := fun y =>
      powerWeightedShiftDensity theta a p y *
          (powerWeightedShiftScoreMean theta S a p - S (a + y)) -
        qx *
          (powerWeightedShiftDensity theta a p y *
            (p + 1 - y * S (a + y)))

    have hFder : ∀ y ∈ Set.Ici x, HasDerivAt F (F' y) y := by
      intro y hy
      have hypos : 0 < y := hx.trans_le hy
      have hAy := powerWeightedShiftCumulativeShiftNumerator_hasDerivAt_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p) (x := y) ha hp hypos htheta_deriv hS
      have hDy := powerWeightedShiftRadialDensity_hasDerivAt_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p) (x := y)
        ha hp hypos htheta_pos htheta_deriv htheta_int hS hSprime_pos
      have hraw := hAy.sub (hDy.const_mul qx)
      have hfun :
          ((fun z : ℝ => powerWeightedShiftCumulativeShiftNumerator theta S a p z) -
            (fun z : ℝ => qx * powerWeightedShiftRadialDensity theta a p z)) = F := by
        funext z
        rfl
      rw [← hfun]
      simpa [F', A, D] using hraw

    have hFcont : ContinuousOn F (Set.Ici x) := by
      intro y hy
      exact (hFder y hy).continuousAt.continuousWithinAt
    have hFdiff : DifferentiableOn ℝ F (interior (Set.Ici x)) := by
      intro y hyInt
      have hy : y ∈ Set.Ici x := interior_subset hyInt
      exact (hFder y hy).differentiableAt.differentiableWithinAt
    have hFderiv_nonneg : ∀ y ∈ interior (Set.Ici x), 0 ≤ deriv F y := by
      intro y hyInt
      rw [interior_Ici] at hyInt
      change x < y at hyInt
      have hxy : x < y := hyInt
      have hyIci : y ∈ Set.Ici x := by
        change x ≤ y
        exact hxy.le
      have hx0y : x0 < y := hx0x.trans hxy
      have hypos : 0 < y := hx.trans hxy
      have hdenneg : p + 1 - y * S (a + y) < 0 := hdenright y hx0y
      have hdenne : p + 1 - y * S (a + y) ≠ 0 := hdenneg.ne
      have hqy_le_qx : q y ≤ q x := by
        simpa [q] using hqright hx0x hx0y hxy.le
      have hq_mul_den :
          q y * (p + 1 - y * S (a + y)) =
            powerWeightedShiftScoreMean theta S a p - S (a + y) := by
        dsimp [q, powerWeightedShiftSlopeQuotient]
        field_simp [hdenne]
      have hmul :
          q x * (p + 1 - y * S (a + y)) ≤
            q y * (p + 1 - y * S (a + y)) :=
        mul_le_mul_of_nonpos_right hqy_le_qx hdenneg.le
      rw [hq_mul_den] at hmul
      have hbracket :
          0 ≤ powerWeightedShiftScoreMean theta S a p - S (a + y) -
            qx * (p + 1 - y * S (a + y)) := by
        simpa [qx] using sub_nonneg.mpr hmul
      have hdpos := hdensity_pos y hypos
      have hprod :
          0 ≤ powerWeightedShiftDensity theta a p y *
            (powerWeightedShiftScoreMean theta S a p - S (a + y) -
              qx * (p + 1 - y * S (a + y))) :=
        mul_nonneg hdpos.le hbracket
      rw [(hFder y hyIci).deriv]
      have hcoef :
          F' y = powerWeightedShiftDensity theta a p y *
            (powerWeightedShiftScoreMean theta S a p - S (a + y) -
              qx * (p + 1 - y * S (a + y))) := by
        dsimp [F']
        ring
      rw [hcoef]
      exact hprod

    have hFmono : MonotoneOn F (Set.Ici x) := by
      exact monotoneOn_of_deriv_nonneg
        (convex_Ici x) hFcont hFdiff hFderiv_nonneg
    have hFlim : Tendsto F atTop (𝓝 0) := by
      have hqDlim :
          Tendsto (fun y : ℝ => qx * D y) atTop (𝓝 (qx * 0)) :=
        tendsto_const_nhds.mul hDlim
      have hsub := hAlim.sub hqDlim
      simpa [F] using hsub
    have hFx_le_eventually : ∀ᶠ y in atTop, F x ≤ F y := by
      filter_upwards [eventually_ge_atTop x] with y hy
      have hxmem : x ∈ Set.Ici x := by
        change x ≤ x
        exact le_rfl
      have hymem : y ∈ Set.Ici x := by
        change x ≤ y
        exact hy
      exact hFmono hxmem hymem hy
    have hFx_le_zero : F x ≤ 0 :=
      ge_of_tendsto hFlim hFx_le_eventually
    have hDpos : 0 < D x := by
      simpa [D] using
        (powerWeightedShiftRadialDensity_pos_within
          (theta := theta) (S := S) (Sprime := Sprime)
          (a := a) (p := p) (x := x)
          ha hp hx htheta_pos htheta_deriv htheta_int hS hSprime_pos)
    have hA_le : A x ≤ q x * D x := by
      dsimp [F, qx] at hFx_le_zero
      linarith
    have hratio : A x / D x ≤ q x :=
      (div_le_iff₀ hDpos).2 hA_le
    simpa [R, A, D, powerWeightedShiftCumulativeRadialRatio] using hratio

  have hRderiv_nonpos : ∀ x : ℝ, x0 < x → deriv R x ≤ 0 := by
    intro x hx0x
    have hx : 0 < x := hx0.trans hx0x
    have hRq := hR_le_q x hx0x
    have hdenneg : p + 1 - x * S (a + x) < 0 := hdenright x hx0x
    have hdenne : p + 1 - x * S (a + x) ≠ 0 := hdenneg.ne
    have hDpos : 0 < D x := by
      simpa [D] using
        (powerWeightedShiftRadialDensity_pos_within
          (theta := theta) (S := S) (Sprime := Sprime)
          (a := a) (p := p) (x := x)
          ha hp hx htheta_pos htheta_deriv htheta_int hS hSprime_pos)
    have hq_mul_den :
        q x * (p + 1 - x * S (a + x)) =
          powerWeightedShiftScoreMean theta S a p - S (a + x) := by
      dsimp [q, powerWeightedShiftSlopeQuotient]
      field_simp [hdenne]
    have hmul :
        q x * (p + 1 - x * S (a + x)) ≤
          R x * (p + 1 - x * S (a + x)) :=
      mul_le_mul_of_nonpos_right hRq hdenneg.le
    rw [hq_mul_den] at hmul
    have hbracket :
        powerWeightedShiftScoreMean theta S a p - S (a + x) -
          R x * (p + 1 - x * S (a + x)) ≤ 0 := by
      linarith
    have hdpos := hdensity_pos x hx
    have hfactor :
        0 ≤ powerWeightedShiftDensity theta a p x * D x :=
      mul_nonneg hdpos.le hDpos.le
    have hprod :
        powerWeightedShiftDensity theta a p x * D x *
            (powerWeightedShiftScoreMean theta S a p - S (a + x) -
              R x * (p + 1 - x * S (a + x))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hfactor hbracket
    have hDne : D x ≠ 0 := hDpos.ne'
    have hAR : A x = R x * D x := by
      change A x = (A x / D x) * D x
      exact (div_mul_cancel₀ (A x) hDne).symm
    have hnum_nonpos :
        ((powerWeightedShiftDensity theta a p x *
            (powerWeightedShiftScoreMean theta S a p - S (a + x))) * D x -
          A x *
            (powerWeightedShiftDensity theta a p x *
              (p + 1 - x * S (a + x)))) ≤ 0 := by
      rw [hAR]
      nlinarith [hprod]
    have hRder := powerWeightedShiftCumulativeRadialRatio_hasDerivAt_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (x := x)
      ha hp hx htheta_pos htheta_deriv htheta_int hS hSprime_pos
    rw [show deriv R x =
        (((powerWeightedShiftDensity theta a p x *
              (powerWeightedShiftScoreMean theta S a p - S (a + x))) * D x -
            A x *
              (powerWeightedShiftDensity theta a p x *
                (p + 1 - x * S (a + x)))) /
          (D x) ^ 2) by
      simpa [R, A, D] using hRder.deriv]
    exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos (sq_nonneg _)

  have hRdiff : ∀ x ∈ Set.Ioi x0, DifferentiableAt ℝ R x := by
    intro x hxI
    have hx : 0 < x := hx0.trans hxI
    have hRx := powerWeightedShiftCumulativeRadialRatio_hasDerivAt_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (x := x)
      ha hp hx htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [R] using hRx.differentiableAt
  have hRcont : ContinuousOn R (Set.Ioi x0) := by
    intro x hxI
    exact (hRdiff x hxI).continuousAt.continuousWithinAt
  have hRdiffOn : DifferentiableOn ℝ R (interior (Set.Ioi x0)) := by
    intro x hxInt
    have hxI : x ∈ Set.Ioi x0 := interior_subset hxInt
    exact (hRdiff x hxI).differentiableWithinAt
  have hRanti : AntitoneOn R (Set.Ioi x0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi x0) hRcont hRdiffOn
    intro x hxInt
    have hxI : x ∈ Set.Ioi x0 := interior_subset hxInt
    exact hRderiv_nonpos x hxI

  exact ⟨x0, hx0, hroot,
    (by simpa [R, q] using hR_le_q),
    (by simpa [R] using hRderiv_nonpos),
    (by simpa [R] using hRanti)⟩

end ScoreCurvatureStarOrder
