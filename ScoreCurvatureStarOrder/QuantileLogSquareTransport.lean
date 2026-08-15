import Mathlib
import ScoreCurvatureStarOrder.QuantileLogTransport

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- Finite-window quantile transport for the squared logarithm.

For `0 < ε < R`, substitution by the normalized CDF gives

`∫_{F(ε)}^{F(R)} (log(Q(u)))^2 du = ∫_ε^R (log x)^2 f_{p,a}(x) dx`.

This is the second-log-moment companion to the already verified finite-window
logarithmic transport.  It deliberately uses the same CDF derivative,
quantile level-continuity, and inverse identity `Q(F(x)) = x`, so that the
first and second moment transports share one analytic architecture. -/
theorem powerWeightedShift_logQuantile_sq_integral_CDF_window_within
    {theta S Sprime : ℝ → ℝ} {a p ε R : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p) (hε : 0 < ε) (hεR : ε < R)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    (∫ u : ℝ in
        powerWeightedShiftCDF theta a p ε..
          powerWeightedShiftCDF theta a p R,
        (Real.log (powerWeightedShiftQuantile theta a p u)) ^ 2) =
      ∫ x : ℝ in ε..R,
        (Real.log x) ^ 2 * powerWeightedShiftDensity theta a p x := by
  let F : ℝ → ℝ := fun x => powerWeightedShiftCDF theta a p x
  let Q : ℝ → ℝ := fun u => powerWeightedShiftQuantile theta a p u
  let f : ℝ → ℝ := fun x => powerWeightedShiftDensity theta a p x

  have hR : 0 < R := hε.trans hεR

  have hFcont0 : ContinuousOn F (Set.Icc (0 : ℝ) R) := by
    simpa [F] using
      (powerWeightedShiftCDF_continuousOn_Icc_zero_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p) (b := R)
        ha hp hR.le htheta_pos htheta_deriv htheta_int hS hSprime_pos)
  have hFcont : ContinuousOn F [[ε, R]] := by
    rw [uIcc_of_le hεR.le]
    exact hFcont0.mono (by
      intro x hx
      exact ⟨hε.le.trans hx.1, hx.2⟩)

  have hFder :
      ∀ x ∈ Set.Ioo (min ε R) (max ε R),
        HasDerivWithinAt F (f x) (Set.Ioi x) x := by
    intro x hx
    have hxwin : x ∈ Set.Ioo ε R := by
      simpa [min_eq_left hεR.le, max_eq_right hεR.le] using hx
    have hxpos : 0 < x := hε.trans hxwin.1
    have hder := powerWeightedShiftCDF_hasDerivAt_x_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (x := x)
      ha hp hxpos htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [F, f] using hder.hasDerivWithinAt

  have hpow : ContinuousOn (fun x : ℝ => x ^ p) (Set.Icc ε R) :=
    continuousOn_id.rpow_const (by
      intro x hx
      left
      exact (hε.trans_le hx.1).ne')
  have hthetaIci :
      ContinuousOn (fun x : ℝ => theta (a + x)) (Set.Ici (0 : ℝ)) :=
    continuousOn_shift_Ici_of_hasDerivWithinAt ha htheta_deriv
  have hthetaWin :
      ContinuousOn (fun x : ℝ => theta (a + x)) (Set.Icc ε R) :=
    hthetaIci.mono (by
      intro x hx
      exact (hε.le.trans hx.1))
  have hfcontIcc : ContinuousOn f (Set.Icc ε R) := by
    simpa [f, powerWeightedShiftDensity, div_eq_mul_inv] using
      (hpow.mul hthetaWin).mul_const (powerWeightedShiftMoment theta a p)⁻¹
  have hfcont : ContinuousOn f [[ε, R]] := by
    simpa [uIcc_of_le hεR.le] using hfcontIcc

  have himage : F '' [[ε, R]] ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro u hu
    rcases hu with ⟨x, hx, rfl⟩
    have hxIcc : x ∈ Set.Icc ε R := by
      simpa [uIcc_of_le hεR.le] using hx
    have hxpos : 0 < x := hε.trans_le hxIcc.1
    simpa [F] using
      (powerWeightedShiftCDF_pos_lt_one_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p) (x := x)
        ha hp hxpos htheta_pos htheta_deriv htheta_int hS hSprime_pos)

  have hQcontIoo : ContinuousOn Q (Set.Ioo (0 : ℝ) 1) := by
    simpa [Q] using
      (powerWeightedShiftQuantile_continuousOn_Ioo_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)
  have hQcont : ContinuousOn Q (F '' [[ε, R]]) :=
    hQcontIoo.mono himage
  have hQne : ∀ u ∈ F '' [[ε, R]], Q u ≠ 0 := by
    intro u hu
    have huIoo := himage hu
    have hQ := powerWeightedShiftQuantile_pos_and_CDF_eq_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (u := u)
      ha hp huIoo.1 huIoo.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [Q] using hQ.1.ne'
  have hlogQcont :
      ContinuousOn (fun u : ℝ => Real.log (Q u)) (F '' [[ε, R]]) :=
    hQcont.log hQne
  have hsqlogQcont :
      ContinuousOn (fun u : ℝ => (Real.log (Q u)) ^ 2) (F '' [[ε, R]]) :=
    hlogQcont.pow 2

  have hsub := intervalIntegral.integral_comp_mul_deriv''
    (f := F) (f' := f) (g := fun u : ℝ => (Real.log (Q u)) ^ 2)
    hFcont hFder hfcont hsqlogQcont

  have hintegrand :
      Set.EqOn
        (fun x : ℝ => ((fun u : ℝ => (Real.log (Q u)) ^ 2) ∘ F) x * f x)
        (fun x : ℝ => (Real.log x) ^ 2 * f x)
        [[ε, R]] := by
    intro x hx
    have hxIcc : x ∈ Set.Icc ε R := by
      simpa [uIcc_of_le hεR.le] using hx
    have hxpos : 0 < x := hε.trans_le hxIcc.1
    have hInv := powerWeightedShiftQuantile_CDF_eq_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (x := x)
      ha hp hxpos htheta_pos htheta_deriv htheta_int hS hSprime_pos
    have hQF : Q (F x) = x := by
      simpa [Q, F] using hInv
    simp only [Function.comp_apply, hQF]

  change (∫ u : ℝ in F ε..F R, (Real.log (Q u)) ^ 2) =
    ∫ x : ℝ in ε..R, (Real.log x) ^ 2 * f x
  calc
    _ = ∫ x : ℝ in ε..R,
        ((fun u : ℝ => (Real.log (Q u)) ^ 2) ∘ F) x * f x := hsub.symm
    _ = _ := intervalIntegral.integral_congr hintegrand

end ScoreCurvatureStarOrder
