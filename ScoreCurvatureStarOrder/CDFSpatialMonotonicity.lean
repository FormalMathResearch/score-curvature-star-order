import Mathlib
import ScoreCurvatureStarOrder.DistributionShiftDerivativeWithin
import ScoreCurvatureStarOrder.HalfLineRegularity
import ScoreCurvatureStarOrder.Moments

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- The normalized power-weighted density is strictly positive at every
positive observation point under the one-sided half-line assumptions. -/
theorem powerWeightedShiftDensity_pos_within
    {theta S Sprime : ℝ → ℝ} {a p x : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p) (hx : 0 < x)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    0 < powerWeightedShiftDensity theta a p x := by
  have hMpos : 0 < powerWeightedShiftMoment theta a p :=
    powerWeightedShiftMoment_pos_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hax : a + x ∈ Set.Ici (0 : ℝ) := by
    change 0 ≤ a + x
    linarith
  dsimp [powerWeightedShiftDensity]
  exact div_pos
    (mul_pos (Real.rpow_pos_of_pos hx p) (htheta_pos (a + x) hax)) hMpos

/-- For every positive observation point, the spatial derivative of the CDF is
exactly the normalized density.  The endpoint `0` is not differentiated:
ordinary differentiability is used only at the interior point `x>0`. -/
theorem powerWeightedShiftCDF_hasDerivAt_x_within
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
      (fun y : ℝ => powerWeightedShiftCDF theta a p y)
      (powerWeightedShiftDensity theta a p x) x := by
  let g : ℝ → ℝ := fun t => t ^ p * theta (a + t)
  let M : ℝ := powerWeightedShiftMoment theta a p

  have hMpos : 0 < M := by
    dsimp [M]
    exact powerWeightedShiftMoment_pos_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hMne : M ≠ 0 := hMpos.ne'

  have hpow_interval :
      IntervalIntegrable (fun t : ℝ => t ^ p) volume 0 x :=
    intervalIntegral.intervalIntegrable_rpow' hp
  have htheta_shift_Ici :
      ContinuousOn (fun t : ℝ => theta (a + t)) (Set.Ici (0 : ℝ)) :=
    continuousOn_shift_Ici_of_hasDerivWithinAt ha htheta_deriv
  have htheta_uIcc :
      ContinuousOn (fun t : ℝ => theta (a + t)) [[(0 : ℝ), x]] := by
    apply htheta_shift_Ici.mono
    intro t ht
    rw [uIcc_of_le hx.le] at ht
    change 0 ≤ t
    exact ht.1
  have hg_interval : IntervalIntegrable g volume 0 x := by
    change IntervalIntegrable (fun t : ℝ => t ^ p * theta (a + t)) volume 0 x
    exact hpow_interval.mul_continuousOn htheta_uIcc

  have hpow_cont : ContinuousAt (fun t : ℝ => t ^ p) x :=
    continuousAt_id.rpow_const (Or.inl hx.ne')
  have haxpos : 0 < a + x := by linarith
  have htheta_shift_at :
      HasDerivAt (fun t : ℝ => theta (a + t))
        (-S (a + x) * theta (a + x)) x :=
    hasDerivAt_shift_of_pos_of_hasDerivWithinAt_Ici haxpos htheta_deriv
  have hg_cont : ContinuousAt g x := by
    change ContinuousAt (fun t : ℝ => t ^ p * theta (a + t)) x
    exact hpow_cont.mul htheta_shift_at.continuousAt

  have hpow_cont_Ioi : ContinuousOn (fun t : ℝ => t ^ p) (Set.Ioi (0 : ℝ)) :=
    continuousOn_id.rpow_const (by
      intro t ht
      left
      exact ht.ne')
  have hIoi_sub : Set.Ioi (0 : ℝ) ⊆ Set.Ici (0 : ℝ) := by
    intro t ht
    change 0 ≤ t
    exact ht.le
  have hg_cont_Ioi : ContinuousOn g (Set.Ioi (0 : ℝ)) := by
    change ContinuousOn (fun t : ℝ => t ^ p * theta (a + t)) (Set.Ioi (0 : ℝ))
    exact hpow_cont_Ioi.mul (htheta_shift_Ici.mono hIoi_sub)
  have hg_meas_restrict :
      AEStronglyMeasurable g (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hg_cont_Ioi.aestronglyMeasurable measurableSet_Ioi
  have hg_meas : StronglyMeasurableAtFilter g (𝓝 x) :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
      hg_meas_restrict (Ioi_mem_nhds hx)

  have hnum :
      HasDerivAt (fun y : ℝ => ∫ t : ℝ in 0..y, g t) (g x) x :=
    intervalIntegral.integral_hasDerivAt_right hg_interval hg_meas hg_cont
  have hscaled :
      HasDerivAt
        (fun y : ℝ => M⁻¹ * (∫ t : ℝ in 0..y, g t))
        (M⁻¹ * g x) x :=
    hnum.const_mul M⁻¹

  have heq :
      (fun y : ℝ => powerWeightedShiftCDF theta a p y) =ᶠ[𝓝 x]
        (fun y : ℝ => M⁻¹ * (∫ t : ℝ in 0..y, g t)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [powerWeightedShiftCDF, intervalIntegral.integral_of_le hy.le]
    simp only [g, M, div_eq_mul_inv]
    ring
  have hcdf := hscaled.congr_of_eventuallyEq heq
  have hcoef : M⁻¹ * g x = powerWeightedShiftDensity theta a p x := by
    dsimp [g, M, powerWeightedShiftDensity]
    rw [div_eq_mul_inv]
    ring
  rw [← hcoef]
  exact hcdf

/-- Consequently the CDF is strictly increasing on the whole positive
half-line. -/
theorem powerWeightedShiftCDF_strictMonoOn_Ioi_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    StrictMonoOn
      (fun x : ℝ => powerWeightedShiftCDF theta a p x)
      (Set.Ioi (0 : ℝ)) := by
  let F : ℝ → ℝ := fun x => powerWeightedShiftCDF theta a p x
  have hFder : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt F (powerWeightedShiftDensity theta a p x) x := by
    intro x hx
    simpa [F] using powerWeightedShiftCDF_hasDerivAt_x_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (x := x)
      ha hp hx htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hFcont : ContinuousOn F (Set.Ioi (0 : ℝ)) := by
    intro x hx
    exact (hFder x hx).continuousAt.continuousWithinAt
  have hderiv_pos : ∀ x ∈ interior (Set.Ioi (0 : ℝ)), 0 < deriv F x := by
    intro x hxInt
    have hx : x ∈ Set.Ioi (0 : ℝ) := interior_subset hxInt
    rw [(hFder x hx).deriv]
    exact powerWeightedShiftDensity_pos_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (x := x)
      ha hp hx htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hstrict : StrictMonoOn F (Set.Ioi (0 : ℝ)) :=
    strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ)) hFcont hderiv_pos
  simpa [F] using hstrict

end ScoreCurvatureStarOrder
