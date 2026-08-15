import Mathlib
import ScoreCurvatureStarOrder.CDFSpatialMonotonicity

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- The normalized distribution function vanishes at the left endpoint. -/
@[simp] theorem powerWeightedShiftCDF_zero
    (theta : ℝ → ℝ) (a p : ℝ) :
    powerWeightedShiftCDF theta a p 0 = 0 := by
  simp [powerWeightedShiftCDF]

/-- On every compact interval starting at the origin, the normalized CDF is
continuous under the one-sided half-line hypotheses.  No continuity of the
pointwise kernel `x^p * theta (a+x)` at `0` is required: continuity of the
primitive follows from interval integrability. -/
theorem powerWeightedShiftCDF_continuousOn_Icc_zero_within
    {theta S Sprime : ℝ → ℝ} {a p b : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p) (hb : 0 ≤ b)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ContinuousOn
      (fun x : ℝ => powerWeightedShiftCDF theta a p x)
      (Set.Icc (0 : ℝ) b) := by
  let g : ℝ → ℝ := fun x => x ^ p * theta (a + x)
  let M : ℝ := powerWeightedShiftMoment theta a p

  have hgIoi : IntegrableOn g (Set.Ioi (0 : ℝ)) := by
    simpa [g] using
      (powerWeightedShift_integrableOn_Ioi_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)
  have hg_interval : IntervalIntegrable g volume 0 b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb]
    exact hgIoi.mono_set Ioc_subset_Ioi_self
  have hprim_uIcc :
      ContinuousOn (fun y : ℝ => ∫ x : ℝ in 0..y, g x) [[(0 : ℝ), b]] :=
    intervalIntegral.continuousOn_primitive_interval' hg_interval left_mem_uIcc
  have hprim :
      ContinuousOn (fun y : ℝ => ∫ x : ℝ in 0..y, g x) (Set.Icc (0 : ℝ) b) := by
    simpa [uIcc_of_le hb] using hprim_uIcc
  have hscaled :
      ContinuousOn (fun y : ℝ => M⁻¹ * (∫ x : ℝ in 0..y, g x)) (Set.Icc (0 : ℝ) b) :=
    continuousOn_const.mul hprim

  rw [continuousOn_congr (fun y hy => ?_)]
  · exact hscaled
  · rw [powerWeightedShiftCDF, intervalIntegral.integral_of_le hy.1]
    simp only [g, M, div_eq_mul_inv]
    ring

/-- The normalized CDF tends to one at the right endpoint.  This is the
improper-integral statement that the truncated normalization integral exhausts
the full normalization moment. -/
theorem powerWeightedShiftCDF_tendsto_one_atTop_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    Tendsto
      (fun x : ℝ => powerWeightedShiftCDF theta a p x)
      atTop (𝓝 1) := by
  let g : ℝ → ℝ := fun x => x ^ p * theta (a + x)
  let M : ℝ := powerWeightedShiftMoment theta a p

  have hgIoi : IntegrableOn g (Set.Ioi (0 : ℝ)) := by
    simpa [g] using
      (powerWeightedShift_integrableOn_Ioi_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)
  have hMpos : 0 < M := by
    dsimp [M]
    exact powerWeightedShiftMoment_pos_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hMne : M ≠ 0 := hMpos.ne'

  have hprim :
      Tendsto (fun x : ℝ => ∫ t : ℝ in 0..x, g t) atTop (𝓝 M) := by
    simpa [g, M, powerWeightedShiftMoment] using
      (MeasureTheory.intervalIntegral_tendsto_integral_Ioi
        (f := g) (μ := volume) (a := (0 : ℝ))
        (b := fun x : ℝ => x) hgIoi tendsto_id)
  have hconst :
      Tendsto (fun _ : ℝ => M⁻¹) atTop (𝓝 (M⁻¹)) :=
    tendsto_const_nhds
  have hscaled :
      Tendsto
        (fun x : ℝ => M⁻¹ * (∫ t : ℝ in 0..x, g t))
        atTop (𝓝 1) := by
    have hmul := hconst.mul hprim
    simpa [hMne] using hmul

  refine hscaled.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [powerWeightedShiftCDF, intervalIntegral.integral_of_le hx]
  simp only [g, M, div_eq_mul_inv]
  ring

/-- Every level `u∈(0,1)` is attained at exactly one positive point by the
normalized CDF.  This is the existence-and-uniqueness theorem needed before a
canonical quantile can be introduced. -/
theorem existsUnique_pos_powerWeightedShiftCDF_eq_within
    {theta S Sprime : ℝ → ℝ} {a p u : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p) (hu0 : 0 < u) (hu1 : u < 1)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ∃! q : ℝ,
      0 < q ∧ powerWeightedShiftCDF theta a p q = u := by
  let F : ℝ → ℝ := fun x => powerWeightedShiftCDF theta a p x
  have hlim : Tendsto F atTop (𝓝 1) := by
    simpa [F] using
      (powerWeightedShiftCDF_tendsto_one_atTop_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)
  have habove : ∀ᶠ x : ℝ in atTop, u < F x :=
    hlim.eventually (Ioi_mem_nhds hu1)
  have hpositive : ∀ᶠ x : ℝ in atTop, 0 < x := Ioi_mem_atTop 0
  rcases (habove.and hpositive).exists with ⟨b, hub, hb⟩

  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) b) := by
    simpa [F] using
      (powerWeightedShiftCDF_continuousOn_Icc_zero_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p) (b := b)
        ha hp hb.le htheta_pos htheta_deriv htheta_int hS hSprime_pos)
  have huIcc : u ∈ Set.Icc (F 0) (F b) := by
    constructor
    · simpa [F] using hu0.le
    · exact hub.le
  have huImage : u ∈ F '' Set.Icc (0 : ℝ) b :=
    isPreconnected_Icc.intermediate_value
      (left_mem_Icc.mpr hb.le) (right_mem_Icc.mpr hb.le) hcont huIcc
  rcases huImage with ⟨q, hqIcc, hFq⟩
  have hqpos : 0 < q := by
    rcases hqIcc.1.eq_or_lt with hqzero | hqpos
    · subst q
      simp [F] at hFq
      linarith
    · exact hqpos

  refine ⟨q, ⟨hqpos, by simpa [F] using hFq⟩, ?_⟩
  intro y hy
  have hstrict : StrictMonoOn F (Set.Ioi (0 : ℝ)) := by
    simpa [F] using
      (powerWeightedShiftCDF_strictMonoOn_Ioi_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)
  apply hstrict.injOn hy.1 hqpos
  exact hy.2.trans (by simpa [F] using hFq.symm)

end ScoreCurvatureStarOrder
