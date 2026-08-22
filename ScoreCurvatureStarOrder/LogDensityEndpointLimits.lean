import Mathlib
import ScoreCurvatureStarOrder.LogDensityIntegrability

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Topology

/-- Generic left-endpoint control for an integrable half-line integrand.

If `g` is integrable on `(0, ∞)` and `0 < R`, then the interval integral over
`[ε, R]` converges to the interval integral over `[0, R]` as `ε ↓ 0`.
The proof deliberately uses continuity of the interval-integral primitive rather
than any pointwise regularity of `g` at `0`; this is the interface needed for
logarithmic integrands with an endpoint singularity. -/
private theorem intervalIntegral_tendsto_left_zero_of_integrableOn_Ioi
    {g : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hint : IntegrableOn g (Set.Ioi (0 : ℝ))) :
    Tendsto
      (fun ε : ℝ => ∫ x : ℝ in ε..R, g x)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x : ℝ in 0..R, g x)) := by
  have hIoc : IntegrableOn g (Set.Ioc 0 R) :=
    hint.mono_set Set.Ioc_subset_Ioi_self
  have hinterval : IntervalIntegrable g volume 0 R :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).2 hIoc
  have hintervalMinMax :
      IntervalIntegrable g volume (min 0 0) (max 0 R) := by
    simpa [max_eq_right hR.le] using hinterval

  have hcontIcc :
      ContinuousWithinAt
        (fun ε : ℝ => ∫ x : ℝ in 0..ε, g x)
        (Set.Icc 0 R) 0 := by
    simpa [max_eq_right hR.le] using
      (intervalIntegral.continuousWithinAt_primitive
        (μ := volume) (f := g)
        (a := (0 : ℝ)) (b₀ := (0 : ℝ)) (b₁ := (0 : ℝ)) (b₂ := R)
        (by simp) hintervalMinMax)
  have hcontGT :
      ContinuousWithinAt
        (fun ε : ℝ => ∫ x : ℝ in 0..ε, g x)
        (Set.Ioi 0) 0 :=
    hcontIcc.mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGT_of_mem ⟨le_rfl, hR⟩)
  have hsmall :
      Tendsto
        (fun ε : ℝ => ∫ x : ℝ in 0..ε, g x)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hcontGT.tendsto

  have hsub :
      Tendsto
        (fun ε : ℝ =>
          (∫ x : ℝ in 0..R, g x) - ∫ x : ℝ in 0..ε, g x)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ x : ℝ in 0..R, g x)) := by
    simpa using (tendsto_const_nhds.sub hsmall)

  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hintervalε : IntervalIntegrable g volume 0 ε := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hε.le).2 ?_
    exact hint.mono_set Set.Ioc_subset_Ioi_self
  exact intervalIntegral.integral_interval_sub_left hinterval hintervalε

/-- As the upper cutoff tends to `+∞`, the finite interval integral of `log x`
against the normalized power-weighted shifted density converges to the full
half-line log moment.  This is a direct improper-integral consequence of the
already verified normalized-density integrability. -/
theorem powerWeightedShift_log_density_intervalIntegral_tendsto_Ioi_within
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
      (fun R : ℝ => ∫ x : ℝ in 0..R,
        Real.log x * powerWeightedShiftDensity theta a p x)
      atTop
      (𝓝 (∫ x : ℝ in Set.Ioi 0,
        Real.log x * powerWeightedShiftDensity theta a p x)) := by
  have hint := powerWeightedShift_log_density_integrableOn_Ioi_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p)
    ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  simpa using
    (MeasureTheory.intervalIntegral_tendsto_integral_Ioi
      (μ := volume)
      (f := fun x : ℝ =>
        Real.log x * powerWeightedShiftDensity theta a p x)
      (a := (0 : ℝ)) hint tendsto_id)

/-- For fixed `R > 0`, the lower cutoff may be sent to zero from the right in
the normalized logarithmic moment. -/
theorem powerWeightedShift_log_density_intervalIntegral_tendsto_left_zero_within
    {theta S Sprime : ℝ → ℝ} {a p R : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p) (hR : 0 < R)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    Tendsto
      (fun ε : ℝ => ∫ x : ℝ in ε..R,
        Real.log x * powerWeightedShiftDensity theta a p x)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x : ℝ in 0..R,
        Real.log x * powerWeightedShiftDensity theta a p x)) := by
  have hint := powerWeightedShift_log_density_integrableOn_Ioi_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p)
    ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  exact intervalIntegral_tendsto_left_zero_of_integrableOn_Ioi hR hint

/-- The squared-log analogue of
`powerWeightedShift_log_density_intervalIntegral_tendsto_Ioi_within`. -/
theorem powerWeightedShift_log_sq_density_intervalIntegral_tendsto_Ioi_within
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
      (fun R : ℝ => ∫ x : ℝ in 0..R,
        (Real.log x) ^ 2 * powerWeightedShiftDensity theta a p x)
      atTop
      (𝓝 (∫ x : ℝ in Set.Ioi 0,
        (Real.log x) ^ 2 * powerWeightedShiftDensity theta a p x)) := by
  have hint := powerWeightedShift_log_sq_density_integrableOn_Ioi_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p)
    ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  simpa using
    (MeasureTheory.intervalIntegral_tendsto_integral_Ioi
      (μ := volume)
      (f := fun x : ℝ =>
        (Real.log x) ^ 2 * powerWeightedShiftDensity theta a p x)
      (a := (0 : ℝ)) hint tendsto_id)

/-- For fixed `R > 0`, the lower cutoff may be sent to zero from the right in
the normalized squared-logarithmic moment. -/
theorem powerWeightedShift_log_sq_density_intervalIntegral_tendsto_left_zero_within
    {theta S Sprime : ℝ → ℝ} {a p R : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p) (hR : 0 < R)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    Tendsto
      (fun ε : ℝ => ∫ x : ℝ in ε..R,
        (Real.log x) ^ 2 * powerWeightedShiftDensity theta a p x)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x : ℝ in 0..R,
        (Real.log x) ^ 2 * powerWeightedShiftDensity theta a p x)) := by
  have hint := powerWeightedShift_log_sq_density_integrableOn_Ioi_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p)
    ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  exact intervalIntegral_tendsto_left_zero_of_integrableOn_Ioi hR hint

end ScoreCurvatureStarOrder
