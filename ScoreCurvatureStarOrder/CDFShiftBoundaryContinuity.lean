import Mathlib
import ScoreCurvatureStarOrder.ShiftBoundaryContinuity
import ScoreCurvatureStarOrder.DistributionShiftDerivative

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Topology Interval

/-- For every fixed positive endpoint `x`, the unnormalized CDF numerator is
right-continuous at the boundary shift `a = 0`.

Only compact dominated convergence is needed: for shifts `0 ≤ a ≤ 1` and
`t ∈ (0,x]`, the argument `a+t` remains in the compact interval `[0,x+1]`.
No derivative with respect to the shift at the boundary is used. -/
theorem powerWeightedShiftCDFNumerator_continuousWithinAt_zero_within
    {theta S Sprime : ℝ → ℝ} {p x : ℝ}
    (hp : -1 < p) (hx : 0 < x)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ContinuousWithinAt
      (fun a : ℝ => ∫ t : ℝ in Set.Ioc 0 x, t ^ p * theta (a + t))
      (Set.Ici (0 : ℝ)) 0 := by
  have hx1 : 0 ≤ x + 1 := by linarith
  have htheta_cont_Ici : ContinuousOn theta (Set.Ici (0 : ℝ)) :=
    continuousOn_Ici_of_hasDerivWithinAt htheta_deriv
  have htheta_cont_compact : ContinuousOn theta (Set.Icc (0 : ℝ) (x + 1)) :=
    htheta_cont_Ici.mono (by
      intro z hz
      exact hz.1)
  rcases isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.mpr hx1) htheta_cont_compact with
    ⟨zmax, hzmax, hzmaximal⟩
  let C : ℝ := theta zmax
  have hCpos : 0 < C := by
    dsimp [C]
    exact htheta_pos zmax hzmax.1

  let bound : ℝ → ℝ := fun t => C * t ^ p
  have hpow : IntegrableOn (fun t : ℝ => t ^ p) (Set.Ioc 0 x) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le]
    exact intervalIntegral.intervalIntegrable_rpow' hp
  have hbound_set : IntegrableOn bound (Set.Ioc 0 x) := by
    have hlocal : IntegrableOn (fun t : ℝ => C * t ^ p) (Set.Ioc 0 x) :=
      hpow.const_mul C
    simpa [bound] using hlocal

  let F : ℝ → ℝ → ℝ := fun a t => t ^ p * theta (a + t)

  have hparam :
      ∀ᶠ a : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0, a ∈ Set.Icc (0 : ℝ) 1 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with a ha1 ha0
    exact ⟨ha0, ha1.le⟩

  have hF_meas :
      ∀ᶠ a : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0,
        AEStronglyMeasurable (F a) (volume.restrict (Set.Ioc 0 x)) := by
    filter_upwards [hparam] with a ha
    have hint := powerWeightedShift_integrableOn_Ioi_within
      (theta := theta) (S := S) (Sprime := Sprime) (a := a) (p := p)
      ha.1 hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
    have hint_local : IntegrableOn (F a) (Set.Ioc 0 x) := by
      apply hint.mono_set
      intro t ht
      exact ht.1
    exact hint_local.aestronglyMeasurable

  have h_bound :
      ∀ᶠ a : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0,
        ∀ᵐ t ∂volume.restrict (Set.Ioc 0 x), ‖F a t‖ ≤ bound t := by
    filter_upwards [hparam] with a ha
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ha0 : 0 ≤ a := ha.1
    have ha1 : a ≤ 1 := ha.2
    have ht0 : 0 < t := ht.1
    have htx : t ≤ x := ht.2
    have htpow : 0 ≤ t ^ p := Real.rpow_nonneg ht0.le p
    have hat0 : 0 ≤ a + t := add_nonneg ha0 ht0.le
    have hatx1 : a + t ≤ x + 1 := by linarith
    have htheta_le : theta (a + t) ≤ C := by
      dsimp [C]
      exact hzmaximal ⟨hat0, hatx1⟩
    have hFnonneg : 0 ≤ F a t := by
      dsimp [F]
      exact mul_nonneg htpow (htheta_pos (a + t) hat0).le
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg hFnonneg]
    calc
      F a t = t ^ p * theta (a + t) := by rfl
      _ ≤ t ^ p * C := mul_le_mul_of_nonneg_left htheta_le htpow
      _ = bound t := by dsimp [bound]; ring

  have h_lim :
      ∀ᵐ t ∂volume.restrict (Set.Ioc 0 x),
        Tendsto (fun a : ℝ => F a t) (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 (F 0 t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htpos : 0 < t := ht.1
    have htI : t ∈ Set.Ici (0 : ℝ) := htpos.le
    have htheta_at : ContinuousAt theta t :=
      (hasDerivAt_of_pos_of_hasDerivWithinAt_Ici
        htpos (htheta_deriv t htI)).continuousAt
    have harg_full : Tendsto (fun a : ℝ => a + t) (𝓝 (0 : ℝ)) (𝓝 t) := by
      have hcont : ContinuousAt (fun a : ℝ => a + t) 0 := by fun_prop
      simpa using hcont.tendsto
    have harg :
        Tendsto (fun a : ℝ => a + t) (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 t) :=
      harg_full.mono_left nhdsWithin_le_nhds
    have htheta_lim :
        Tendsto (fun a : ℝ => theta (a + t))
          (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 (theta t)) :=
      htheta_at.tendsto.comp harg
    have hconst :
        Tendsto (fun _a : ℝ => t ^ p)
          (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 (t ^ p)) :=
      tendsto_const_nhds
    have hprod :
        Tendsto (fun a : ℝ => t ^ p * theta (a + t))
          (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 (t ^ p * theta t)) :=
      hconst.mul htheta_lim
    simpa [F] using hprod

  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Ioc 0 x))
    (F := F)
    (f := F 0)
    (l := 𝓝[Set.Ici (0 : ℝ)] 0)
    bound hF_meas h_bound hbound_set h_lim

  change Tendsto
    (fun a : ℝ => ∫ t : ℝ in Set.Ioc 0 x, t ^ p * theta (a + t))
    (𝓝[Set.Ici (0 : ℝ)] 0)
    (𝓝 (∫ t : ℝ in Set.Ioc 0 x, t ^ p * theta (0 + t)))
  simpa [F] using hDCT

/-- For every fixed positive spatial endpoint, the normalized CDF is
right-continuous in the shift parameter at `a = 0` under the one-sided
half-line hypotheses. -/
theorem powerWeightedShiftCDF_continuousWithinAt_zero_within
    {theta S Sprime : ℝ → ℝ} {p x : ℝ}
    (hp : -1 < p) (hx : 0 < x)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ContinuousWithinAt
      (fun a : ℝ => powerWeightedShiftCDF theta a p x)
      (Set.Ici (0 : ℝ)) 0 := by
  have hnum := powerWeightedShiftCDFNumerator_continuousWithinAt_zero_within
    (theta := theta) (S := S) (Sprime := Sprime) (p := p) (x := x)
    hp hx htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hden := powerWeightedShiftMoment_continuousWithinAt_zero_within
    (theta := theta) (S := S) (Sprime := Sprime) (p := p)
    hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hMpos : 0 < powerWeightedShiftMoment theta 0 p :=
    powerWeightedShiftMoment_pos_within
      (theta := theta) (S := S) (Sprime := Sprime) (a := 0) (p := p)
      (by norm_num) hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hquot := hnum.div hden hMpos.ne'
  unfold powerWeightedShiftCDF
  have hfun :
      (fun a : ℝ =>
        (∫ t : ℝ in Set.Ioc 0 x, t ^ p * theta (a + t)) /
          powerWeightedShiftMoment theta a p) =
      ((fun a : ℝ => ∫ t : ℝ in Set.Ioc 0 x, t ^ p * theta (a + t)) /
        (fun a : ℝ => powerWeightedShiftMoment theta a p)) := by
    funext a
    rfl
  rw [hfun]
  exact hquot

end ScoreCurvatureStarOrder
