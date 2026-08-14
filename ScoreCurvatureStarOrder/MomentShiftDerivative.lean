import Mathlib
import ScoreCurvatureStarOrder.LocalShiftMajorant

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter Metric
open scoped Interval Topology

/-- At every interior shift `a > 0`, the normalization moment can be
differentiated under the integral sign with respect to the shift parameter. -/
theorem powerWeightedShiftMoment_hasDerivAt
    {theta S Sprime Ssecond : ℝ → ℝ} {a p : ℝ}
    (ha : 0 < a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt Sprime (Ssecond z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ), Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    HasDerivAt
      (fun b : ℝ => powerWeightedShiftMoment theta b p)
      (∫ x : ℝ in Set.Ioi 0,
        x ^ p * (-S (a + x) * theta (a + x))) a := by
  rcases exists_shifted_thetaDeriv_tail_majorant
      htheta_pos htheta_deriv htheta_int hS hSprime hSprime_pos hcurv with
    ⟨T₀, hT₀, htail⟩
  let B : ℝ := max T₀ 1
  have hT₀B : T₀ ≤ B := by
    dsimp [B]
    exact le_max_left _ _
  have h1B : 1 ≤ B := by
    dsimp [B]
    exact le_max_right _ _
  have hB0 : 0 ≤ B := zero_le_one.trans h1B
  have hA0 : 0 ≤ a + 1 := by linarith
  rcases exists_shifted_thetaDeriv_local_majorant
      (A := a + 1) (T := B) hA0 hB0 htheta_deriv hS with
    ⟨C, hC, hlocal⟩

  let s : Set ℝ := Set.Ioo (a / 2) (a + 1)
  have hs : s ∈ 𝓝 a := by
    dsimp [s]
    exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hs_nonneg : ∀ b ∈ s, 0 ≤ b := by
    intro b hb
    dsimp [s] at hb
    rcases hb with ⟨hb_lower, _⟩
    linarith
  have hs_upper : ∀ b ∈ s, b ≤ a + 1 := by
    intro b hb
    dsimp [s] at hb
    exact hb.2.le

  let F : ℝ → ℝ → ℝ := fun b x => x ^ p * theta (b + x)
  let F' : ℝ → ℝ → ℝ := fun b x => x ^ p * (-S (b + x) * theta (b + x))
  let bound : ℝ → ℝ := fun x =>
    if x ≤ B then C * x ^ p else x ^ p * S x * theta x

  have hbound_set : IntegrableOn bound (Set.Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi hB0, integrableOn_union]
    constructor
    · have hpow : IntegrableOn (fun x : ℝ => x ^ p) (Set.Ioc 0 B) := by
        rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hB0]
        exact intervalIntegral.intervalIntegrable_rpow' hp
      have hlocal_int : IntegrableOn (fun x : ℝ => C * x ^ p) (Set.Ioc 0 B) :=
        hpow.const_mul C
      refine IntegrableOn.congr_fun hlocal_int ?_ measurableSet_Ioc
      intro x hx
      simp [bound, hx.2]
    · have hscore0 :
          IntegrableOn (fun x : ℝ => x ^ p * S x * theta x) (Set.Ioi (0 : ℝ)) :=
        powerWeightedUnshifted_score_integrableOn_Ioi
          hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
      have hscoreB :
          IntegrableOn (fun x : ℝ => x ^ p * S x * theta x) (Set.Ioi B) :=
        hscore0.mono_set (fun x hx => hB0.trans_lt hx)
      refine IntegrableOn.congr_fun hscoreB ?_ measurableSet_Ioi
      intro x hx
      have hnot : ¬x ≤ B := not_le.mpr hx
      simp [bound, hnot]

  have hF_meas :
      ∀ᶠ b in 𝓝 a,
        AEStronglyMeasurable (F b) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    filter_upwards [hs] with b hb
    have hb0 : 0 ≤ b := hs_nonneg b hb
    have hint := powerWeightedShift_integrableOn_Ioi
      (theta := theta) (S := S) (Sprime := Sprime) (a := b) (p := p)
      hb0 hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [F] using hint.aestronglyMeasurable

  have hF_int : Integrable (F a) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hint := powerWeightedShift_integrableOn_Ioi
      (theta := theta) (S := S) (Sprime := Sprime) (a := a) (p := p)
      ha.le hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
    change IntegrableOn (fun x : ℝ => x ^ p * theta (a + x)) (Set.Ioi (0 : ℝ))
    exact hint

  have hF'_meas :
      AEStronglyMeasurable (F' a) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hrpow_cont : ContinuousOn (fun x : ℝ => x ^ p) (Set.Ioi (0 : ℝ)) :=
      continuousOn_id.rpow_const (by
        intro x hx
        left
        exact hx.ne')
    have hscore_cont :
        ContinuousOn (fun x : ℝ => -S (a + x) * theta (a + x)) (Set.Ioi (0 : ℝ)) := by
      intro x hx
      have hax0 : 0 ≤ a + x := add_nonneg ha.le hx.le
      have hshift : ContinuousAt (fun y : ℝ => a + y) x := by fun_prop
      have hSc : ContinuousAt (fun y : ℝ => S (a + y)) x :=
        (hS (a + x) hax0).continuousAt.comp hshift
      have htc : ContinuousAt (fun y : ℝ => theta (a + y)) x :=
        (htheta_deriv (a + x) hax0).continuousAt.comp hshift
      exact (hSc.neg.mul htc).continuousWithinAt
    have hcont : ContinuousOn (F' a) (Set.Ioi (0 : ℝ)) := by
      change ContinuousOn
        (fun x : ℝ => x ^ p * (-S (a + x) * theta (a + x))) (Set.Ioi (0 : ℝ))
      exact hrpow_cont.mul hscore_cont
    exact hcont.aestronglyMeasurable measurableSet_Ioi

  have h_bound :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ∀ b ∈ s, ‖F' b x‖ ≤ bound x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro b hb
    have hx0 : 0 ≤ x := hx.le
    have hpow0 : 0 ≤ x ^ p := Real.rpow_nonneg hx0 p
    have hb0 : 0 ≤ b := hs_nonneg b hb
    by_cases hxB : x ≤ B
    · have hbA : b ∈ Set.Icc 0 (a + 1) := ⟨hb0, hs_upper b hb⟩
      have hxI : x ∈ Set.Icc 0 B := ⟨hx0, hxB⟩
      have hloc := hlocal b x hbA hxI
      have hinner : ‖-S (b + x) * theta (b + x)‖ ≤ C := by
        simpa only [Real.norm_eq_abs] using hloc
      have hboundx : bound x = C * x ^ p := by
        simp only [bound, if_pos hxB]
      calc
        ‖F' b x‖ = ‖x ^ p‖ * ‖-S (b + x) * theta (b + x)‖ := by
          change ‖x ^ p * (-S (b + x) * theta (b + x))‖ = _
          exact norm_mul _ _
        _ = x ^ p * ‖-S (b + x) * theta (b + x)‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hpow0]
        _ ≤ x ^ p * C := mul_le_mul_of_nonneg_left hinner hpow0
        _ = bound x := by
          rw [hboundx]
          ring
    · have hBx : B < x := lt_of_not_ge hxB
      have hT₀x : T₀ ≤ x := hT₀B.trans hBx.le
      have htail' := htail b x hb0 hT₀x
      have hinner : ‖-S (b + x) * theta (b + x)‖ ≤ S x * theta x := by
        simpa only [Real.norm_eq_abs] using htail'
      have hboundx : bound x = x ^ p * S x * theta x := by
        simp only [bound, if_neg hxB]
      calc
        ‖F' b x‖ = ‖x ^ p‖ * ‖-S (b + x) * theta (b + x)‖ := by
          change ‖x ^ p * (-S (b + x) * theta (b + x))‖ = _
          exact norm_mul _ _
        _ = x ^ p * ‖-S (b + x) * theta (b + x)‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hpow0]
        _ ≤ x ^ p * (S x * theta x) := mul_le_mul_of_nonneg_left hinner hpow0
        _ = bound x := by
          rw [hboundx]
          ring

  have h_diff :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ∀ b ∈ s, HasDerivAt (F · x) (F' b x) b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro b hb
    have hb0 : 0 ≤ b := hs_nonneg b hb
    have hbx0 : 0 ≤ b + x := add_nonneg hb0 hx.le
    have htheta_shift :
        HasDerivAt (fun y : ℝ => theta (y + x))
          (-S (b + x) * theta (b + x)) b :=
      (htheta_deriv (b + x) hbx0).comp_add_const b x
    have hmul := htheta_shift.const_mul (x ^ p)
    simpa [F, F'] using hmul

  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (x₀ := a) (s := s) (bound := bound)
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    hs hF_meas hF_int hF'_meas h_bound hbound_set h_diff
  change HasDerivAt
    (fun b : ℝ => ∫ x : ℝ, F b x ∂(volume.restrict (Set.Ioi (0 : ℝ))))
    (∫ x : ℝ, F' a x ∂(volume.restrict (Set.Ioi (0 : ℝ)))) a
  exact hparam.2

end ScoreCurvatureStarOrder
