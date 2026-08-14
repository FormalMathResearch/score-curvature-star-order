import Mathlib
import ScoreCurvatureStarOrder.DistributionShiftDerivative
import ScoreCurvatureStarOrder.ShiftDerivativeMajorant
import ScoreCurvatureStarOrder.HalfLineRegularity

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter Metric
open scoped Interval Topology

/-- At every interior shift `a > 0`, the normalization moment may be
differentiated with respect to the shift parameter under the mathematically
natural one-sided regularity assumptions on `[0,∞)`.

The parameter derivative is ordinary because the local parameter neighborhood
is chosen inside `(0,∞)`.  Pointwise ordinary derivatives of `theta` are
reconstructed only at arguments `b+x>0`; no two-sided derivative at `0` is
used. -/
theorem powerWeightedShiftMoment_hasDerivAt_within
    {theta S Sprime Ssecond : ℝ → ℝ} {a p : ℝ}
    (ha : 0 < a) (hp : -1 < p)
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
    HasDerivAt
      (fun b : ℝ => powerWeightedShiftMoment theta b p)
      (∫ x : ℝ in Set.Ioi 0,
        x ^ p * (-S (a + x) * theta (a + x))) a := by
  rcases exists_shifted_thetaDeriv_tail_majorant_within
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
  rcases exists_shifted_thetaDeriv_local_majorant_within
      (A := a + 1) (T := B) hA0 hB0 htheta_deriv hS with
    ⟨C, hC, hlocal⟩

  let s : Set ℝ := Set.Ioo (a / 2) (a + 1)
  have hs : s ∈ 𝓝 a := by
    dsimp [s]
    exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hs_nonneg : ∀ b ∈ s, 0 ≤ b := by
    intro b hb
    dsimp [s] at hb
    linarith [hb.1]
  have hs_pos : ∀ b ∈ s, 0 < b := by
    intro b hb
    dsimp [s] at hb
    linarith [hb.1, ha]
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
        powerWeightedUnshifted_score_integrableOn_Ioi_within
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
    have hint := powerWeightedShift_integrableOn_Ioi_within
      (theta := theta) (S := S) (Sprime := Sprime) (a := b) (p := p)
      hb0 hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [F] using hint.aestronglyMeasurable

  have hF_int : Integrable (F a) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hint := powerWeightedShift_integrableOn_Ioi_within
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
    have hSshift : ContinuousOn (fun x : ℝ => S (a + x)) (Set.Ici (0 : ℝ)) :=
      continuousOn_shift_Ici_of_hasDerivWithinAt ha.le hS
    have hthetashift :
        ContinuousOn (fun x : ℝ => theta (a + x)) (Set.Ici (0 : ℝ)) :=
      continuousOn_shift_Ici_of_hasDerivWithinAt ha.le htheta_deriv
    have hIoi_sub : Set.Ioi (0 : ℝ) ⊆ Set.Ici (0 : ℝ) := fun _ hx => hx.le
    have hscore_cont :
        ContinuousOn (fun x : ℝ => -S (a + x) * theta (a + x)) (Set.Ioi (0 : ℝ)) :=
      ((hSshift.mono hIoi_sub).neg).mul (hthetashift.mono hIoi_sub)
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
    have hbpos : 0 < b := hs_pos b hb
    have hbxpos : 0 < b + x := add_pos hbpos hx
    have htheta_at : HasDerivAt theta (-S (b + x) * theta (b + x)) (b + x) :=
      hasDerivAt_of_pos_of_hasDerivWithinAt_Ici
        hbxpos (htheta_deriv (b + x) hbxpos.le)
    have htheta_shift :
        HasDerivAt (fun y : ℝ => theta (y + x))
          (-S (b + x) * theta (b + x)) b :=
      htheta_at.comp_add_const b x
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

/-- The logarithmic shift derivative of the normalization moment is minus the
score mean, under one-sided half-line regularity. -/
theorem powerWeightedShiftMoment_log_hasDerivAt_within
    {theta S Sprime Ssecond : ℝ → ℝ} {a p : ℝ}
    (ha : 0 < a) (hp : -1 < p)
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
    HasDerivAt
      (fun b : ℝ => Real.log (powerWeightedShiftMoment theta b p))
      (-(∫ x : ℝ in Set.Ioi 0,
        S (a + x) * powerWeightedShiftDensity theta a p x)) a := by
  have hMderiv := powerWeightedShiftMoment_hasDerivAt_within
    (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
    (a := a) (p := p) ha hp htheta_pos htheta_deriv htheta_int hS hSprime
    hSprime_pos hcurv
  have hMpos : 0 < powerWeightedShiftMoment theta a p :=
    powerWeightedShiftMoment_pos_within
      ha.le hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hlog := hMderiv.log hMpos.ne'
  have hcoef :
      (∫ x : ℝ in Set.Ioi 0,
        x ^ p * (-S (a + x) * theta (a + x))) /
          powerWeightedShiftMoment theta a p =
      -(∫ x : ℝ in Set.Ioi 0,
        S (a + x) * powerWeightedShiftDensity theta a p x) := by
    calc
      (∫ x : ℝ in Set.Ioi 0,
          x ^ p * (-S (a + x) * theta (a + x))) /
            powerWeightedShiftMoment theta a p =
          (powerWeightedShiftMoment theta a p)⁻¹ *
            ∫ x : ℝ in Set.Ioi 0,
              x ^ p * (-S (a + x) * theta (a + x)) := by
        rw [div_eq_mul_inv]
        ring
      _ = ∫ x : ℝ in Set.Ioi 0,
          (powerWeightedShiftMoment theta a p)⁻¹ *
            (x ^ p * (-S (a + x) * theta (a + x))) := by
        rw [integral_const_mul]
      _ = ∫ x : ℝ in Set.Ioi 0,
          -(S (a + x) * powerWeightedShiftDensity theta a p x) := by
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro x hx
        dsimp [powerWeightedShiftDensity]
        rw [div_eq_mul_inv]
        ring
      _ = -(∫ x : ℝ in Set.Ioi 0,
          S (a + x) * powerWeightedShiftDensity theta a p x) := by
        rw [integral_neg]
  rw [hcoef] at hlog
  exact hlog

/-- For a positive observation endpoint and an interior shift, the
unnormalized CDF numerator is differentiable in the shift under one-sided
regularity.  Ordinary derivatives are reconstructed only at `b+t>0`. -/
theorem powerWeightedShiftCDFNumerator_hasDerivAt_within
    {theta S Sprime : ℝ → ℝ} {a p x : ℝ}
    (ha : 0 < a) (hp : -1 < p) (hx : 0 < x)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z) :
    HasDerivAt
      (fun b : ℝ => ∫ t : ℝ in Set.Ioc 0 x, t ^ p * theta (b + t))
      (∫ t : ℝ in Set.Ioc 0 x,
        t ^ p * (-S (a + t) * theta (a + t))) a := by
  have hA0 : 0 ≤ a + 1 := by linarith
  rcases exists_shifted_thetaDeriv_local_majorant_within
      (A := a + 1) (T := x) hA0 hx.le htheta_deriv hS with
    ⟨C, hC, hlocal⟩

  let s : Set ℝ := Set.Ioo (a / 2) (a + 1)
  have hs : s ∈ 𝓝 a := by
    dsimp [s]
    exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hs_nonneg : ∀ b ∈ s, 0 ≤ b := by
    intro b hb
    dsimp [s] at hb
    linarith [hb.1]
  have hs_pos : ∀ b ∈ s, 0 < b := by
    intro b hb
    dsimp [s] at hb
    linarith [hb.1, ha]
  have hs_upper : ∀ b ∈ s, b ≤ a + 1 := by
    intro b hb
    dsimp [s] at hb
    exact hb.2.le

  let F : ℝ → ℝ → ℝ := fun b t => t ^ p * theta (b + t)
  let F' : ℝ → ℝ → ℝ := fun b t =>
    t ^ p * (-S (b + t) * theta (b + t))
  let bound : ℝ → ℝ := fun t => C * t ^ p

  have hpow_interval :
      IntervalIntegrable (fun t : ℝ => t ^ p) volume 0 x :=
    intervalIntegral.intervalIntegrable_rpow' hp
  have hpow_set :
      IntegrableOn (fun t : ℝ => t ^ p) (Set.Ioc 0 x) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le]
    exact hpow_interval
  have hbound_int :
      Integrable bound (volume.restrict (Set.Ioc 0 x)) := by
    simpa [bound] using hpow_set.const_mul C

  have hF_meas :
      ∀ᶠ b in 𝓝 a,
        AEStronglyMeasurable (F b) (volume.restrict (Set.Ioc 0 x)) := by
    filter_upwards [hs] with b hb
    have hb0 : 0 ≤ b := hs_nonneg b hb
    have htheta_cont_Ici :
        ContinuousOn (fun t : ℝ => theta (b + t)) (Set.Ici (0 : ℝ)) :=
      continuousOn_shift_Ici_of_hasDerivWithinAt hb0 htheta_deriv
    have htheta_cont :
        ContinuousOn (fun t : ℝ => theta (b + t)) [[0, x]] := by
      apply htheta_cont_Ici.mono
      intro t ht
      rw [uIcc_of_le hx.le] at ht
      exact ht.1
    have hint : IntervalIntegrable (F b) volume 0 x := by
      change IntervalIntegrable (fun t : ℝ => t ^ p * theta (b + t)) volume 0 x
      exact hpow_interval.mul_continuousOn htheta_cont
    have hint_set : IntegrableOn (F b) (Set.Ioc 0 x) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le]
      exact hint
    exact hint_set.aestronglyMeasurable

  have hF_int : Integrable (F a) (volume.restrict (Set.Ioc 0 x)) := by
    have htheta_cont_Ici :
        ContinuousOn (fun t : ℝ => theta (a + t)) (Set.Ici (0 : ℝ)) :=
      continuousOn_shift_Ici_of_hasDerivWithinAt ha.le htheta_deriv
    have htheta_cont :
        ContinuousOn (fun t : ℝ => theta (a + t)) [[0, x]] := by
      apply htheta_cont_Ici.mono
      intro t ht
      rw [uIcc_of_le hx.le] at ht
      exact ht.1
    have hint : IntervalIntegrable (F a) volume 0 x := by
      change IntervalIntegrable (fun t : ℝ => t ^ p * theta (a + t)) volume 0 x
      exact hpow_interval.mul_continuousOn htheta_cont
    change IntegrableOn (F a) (Set.Ioc 0 x)
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le]
    exact hint

  have hF'_meas :
      AEStronglyMeasurable (F' a) (volume.restrict (Set.Ioc 0 x)) := by
    have hS_cont_Ici :
        ContinuousOn (fun t : ℝ => S (a + t)) (Set.Ici (0 : ℝ)) :=
      continuousOn_shift_Ici_of_hasDerivWithinAt ha.le hS
    have htheta_cont_Ici :
        ContinuousOn (fun t : ℝ => theta (a + t)) (Set.Ici (0 : ℝ)) :=
      continuousOn_shift_Ici_of_hasDerivWithinAt ha.le htheta_deriv
    have huIcc_sub : [[0, x]] ⊆ Set.Ici (0 : ℝ) := by
      intro t ht
      rw [uIcc_of_le hx.le] at ht
      exact ht.1
    have hcoeff_cont :
        ContinuousOn
          (fun t : ℝ => -S (a + t) * theta (a + t)) [[0, x]] :=
      ((hS_cont_Ici.mono huIcc_sub).neg).mul (htheta_cont_Ici.mono huIcc_sub)
    have hint : IntervalIntegrable (F' a) volume 0 x := by
      change IntervalIntegrable
        (fun t : ℝ => t ^ p * (-S (a + t) * theta (a + t))) volume 0 x
      exact hpow_interval.mul_continuousOn hcoeff_cont
    have hint_set : IntegrableOn (F' a) (Set.Ioc 0 x) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le]
      exact hint
    exact hint_set.aestronglyMeasurable

  have h_bound :
      ∀ᵐ t ∂volume.restrict (Set.Ioc 0 x),
        ∀ b ∈ s, ‖F' b t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro b hb
    have hb0 : 0 ≤ b := hs_nonneg b hb
    have hpow0 : 0 ≤ t ^ p := Real.rpow_nonneg ht.1.le p
    have hbI : b ∈ Set.Icc 0 (a + 1) := ⟨hb0, hs_upper b hb⟩
    have htI : t ∈ Set.Icc 0 x := ⟨ht.1.le, ht.2⟩
    have hloc := hlocal b t hbI htI
    have hinner : ‖-S (b + t) * theta (b + t)‖ ≤ C := by
      simpa only [Real.norm_eq_abs] using hloc
    calc
      ‖F' b t‖ = ‖t ^ p‖ * ‖-S (b + t) * theta (b + t)‖ := by
        change ‖t ^ p * (-S (b + t) * theta (b + t))‖ = _
        exact norm_mul _ _
      _ = t ^ p * ‖-S (b + t) * theta (b + t)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hpow0]
      _ ≤ t ^ p * C := mul_le_mul_of_nonneg_left hinner hpow0
      _ = bound t := by
        dsimp [bound]
        ring

  have h_diff :
      ∀ᵐ t ∂volume.restrict (Set.Ioc 0 x),
        ∀ b ∈ s, HasDerivAt (F · t) (F' b t) b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro b hb
    have hbpos : 0 < b := hs_pos b hb
    have hbtpos : 0 < b + t := add_pos hbpos ht.1
    have htheta_at : HasDerivAt theta (-S (b + t) * theta (b + t)) (b + t) :=
      hasDerivAt_of_pos_of_hasDerivWithinAt_Ici
        hbtpos (htheta_deriv (b + t) hbtpos.le)
    have htheta_shift :
        HasDerivAt (fun y : ℝ => theta (y + t))
          (-S (b + t) * theta (b + t)) b :=
      htheta_at.comp_add_const b t
    have hmul := htheta_shift.const_mul (t ^ p)
    simpa [F, F'] using hmul

  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (x₀ := a) (s := s) (bound := bound)
    (μ := volume.restrict (Set.Ioc 0 x))
    hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  change HasDerivAt
    (fun b : ℝ => ∫ t : ℝ, F b t ∂(volume.restrict (Set.Ioc 0 x)))
    (∫ t : ℝ, F' a t ∂(volume.restrict (Set.Ioc 0 x))) a
  exact hparam.2

/-- At every interior shift `a>0` and positive observation `x>0`, the shift
derivative of the normalized CDF is the cumulative centered-score numerator
`A`, under one-sided half-line regularity. -/
theorem powerWeightedShiftCDF_hasDerivAt_within
    {theta S Sprime Ssecond : ℝ → ℝ} {a p x : ℝ}
    (ha : 0 < a) (hp : -1 < p) (hx : 0 < x)
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
    HasDerivAt
      (fun b : ℝ => powerWeightedShiftCDF theta b p x)
      (powerWeightedShiftCumulativeShiftNumerator theta S a p x) a := by
  let N : ℝ := ∫ t : ℝ in Set.Ioc 0 x, t ^ p * theta (a + t)
  let N' : ℝ := ∫ t : ℝ in Set.Ioc 0 x,
    t ^ p * (-S (a + t) * theta (a + t))
  let M : ℝ := powerWeightedShiftMoment theta a p
  let D : ℝ := ∫ t : ℝ in Set.Ioi 0,
    t ^ p * (-S (a + t) * theta (a + t))
  let G : ℝ := powerWeightedShiftScoreMean theta S a p

  have hNderiv :
      HasDerivAt
        (fun b : ℝ => ∫ t : ℝ in Set.Ioc 0 x, t ^ p * theta (b + t)) N' a := by
    simpa [N'] using powerWeightedShiftCDFNumerator_hasDerivAt_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (x := x) ha hp hx htheta_deriv hS
  have hMderiv :
      HasDerivAt (fun b : ℝ => powerWeightedShiftMoment theta b p) D a := by
    simpa [D] using powerWeightedShiftMoment_hasDerivAt_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (a := a) (p := p) ha hp htheta_pos htheta_deriv htheta_int hS hSprime
      hSprime_pos hcurv
  have hMpos : 0 < M := by
    dsimp [M]
    exact powerWeightedShiftMoment_pos_within
      ha.le hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hMne : M ≠ 0 := hMpos.ne'

  have hrawlog := hMderiv.log hMne
  have hmeanlog := powerWeightedShiftMoment_log_hasDerivAt_within
    (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
    (a := a) (p := p) ha hp htheta_pos htheta_deriv htheta_int hS hSprime
    hSprime_pos hcurv
  have hDdiv : D / M = -G := by
    calc
      D / M = deriv (fun b : ℝ => Real.log (powerWeightedShiftMoment theta b p)) a := by
        simpa [M] using hrawlog.deriv.symm
      _ = -G := by
        simpa [G, powerWeightedShiftScoreMean] using hmeanlog.deriv
  have hD : D = (-G) * M := (div_eq_iff hMne).mp hDdiv

  have hbaseIoi :
      IntegrableOn (fun t : ℝ => t ^ p * theta (a + t)) (Set.Ioi (0 : ℝ)) :=
    powerWeightedShift_integrableOn_Ioi_within
      ha.le hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hbase :
      Integrable (fun t : ℝ => t ^ p * theta (a + t))
        (volume.restrict (Set.Ioc 0 x)) :=
    (hbaseIoi.mono_set (fun t ht => ht.1)).integrable

  have hpow_interval :
      IntervalIntegrable (fun t : ℝ => t ^ p) volume 0 x :=
    intervalIntegral.intervalIntegrable_rpow' hp
  have hS_shift_Ici :
      ContinuousOn (fun t : ℝ => S (a + t)) (Set.Ici (0 : ℝ)) :=
    continuousOn_shift_Ici_of_hasDerivWithinAt ha.le hS
  have htheta_shift_Ici :
      ContinuousOn (fun t : ℝ => theta (a + t)) (Set.Ici (0 : ℝ)) :=
    continuousOn_shift_Ici_of_hasDerivWithinAt ha.le htheta_deriv
  have huIcc_sub : [[0, x]] ⊆ Set.Ici (0 : ℝ) := by
    intro t ht
    rw [uIcc_of_le hx.le] at ht
    exact ht.1
  have hscore_coeff_cont :
      ContinuousOn
        (fun t : ℝ => -S (a + t) * theta (a + t)) [[0, x]] :=
    ((hS_shift_Ici.mono huIcc_sub).neg).mul (htheta_shift_Ici.mono huIcc_sub)
  have hscore_interval :
      IntervalIntegrable
        (fun t : ℝ => t ^ p * (-S (a + t) * theta (a + t))) volume 0 x :=
    hpow_interval.mul_continuousOn hscore_coeff_cont
  have hscore :
      Integrable (fun t : ℝ => t ^ p * (-S (a + t) * theta (a + t)))
        (volume.restrict (Set.Ioc 0 x)) := by
    change IntegrableOn
      (fun t : ℝ => t ^ p * (-S (a + t) * theta (a + t))) (Set.Ioc 0 x)
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le]
    exact hscore_interval

  have hAeq :
      powerWeightedShiftCumulativeShiftNumerator theta S a p x =
        (N' + G * N) / M := by
    rw [powerWeightedShiftCumulativeShiftNumerator,
      intervalIntegral.integral_of_le hx.le]
    calc
      (∫ t : ℝ in Set.Ioc 0 x,
          powerWeightedShiftDensity theta a p t *
            (powerWeightedShiftScoreMean theta S a p - S (a + t))) =
        ∫ t : ℝ in Set.Ioc 0 x,
          (M⁻¹ * (t ^ p * (-S (a + t) * theta (a + t))) +
            (G * M⁻¹) * (t ^ p * theta (a + t))) := by
          refine setIntegral_congr_fun measurableSet_Ioc ?_
          intro t ht
          dsimp [powerWeightedShiftDensity, M, G]
          rw [div_eq_mul_inv]
          ring
      _ = M⁻¹ * N' + (G * M⁻¹) * N := by
          have hs1 := hscore.const_mul M⁻¹
          have hs2 := hbase.const_mul (G * M⁻¹)
          rw [integral_add hs1 hs2, integral_const_mul, integral_const_mul]
      _ = (N' + G * N) / M := by
          rw [div_eq_mul_inv]
          ring

  have hquot := hNderiv.fun_div hMderiv hMne
  have hcoef :
      ((N' * M - N * D) / M ^ 2) =
        powerWeightedShiftCumulativeShiftNumerator theta S a p x := by
    rw [hD, hAeq]
    field_simp [hMne]
    ring

  change HasDerivAt
    (fun b : ℝ =>
      (∫ t : ℝ in Set.Ioc 0 x, t ^ p * theta (b + t)) /
        powerWeightedShiftMoment theta b p)
    (powerWeightedShiftCumulativeShiftNumerator theta S a p x) a
  rw [← hcoef]
  simpa [N, M, D] using hquot

end ScoreCurvatureStarOrder
