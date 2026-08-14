import Mathlib
import ScoreCurvatureStarOrder.CumulativeShiftNumerator
import ScoreCurvatureStarOrder.LocalShiftMajorant
import ScoreCurvatureStarOrder.MomentLogDerivative

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- The distribution function of the normalized power-weighted shifted family on the
positive half-line. For `x ≤ 0` the set `Ioc 0 x` is empty, so this definition is zero. -/
noncomputable def powerWeightedShiftCDF
    (theta : ℝ → ℝ) (a p x : ℝ) : ℝ :=
  (∫ t : ℝ in Set.Ioc 0 x, t ^ p * theta (a + t)) /
    powerWeightedShiftMoment theta a p

/-- For a positive upper endpoint, the unnormalized CDF numerator can be
differentiated with respect to an interior shift. -/
theorem powerWeightedShiftCDFNumerator_hasDerivAt
    {theta S Sprime : ℝ → ℝ} {a p x : ℝ}
    (ha : 0 < a) (hp : -1 < p) (hx : 0 < x)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z) :
    HasDerivAt
      (fun b : ℝ => ∫ t : ℝ in Set.Ioc 0 x, t ^ p * theta (b + t))
      (∫ t : ℝ in Set.Ioc 0 x,
        t ^ p * (-S (a + t) * theta (a + t))) a := by
  have hA0 : 0 ≤ a + 1 := by linarith
  rcases exists_shifted_thetaDeriv_local_majorant
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
    have htheta_cont :
        ContinuousOn (fun t : ℝ => theta (b + t)) [[0, x]] := by
      intro t ht
      rw [uIcc_of_le hx.le] at ht
      have hbt0 : 0 ≤ b + t := add_nonneg hb0 ht.1
      have hshift : ContinuousAt (fun y : ℝ => b + y) t := by fun_prop
      exact ((htheta_deriv (b + t) hbt0).continuousAt.comp hshift).continuousWithinAt
    have hint : IntervalIntegrable (F b) volume 0 x := by
      change IntervalIntegrable (fun t : ℝ => t ^ p * theta (b + t)) volume 0 x
      exact hpow_interval.mul_continuousOn htheta_cont
    have hint_set : IntegrableOn (F b) (Set.Ioc 0 x) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le]
      exact hint
    exact hint_set.aestronglyMeasurable

  have hF_int : Integrable (F a) (volume.restrict (Set.Ioc 0 x)) := by
    have htheta_cont :
        ContinuousOn (fun t : ℝ => theta (a + t)) [[0, x]] := by
      intro t ht
      rw [uIcc_of_le hx.le] at ht
      have hat0 : 0 ≤ a + t := add_nonneg ha.le ht.1
      have hshift : ContinuousAt (fun y : ℝ => a + y) t := by fun_prop
      exact ((htheta_deriv (a + t) hat0).continuousAt.comp hshift).continuousWithinAt
    have hint : IntervalIntegrable (F a) volume 0 x := by
      change IntervalIntegrable (fun t : ℝ => t ^ p * theta (a + t)) volume 0 x
      exact hpow_interval.mul_continuousOn htheta_cont
    change IntegrableOn (F a) (Set.Ioc 0 x)
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le]
    exact hint

  have hF'_meas :
      AEStronglyMeasurable (F' a) (volume.restrict (Set.Ioc 0 x)) := by
    have hcoeff_cont :
        ContinuousOn
          (fun t : ℝ => -S (a + t) * theta (a + t)) [[0, x]] := by
      intro t ht
      rw [uIcc_of_le hx.le] at ht
      have hat0 : 0 ≤ a + t := add_nonneg ha.le ht.1
      have hshift : ContinuousAt (fun y : ℝ => a + y) t := by fun_prop
      have hSc : ContinuousAt (fun y : ℝ => S (a + y)) t :=
        (hS (a + t) hat0).continuousAt.comp hshift
      have htc : ContinuousAt (fun y : ℝ => theta (a + y)) t :=
        (htheta_deriv (a + t) hat0).continuousAt.comp hshift
      exact (hSc.neg.mul htc).continuousWithinAt
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
    have hb0 : 0 ≤ b := hs_nonneg b hb
    have hbt0 : 0 ≤ b + t := add_nonneg hb0 ht.1.le
    have htheta_shift :
        HasDerivAt (fun y : ℝ => theta (y + t))
          (-S (b + t) * theta (b + t)) b :=
      (htheta_deriv (b + t) hbt0).comp_add_const b t
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

/-- At every interior shift and positive observation, the shift derivative of the
CDF is the cumulative centered-score numerator `A`. -/
theorem powerWeightedShiftCDF_hasDerivAt
    {theta S Sprime Ssecond : ℝ → ℝ} {a p x : ℝ}
    (ha : 0 < a) (hp : -1 < p) (hx : 0 < x)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt Sprime (Ssecond z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ), Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
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
    simpa [N'] using powerWeightedShiftCDFNumerator_hasDerivAt
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (x := x) ha hp hx htheta_deriv hS
  have hMderiv :
      HasDerivAt (fun b : ℝ => powerWeightedShiftMoment theta b p) D a := by
    simpa [D] using powerWeightedShiftMoment_hasDerivAt
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (a := a) (p := p) ha hp htheta_pos htheta_deriv htheta_int hS hSprime
      hSprime_pos hcurv
  have hMpos : 0 < M := by
    dsimp [M]
    exact powerWeightedShiftMoment_pos
      ha.le hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hMne : M ≠ 0 := hMpos.ne'

  have hrawlog := hMderiv.log hMne
  have hmeanlog := powerWeightedShiftMoment_log_hasDerivAt
    (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
    (a := a) (p := p) ha hp htheta_pos htheta_deriv htheta_int hS hSprime
    hSprime_pos hcurv
  have hDdiv : D / M = -G := by
    calc
      D / M = deriv (fun b : ℝ => Real.log (powerWeightedShiftMoment theta b p)) a := by
        simpa [M] using hrawlog.deriv.symm
      _ = -G := by
        simpa [G] using hmeanlog.deriv
  have hD : D = (-G) * M := (div_eq_iff hMne).mp hDdiv

  have hbaseIoi :
      IntegrableOn (fun t : ℝ => t ^ p * theta (a + t)) (Set.Ioi (0 : ℝ)) :=
    powerWeightedShift_integrableOn_Ioi
      ha.le hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hbase :
      Integrable (fun t : ℝ => t ^ p * theta (a + t))
        (volume.restrict (Set.Ioc 0 x)) :=
    (hbaseIoi.mono_set (fun t ht => ht.1)).integrable

  have hpow_interval :
      IntervalIntegrable (fun t : ℝ => t ^ p) volume 0 x :=
    intervalIntegral.intervalIntegrable_rpow' hp
  have hscore_coeff_cont :
      ContinuousOn
        (fun t : ℝ => -S (a + t) * theta (a + t)) [[0, x]] := by
    intro t ht
    rw [uIcc_of_le hx.le] at ht
    have hat0 : 0 ≤ a + t := add_nonneg ha.le ht.1
    have hshift : ContinuousAt (fun y : ℝ => a + y) t := by fun_prop
    have hSc : ContinuousAt (fun y : ℝ => S (a + y)) t :=
      (hS (a + t) hat0).continuousAt.comp hshift
    have htc : ContinuousAt (fun y : ℝ => theta (a + y)) t :=
      (htheta_deriv (a + t) hat0).continuousAt.comp hshift
    exact (hSc.neg.mul htc).continuousWithinAt
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
          rfl
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
