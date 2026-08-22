import Mathlib
import ScoreCurvatureStarOrder.DistributionShiftDerivativeWithin
import ScoreCurvatureStarOrder.ShiftBoundaryContinuity

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- The shift-derivative integral is right-continuous at the boundary `a = 0`.

This is the analytic input needed to extend the already verified ordinary
shift derivative from `a > 0` to the natural one-sided derivative at `a = 0`.
The proof uses the same compact/tail majorants as Proposition 2.4. -/
theorem powerWeightedShiftMoment_shiftDerivative_continuousWithinAt_zero_within
    {theta S Sprime Ssecond : ℝ → ℝ} {p : ℝ}
    (hp : -1 < p)
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
    ContinuousWithinAt
      (fun a : ℝ =>
        ∫ x : ℝ in Set.Ioi 0,
          x ^ p * (-S (a + x) * theta (a + x)))
      (Set.Ici (0 : ℝ)) 0 := by
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
  rcases exists_shifted_thetaDeriv_local_majorant_within
      (A := (1 : ℝ)) (T := B) (by norm_num) hB0 htheta_deriv hS with
    ⟨C, hC, hlocal⟩

  let F : ℝ → ℝ → ℝ := fun a x =>
    x ^ p * (-S (a + x) * theta (a + x))
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

  have hparam :
      ∀ᶠ a : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0, a ∈ Set.Icc (0 : ℝ) 1 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with a ha1 ha0
    exact ⟨ha0, ha1.le⟩

  have hF_meas :
      ∀ᶠ a : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0,
        AEStronglyMeasurable (F a) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    filter_upwards [hparam] with a ha
    have hSshift : ContinuousOn (fun x : ℝ => S (a + x)) (Set.Ici (0 : ℝ)) :=
      continuousOn_shift_Ici_of_hasDerivWithinAt ha.1 hS
    have hthetashift :
        ContinuousOn (fun x : ℝ => theta (a + x)) (Set.Ici (0 : ℝ)) :=
      continuousOn_shift_Ici_of_hasDerivWithinAt ha.1 htheta_deriv
    have hrpow_cont : ContinuousOn (fun x : ℝ => x ^ p) (Set.Ioi (0 : ℝ)) :=
      continuousOn_id.rpow_const (by
        intro x hx
        left
        exact hx.ne')
    have hsub : Set.Ioi (0 : ℝ) ⊆ Set.Ici (0 : ℝ) := by
      intro x hx
      exact (show 0 < x from hx).le
    have hcont : ContinuousOn (F a) (Set.Ioi (0 : ℝ)) := by
      change ContinuousOn
        (fun x : ℝ => x ^ p * (-S (a + x) * theta (a + x))) (Set.Ioi (0 : ℝ))
      exact hrpow_cont.mul (((hSshift.mono hsub).neg).mul (hthetashift.mono hsub))
    exact hcont.aestronglyMeasurable measurableSet_Ioi

  have h_bound :
      ∀ᶠ a : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0,
        ∀ᵐ x ∂volume.restrict (Set.Ioi (0 : ℝ)), ‖F a x‖ ≤ bound x := by
    filter_upwards [hparam] with a ha
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have hpow0 : 0 ≤ x ^ p := Real.rpow_nonneg hx0 p
    by_cases hxB : x ≤ B
    · have hxI : x ∈ Set.Icc (0 : ℝ) B := ⟨hx0, hxB⟩
      have hloc := hlocal a x ha hxI
      have hinner : ‖-S (a + x) * theta (a + x)‖ ≤ C := by
        simpa only [Real.norm_eq_abs] using hloc
      have hboundx : bound x = C * x ^ p := by
        simp only [bound, if_pos hxB]
      calc
        ‖F a x‖ = ‖x ^ p‖ * ‖-S (a + x) * theta (a + x)‖ := by
          change ‖x ^ p * (-S (a + x) * theta (a + x))‖ = _
          exact norm_mul _ _
        _ = x ^ p * ‖-S (a + x) * theta (a + x)‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hpow0]
        _ ≤ x ^ p * C := mul_le_mul_of_nonneg_left hinner hpow0
        _ = bound x := by
          rw [hboundx]
          ring
    · have hBx : B < x := lt_of_not_ge hxB
      have hT₀x : T₀ ≤ x := hT₀B.trans hBx.le
      have htail' := htail a x ha.1 hT₀x
      have hinner : ‖-S (a + x) * theta (a + x)‖ ≤ S x * theta x := by
        simpa only [Real.norm_eq_abs] using htail'
      have hboundx : bound x = x ^ p * S x * theta x := by
        simp only [bound, if_neg hxB]
      calc
        ‖F a x‖ = ‖x ^ p‖ * ‖-S (a + x) * theta (a + x)‖ := by
          change ‖x ^ p * (-S (a + x) * theta (a + x))‖ = _
          exact norm_mul _ _
        _ = x ^ p * ‖-S (a + x) * theta (a + x)‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hpow0]
        _ ≤ x ^ p * (S x * theta x) := mul_le_mul_of_nonneg_left hinner hpow0
        _ = bound x := by
          rw [hboundx]
          ring

  have h_cont :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ContinuousWithinAt (fun a : ℝ => F a x) (Set.Ici (0 : ℝ)) 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hSshift : ContinuousOn (fun a : ℝ => S (x + a)) (Set.Ici (0 : ℝ)) :=
      continuousOn_shift_Ici_of_hasDerivWithinAt hx.le hS
    have hthetashift :
        ContinuousOn (fun a : ℝ => theta (x + a)) (Set.Ici (0 : ℝ)) :=
      continuousOn_shift_Ici_of_hasDerivWithinAt hx.le htheta_deriv
    have hS0 :
        ContinuousWithinAt (fun a : ℝ => S (a + x)) (Set.Ici (0 : ℝ)) 0 := by
      simpa [add_comm] using hSshift 0 (by simp)
    have htheta0 :
        ContinuousWithinAt (fun a : ℝ => theta (a + x)) (Set.Ici (0 : ℝ)) 0 := by
      simpa [add_comm] using hthetashift 0 (by simp)
    have hpow_const :
        ContinuousWithinAt
          (fun _ : ℝ => x ^ p)
          (Set.Ici (0 : ℝ)) 0 :=
      continuousWithinAt_const
    have hprod :
        ContinuousWithinAt
          (fun a : ℝ => x ^ p * (-S (a + x) * theta (a + x)))
          (Set.Ici (0 : ℝ)) 0 :=
      hpow_const.mul (hS0.neg.mul htheta0)
    simpa [F] using hprod

  have hdom :=
    MeasureTheory.continuousWithinAt_of_dominated
      (F := F) (x₀ := (0 : ℝ)) (s := Set.Ici (0 : ℝ))
      (μ := volume.restrict (Set.Ioi (0 : ℝ))) (bound := bound)
      hF_meas h_bound hbound_set h_cont
  simpa [F] using hdom

/-- **Proposition 2.4, boundary shift derivative.**

For every `p > -1`, the normalization moment has the natural right derivative
at `a = 0`, with the derivative obtained by differentiating under the integral:

`∂ₐ⁺ M_p(0) = ∫₀∞ x^p θ'(x) dx = ∫₀∞ x^p (-S(x) θ(x)) dx`.

Together with the already verified ordinary derivative for `a > 0`, this closes
the shift-differentiability coverage of Proposition 2.4 on `[0,∞)`. -/
theorem powerWeightedShiftMoment_hasDerivWithinAt_zero_within
    {theta S Sprime Ssecond : ℝ → ℝ} {p : ℝ}
    (hp : -1 < p)
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
    HasDerivWithinAt
      (fun a : ℝ => powerWeightedShiftMoment theta a p)
      (∫ x : ℝ in Set.Ioi 0, x ^ p * (-S x * theta x))
      (Set.Ici (0 : ℝ)) 0 := by
  let f : ℝ → ℝ := fun a => powerWeightedShiftMoment theta a p
  let g : ℝ → ℝ := fun a =>
    ∫ x : ℝ in Set.Ioi 0, x ^ p * (-S (a + x) * theta (a + x))

  have hfdiff : DifferentiableOn ℝ f (Set.Ioi (0 : ℝ)) := by
    intro a ha
    have hd :=
      powerWeightedShiftMoment_hasDerivAt_within
        (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime
        hSprime_pos hcurv
    exact hd.differentiableAt.differentiableWithinAt

  have hfcontIci :=
    powerWeightedShiftMoment_continuousWithinAt_zero_within
      (theta := theta) (S := S) (Sprime := Sprime) (p := p)
      hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hfcont : ContinuousWithinAt f (Set.Ioi (0 : ℝ)) 0 := by
    have hsub : Set.Ioi (0 : ℝ) ⊆ Set.Ici (0 : ℝ) := by
      intro a ha
      exact (show 0 < a from ha).le
    simpa [f] using hfcontIci.mono hsub

  have hgcontIci :=
    powerWeightedShiftMoment_shiftDerivative_continuousWithinAt_zero_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (p := p)
      hp htheta_pos htheta_deriv htheta_int hS hSprime hSprime_pos hcurv
  have hglim :
      Tendsto g (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (g 0)) := by
    have hsub : Set.Ioi (0 : ℝ) ⊆ Set.Ici (0 : ℝ) := by
      intro a ha
      exact (show 0 < a from ha).le
    simpa [g] using (hgcontIci.mono hsub).tendsto

  have hderiv_eq :
      (fun a : ℝ => deriv f a) =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0] g := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have hd :=
      powerWeightedShiftMoment_hasDerivAt_within
        (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime
        hSprime_pos hcurv
    simpa [f, g] using hd.deriv

  have hderivlim :
      Tendsto (fun a : ℝ => deriv f a)
        (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (g 0)) :=
    hglim.congr' hderiv_eq.symm

  have hs : Set.Ioi (0 : ℝ) ∈ 𝓝[Set.Ioi (0 : ℝ)] 0 :=
    self_mem_nhdsWithin
  have hboundary :=
    hasDerivWithinAt_Ici_of_tendsto_deriv
      (s := Set.Ioi (0 : ℝ)) (a := (0 : ℝ)) (f := f) (e := g 0)
      hfdiff hfcont hs hderivlim
  simpa [f, g] using hboundary

end ScoreCurvatureStarOrder