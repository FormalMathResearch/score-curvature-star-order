import Mathlib
import ScoreCurvatureStarOrder.PowerLogMoments

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Topology Interval

/-- For every nonnegative shift and every `p > -1`, the first logarithmic
power-weighted moment may be differentiated with respect to the power parameter:

`∂ₚ ∫ x^p log(x) theta(a+x) dx = ∫ x^p (log x)^2 theta(a+x) dx`.

The proof uses the same symmetric parameter neighborhood as the verified
moment derivative.  On `0 < x ≤ 1` the derivative is dominated by the lower
endpoint power and on `x > 1` by the upper endpoint power; the required
square-log majorants are integrable by
`powerWeightedShift_log_sq_integrableOn_Ioi_within`. -/
theorem powerWeightedShift_logMoment_hasDerivAt_power_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    HasDerivAt
      (fun q : ℝ =>
        ∫ x : ℝ in Set.Ioi 0,
          x ^ q * Real.log x * theta (a + x))
      (∫ x : ℝ in Set.Ioi 0,
        x ^ p * (Real.log x) ^ 2 * theta (a + x)) p := by
  let δ : ℝ := (p + 1) / 2
  let plo : ℝ := p - δ
  let phi : ℝ := p + δ
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hplo : -1 < plo := by
    dsimp [plo, δ]
    linarith
  have hphi : -1 < phi := hplo.trans (by
    dsimp [plo, phi]
    linarith)

  let s : Set ℝ := Set.Ioo plo phi
  have hs : s ∈ 𝓝 p := by
    dsimp [s, plo, phi]
    exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩

  let F : ℝ → ℝ → ℝ := fun q x =>
    x ^ q * Real.log x * theta (a + x)
  let F' : ℝ → ℝ → ℝ := fun q x =>
    x ^ q * (Real.log x) ^ 2 * theta (a + x)
  let bound : ℝ → ℝ := fun x =>
    if x ≤ 1 then
      ‖x ^ plo * (Real.log x) ^ 2 * theta (a + x)‖
    else
      ‖x ^ phi * (Real.log x) ^ 2 * theta (a + x)‖

  have hF_meas :
      ∀ᶠ q in 𝓝 p,
        AEStronglyMeasurable (F q) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    filter_upwards [hs] with q hq
    have hqgood : -1 < q := hplo.trans hq.1
    have hint := powerWeightedShift_log_integrableOn_Ioi_within
      (theta := theta) (S := S) (Sprime := Sprime) (a := a) (p := q)
      ha hqgood htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [F] using hint.aestronglyMeasurable

  have hF_int : Integrable (F p) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hint := powerWeightedShift_log_integrableOn_Ioi_within
      (theta := theta) (S := S) (Sprime := Sprime) (a := a) (p := p)
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
    change IntegrableOn
      (fun x : ℝ => x ^ p * Real.log x * theta (a + x))
      (Set.Ioi (0 : ℝ))
    exact hint

  have hF'_meas :
      AEStronglyMeasurable (F' p) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hint := powerWeightedShift_log_sq_integrableOn_Ioi_within
      (theta := theta) (S := S) (Sprime := Sprime) (a := a) (p := p)
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [F'] using hint.aestronglyMeasurable

  have hlo := powerWeightedShift_log_sq_integrableOn_Ioi_within
    (theta := theta) (S := S) (Sprime := Sprime) (a := a) (p := plo)
    ha hplo htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hhi := powerWeightedShift_log_sq_integrableOn_Ioi_within
    (theta := theta) (S := S) (Sprime := Sprime) (a := a) (p := phi)
    ha hphi htheta_pos htheta_deriv htheta_int hS hSprime_pos

  have hbound_set : IntegrableOn bound (Set.Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
    constructor
    · have hlo_local :
          IntegrableOn
            (fun x : ℝ => x ^ plo * (Real.log x) ^ 2 * theta (a + x))
            (Set.Ioc (0 : ℝ) 1) :=
        hlo.mono_set (by
          intro x hx
          exact hx.1)
      have hlo_norm :
          IntegrableOn
            (fun x : ℝ => ‖x ^ plo * (Real.log x) ^ 2 * theta (a + x)‖)
            (Set.Ioc (0 : ℝ) 1) := by
        change Integrable
          (fun x : ℝ => ‖x ^ plo * (Real.log x) ^ 2 * theta (a + x)‖)
          (volume.restrict (Set.Ioc (0 : ℝ) 1))
        exact hlo_local.norm
      refine IntegrableOn.congr_fun hlo_norm ?_ measurableSet_Ioc
      intro x hx
      simp [bound, hx.2]
    · have hhi_local :
          IntegrableOn
            (fun x : ℝ => x ^ phi * (Real.log x) ^ 2 * theta (a + x))
            (Set.Ioi (1 : ℝ)) :=
        hhi.mono_set (by
          intro x hx
          change 1 < x at hx
          exact zero_lt_one.trans hx)
      have hhi_norm :
          IntegrableOn
            (fun x : ℝ => ‖x ^ phi * (Real.log x) ^ 2 * theta (a + x)‖)
            (Set.Ioi (1 : ℝ)) := by
        change Integrable
          (fun x : ℝ => ‖x ^ phi * (Real.log x) ^ 2 * theta (a + x)‖)
          (volume.restrict (Set.Ioi (1 : ℝ)))
        exact hhi_local.norm
      refine IntegrableOn.congr_fun hhi_norm ?_ measurableSet_Ioi
      intro x hx
      have hxnot : ¬ x ≤ 1 := not_le.mpr hx
      simp [bound, hxnot]

  have h_bound :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ∀ q ∈ s, ‖F' q x‖ ≤ bound x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro q hq
    have hxpos : 0 < x := hx
    have hxnonneg : 0 ≤ x := hxpos.le
    have hA_nonneg : 0 ≤ |Real.log x| ^ 2 * |theta (a + x)| :=
      mul_nonneg (sq_nonneg _) (abs_nonneg _)
    by_cases hx1 : x ≤ 1
    · have hrpow : x ^ q ≤ x ^ plo :=
        Real.rpow_le_rpow_of_exponent_ge hxpos hx1 hq.1.le
      have hnorm_q :
          ‖F' q x‖ = x ^ q * (|Real.log x| ^ 2 * |theta (a + x)|) := by
        dsimp [F']
        change |x ^ q * (Real.log x) ^ 2 * theta (a + x)| = _
        rw [abs_mul, abs_mul, abs_pow,
          abs_of_nonneg (Real.rpow_nonneg hxnonneg q)]
        ring
      have hnorm_plo :
          ‖x ^ plo * (Real.log x) ^ 2 * theta (a + x)‖ =
            x ^ plo * (|Real.log x| ^ 2 * |theta (a + x)|) := by
        change |x ^ plo * (Real.log x) ^ 2 * theta (a + x)| = _
        rw [abs_mul, abs_mul, abs_pow,
          abs_of_nonneg (Real.rpow_nonneg hxnonneg plo)]
        ring
      calc
        ‖F' q x‖ = x ^ q * (|Real.log x| ^ 2 * |theta (a + x)|) := hnorm_q
        _ ≤ x ^ plo * (|Real.log x| ^ 2 * |theta (a + x)|) :=
          mul_le_mul_of_nonneg_right hrpow hA_nonneg
        _ = ‖x ^ plo * (Real.log x) ^ 2 * theta (a + x)‖ := hnorm_plo.symm
        _ = bound x := by simp [bound, hx1]
    · have hx1lt : 1 < x := lt_of_not_ge hx1
      have hrpow : x ^ q ≤ x ^ phi :=
        Real.rpow_le_rpow_of_exponent_le hx1lt.le hq.2.le
      have hnorm_q :
          ‖F' q x‖ = x ^ q * (|Real.log x| ^ 2 * |theta (a + x)|) := by
        dsimp [F']
        change |x ^ q * (Real.log x) ^ 2 * theta (a + x)| = _
        rw [abs_mul, abs_mul, abs_pow,
          abs_of_nonneg (Real.rpow_nonneg hxnonneg q)]
        ring
      have hnorm_phi :
          ‖x ^ phi * (Real.log x) ^ 2 * theta (a + x)‖ =
            x ^ phi * (|Real.log x| ^ 2 * |theta (a + x)|) := by
        change |x ^ phi * (Real.log x) ^ 2 * theta (a + x)| = _
        rw [abs_mul, abs_mul, abs_pow,
          abs_of_nonneg (Real.rpow_nonneg hxnonneg phi)]
        ring
      calc
        ‖F' q x‖ = x ^ q * (|Real.log x| ^ 2 * |theta (a + x)|) := hnorm_q
        _ ≤ x ^ phi * (|Real.log x| ^ 2 * |theta (a + x)|) :=
          mul_le_mul_of_nonneg_right hrpow hA_nonneg
        _ = ‖x ^ phi * (Real.log x) ^ 2 * theta (a + x)‖ := hnorm_phi.symm
        _ = bound x := by simp [bound, hx1]

  have h_diff :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ∀ q ∈ s, HasDerivAt (F · x) (F' q x) q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro q _hq
    have hpow :
        HasDerivAt (fun r : ℝ => x ^ r) (x ^ q * Real.log x) q :=
      (Real.hasStrictDerivAt_const_rpow hx q).hasDerivAt
    have hmul := hpow.mul_const (Real.log x * theta (a + x))
    simpa [F, F', pow_two, mul_assoc] using hmul

  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (x₀ := p) (s := s) (bound := bound)
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    hs hF_meas hF_int hF'_meas h_bound hbound_set h_diff

  simpa [F, F'] using hparam.2

end ScoreCurvatureStarOrder
