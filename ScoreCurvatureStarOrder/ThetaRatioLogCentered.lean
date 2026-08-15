import Mathlib
import ScoreCurvatureStarOrder.KernelRatioMonotonicity
import ScoreCurvatureStarOrder.LogDensityIntegrability

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter

/-- Strict centered covariance step in manuscript Theorem 5.4.

Let

`r(x) = theta(a₂+x) / theta(a₁+x)`

and let `rho` be the normalized power-weighted density at the earlier shift
`a₁`.  If `m = E_rho[log X]` and `c = exp m`, then

`E_rho[(r(X)-r(c)) (log X-m)] < 0`.

The sign is pointwise: `r` is strictly decreasing, `log` is strictly
increasing, and `rho` is strictly positive on `(0,∞)`.  Strictness of the
integral is obtained on the positive-measure interval `(0,c/2)`. -/
theorem powerWeightedShift_thetaRatio_log_centered_integral_neg_within
    {theta S Sprime : ℝ → ℝ} {a₁ a₂ p : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₁₂ : a₁ < a₂) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    let r : ℝ → ℝ := fun x => theta (a₂ + x) / theta (a₁ + x)
    let rho : ℝ → ℝ := powerWeightedShiftDensity theta a₁ p
    let m : ℝ := ∫ x : ℝ in Set.Ioi 0, Real.log x * rho x
    let c : ℝ := Real.exp m
    (∫ x : ℝ in Set.Ioi 0,
      (r x - r c) * (Real.log x - m) * rho x) < 0 := by
  let r : ℝ → ℝ := fun x => theta (a₂ + x) / theta (a₁ + x)
  let rho : ℝ → ℝ := powerWeightedShiftDensity theta a₁ p
  let m : ℝ := ∫ x : ℝ in Set.Ioi 0, Real.log x * rho x
  let c : ℝ := Real.exp m

  have ha₂ : 0 ≤ a₂ := ha₁.trans ha₁₂.le
  have hM₁pos : 0 < powerWeightedShiftMoment theta a₁ p :=
    powerWeightedShiftMoment_pos_within
      ha₁ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hM₁ne : powerWeightedShiftMoment theta a₁ p ≠ 0 := hM₁pos.ne'

  have hrho : IntegrableOn rho (Set.Ioi (0 : ℝ)) := by
    simpa [rho] using
      (powerWeightedShiftDensity_integrableOn_Ioi_within
        (theta := theta) (S := S) (Sprime := Sprime) (a := a₁) (p := p)
        ha₁ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)

  have hlogrho :
      IntegrableOn (fun x : ℝ => Real.log x * rho x) (Set.Ioi (0 : ℝ)) := by
    simpa [rho] using
      (powerWeightedShift_log_density_integrableOn_Ioi_within
        (theta := theta) (S := S) (Sprime := Sprime) (a := a₁) (p := p)
        ha₁ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)

  have hraw₂ :
      IntegrableOn (fun x : ℝ => x ^ p * theta (a₂ + x)) (Set.Ioi (0 : ℝ)) :=
    powerWeightedShift_integrableOn_Ioi_within
      ha₂ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos

  have hrrho :
      IntegrableOn (fun x : ℝ => r x * rho x) (Set.Ioi (0 : ℝ)) := by
    have hscaled := hraw₂.const_mul (powerWeightedShiftMoment theta a₁ p)⁻¹
    refine IntegrableOn.congr_fun hscaled ?_ measurableSet_Ioi
    intro x hx
    change 0 < x at hx
    have hax₁ : 0 ≤ a₁ + x := add_nonneg ha₁ hx.le
    have ht₁ : theta (a₁ + x) ≠ 0 :=
      (htheta_pos (a₁ + x) hax₁).ne'
    dsimp [r, rho, powerWeightedShiftDensity]
    field_simp [ht₁, hM₁ne]
    <;> ring

  have hrawlog₂ :
      IntegrableOn
        (fun x : ℝ => x ^ p * Real.log x * theta (a₂ + x))
        (Set.Ioi (0 : ℝ)) :=
    powerWeightedShift_log_integrableOn_Ioi_within
      ha₂ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos

  have hrlogrho :
      IntegrableOn
        (fun x : ℝ => r x * Real.log x * rho x)
        (Set.Ioi (0 : ℝ)) := by
    have hscaled := hrawlog₂.const_mul (powerWeightedShiftMoment theta a₁ p)⁻¹
    refine IntegrableOn.congr_fun hscaled ?_ measurableSet_Ioi
    intro x hx
    change 0 < x at hx
    have hax₁ : 0 ≤ a₁ + x := add_nonneg ha₁ hx.le
    have ht₁ : theta (a₁ + x) ≠ 0 :=
      (htheta_pos (a₁ + x) hax₁).ne'
    dsimp [r, rho, powerWeightedShiftDensity]
    field_simp [ht₁, hM₁ne]
    <;> ring

  have hranti : StrictAntiOn r (Set.Ioi (0 : ℝ)) := by
    simpa [r] using
      (powerWeightedShift_thetaRatio_strictAntiOn_Ioi_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a₁ := a₁) (a₂ := a₂)
        ha₁ ha₁₂ htheta_pos htheta_deriv hS hSprime_pos)

  have hcpos : 0 < c := by
    dsimp [c]
    exact Real.exp_pos m

  have hlogc : Real.log c = m := by
    simp [c]

  have hrhopos (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) : 0 < rho x := by
    change 0 < x at hx
    have hax₁ : 0 ≤ a₁ + x := add_nonneg ha₁ hx.le
    have hxpow : 0 < x ^ p := Real.rpow_pos_of_pos hx p
    have ht₁ : 0 < theta (a₁ + x) := htheta_pos (a₁ + x) hax₁
    dsimp [rho, powerWeightedShiftDensity]
    exact div_pos (mul_pos hxpow ht₁) hM₁pos

  have hcenter_neg (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) (hxc : x ≠ c) :
      (r x - r c) * (Real.log x - m) * rho x < 0 := by
    have hcmem : c ∈ Set.Ioi (0 : ℝ) := hcpos
    have hrhop := hrhopos x hx
    rcases lt_trichotomy x c with hlt | heq | hgt
    · have hrgt : r c < r x := hranti hx hcmem hlt
      have hloglt : Real.log x < m := by
        have h := Real.strictMonoOn_log hx hcmem hlt
        simpa [hlogc] using h
      exact mul_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (sub_pos.mpr hrgt) (sub_neg.mpr hloglt)) hrhop
    · exact (hxc heq).elim
    · have hrlt : r x < r c := hranti hcmem hx hgt
      have hloggt : m < Real.log x := by
        have h := Real.strictMonoOn_log hcmem hx hgt
        simpa [hlogc] using h
      exact mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (sub_neg.mpr hrlt) (sub_pos.mpr hloggt)) hrhop

  have hcenter_nonpos (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
      (r x - r c) * (Real.log x - m) * rho x ≤ 0 := by
    by_cases hxc : x = c
    · subst x
      simp
    · exact (hcenter_neg x hx hxc).le

  have hcenter_int :
      IntegrableOn
        (fun x : ℝ => (r x - r c) * (Real.log x - m) * rho x)
        (Set.Ioi (0 : ℝ)) := by
    have hmrrho :
        IntegrableOn (fun x : ℝ => m * (r x * rho x)) (Set.Ioi (0 : ℝ)) :=
      hrrho.const_mul m
    have hrc_logrho :
        IntegrableOn
          (fun x : ℝ => r c * (Real.log x * rho x))
          (Set.Ioi (0 : ℝ)) :=
      hlogrho.const_mul (r c)
    have hrcm_rho :
        IntegrableOn (fun x : ℝ => (r c * m) * rho x) (Set.Ioi (0 : ℝ)) :=
      hrho.const_mul (r c * m)
    have hcomb := ((hrlogrho.sub hmrrho).sub hrc_logrho).add hrcm_rho
    refine IntegrableOn.congr_fun hcomb ?_ measurableSet_Ioi
    intro x hx
    change
      (r x * Real.log x * rho x - m * (r x * rho x) -
          r c * (Real.log x * rho x) + (r c * m) * rho x) =
        (r x - r c) * (Real.log x - m) * rho x
    ring

  let F : ℝ → ℝ := fun x =>
    -((r x - r c) * (Real.log x - m) * rho x)

  have hFint : IntegrableOn F (Set.Ioi (0 : ℝ)) := by
    simpa [F] using hcenter_int.neg

  have hFnonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] F := by
    refine eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) ?_
    intro x hx
    dsimp [F]
    exact neg_nonneg.mpr (hcenter_nonpos x hx)

  have hhalfpos : 0 < c / 2 := half_pos hcpos
  have hhalf_lt : c / 2 < c := by linarith

  have hsupport :
      Set.Ioo (0 : ℝ) (c / 2) ⊆ Function.support F ∩ Set.Ioi (0 : ℝ) := by
    intro x hx
    constructor
    · rw [Function.mem_support]
      have hxIoi : x ∈ Set.Ioi (0 : ℝ) := hx.1
      have hxc_lt : x < c := hx.2.trans hhalf_lt
      have hneg := hcenter_neg x hxIoi (ne_of_lt hxc_lt)
      dsimp [F]
      exact (neg_pos.mpr hneg).ne'
    · exact hx.1

  have hinterval_ne : volume (Set.Ioo (0 : ℝ) (c / 2)) ≠ 0 := by
    have hpos : 0 < volume (Set.Ioo (0 : ℝ) (c / 2)) := by
      rw [Real.volume_Ioo]
      simpa using (ENNReal.ofReal_pos.mpr hhalfpos)
    exact hpos.ne'

  have hsupport_ne : volume (Function.support F ∩ Set.Ioi (0 : ℝ)) ≠ 0 := by
    intro hzero
    have hz : volume (Set.Ioo (0 : ℝ) (c / 2)) = 0 :=
      measure_mono_null hsupport hzero
    exact hinterval_ne hz

  have hFpos : 0 < ∫ x : ℝ in Set.Ioi 0, F x := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · exact hsupport_ne
    · exact hFnonneg
    · exact hFint

  have hnegint :
      (∫ x : ℝ in Set.Ioi 0, F x) =
        -(∫ x : ℝ in Set.Ioi 0,
          (r x - r c) * (Real.log x - m) * rho x) := by
    simp [F]
  rw [hnegint] at hFpos
  linarith

end ScoreCurvatureStarOrder
