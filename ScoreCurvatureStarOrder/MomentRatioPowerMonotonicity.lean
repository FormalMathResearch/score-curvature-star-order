import Mathlib
import ScoreCurvatureStarOrder.PowerMomentDerivative
import ScoreCurvatureStarOrder.MomentRatioExpectation
import ScoreCurvatureStarOrder.ThetaRatioLogCentered

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- The logarithmic mean under the normalized shifted density is the normalized
first logarithmic power moment.  This is a purely algebraic normalization
identity and uses no new differentiation under the integral sign. -/
theorem powerWeightedShift_log_expectation_eq_logMomentRatio
    (theta : ℝ → ℝ) (a p : ℝ) :
    (∫ x : ℝ in Set.Ioi 0,
        Real.log x * powerWeightedShiftDensity theta a p x) =
      (∫ x : ℝ in Set.Ioi 0,
          x ^ p * Real.log x * theta (a + x)) /
        powerWeightedShiftMoment theta a p := by
  calc
    (∫ x : ℝ in Set.Ioi 0,
        Real.log x * powerWeightedShiftDensity theta a p x) =
        ∫ x : ℝ in Set.Ioi 0,
          (powerWeightedShiftMoment theta a p)⁻¹ *
            (x ^ p * Real.log x * theta (a + x)) := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro x hx
      dsimp [powerWeightedShiftDensity]
      rw [div_eq_mul_inv]
      ring
    _ = (powerWeightedShiftMoment theta a p)⁻¹ *
        ∫ x : ℝ in Set.Ioi 0,
          x ^ p * Real.log x * theta (a + x) := by
      rw [integral_const_mul]
    _ = (∫ x : ℝ in Set.Ioi 0,
          x ^ p * Real.log x * theta (a + x)) /
        powerWeightedShiftMoment theta a p := by
      rw [div_eq_mul_inv]
      ring

/-- The logarithmically weighted expectation of the spatial kernel ratio is
the later-shift logarithmic raw moment divided by the earlier normalization
moment.  On `(0,∞)` this is just cancellation of the positive factor
`theta (a₁+x)`. -/
theorem powerWeightedShift_thetaRatio_log_expectation_eq_logMomentRatio
    {theta : ℝ → ℝ} {a₁ a₂ p : ℝ}
    (ha₁ : 0 ≤ a₁)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z) :
    (∫ x : ℝ in Set.Ioi 0,
        (theta (a₂ + x) / theta (a₁ + x)) * Real.log x *
          powerWeightedShiftDensity theta a₁ p x) =
      (∫ x : ℝ in Set.Ioi 0,
          x ^ p * Real.log x * theta (a₂ + x)) /
        powerWeightedShiftMoment theta a₁ p := by
  calc
    (∫ x : ℝ in Set.Ioi 0,
        (theta (a₂ + x) / theta (a₁ + x)) * Real.log x *
          powerWeightedShiftDensity theta a₁ p x) =
        ∫ x : ℝ in Set.Ioi 0,
          (powerWeightedShiftMoment theta a₁ p)⁻¹ *
            (x ^ p * Real.log x * theta (a₂ + x)) := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro x hx
      change 0 < x at hx
      have hax₁ : 0 ≤ a₁ + x := add_nonneg ha₁ hx.le
      have ht₁ : theta (a₁ + x) ≠ 0 :=
        (htheta_pos (a₁ + x) hax₁).ne'
      dsimp [powerWeightedShiftDensity]
      rw [div_eq_mul_inv]
      field_simp [ht₁]
      <;> ring
    _ = (powerWeightedShiftMoment theta a₁ p)⁻¹ *
        ∫ x : ℝ in Set.Ioi 0,
          x ^ p * Real.log x * theta (a₂ + x) := by
      rw [integral_const_mul]
    _ = (∫ x : ℝ in Set.Ioi 0,
          x ^ p * Real.log x * theta (a₂ + x)) /
        powerWeightedShiftMoment theta a₁ p := by
      rw [div_eq_mul_inv]
      ring

/-- Quotient-rule form of the `p`-derivative of the normalization-moment
ratio.  Both moment derivatives are the already verified Lemma 5.2 raw
logarithmic moments. -/
theorem powerWeightedShift_momentRatio_hasDerivAt_power_within
    {theta S Sprime : ℝ → ℝ} {a₁ a₂ p : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₁₂ : a₁ < a₂) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    HasDerivAt
      (fun q : ℝ =>
        powerWeightedShiftMoment theta a₂ q /
          powerWeightedShiftMoment theta a₁ q)
      (((∫ x : ℝ in Set.Ioi 0,
            x ^ p * Real.log x * theta (a₂ + x)) *
          powerWeightedShiftMoment theta a₁ p -
        powerWeightedShiftMoment theta a₂ p *
          (∫ x : ℝ in Set.Ioi 0,
            x ^ p * Real.log x * theta (a₁ + x))) /
        (powerWeightedShiftMoment theta a₁ p) ^ 2) p := by
  have ha₂ : 0 ≤ a₂ := ha₁.trans ha₁₂.le
  have hM₁ :=
    powerWeightedShiftMoment_hasDerivAt_power_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a₁) (p := p)
      ha₁ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hM₂ :=
    powerWeightedShiftMoment_hasDerivAt_power_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a₂) (p := p)
      ha₂ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hM₁pos : 0 < powerWeightedShiftMoment theta a₁ p :=
    powerWeightedShiftMoment_pos_within
      ha₁ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  exact hM₂.fun_div hM₁ hM₁pos.ne'

/-- The derivative from the preceding quotient rule is strictly negative.
This is the covariance step of manuscript Theorem 5.4: the derivative equals
the already verified strictly negative centered integral of the decreasing
kernel ratio against `log X`. -/
theorem powerWeightedShift_momentRatio_powerDerivative_neg_within
    {theta S Sprime : ℝ → ℝ} {a₁ a₂ p : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₁₂ : a₁ < a₂) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    (((∫ x : ℝ in Set.Ioi 0,
          x ^ p * Real.log x * theta (a₂ + x)) *
        powerWeightedShiftMoment theta a₁ p -
      powerWeightedShiftMoment theta a₂ p *
        (∫ x : ℝ in Set.Ioi 0,
          x ^ p * Real.log x * theta (a₁ + x))) /
      (powerWeightedShiftMoment theta a₁ p) ^ 2) < 0 := by
  let r : ℝ → ℝ := fun x => theta (a₂ + x) / theta (a₁ + x)
  let rho : ℝ → ℝ := powerWeightedShiftDensity theta a₁ p
  let m : ℝ := ∫ x : ℝ in Set.Ioi 0, Real.log x * rho x
  let c : ℝ := Real.exp m

  have ha₂ : 0 ≤ a₂ := ha₁.trans ha₁₂.le
  have hM₁pos : 0 < powerWeightedShiftMoment theta a₁ p :=
    powerWeightedShiftMoment_pos_within
      ha₁ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hM₁ne : powerWeightedShiftMoment theta a₁ p ≠ 0 := hM₁pos.ne'

  have hcenter :
      (∫ x : ℝ in Set.Ioi 0,
        (r x - r c) * (Real.log x - m) * rho x) < 0 := by
    simpa [r, rho, m, c] using
      (powerWeightedShift_thetaRatio_log_centered_integral_neg_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a₁ := a₁) (a₂ := a₂) (p := p)
        ha₁ ha₁₂ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)

  have hrho : IntegrableOn rho (Set.Ioi (0 : ℝ)) := by
    simpa [rho] using
      (powerWeightedShiftDensity_integrableOn_Ioi_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a₁) (p := p)
        ha₁ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)

  have hlogrho :
      IntegrableOn (fun x : ℝ => Real.log x * rho x) (Set.Ioi (0 : ℝ)) := by
    simpa [rho] using
      (powerWeightedShift_log_density_integrableOn_Ioi_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a₁) (p := p)
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

  have hrho_one : (∫ x : ℝ in Set.Ioi 0, rho x) = 1 := by
    simpa [rho] using
      (powerWeightedShiftDensity_integral_eq_one_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a₁) (p := p)
        ha₁ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)

  have hlogmean :
      (∫ x : ℝ in Set.Ioi 0, Real.log x * rho x) =
        (∫ x : ℝ in Set.Ioi 0,
            x ^ p * Real.log x * theta (a₁ + x)) /
          powerWeightedShiftMoment theta a₁ p := by
    simpa [rho] using
      (powerWeightedShift_log_expectation_eq_logMomentRatio theta a₁ p)

  have hrmean :
      (∫ x : ℝ in Set.Ioi 0, r x * rho x) =
        powerWeightedShiftMoment theta a₂ p /
          powerWeightedShiftMoment theta a₁ p := by
    simpa [r, rho] using
      (powerWeightedShift_momentRatio_eq_thetaRatio_expectation_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a₁ := a₁) (a₂ := a₂) (p := p)
        ha₁ ha₁₂ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos).symm

  have hrlogmean :
      (∫ x : ℝ in Set.Ioi 0, r x * Real.log x * rho x) =
        (∫ x : ℝ in Set.Ioi 0,
            x ^ p * Real.log x * theta (a₂ + x)) /
          powerWeightedShiftMoment theta a₁ p := by
    simpa [r, rho] using
      (powerWeightedShift_thetaRatio_log_expectation_eq_logMomentRatio
        (theta := theta) (a₁ := a₁) (a₂ := a₂) (p := p)
        ha₁ htheta_pos)

  have hmlog : (∫ x : ℝ in Set.Ioi 0, Real.log x * rho x) = m := by
    rfl
  have hm :
      m =
        (∫ x : ℝ in Set.Ioi 0,
            x ^ p * Real.log x * theta (a₁ + x)) /
          powerWeightedShiftMoment theta a₁ p := by
    calc
      m = ∫ x : ℝ in Set.Ioi 0, Real.log x * rho x := hmlog.symm
      _ = _ := hlogmean

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

  have hsub1 :
      (∫ x : ℝ in Set.Ioi 0,
          r x * Real.log x * rho x - m * (r x * rho x)) =
        (∫ x : ℝ in Set.Ioi 0, r x * Real.log x * rho x) -
          ∫ x : ℝ in Set.Ioi 0, m * (r x * rho x) := by
    exact integral_sub hrlogrho hmrrho

  have hsub2 :
      (∫ x : ℝ in Set.Ioi 0,
          (r x * Real.log x * rho x - m * (r x * rho x)) -
            r c * (Real.log x * rho x)) =
        (∫ x : ℝ in Set.Ioi 0,
            r x * Real.log x * rho x - m * (r x * rho x)) -
          ∫ x : ℝ in Set.Ioi 0, r c * (Real.log x * rho x) := by
    exact integral_sub (hrlogrho.sub hmrrho) hrc_logrho

  have hadd :
      (∫ x : ℝ in Set.Ioi 0,
          ((r x * Real.log x * rho x - m * (r x * rho x)) -
              r c * (Real.log x * rho x)) +
            (r c * m) * rho x) =
        (∫ x : ℝ in Set.Ioi 0,
            (r x * Real.log x * rho x - m * (r x * rho x)) -
              r c * (Real.log x * rho x)) +
          ∫ x : ℝ in Set.Ioi 0, (r c * m) * rho x := by
    exact integral_add ((hrlogrho.sub hmrrho).sub hrc_logrho) hrcm_rho

  have hcenter_expand :
      (∫ x : ℝ in Set.Ioi 0,
          (r x - r c) * (Real.log x - m) * rho x) =
        (∫ x : ℝ in Set.Ioi 0, r x * Real.log x * rho x) -
          m * (∫ x : ℝ in Set.Ioi 0, r x * rho x) -
          r c * (∫ x : ℝ in Set.Ioi 0, Real.log x * rho x) +
          (r c * m) * (∫ x : ℝ in Set.Ioi 0, rho x) := by
    calc
      (∫ x : ℝ in Set.Ioi 0,
          (r x - r c) * (Real.log x - m) * rho x) =
          ∫ x : ℝ in Set.Ioi 0,
            ((r x * Real.log x * rho x - m * (r x * rho x)) -
                r c * (Real.log x * rho x)) +
              (r c * m) * rho x := by
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro x hx
        ring
      _ = (∫ x : ℝ in Set.Ioi 0,
            (r x * Real.log x * rho x - m * (r x * rho x)) -
              r c * (Real.log x * rho x)) +
          ∫ x : ℝ in Set.Ioi 0, (r c * m) * rho x := hadd
      _ = ((∫ x : ℝ in Set.Ioi 0,
              r x * Real.log x * rho x - m * (r x * rho x)) -
            ∫ x : ℝ in Set.Ioi 0, r c * (Real.log x * rho x)) +
          ∫ x : ℝ in Set.Ioi 0, (r c * m) * rho x := by
        rw [hsub2]
      _ = (((∫ x : ℝ in Set.Ioi 0, r x * Real.log x * rho x) -
              ∫ x : ℝ in Set.Ioi 0, m * (r x * rho x)) -
            ∫ x : ℝ in Set.Ioi 0, r c * (Real.log x * rho x)) +
          ∫ x : ℝ in Set.Ioi 0, (r c * m) * rho x := by
        rw [hsub1]
      _ = (∫ x : ℝ in Set.Ioi 0, r x * Real.log x * rho x) -
          m * (∫ x : ℝ in Set.Ioi 0, r x * rho x) -
          r c * (∫ x : ℝ in Set.Ioi 0, Real.log x * rho x) +
          (r c * m) * (∫ x : ℝ in Set.Ioi 0, rho x) := by
        rw [integral_const_mul, integral_const_mul, integral_const_mul]

  have hcenter_cov :
      (∫ x : ℝ in Set.Ioi 0,
          (r x - r c) * (Real.log x - m) * rho x) =
        (∫ x : ℝ in Set.Ioi 0, r x * Real.log x * rho x) -
          m * (∫ x : ℝ in Set.Ioi 0, r x * rho x) := by
    calc
      (∫ x : ℝ in Set.Ioi 0,
          (r x - r c) * (Real.log x - m) * rho x) =
          (∫ x : ℝ in Set.Ioi 0, r x * Real.log x * rho x) -
            m * (∫ x : ℝ in Set.Ioi 0, r x * rho x) -
            r c * (∫ x : ℝ in Set.Ioi 0, Real.log x * rho x) +
            (r c * m) * (∫ x : ℝ in Set.Ioi 0, rho x) := hcenter_expand
      _ = (∫ x : ℝ in Set.Ioi 0, r x * Real.log x * rho x) -
          m * (∫ x : ℝ in Set.Ioi 0, r x * rho x) := by
        rw [hmlog, hrho_one]
        ring

  have hcenter_deriv :
      (∫ x : ℝ in Set.Ioi 0,
          (r x - r c) * (Real.log x - m) * rho x) =
        (((∫ x : ℝ in Set.Ioi 0,
              x ^ p * Real.log x * theta (a₂ + x)) *
            powerWeightedShiftMoment theta a₁ p -
          powerWeightedShiftMoment theta a₂ p *
            (∫ x : ℝ in Set.Ioi 0,
              x ^ p * Real.log x * theta (a₁ + x))) /
          (powerWeightedShiftMoment theta a₁ p) ^ 2) := by
    calc
      (∫ x : ℝ in Set.Ioi 0,
          (r x - r c) * (Real.log x - m) * rho x) =
          (∫ x : ℝ in Set.Ioi 0, r x * Real.log x * rho x) -
            m * (∫ x : ℝ in Set.Ioi 0, r x * rho x) := hcenter_cov
      _ = (∫ x : ℝ in Set.Ioi 0,
              x ^ p * Real.log x * theta (a₂ + x)) /
            powerWeightedShiftMoment theta a₁ p -
          ((∫ x : ℝ in Set.Ioi 0,
              x ^ p * Real.log x * theta (a₁ + x)) /
            powerWeightedShiftMoment theta a₁ p) *
            (powerWeightedShiftMoment theta a₂ p /
              powerWeightedShiftMoment theta a₁ p) := by
        rw [hrlogmean, hm, hrmean]
      _ = (((∫ x : ℝ in Set.Ioi 0,
              x ^ p * Real.log x * theta (a₂ + x)) *
            powerWeightedShiftMoment theta a₁ p -
          powerWeightedShiftMoment theta a₂ p *
            (∫ x : ℝ in Set.Ioi 0,
              x ^ p * Real.log x * theta (a₁ + x))) /
          (powerWeightedShiftMoment theta a₁ p) ^ 2) := by
        field_simp [hM₁ne]
        <;> ring

  rw [hcenter_deriv] at hcenter
  exact hcenter

/-- Manuscript Theorem 5.4: for ordered nonnegative shifts `a₁ < a₂`, the
normalization-moment ratio `M_p(a₂) / M_p(a₁)` is strictly decreasing in the
power parameter on `(-1,∞)`.

The proof composes the three verified manuscript steps: the spatial kernel
ratio is strictly decreasing, the moment ratio is its expectation under the
earlier shifted density, and the `p`-derivative is the resulting strictly
negative covariance with `log X`. -/
theorem powerWeightedShift_momentRatio_strictAntiOn_power_within
    {theta S Sprime : ℝ → ℝ} {a₁ a₂ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₁₂ : a₁ < a₂)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    StrictAntiOn
      (fun q : ℝ =>
        powerWeightedShiftMoment theta a₂ q /
          powerWeightedShiftMoment theta a₁ q)
      (Set.Ioi (-1 : ℝ)) := by
  let dR : ℝ → ℝ := fun q =>
    (((∫ x : ℝ in Set.Ioi 0,
          x ^ q * Real.log x * theta (a₂ + x)) *
        powerWeightedShiftMoment theta a₁ q -
      powerWeightedShiftMoment theta a₂ q *
        (∫ x : ℝ in Set.Ioi 0,
          x ^ q * Real.log x * theta (a₁ + x))) /
      (powerWeightedShiftMoment theta a₁ q) ^ 2)

  have hcont :
      ContinuousOn
        (fun q : ℝ =>
          powerWeightedShiftMoment theta a₂ q /
            powerWeightedShiftMoment theta a₁ q)
        (Set.Ioi (-1 : ℝ)) := by
    intro q hq
    have hq' : -1 < q := hq
    have hd :=
      powerWeightedShift_momentRatio_hasDerivAt_power_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a₁ := a₁) (a₂ := a₂) (p := q)
        ha₁ ha₁₂ hq' htheta_pos htheta_deriv htheta_int hS hSprime_pos
    exact hd.continuousAt.continuousWithinAt

  have hderiv :
      ∀ q ∈ interior (Set.Ioi (-1 : ℝ)),
        HasDerivWithinAt
          (fun t : ℝ =>
            powerWeightedShiftMoment theta a₂ t /
              powerWeightedShiftMoment theta a₁ t)
          (dR q) (interior (Set.Ioi (-1 : ℝ))) q := by
    intro q hq
    have hq' : -1 < q := by
      exact (interior_subset hq : q ∈ Set.Ioi (-1 : ℝ))
    have hd :=
      powerWeightedShift_momentRatio_hasDerivAt_power_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a₁ := a₁) (a₂ := a₂) (p := q)
        ha₁ ha₁₂ hq' htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [dR] using hd.hasDerivWithinAt

  have hneg :
      ∀ q ∈ interior (Set.Ioi (-1 : ℝ)), dR q < 0 := by
    intro q hq
    have hq' : -1 < q := by
      exact (interior_subset hq : q ∈ Set.Ioi (-1 : ℝ))
    have hdneg :=
      powerWeightedShift_momentRatio_powerDerivative_neg_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a₁ := a₁) (a₂ := a₂) (p := q)
        ha₁ ha₁₂ hq' htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [dR] using hdneg

  exact strictAntiOn_of_hasDerivWithinAt_neg
    (convex_Ioi (-1 : ℝ)) hcont hderiv hneg

end ScoreCurvatureStarOrder
