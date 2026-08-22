import Mathlib
import ScoreCurvatureStarOrder.ShiftDerivativeMajorant
import ScoreCurvatureStarOrder.LocalShiftMajorant

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- Joint compact-parameter domination for the shift derivative of the kernel.

For every compact rectangle `p ∈ [p₀,p₁]`, `a ∈ [0,A]` with `p₀ > -1`,
there is a single integrable function on `(0,∞)` dominating

`x^p * |theta'(a+x)| = x^p * |-S(a+x) * theta(a+x)|`

simultaneously for all parameters in the rectangle.  On a bounded spatial
interval, continuity gives a shift-uniform bound for the derivative factor.
Near zero the lower exponent `p₀` is the worst power, while for `x ≥ 1` the
upper exponent `p₁` is the worst.  On the tail, the verified curvature argument
bounds the shifted derivative factor by the unshifted score weight
`S(x) * theta(x)`, whose `p₁`-weighted version is integrable. -/
theorem exists_powerWeightedShift_thetaDeriv_compact_majorant_within
    {theta S Sprime Ssecond : ℝ → ℝ} {p₀ p₁ A : ℝ}
    (hp₀ : -1 < p₀) (hp₀₁ : p₀ ≤ p₁) (hA : 0 ≤ A)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt Sprime (Ssecond z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ), Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    ∃ bound : ℝ → ℝ,
      IntegrableOn bound (Set.Ioi (0 : ℝ)) ∧
      ∀ p ∈ Set.Icc p₀ p₁, ∀ a ∈ Set.Icc (0 : ℝ) A, ∀ x ∈ Set.Ioi (0 : ℝ),
        x ^ p * |(-S (a + x) * theta (a + x))| ≤ bound x := by
  have hp₁ : -1 < p₁ := hp₀.trans_le hp₀₁
  rcases exists_shifted_thetaDeriv_tail_majorant_within
      htheta_pos htheta_deriv htheta_int hS hSprime hSprime_pos hcurv with
    ⟨T, hT, htail⟩

  let B : ℝ := max T 1
  have hTB : T ≤ B := le_max_left T 1
  have h1B : 1 ≤ B := le_max_right T 1
  have hB0 : 0 ≤ B := zero_le_one.trans h1B

  rcases exists_shifted_thetaDeriv_local_majorant_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (A := A) (T := B) hA hB0 htheta_deriv hS with
    ⟨C, hC, hlocal⟩

  let bound : ℝ → ℝ := fun x =>
    if x ≤ 1 then C * x ^ p₀
    else if x ≤ B then C * x ^ p₁
    else x ^ p₁ * S x * theta x

  have hscore_int := powerWeightedUnshifted_score_integrableOn_Ioi_within
    (theta := theta) (S := S) (Sprime := Sprime) (p := p₁)
    hp₁ htheta_pos htheta_deriv htheta_int hS hSprime_pos

  have hbound_int : IntegrableOn bound (Set.Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
    constructor
    · have hpow : IntegrableOn (fun x : ℝ => x ^ p₀) (Set.Ioc (0 : ℝ) 1) := by
        rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
        exact intervalIntegral.intervalIntegrable_rpow' hp₀
      have hlocal_int : IntegrableOn (fun x : ℝ => C * x ^ p₀) (Set.Ioc (0 : ℝ) 1) :=
        hpow.const_mul C
      refine IntegrableOn.congr_fun hlocal_int ?_ measurableSet_Ioc
      intro x hx
      simp [bound, hx.2]
    · rw [← Ioc_union_Ioi_eq_Ioi h1B, integrableOn_union]
      constructor
      · have hpow0 : IntegrableOn (fun x : ℝ => x ^ p₁) (Set.Ioc (0 : ℝ) B) := by
          rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hB0]
          exact intervalIntegral.intervalIntegrable_rpow' hp₁
        have hpow : IntegrableOn (fun x : ℝ => x ^ p₁) (Set.Ioc (1 : ℝ) B) :=
          hpow0.mono_set (by
            intro x hx
            exact ⟨zero_lt_one.trans hx.1, hx.2⟩)
        have hmid_int : IntegrableOn (fun x : ℝ => C * x ^ p₁) (Set.Ioc (1 : ℝ) B) :=
          hpow.const_mul C
        refine IntegrableOn.congr_fun hmid_int ?_ measurableSet_Ioc
        intro x hx
        have hx1 : ¬ x ≤ 1 := not_le.mpr hx.1
        simp [bound, hx1, hx.2]
      · have htail_int := hscore_int.mono_set (by
          intro x hx
          exact hB0.trans_lt hx)
        refine IntegrableOn.congr_fun htail_int ?_ measurableSet_Ioi
        intro x hx
        have hx1 : ¬ x ≤ 1 := not_le.mpr (h1B.trans_lt hx)
        have hxB : ¬ x ≤ B := not_le.mpr hx
        simp [bound, hx1, hxB]

  refine ⟨bound, hbound_int, ?_⟩
  intro p hp a ha x hx
  have hxpos : 0 < x := hx
  have habs_nonneg : 0 ≤ |(-S (a + x) * theta (a + x))| := abs_nonneg _

  by_cases hx1 : x ≤ 1
  · have hpow_le : x ^ p ≤ x ^ p₀ :=
      Real.rpow_le_rpow_of_exponent_ge hxpos hx1 hp.1
    have hxB : x ≤ B := hx1.trans h1B
    have hderiv_le : |(-S (a + x) * theta (a + x))| ≤ C :=
      hlocal a x ha ⟨hxpos.le, hxB⟩
    have hp₀_nonneg : 0 ≤ x ^ p₀ := Real.rpow_nonneg hxpos.le p₀
    calc
      x ^ p * |(-S (a + x) * theta (a + x))| ≤
          x ^ p₀ * |(-S (a + x) * theta (a + x))| :=
        mul_le_mul_of_nonneg_right hpow_le habs_nonneg
      _ ≤ x ^ p₀ * C := mul_le_mul_of_nonneg_left hderiv_le hp₀_nonneg
      _ = bound x := by simp [bound, hx1]; ring
  · have hx1lt : 1 < x := lt_of_not_ge hx1
    have hpow_le : x ^ p ≤ x ^ p₁ :=
      Real.rpow_le_rpow_of_exponent_le hx1lt.le hp.2
    have hp₁_nonneg : 0 ≤ x ^ p₁ := Real.rpow_nonneg hxpos.le p₁
    by_cases hxB : x ≤ B
    · have hderiv_le : |(-S (a + x) * theta (a + x))| ≤ C :=
        hlocal a x ha ⟨hxpos.le, hxB⟩
      calc
        x ^ p * |(-S (a + x) * theta (a + x))| ≤
            x ^ p₁ * |(-S (a + x) * theta (a + x))| :=
          mul_le_mul_of_nonneg_right hpow_le habs_nonneg
        _ ≤ x ^ p₁ * C := mul_le_mul_of_nonneg_left hderiv_le hp₁_nonneg
        _ = bound x := by simp [bound, hx1, hxB]; ring
    · have hBx : B < x := lt_of_not_ge hxB
      have hTx : T ≤ x := hTB.trans hBx.le
      have hderiv_le :
          |(-S (a + x) * theta (a + x))| ≤ S x * theta x :=
        htail a x ha.1 hTx
      have hscore_nonneg : 0 ≤ S x * theta x := habs_nonneg.trans hderiv_le
      calc
        x ^ p * |(-S (a + x) * theta (a + x))| ≤
            x ^ p₁ * |(-S (a + x) * theta (a + x))| :=
          mul_le_mul_of_nonneg_right hpow_le habs_nonneg
        _ ≤ x ^ p₁ * (S x * theta x) :=
          mul_le_mul_of_nonneg_left hderiv_le hp₁_nonneg
        _ = bound x := by simp [bound, hx1, hxB]; ring

end ScoreCurvatureStarOrder
