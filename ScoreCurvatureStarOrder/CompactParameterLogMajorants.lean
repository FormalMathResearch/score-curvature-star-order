import Mathlib
import ScoreCurvatureStarOrder.CompactParameterMajorants
import ScoreCurvatureStarOrder.PowerLogMoments

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- Joint compact-parameter domination for the first logarithmic power moment.

For every compact rectangle `p ∈ [p₀,p₁]`, `a ∈ [0,A]` with `p₀ > -1`,
there is a single integrable function on `(0,∞)` dominating

`x^p * log(x) * theta(a+x)`

simultaneously for all parameters in the rectangle.

The proof keeps the endpoint singularity and the tail mathematically separate.
On `(0,1]`, the lower exponent `p₀` is the worst power; on `[1,∞)`, the upper
exponent `p₁` is the worst power.  On the bounded spatial region, positivity
and continuity of `theta` give a positive minimum for the unshifted kernel and
a finite maximum for all shifts `a ∈ [0,A]`, so the shifted kernel is bounded
by a fixed multiple of the unshifted one.  On the tail, the already verified
positive-score tail makes `theta` decreasing, hence `theta(a+x) ≤ theta(x)`
for every nonnegative shift.  The resulting endpoint majorants are integrable
by the already verified first logarithmic moment theorem. -/
theorem exists_powerWeightedShift_log_compact_majorant_within
    {theta S Sprime : ℝ → ℝ} {p₀ p₁ A : ℝ}
    (hp₀ : -1 < p₀) (hp₀₁ : p₀ ≤ p₁) (hA : 0 ≤ A)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ∃ bound : ℝ → ℝ,
      IntegrableOn bound (Set.Ioi (0 : ℝ)) ∧
      ∀ p ∈ Set.Icc p₀ p₁, ∀ a ∈ Set.Icc (0 : ℝ) A, ∀ x ∈ Set.Ioi (0 : ℝ),
        ‖x ^ p * Real.log x * theta (a + x)‖ ≤ bound x := by
  have hp₁ : -1 < p₁ := hp₀.trans_le hp₀₁
  rcases automatic_positive_score_and_exponential_tail_within
      htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨R, c, hR, hc, hS_lower, _htail⟩

  let B : ℝ := max R 1
  have hRB : R ≤ B := le_max_left R 1
  have h1B : 1 ≤ B := le_max_right R 1
  have hB0 : 0 ≤ B := zero_le_one.trans h1B
  have hAB0 : 0 ≤ A + B := add_nonneg hA hB0

  have htheta_cont_Ici : ContinuousOn theta (Set.Ici (0 : ℝ)) :=
    continuousOn_Ici_of_hasDerivWithinAt htheta_deriv
  have htheta_cont_AB : ContinuousOn theta (Set.Icc (0 : ℝ) (A + B)) :=
    htheta_cont_Ici.mono (by
      intro z hz
      exact hz.1)
  rcases isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.mpr hAB0) htheta_cont_AB with
    ⟨zmax, hzmax, hzmaximal⟩
  let C : ℝ := theta zmax
  have hCpos : 0 < C := by
    dsimp [C]
    exact htheta_pos zmax hzmax.1

  have htheta_cont_B : ContinuousOn theta (Set.Icc (0 : ℝ) B) :=
    htheta_cont_Ici.mono (by
      intro z hz
      exact hz.1)
  rcases isCompact_Icc.exists_isMinOn
      (Set.nonempty_Icc.mpr hB0) htheta_cont_B with
    ⟨zmin, hzmin, hzminimal⟩
  let m : ℝ := theta zmin
  have hmpos : 0 < m := by
    dsimp [m]
    exact htheta_pos zmin hzmin.1

  let D : ℝ := C / m
  have hDpos : 0 < D := by
    dsimp [D]
    exact div_pos hCpos hmpos
  have hDm : D * m = C := by
    dsimp [D]
    field_simp [ne_of_gt hmpos]

  have hlog₀ := powerWeightedShift_log_integrableOn_Ioi_within
    (theta := theta) (S := S) (Sprime := Sprime) (a := (0 : ℝ)) (p := p₀)
    (by norm_num) hp₀ htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hlog₁ := powerWeightedShift_log_integrableOn_Ioi_within
    (theta := theta) (S := S) (Sprime := Sprime) (a := (0 : ℝ)) (p := p₁)
    (by norm_num) hp₁ htheta_pos htheta_deriv htheta_int hS hSprime_pos

  have hnorm₀ :
      IntegrableOn
        (fun x : ℝ => ‖x ^ p₀ * Real.log x * theta x‖)
        (Set.Ioi (0 : ℝ)) := by
    change Integrable
      (fun x : ℝ => ‖x ^ p₀ * Real.log x * theta x‖)
      (volume.restrict (Set.Ioi (0 : ℝ)))
    simpa using hlog₀.norm
  have hnorm₁ :
      IntegrableOn
        (fun x : ℝ => ‖x ^ p₁ * Real.log x * theta x‖)
        (Set.Ioi (0 : ℝ)) := by
    change Integrable
      (fun x : ℝ => ‖x ^ p₁ * Real.log x * theta x‖)
      (volume.restrict (Set.Ioi (0 : ℝ)))
    simpa using hlog₁.norm

  let bound : ℝ → ℝ := fun x =>
    if x ≤ 1 then D * ‖x ^ p₀ * Real.log x * theta x‖
    else if x ≤ B then D * ‖x ^ p₁ * Real.log x * theta x‖
    else ‖x ^ p₁ * Real.log x * theta x‖

  have hbound_int : IntegrableOn bound (Set.Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
    constructor
    · have hlocal₀ := hnorm₀.mono_set (by
        intro x hx
        exact hx.1)
      have hscaled₀ := hlocal₀.const_mul D
      refine IntegrableOn.congr_fun hscaled₀ ?_ measurableSet_Ioc
      intro x hx
      simp [bound, hx.2]
    · rw [← Ioc_union_Ioi_eq_Ioi h1B, integrableOn_union]
      constructor
      · have hmid₁ := hnorm₁.mono_set (by
          intro x hx
          exact zero_lt_one.trans hx.1)
        have hscaled₁ := hmid₁.const_mul D
        refine IntegrableOn.congr_fun hscaled₁ ?_ measurableSet_Ioc
        intro x hx
        have hx1 : ¬ x ≤ 1 := not_le.mpr hx.1
        simp [bound, hx1, hx.2]
      · have htail₁ := hnorm₁.mono_set (by
          intro x hx
          exact hB0.trans_lt hx)
        refine IntegrableOn.congr_fun htail₁ ?_ measurableSet_Ioi
        intro x hx
        have hx1 : ¬ x ≤ 1 := not_le.mpr (h1B.trans_lt hx)
        have hxB : ¬ x ≤ B := not_le.mpr hx
        simp [bound, hx1, hxB]

  refine ⟨bound, hbound_int, ?_⟩
  intro p hp a ha x hx
  have hxpos : 0 < x := hx
  have hax0 : 0 ≤ a + x := add_nonneg ha.1 hxpos.le
  have htheta_shift_pos : 0 < theta (a + x) := htheta_pos (a + x) hax0
  have htheta_x_pos : 0 < theta x := htheta_pos x hxpos.le
  have hlog_nonneg : 0 ≤ |Real.log x| := abs_nonneg _

  have hnorm_shift :
      ‖x ^ p * Real.log x * theta (a + x)‖ =
        x ^ p * |Real.log x| * theta (a + x) := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hxpos.le p), abs_of_pos htheta_shift_pos]
  rw [hnorm_shift]

  by_cases hx1 : x ≤ 1
  · have hpow_le : x ^ p ≤ x ^ p₀ :=
      Real.rpow_le_rpow_of_exponent_ge hxpos hx1 hp.1
    have haxAB : a + x ≤ A + B := by
      linarith [ha.2, h1B]
    have htheta_shift_C : theta (a + x) ≤ C := by
      dsimp [C]
      exact hzmaximal ⟨hax0, haxAB⟩
    have hm_le_theta : m ≤ theta x := by
      dsimp [m]
      exact hzminimal ⟨hxpos.le, hx1.trans h1B⟩
    have htheta_ratio : theta (a + x) ≤ D * theta x := by
      calc
        theta (a + x) ≤ C := htheta_shift_C
        _ = D * m := hDm.symm
        _ ≤ D * theta x := mul_le_mul_of_nonneg_left hm_le_theta hDpos.le
    have hpowlog_le :
        x ^ p * |Real.log x| ≤ x ^ p₀ * |Real.log x| :=
      mul_le_mul_of_nonneg_right hpow_le hlog_nonneg
    have hleft_nonneg : 0 ≤ x ^ p₀ * |Real.log x| :=
      mul_nonneg (Real.rpow_nonneg hxpos.le p₀) hlog_nonneg
    have hnorm₀x :
        ‖x ^ p₀ * Real.log x * theta x‖ =
          x ^ p₀ * |Real.log x| * theta x := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hxpos.le p₀), abs_of_pos htheta_x_pos]
    calc
      x ^ p * |Real.log x| * theta (a + x) ≤
          x ^ p₀ * |Real.log x| * theta (a + x) :=
        mul_le_mul_of_nonneg_right hpowlog_le htheta_shift_pos.le
      _ ≤ x ^ p₀ * |Real.log x| * (D * theta x) :=
        mul_le_mul_of_nonneg_left htheta_ratio hleft_nonneg
      _ = D * ‖x ^ p₀ * Real.log x * theta x‖ := by
        rw [hnorm₀x]
        ring
      _ = bound x := by simp [bound, hx1]
  · have hx1lt : 1 < x := lt_of_not_ge hx1
    have hpow_le : x ^ p ≤ x ^ p₁ :=
      Real.rpow_le_rpow_of_exponent_le hx1lt.le hp.2
    have hpowlog_le :
        x ^ p * |Real.log x| ≤ x ^ p₁ * |Real.log x| :=
      mul_le_mul_of_nonneg_right hpow_le hlog_nonneg
    have hleft_nonneg : 0 ≤ x ^ p₁ * |Real.log x| :=
      mul_nonneg (Real.rpow_nonneg hxpos.le p₁) hlog_nonneg
    have hnorm₁x :
        ‖x ^ p₁ * Real.log x * theta x‖ =
          x ^ p₁ * |Real.log x| * theta x := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hxpos.le p₁), abs_of_pos htheta_x_pos]
    by_cases hxB : x ≤ B
    · have haxAB : a + x ≤ A + B := by
        linarith [ha.2]
      have htheta_shift_C : theta (a + x) ≤ C := by
        dsimp [C]
        exact hzmaximal ⟨hax0, haxAB⟩
      have hm_le_theta : m ≤ theta x := by
        dsimp [m]
        exact hzminimal ⟨hxpos.le, hxB⟩
      have htheta_ratio : theta (a + x) ≤ D * theta x := by
        calc
          theta (a + x) ≤ C := htheta_shift_C
          _ = D * m := hDm.symm
          _ ≤ D * theta x := mul_le_mul_of_nonneg_left hm_le_theta hDpos.le
      calc
        x ^ p * |Real.log x| * theta (a + x) ≤
            x ^ p₁ * |Real.log x| * theta (a + x) :=
          mul_le_mul_of_nonneg_right hpowlog_le htheta_shift_pos.le
        _ ≤ x ^ p₁ * |Real.log x| * (D * theta x) :=
          mul_le_mul_of_nonneg_left htheta_ratio hleft_nonneg
        _ = D * ‖x ^ p₁ * Real.log x * theta x‖ := by
          rw [hnorm₁x]
          ring
        _ = bound x := by simp [bound, hx1, hxB]
    · have hBx : B < x := lt_of_not_ge hxB
      have hRx : R ≤ x := hRB.trans hBx.le
      have hS_lower_x : ∀ z, x ≤ z → c ≤ S z := by
        intro z hxz
        exact hS_lower z (hRx.trans hxz)
      have htheta_tail_from_x := theta_le_exp_tail
        (theta := theta) (S := S) (R := x) (c := c)
        hxpos.le hc htheta_pos htheta_deriv hS_lower_x
      have htheta_shift_exp :
          theta (a + x) ≤ theta x * Real.exp (-c * ((a + x) - x)) :=
        htheta_tail_from_x (a + x) (by linarith [ha.1])
      have hexp_le_one : Real.exp (-c * ((a + x) - x)) ≤ 1 := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        have hca : 0 ≤ c * a := mul_nonneg hc.le ha.1
        nlinarith
      have htheta_shift_le : theta (a + x) ≤ theta x := by
        calc
          theta (a + x) ≤ theta x * Real.exp (-c * ((a + x) - x)) :=
            htheta_shift_exp
          _ ≤ theta x * 1 :=
            mul_le_mul_of_nonneg_left hexp_le_one htheta_x_pos.le
          _ = theta x := by ring
      calc
        x ^ p * |Real.log x| * theta (a + x) ≤
            x ^ p₁ * |Real.log x| * theta (a + x) :=
          mul_le_mul_of_nonneg_right hpowlog_le htheta_shift_pos.le
        _ ≤ x ^ p₁ * |Real.log x| * theta x :=
          mul_le_mul_of_nonneg_left htheta_shift_le hleft_nonneg
        _ = ‖x ^ p₁ * Real.log x * theta x‖ := hnorm₁x.symm
        _ = bound x := by simp [bound, hx1, hxB]

end ScoreCurvatureStarOrder
