import Mathlib
import ScoreCurvatureStarOrder.Moments
import ScoreCurvatureStarOrder.HalfLineRegularity

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- Joint compact-parameter domination for the normalization integrand.

For every compact rectangle `p ∈ [p₀,p₁]`, `a ∈ [0,A]` with `p₀ > -1`,
there is a single integrable function on `(0,∞)` which dominates
`x^p * theta (a+x)` simultaneously for every `(p,a)` in the rectangle.

This is the `r = 0` compact-parameter majorant required by the manuscript's
local-uniform dominated-convergence argument.  Near zero the lower exponent
`p₀` is the worst case; on `x ≥ 1` the upper exponent `p₁` is the worst case.
The shift is controlled on a compact spatial interval, while the already
verified exponential tail estimate is uniform over all nonnegative shifts. -/
theorem exists_powerWeightedShift_compact_majorant_within
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
        ‖x ^ p * theta (a + x)‖ ≤ bound x := by
  have hp₁ : -1 < p₁ := hp₀.trans_le hp₀₁
  rcases automatic_positive_score_and_exponential_tail_within
      htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨R, c, hR, hc, _hS_lower, htail⟩

  let B : ℝ := max R 1
  have hRB : R ≤ B := le_max_left R 1
  have h1B : 1 ≤ B := le_max_right R 1
  have hB0 : 0 ≤ B := zero_le_one.trans h1B
  have hAB0 : 0 ≤ A + B := add_nonneg hA hB0

  have htheta_cont_Ici : ContinuousOn theta (Set.Ici (0 : ℝ)) :=
    continuousOn_Ici_of_hasDerivWithinAt htheta_deriv
  have htheta_cont_compact : ContinuousOn theta (Set.Icc (0 : ℝ) (A + B)) :=
    htheta_cont_Ici.mono (by
      intro z hz
      exact hz.1)
  rcases isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.mpr hAB0) htheta_cont_compact with
    ⟨zmax, hzmax, hzmaximal⟩
  let C : ℝ := theta zmax
  have hCpos : 0 < C := by
    dsimp [C]
    exact htheta_pos zmax hzmax.1

  let K : ℝ := theta R * Real.exp (c * R)
  have hKpos : 0 < K := by
    dsimp [K]
    exact mul_pos (htheta_pos R hR) (Real.exp_pos _)

  let bound : ℝ → ℝ := fun x =>
    if x ≤ 1 then C * x ^ p₀
    else if x ≤ B then C * x ^ p₁
    else K * (x ^ p₁ * Real.exp (-c * x))

  have hbound_int : IntegrableOn bound (Set.Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
    constructor
    · have hpow : IntegrableOn (fun x : ℝ => x ^ p₀) (Set.Ioc (0 : ℝ) 1) := by
        rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
        exact intervalIntegral.intervalIntegrable_rpow' hp₀
      have hlocal : IntegrableOn (fun x : ℝ => C * x ^ p₀) (Set.Ioc (0 : ℝ) 1) :=
        hpow.const_mul C
      refine IntegrableOn.congr_fun hlocal ?_ measurableSet_Ioc
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
        have hmid : IntegrableOn (fun x : ℝ => C * x ^ p₁) (Set.Ioc (1 : ℝ) B) :=
          hpow.const_mul C
        refine IntegrableOn.congr_fun hmid ?_ measurableSet_Ioc
        intro x hx
        have hx1 : ¬ x ≤ 1 := not_le.mpr hx.1
        simp [bound, hx1, hx.2]
      · have hbase :
            IntegrableOn (fun x : ℝ => x ^ p₁ * Real.exp (-c * x))
              (Set.Ioi (0 : ℝ)) :=
          rpow_mul_exp_neg_integrableOn_Ioi hp₁ hc
        have hbaseB :
            IntegrableOn (fun x : ℝ => x ^ p₁ * Real.exp (-c * x))
              (Set.Ioi B) :=
          hbase.mono_set (fun x hx => hB0.trans_lt hx)
        have htail_int :
            IntegrableOn (fun x : ℝ => K * (x ^ p₁ * Real.exp (-c * x)))
              (Set.Ioi B) :=
          hbaseB.const_mul K
        refine IntegrableOn.congr_fun htail_int ?_ measurableSet_Ioi
        intro x hx
        have hx1 : ¬ x ≤ 1 := not_le.mpr (h1B.trans_lt hx)
        have hxB : ¬ x ≤ B := not_le.mpr hx
        simp [bound, hx1, hxB]

  refine ⟨bound, hbound_int, ?_⟩
  intro p hp a ha x hx
  have hxpos : 0 < x := hx
  have hax0 : 0 ≤ a + x := add_nonneg ha.1 hxpos.le
  have htheta_posx : 0 < theta (a + x) := htheta_pos (a + x) hax0
  change ‖x ^ p * theta (a + x)‖ ≤ bound x
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hxpos.le p), abs_of_pos htheta_posx]

  by_cases hx1 : x ≤ 1
  · have hpow_le : x ^ p ≤ x ^ p₀ :=
      Real.rpow_le_rpow_of_exponent_ge hxpos hx1 hp.1
    have haxAB : a + x ≤ A + B := by
      linarith [ha.2, h1B]
    have htheta_le : theta (a + x) ≤ C := by
      dsimp [C]
      exact hzmaximal ⟨hax0, haxAB⟩
    have hp₀_nonneg : 0 ≤ x ^ p₀ := Real.rpow_nonneg hxpos.le p₀
    calc
      x ^ p * theta (a + x) ≤ x ^ p₀ * theta (a + x) :=
        mul_le_mul_of_nonneg_right hpow_le htheta_posx.le
      _ ≤ x ^ p₀ * C := mul_le_mul_of_nonneg_left htheta_le hp₀_nonneg
      _ = bound x := by simp [bound, hx1]; ring
  · have hx1lt : 1 < x := lt_of_not_ge hx1
    have hpow_le : x ^ p ≤ x ^ p₁ :=
      Real.rpow_le_rpow_of_exponent_le hx1lt.le hp.2
    have hp₁_nonneg : 0 ≤ x ^ p₁ := Real.rpow_nonneg hxpos.le p₁
    by_cases hxB : x ≤ B
    · have haxAB : a + x ≤ A + B := by
        linarith [ha.2]
      have htheta_le : theta (a + x) ≤ C := by
        dsimp [C]
        exact hzmaximal ⟨hax0, haxAB⟩
      calc
        x ^ p * theta (a + x) ≤ x ^ p₁ * theta (a + x) :=
          mul_le_mul_of_nonneg_right hpow_le htheta_posx.le
        _ ≤ x ^ p₁ * C := mul_le_mul_of_nonneg_left htheta_le hp₁_nonneg
        _ = bound x := by simp [bound, hx1, hxB]; ring
    · have hBx : B < x := lt_of_not_ge hxB
      have hRx : R ≤ x := hRB.trans hBx.le
      have hRax : R ≤ a + x := by linarith [ha.1, hRx]
      have htheta_tail :
          theta (a + x) ≤ theta R * Real.exp (-c * ((a + x) - R)) :=
        htail (a + x) hRax
      have hexp_le :
          Real.exp (-c * ((a + x) - R)) ≤
            Real.exp (c * R) * Real.exp (-c * x) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hca : 0 ≤ c * a := mul_nonneg hc.le ha.1
        nlinarith
      have htheta_bound : theta (a + x) ≤ K * Real.exp (-c * x) := by
        dsimp [K]
        calc
          theta (a + x) ≤ theta R * Real.exp (-c * ((a + x) - R)) := htheta_tail
          _ ≤ theta R * (Real.exp (c * R) * Real.exp (-c * x)) :=
            mul_le_mul_of_nonneg_left hexp_le (htheta_pos R hR).le
          _ = (theta R * Real.exp (c * R)) * Real.exp (-c * x) := by ring
      calc
        x ^ p * theta (a + x) ≤ x ^ p₁ * theta (a + x) :=
          mul_le_mul_of_nonneg_right hpow_le htheta_posx.le
        _ ≤ x ^ p₁ * (K * Real.exp (-c * x)) :=
          mul_le_mul_of_nonneg_left htheta_bound hp₁_nonneg
        _ = bound x := by simp [bound, hx1, hxB]; ring

end ScoreCurvatureStarOrder
