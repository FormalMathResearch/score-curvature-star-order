import Mathlib
import ScoreCurvatureStarOrder.Tail

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter Asymptotics

/-- A real power times a decaying exponential is little-o of an exponential
with half the decay rate. -/
theorem rpow_mul_exp_neg_isLittleO (p : ℝ) {c : ℝ} (hc : 0 < c) :
    (fun x : ℝ => x ^ p * Real.exp (-c * x)) =o[atTop]
      (fun x : ℝ => Real.exp (-(c / 2) * x)) := by
  refine isLittleO_of_tendsto (fun x hx => ?_) ?_
  · exfalso
    exact (Real.exp_pos (-(c / 2) * x)).ne' hx
  have hfun :
      (fun x : ℝ =>
        (x ^ p * Real.exp (-c * x)) / Real.exp (-(c / 2) * x)) =
        (fun x : ℝ => x ^ p * Real.exp (-(c / 2) * x)) := by
    funext x
    rw [div_eq_mul_inv, mul_assoc, ← Real.exp_neg, ← Real.exp_add]
    congr 2
    ring
  rw [hfun]
  exact Real.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p (c / 2) (by linarith)

/-- For every `p > -1` and `c > 0`, the function `x^p exp(-c x)` is
integrable on the positive half-line. -/
theorem rpow_mul_exp_neg_integrableOn_Ioi
    {p c : ℝ} (hp : -1 < p) (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x ^ p * Real.exp (-c * x)) (Set.Ioi (0 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (@zero_le_one ℝ _ _ _ _), integrableOn_union]
  constructor
  · rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact
      (intervalIntegral.intervalIntegrable_rpow' hp).mul_continuousOn (by fun_prop)
  · exact integrable_of_isBigO_exp_neg (by linarith : 0 < c / 2)
      ((continuousOn_id.rpow_const (by
        intro x hx
        left
        linarith)).mul (by fun_prop))
      (rpow_mul_exp_neg_isLittleO p hc).isBigO

/-- Under the project hypotheses, every power-weighted shifted kernel with
`p > -1` is integrable on `(0, ∞)`. This is the finiteness statement needed
for the normalization constant `M_p(a)`. -/
theorem powerWeightedShift_integrableOn_Ioi
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    IntegrableOn (fun x : ℝ => x ^ p * theta (a + x)) (Set.Ioi (0 : ℝ)) := by
  rcases automatic_positive_score_and_exponential_tail
      htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨R, c, hR, hc, _hS_lower, htail⟩
  let B : ℝ := max R 1
  have hRB : R ≤ B := le_max_left R 1
  have hB1 : 1 ≤ B := le_max_right R 1
  have hB0 : 0 ≤ B := hR.trans hRB
  rw [← Ioc_union_Ioi_eq_Ioi hB0, integrableOn_union]
  constructor
  · rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hB0]
    have htheta_shift_cont :
        ContinuousOn (fun x : ℝ => theta (a + x)) [[0, B]] := by
      intro x hx
      rw [uIcc_of_le hB0] at hx
      have hax0 : 0 ≤ a + x := by linarith
      exact (htheta_deriv (a + x) hax0).continuousAt.continuousWithinAt
    exact
      (intervalIntegral.intervalIntegrable_rpow' hp).mul_continuousOn htheta_shift_cont
  · have hbase :
        IntegrableOn (fun x : ℝ => x ^ p * Real.exp (-c * x)) (Set.Ioi (0 : ℝ)) :=
      rpow_mul_exp_neg_integrableOn_Ioi hp hc
    have hbaseB :
        IntegrableOn (fun x : ℝ => x ^ p * Real.exp (-c * x)) (Set.Ioi B) :=
      hbase.mono_set (fun x hx => lt_of_le_of_lt hB0 hx)
    let K : ℝ := theta R * Real.exp (c * R)
    have hKpos : 0 < K := by
      dsimp [K]
      exact mul_pos (htheta_pos R hR) (Real.exp_pos _)
    have hmajor :
        IntegrableOn
          (fun x : ℝ => K * (x ^ p * Real.exp (-c * x)))
          (Set.Ioi B) :=
      hbaseB.const_mul K
    have hrpow_cont : ContinuousOn (fun x : ℝ => x ^ p) (Set.Ioi B) :=
      continuousOn_id.rpow_const (by
        intro x hx
        left
        have hx0 : 0 < x := by linarith
        exact hx0.ne')
    have htheta_shift_cont :
        ContinuousOn (fun x : ℝ => theta (a + x)) (Set.Ioi B) := by
      intro x hx
      have hx0 : 0 < x := by linarith
      have hax0 : 0 ≤ a + x := by linarith
      exact (htheta_deriv (a + x) hax0).continuousAt.continuousWithinAt
    have hfcont :
        ContinuousOn (fun x : ℝ => x ^ p * theta (a + x)) (Set.Ioi B) :=
      hrpow_cont.mul htheta_shift_cont
    apply hmajor.mono (hfcont.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxB : B < x := hx
    have hxR : R ≤ x := hRB.trans hxB.le
    have hx0 : 0 < x := by linarith
    have hax0 : 0 ≤ a + x := by linarith
    have haxR : R ≤ a + x := by linarith
    have htheta_tail :
        theta (a + x) ≤ theta R * Real.exp (-c * ((a + x) - R)) :=
      htail (a + x) haxR
    have hexp_le :
        Real.exp (-c * ((a + x) - R)) ≤
          Real.exp (c * R) * Real.exp (-c * x) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hca : 0 ≤ c * a := mul_nonneg hc.le ha
      nlinarith
    have htheta_bound :
        theta (a + x) ≤ K * Real.exp (-c * x) := by
      dsimp [K]
      calc
        theta (a + x) ≤ theta R * Real.exp (-c * ((a + x) - R)) := htheta_tail
        _ ≤ theta R * (Real.exp (c * R) * Real.exp (-c * x)) :=
          mul_le_mul_of_nonneg_left hexp_le (htheta_pos R hR).le
        _ = (theta R * Real.exp (c * R)) * Real.exp (-c * x) := by ring
    have hxpow : 0 ≤ x ^ p := Real.rpow_nonneg x p
    have hprod :
        x ^ p * theta (a + x) ≤ K * (x ^ p * Real.exp (-c * x)) := by
      calc
        x ^ p * theta (a + x) ≤ x ^ p * (K * Real.exp (-c * x)) :=
          mul_le_mul_of_nonneg_left htheta_bound hxpow
        _ = K * (x ^ p * Real.exp (-c * x)) := by ring
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hxpow (htheta_pos (a + x) hax0).le),
      abs_of_nonneg
        (mul_nonneg hKpos.le (mul_nonneg hxpow (Real.exp_pos (-c * x)).le))]
    exact hprod

end ScoreCurvatureStarOrder
