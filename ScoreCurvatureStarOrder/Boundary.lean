import Mathlib
import ScoreCurvatureStarOrder.Tail

namespace ScoreCurvatureStarOrder

open Set Filter
open scoped Topology

/-- For `p > -1`, the integration-by-parts boundary term vanishes at the origin. -/
theorem powerWeightedShift_boundary_zero
    {theta S : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z) :
    Tendsto (fun x : ℝ => x ^ (p + 1) * theta (a + x))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  have hp1 : 0 < p + 1 := by linarith
  have hxpow :
      Tendsto (fun x : ℝ => x ^ (p + 1))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    exact (tendsto_id.mono_left inf_le_left).rpow_const_nhds_zero hp1
  have hshift :
      Tendsto (fun x : ℝ => a + x)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 a) := by
    have hfull : Tendsto (fun x : ℝ => a + x) (𝓝 0) (𝓝 a) := by
      simpa using tendsto_const_nhds.add tendsto_id
    exact hfull.mono_left inf_le_left
  have htheta :
      Tendsto (fun x : ℝ => theta (a + x))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (theta a)) :=
    (htheta_deriv a ha).continuousAt.tendsto.comp hshift
  simpa using hxpow.mul htheta

/-- The integration-by-parts boundary term also vanishes at `+∞`.
The exponential tail dominates every real power, so this statement does not
need the restriction `p > -1`. -/
theorem powerWeightedShift_boundary_atTop
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : MeasureTheory.IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    Tendsto (fun x : ℝ => x ^ (p + 1) * theta (a + x)) atTop (𝓝 0) := by
  rcases automatic_positive_score_and_exponential_tail
      htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨R, c, hR, hc, _hS_lower, htail⟩
  let K : ℝ := theta R * Real.exp (c * R)
  have hKpos : 0 < K := by
    dsimp [K]
    exact mul_pos (htheta_pos R hR) (Real.exp_pos _)
  have hmajor0 :
      Tendsto
        (fun x : ℝ => K * (x ^ (p + 1) * Real.exp (-c * x)))
        atTop (𝓝 0) := by
    simpa using
      tendsto_const_nhds.mul
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p + 1) c hc)
  refine squeeze_zero' ?_ ?_ hmajor0
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx0
    have hax0 : 0 ≤ a + x := by linarith
    exact mul_nonneg (Real.rpow_nonneg hx0.le (p + 1)) (htheta_pos (a + x) hax0).le
  · filter_upwards [eventually_ge_atTop R, eventually_gt_atTop (0 : ℝ)] with x hxR hx0
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
    have htheta_bound : theta (a + x) ≤ K * Real.exp (-c * x) := by
      dsimp [K]
      calc
        theta (a + x) ≤ theta R * Real.exp (-c * ((a + x) - R)) := htheta_tail
        _ ≤ theta R * (Real.exp (c * R) * Real.exp (-c * x)) :=
          mul_le_mul_of_nonneg_left hexp_le (htheta_pos R hR).le
        _ = (theta R * Real.exp (c * R)) * Real.exp (-c * x) := by ring
    have hxpow : 0 ≤ x ^ (p + 1) := Real.rpow_nonneg hx0.le (p + 1)
    calc
      x ^ (p + 1) * theta (a + x) ≤
          x ^ (p + 1) * (K * Real.exp (-c * x)) :=
        mul_le_mul_of_nonneg_left htheta_bound hxpow
      _ = K * (x ^ (p + 1) * Real.exp (-c * x)) := by ring

end ScoreCurvatureStarOrder
