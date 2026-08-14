import Mathlib
import ScoreCurvatureStarOrder.Moments
import ScoreCurvatureStarOrder.Boundary

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- Derivative of the integration-by-parts boundary product on the positive half-line. -/
theorem powerWeightedShift_product_deriv
    {theta S : ℝ → ℝ} {a p x : ℝ}
    (hx : 0 < x) (hax : 0 ≤ a + x)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z) :
    HasDerivAt (fun y : ℝ => y ^ (p + 1) * theta (a + y))
      ((p + 1) * x ^ p * theta (a + x) -
        x ^ (p + 1) * S (a + x) * theta (a + x)) x := by
  have hrpow :
      HasDerivAt (fun y : ℝ => y ^ (p + 1)) ((p + 1) * x ^ p) x := by
    have h := Real.hasDerivAt_rpow_const (x := x) (p := p + 1) (Or.inl hx.ne')
    have hexp : p + 1 - 1 = p := by ring
    simpa only [hexp] using h
  have htheta_shift :
      HasDerivAt (fun y : ℝ => theta (a + y)) (-S (a + x) * theta (a + x)) x :=
    (htheta_deriv (a + x) hax).comp_const_add a x
  change HasDerivAt
    ((fun y : ℝ => y ^ (p + 1)) * (fun y : ℝ => theta (a + y)))
    ((p + 1) * x ^ p * theta (a + x) -
      x ^ (p + 1) * S (a + x) * theta (a + x)) x
  have hscalar :
      ((p + 1) * x ^ p) * theta (a + x) +
          x ^ (p + 1) * (-S (a + x) * theta (a + x)) =
        (p + 1) * x ^ p * theta (a + x) -
          x ^ (p + 1) * S (a + x) * theta (a + x) := by
    ring
  rw [← hscalar]
  exact hrpow.mul htheta_shift

/-- The derivative of `x ↦ x^(p+1) θ(a+x)` is eventually nonpositive under the
positive-score-tail assumptions. -/
theorem powerWeightedShift_product_deriv_nonpos_tail
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ∃ T : ℝ, 0 < T ∧ ∀ x, T ≤ x →
      HasDerivAt (fun y : ℝ => y ^ (p + 1) * theta (a + y))
          ((p + 1) * x ^ p * theta (a + x) -
            x ^ (p + 1) * S (a + x) * theta (a + x)) x ∧
        (p + 1) * x ^ p * theta (a + x) -
            x ^ (p + 1) * S (a + x) * theta (a + x) ≤ 0 := by
  rcases exists_positive_score_tail
      htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨R, c, hR, hc, hS_lower⟩
  let T : ℝ := max R ((p + 1) / c)
  have hp1 : 0 < p + 1 := by
    linarith
  have hquot : 0 < (p + 1) / c := div_pos hp1 hc
  have hRT : R ≤ T := by
    dsimp [T]
    exact le_max_left _ _
  have hquotT : (p + 1) / c ≤ T := by
    dsimp [T]
    exact le_max_right _ _
  have hTpos : 0 < T := hquot.trans_le hquotT
  refine ⟨T, hTpos, ?_⟩
  intro x hTx
  have hRx : R ≤ x := hRT.trans hTx
  have hquotx : (p + 1) / c ≤ x := hquotT.trans hTx
  have hxpos : 0 < x := hTpos.trans_le hTx
  have hax0 : 0 ≤ a + x := by
    linarith
  have hSax : c ≤ S (a + x) := by
    apply hS_lower
    linarith
  have hpcx : p + 1 ≤ x * c := by
    exact (div_le_iff₀ hc).mp hquotx
  have hxS : p + 1 ≤ x * S (a + x) := by
    exact hpcx.trans (mul_le_mul_of_nonneg_left hSax hxpos.le)
  have hrpow_add : x ^ (p + 1) = x ^ p * x := by
    simpa using Real.rpow_add hxpos p 1
  have hfactor :
      (p + 1) * x ^ p * theta (a + x) -
          x ^ (p + 1) * S (a + x) * theta (a + x) =
        (x ^ p * theta (a + x)) * ((p + 1) - x * S (a + x)) := by
    rw [hrpow_add]
    ring
  have hfac : 0 ≤ x ^ p * theta (a + x) :=
    mul_nonneg (Real.rpow_nonneg hxpos.le p) (htheta_pos (a + x) hax0).le
  have hdiff : (p + 1) - x * S (a + x) ≤ 0 := sub_nonpos.mpr hxS
  refine ⟨powerWeightedShift_product_deriv hxpos hax0 htheta_deriv, ?_⟩
  rw [hfactor]
  exact mul_nonpos_of_nonneg_of_nonpos hfac hdiff

/-- The score-weighted moment integrand is integrable on the positive half-line.
This is the absolute-integrability input needed for the improper integration-by-parts identity. -/
theorem powerWeightedShift_score_integrableOn_Ioi
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    IntegrableOn
      (fun x : ℝ => x ^ (p + 1) * S (a + x) * theta (a + x))
      (Set.Ioi (0 : ℝ)) := by
  rcases powerWeightedShift_product_deriv_nonpos_tail
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨T, hTpos, htail⟩
  rw [← Ioc_union_Ioi_eq_Ioi hTpos.le, integrableOn_union]
  constructor
  · rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hTpos.le]
    have hp1nonneg : 0 ≤ p + 1 := by
      linarith
    have hrpow_cont : ContinuousOn (fun x : ℝ => x ^ (p + 1)) [[0, T]] :=
      continuousOn_id.rpow_const (by
        intro x hx
        exact Or.inr hp1nonneg)
    have hS_shift_cont : ContinuousOn (fun x : ℝ => S (a + x)) [[0, T]] := by
      intro x hx
      rw [uIcc_of_le hTpos.le] at hx
      have hax0 : 0 ≤ a + x := by
        linarith [ha, hx.1]
      have hshift : ContinuousAt (fun y : ℝ => a + y) x := by
        fun_prop
      exact ((hS (a + x) hax0).continuousAt.comp hshift).continuousWithinAt
    have htheta_shift_cont : ContinuousOn (fun x : ℝ => theta (a + x)) [[0, T]] := by
      intro x hx
      rw [uIcc_of_le hTpos.le] at hx
      have hax0 : 0 ≤ a + x := by
        linarith [ha, hx.1]
      have hshift : ContinuousAt (fun y : ℝ => a + y) x := by
        fun_prop
      exact ((htheta_deriv (a + x) hax0).continuousAt.comp hshift).continuousWithinAt
    exact ((hrpow_cont.mul hS_shift_cont).mul htheta_shift_cont).intervalIntegrable
  · let g : ℝ → ℝ := fun x => x ^ (p + 1) * theta (a + x)
    let d : ℝ → ℝ := fun x =>
      (p + 1) * x ^ p * theta (a + x) -
        x ^ (p + 1) * S (a + x) * theta (a + x)
    have hderiv : ∀ x ∈ Set.Ici T, HasDerivAt g (d x) x := by
      intro x hx
      simpa [g, d] using (htail x hx).1
    have hneg : ∀ x ∈ Set.Ioi T, d x ≤ 0 := by
      intro x hx
      simpa [d] using (htail x hx.le).2
    have hg : Tendsto g atTop (𝓝 0) := by
      dsimp [g]
      exact powerWeightedShift_boundary_atTop
        ha htheta_pos htheta_deriv htheta_int hS hSprime_pos
    have hdint : IntegrableOn d (Set.Ioi T) :=
      integrableOn_Ioi_deriv_of_nonpos' hderiv hneg hg
    have hbase0 :
        IntegrableOn (fun x : ℝ => x ^ p * theta (a + x)) (Set.Ioi (0 : ℝ)) :=
      powerWeightedShift_integrableOn_Ioi
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
    have hbaseT :
        IntegrableOn (fun x : ℝ => x ^ p * theta (a + x)) (Set.Ioi T) :=
      hbase0.mono_set (fun x hx => lt_of_le_of_lt hTpos.le hx)
    have hscaled :
        IntegrableOn (fun x : ℝ => (p + 1) * (x ^ p * theta (a + x))) (Set.Ioi T) :=
      hbaseT.const_mul (p + 1)
    have hscore :
        IntegrableOn (fun x : ℝ => (p + 1) * (x ^ p * theta (a + x)) - d x)
          (Set.Ioi T) :=
      hscaled.sub hdint
    refine IntegrableOn.congr_fun hscore ?_ measurableSet_Ioi
    intro x hx
    dsimp [d]
    ring

end ScoreCurvatureStarOrder
