import Mathlib
import ScoreCurvatureStarOrder.Moments
import ScoreCurvatureStarOrder.Boundary
import ScoreCurvatureStarOrder.HalfLineRegularity

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- Derivative of the integration-by-parts boundary product at an interior
shifted point.  The kernel derivative is assumed only within `[0, ∞)`; the
strict inequality `0 < a + x` is exactly what promotes it to an ordinary
derivative at the point used by integration by parts. -/
theorem powerWeightedShift_product_deriv_within
    {theta S : ℝ → ℝ} {a p x : ℝ}
    (hx : 0 < x) (hax : 0 < a + x)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z) :
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
    hasDerivAt_shift_of_pos_of_hasDerivWithinAt_Ici hax htheta_deriv
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

/-- Backward-compatible derivative lemma with the former stronger pointwise
`HasDerivAt` assumption. -/
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
positive-score-tail assumptions, with only half-line differentiability at the
boundary. -/
theorem powerWeightedShift_product_deriv_nonpos_tail_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ∃ T : ℝ, 0 < T ∧ ∀ x, T ≤ x →
      HasDerivAt (fun y : ℝ => y ^ (p + 1) * theta (a + y))
          ((p + 1) * x ^ p * theta (a + x) -
            x ^ (p + 1) * S (a + x) * theta (a + x)) x ∧
        (p + 1) * x ^ p * theta (a + x) -
            x ^ (p + 1) * S (a + x) * theta (a + x) ≤ 0 := by
  rcases exists_positive_score_tail_within
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
  have haxpos : 0 < a + x := by
    linarith
  have hax0 : 0 ≤ a + x := haxpos.le
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
  refine ⟨powerWeightedShift_product_deriv_within hxpos haxpos htheta_deriv, ?_⟩
  rw [hfactor]
  exact mul_nonpos_of_nonneg_of_nonpos hfac hdiff

/-- Backward-compatible wrapper for the old two-sided assumptions. -/
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
  exact powerWeightedShift_product_deriv_nonpos_tail_within
    ha hp htheta_pos
    (fun z hz => (htheta_deriv z hz).hasDerivWithinAt)
    htheta_int
    (fun z hz => (hS z hz).hasDerivWithinAt)
    hSprime_pos

/-- The score-weighted moment integrand is integrable on the positive half-line.
This is the absolute-integrability input needed for the improper integration-by-parts identity.
All boundary differentiability assumptions are one-sided on `[0, ∞)`. -/
theorem powerWeightedShift_score_integrableOn_Ioi_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    IntegrableOn
      (fun x : ℝ => x ^ (p + 1) * S (a + x) * theta (a + x))
      (Set.Ioi (0 : ℝ)) := by
  rcases powerWeightedShift_product_deriv_nonpos_tail_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨T, hTpos, htail⟩
  have hS_shift_Ici : ContinuousOn (fun x : ℝ => S (a + x)) (Set.Ici (0 : ℝ)) :=
    continuousOn_shift_Ici_of_hasDerivWithinAt ha hS
  have htheta_shift_Ici : ContinuousOn (fun x : ℝ => theta (a + x)) (Set.Ici (0 : ℝ)) :=
    continuousOn_shift_Ici_of_hasDerivWithinAt ha htheta_deriv
  rw [← Ioc_union_Ioi_eq_Ioi hTpos.le, integrableOn_union]
  constructor
  · rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hTpos.le]
    have hp1nonneg : 0 ≤ p + 1 := by
      linarith
    have hrpow_cont : ContinuousOn (fun x : ℝ => x ^ (p + 1)) [[0, T]] :=
      continuousOn_id.rpow_const (by
        intro x hx
        exact Or.inr hp1nonneg)
    have huIcc_sub : [[0, T]] ⊆ Set.Ici (0 : ℝ) := by
      intro x hx
      rw [uIcc_of_le hTpos.le] at hx
      exact hx.1
    have hS_shift_cont : ContinuousOn (fun x : ℝ => S (a + x)) [[0, T]] :=
      hS_shift_Ici.mono huIcc_sub
    have htheta_shift_cont : ContinuousOn (fun x : ℝ => theta (a + x)) [[0, T]] :=
      htheta_shift_Ici.mono huIcc_sub
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
      exact powerWeightedShift_boundary_atTop_within
        ha htheta_pos htheta_deriv htheta_int hS hSprime_pos
    have hdint : IntegrableOn d (Set.Ioi T) :=
      integrableOn_Ioi_deriv_of_nonpos' hderiv hneg hg
    have hbase0 :
        IntegrableOn (fun x : ℝ => x ^ p * theta (a + x)) (Set.Ioi (0 : ℝ)) :=
      powerWeightedShift_integrableOn_Ioi_within
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

/-- Backward-compatible wrapper for `powerWeightedShift_score_integrableOn_Ioi_within`. -/
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
  exact powerWeightedShift_score_integrableOn_Ioi_within
    ha hp htheta_pos
    (fun z hz => (htheta_deriv z hz).hasDerivWithinAt)
    htheta_int
    (fun z hz => (hS z hz).hasDerivWithinAt)
    hSprime_pos

end ScoreCurvatureStarOrder
