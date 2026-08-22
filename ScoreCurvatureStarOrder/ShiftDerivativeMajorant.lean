import Mathlib
import ScoreCurvatureStarOrder.ScoreIntegrability
import ScoreCurvatureStarOrder.DerivativeTail
import ScoreCurvatureStarOrder.HalfLineRegularity

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- For every `p > -1`, the unshifted score weight `x^p S(x) theta(x)` is
absolutely integrable on the positive half-line under one-sided regularity on
`[0, ∞)`.  Ordinary differentiability of `theta` is used only on a tail bounded
away from zero. -/
theorem powerWeightedUnshifted_score_integrableOn_Ioi_within
    {theta S Sprime : ℝ → ℝ} {p : ℝ}
    (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    IntegrableOn (fun x : ℝ => x ^ p * S x * theta x) (Set.Ioi (0 : ℝ)) := by
  by_cases hp0 : 0 < p
  · have hp' : -1 < p - 1 := by linarith
    have h := powerWeightedShift_score_integrableOn_Ioi_within
      (theta := theta) (S := S) (Sprime := Sprime) (a := 0) (p := p - 1)
      (by norm_num) hp' htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa using h
  · have hp_nonpos : p ≤ 0 := le_of_not_gt hp0
    rcases exists_positive_score_tail_within
        htheta_pos htheta_deriv htheta_int hS hSprime_pos with
      ⟨R, c, hR, hc, hS_lower⟩
    let B : ℝ := max R 1
    have hRB : R ≤ B := by
      dsimp [B]
      exact le_max_left _ _
    have h1B : 1 ≤ B := by
      dsimp [B]
      exact le_max_right _ _
    have hBpos : 0 < B := zero_lt_one.trans_le h1B
    have hScont_Ici : ContinuousOn S (Set.Ici (0 : ℝ)) :=
      continuousOn_Ici_of_hasDerivWithinAt hS
    have htheta_cont_Ici : ContinuousOn theta (Set.Ici (0 : ℝ)) :=
      continuousOn_Ici_of_hasDerivWithinAt htheta_deriv
    rw [← Ioc_union_Ioi_eq_Ioi hBpos.le, integrableOn_union]
    constructor
    · rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hBpos.le]
      have hIcc_sub : [[0, B]] ⊆ Set.Ici (0 : ℝ) := by
        intro x hx
        rw [uIcc_of_le hBpos.le] at hx
        exact hx.1
      have hScont : ContinuousOn S [[0, B]] := hScont_Ici.mono hIcc_sub
      have hthetacont : ContinuousOn theta [[0, B]] := htheta_cont_Ici.mono hIcc_sub
      have hlocal :=
        (intervalIntegral.intervalIntegrable_rpow' hp).mul_continuousOn
          (hScont.mul hthetacont)
      simpa [mul_assoc] using hlocal
    · have htheta_zero : Tendsto theta atTop (𝓝 0) := by
        have hboundary := powerWeightedShift_boundary_atTop_within
          (theta := theta) (S := S) (Sprime := Sprime) (a := 0) (p := -1)
          (by norm_num) htheta_pos htheta_deriv htheta_int hS hSprime_pos
        simpa using hboundary
      have hderivB :
          ∀ x ∈ Set.Ici B, HasDerivAt theta (-S x * theta x) x := by
        intro x hx
        have hxpos : 0 < x := zero_lt_one.trans_le (h1B.trans hx)
        exact hasDerivAt_of_pos_of_hasDerivWithinAt_Ici
          hxpos (htheta_deriv x hxpos.le)
      have hneg : ∀ x ∈ Set.Ioi B, -S x * theta x ≤ 0 := by
        intro x hx
        have hxR : R ≤ x := hRB.trans hx.le
        have hx0 : 0 ≤ x := hR.trans hxR
        have hSx : 0 < S x := hc.trans_le (hS_lower x hxR)
        have hthetax : 0 < theta x := htheta_pos x hx0
        nlinarith [mul_pos hSx hthetax]
      have hderivInt : IntegrableOn (fun x : ℝ => -S x * theta x) (Set.Ioi B) :=
        integrableOn_Ioi_deriv_of_nonpos' hderivB hneg htheta_zero
      have hscoreB : IntegrableOn (fun x : ℝ => S x * theta x) (Set.Ioi B) := by
        have hnegInt := hderivInt.neg
        refine IntegrableOn.congr_fun hnegInt ?_ measurableSet_Ioi
        intro x hx
        simp
      have hrpow_cont : ContinuousOn (fun x : ℝ => x ^ p) (Set.Ioi B) :=
        continuousOn_id.rpow_const (by
          intro x hx
          left
          change x ≠ 0
          exact (hBpos.trans hx).ne')
      have hIoi_sub : Set.Ioi B ⊆ Set.Ici (0 : ℝ) := by
        intro x hx
        exact (hBpos.trans hx).le
      have hScont : ContinuousOn S (Set.Ioi B) := hScont_Ici.mono hIoi_sub
      have hthetacont : ContinuousOn theta (Set.Ioi B) := htheta_cont_Ici.mono hIoi_sub
      have hfcont : ContinuousOn (fun x : ℝ => x ^ p * S x * theta x) (Set.Ioi B) :=
        (hrpow_cont.mul hScont).mul hthetacont
      change Integrable (fun x : ℝ => x ^ p * S x * theta x) (volume.restrict (Set.Ioi B))
      refine hscoreB.integrable.mono (hfcont.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : 1 ≤ x := h1B.trans hx.le
      have hxpos : 0 < x := zero_lt_one.trans_le hx1
      have hxR : R ≤ x := hRB.trans hx.le
      have hx0 : 0 ≤ x := hxpos.le
      have hpow_nonneg : 0 ≤ x ^ p := Real.rpow_nonneg hx0 p
      have hpow_le : x ^ p ≤ 1 :=
        (Real.rpow_le_one_iff_of_pos hxpos).2 (Or.inl ⟨hx1, hp_nonpos⟩)
      have hSx : 0 < S x := hc.trans_le (hS_lower x hxR)
      have hthetax : 0 < theta x := htheta_pos x hx0
      have hscore_nonneg : 0 ≤ S x * theta x := (mul_pos hSx hthetax).le
      have hweighted_nonneg : 0 ≤ x ^ p * S x * theta x :=
        mul_nonneg (mul_nonneg hpow_nonneg hSx.le) hthetax.le
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg hweighted_nonneg, abs_of_nonneg hscore_nonneg]
      calc
        x ^ p * S x * theta x = x ^ p * (S x * theta x) := by ring
        _ ≤ 1 * (S x * theta x) := mul_le_mul_of_nonneg_right hpow_le hscore_nonneg
        _ = S x * theta x := one_mul _

/-- Backward-compatible wrapper for the former two-sided assumptions. -/
theorem powerWeightedUnshifted_score_integrableOn_Ioi
    {theta S Sprime : ℝ → ℝ} {p : ℝ}
    (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    IntegrableOn (fun x : ℝ => x ^ p * S x * theta x) (Set.Ioi (0 : ℝ)) := by
  exact powerWeightedUnshifted_score_integrableOn_Ioi_within hp htheta_pos
    (fun z hz => (htheta_deriv z hz).hasDerivWithinAt)
    htheta_int
    (fun z hz => (hS z hz).hasDerivWithinAt)
    hSprime_pos

/-- On a sufficiently late tail, the absolute shifted `a`-derivative of
`theta(a+x)` is bounded by the unshifted score weight, uniformly for every
`a ≥ 0`, under one-sided half-line regularity. -/
theorem exists_shifted_thetaDeriv_tail_majorant_within
    {theta S Sprime Ssecond : ℝ → ℝ}
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
    ∃ T, 0 ≤ T ∧ ∀ a x : ℝ, 0 ≤ a → T ≤ x →
      |(-S (a + x) * theta (a + x))| ≤ S x * theta x := by
  rcases automatic_score_mul_theta_antitoneOn_tail_within
      htheta_pos htheta_deriv htheta_int hS hSprime hSprime_pos hcurv with
    ⟨T₀, hT₀, hanti⟩
  rcases exists_positive_score_tail_within
      htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨R, c, hR, hc, hS_lower⟩
  let T : ℝ := max T₀ R
  have hT₀T : T₀ ≤ T := by
    dsimp [T]
    exact le_max_left _ _
  have hRT : R ≤ T := by
    dsimp [T]
    exact le_max_right _ _
  have hT0 : 0 ≤ T := hT₀.trans hT₀T
  refine ⟨T, hT0, ?_⟩
  intro a x ha hTx
  have hxT₀ : T₀ ≤ x := hT₀T.trans hTx
  have haxT₀ : T₀ ≤ a + x := by linarith
  have hxxa : x ≤ a + x := by linarith
  have hprod_le : S (a + x) * theta (a + x) ≤ S x * theta x :=
    hanti hxT₀ haxT₀ hxxa
  have haxR : R ≤ a + x := by linarith [hRT.trans hTx]
  have hax0 : 0 ≤ a + x := hR.trans haxR
  have hSax : 0 < S (a + x) := hc.trans_le (hS_lower (a + x) haxR)
  have hthetaax : 0 < theta (a + x) := htheta_pos (a + x) hax0
  rw [abs_mul, abs_neg, abs_of_pos hSax, abs_of_pos hthetaax]
  exact hprod_le

/-- Backward-compatible wrapper for the former two-sided assumptions. -/
theorem exists_shifted_thetaDeriv_tail_majorant
    {theta S Sprime Ssecond : ℝ → ℝ}
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt Sprime (Ssecond z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ), Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    ∃ T, 0 ≤ T ∧ ∀ a x : ℝ, 0 ≤ a → T ≤ x →
      |(-S (a + x) * theta (a + x))| ≤ S x * theta x := by
  exact exists_shifted_thetaDeriv_tail_majorant_within htheta_pos
    (fun z hz => (htheta_deriv z hz).hasDerivWithinAt)
    htheta_int
    (fun z hz => (hS z hz).hasDerivWithinAt)
    (fun z hz => (hSprime z hz).hasDerivWithinAt)
    hSprime_pos hcurv

end ScoreCurvatureStarOrder
