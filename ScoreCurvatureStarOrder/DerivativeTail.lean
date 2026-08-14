import Mathlib
import ScoreCurvatureStarOrder.ScoreRatio

namespace ScoreCurvatureStarOrder

open Set

/-- On a tail where the score is bounded below by a positive constant, the
logarithmic derivative `S'/S` must eventually fall strictly below `S`.
This is the key tail regularity step behind eventual monotonicity of `|theta'|`. -/
theorem exists_scoreRatio_lt_score_on_tail
    {S Sprime Ssecond : ℝ → ℝ} {R c : ℝ}
    (hR : 0 ≤ R) (hc : 0 < c)
    (hS_lower : ∀ z ∈ Set.Ici R, c ≤ S z)
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt Sprime (Ssecond z) z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ), Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    ∃ T ∈ Set.Ici R, Sprime T / S T < S T := by
  have hsubset : Set.Ici R ⊆ Set.Ici (0 : ℝ) := by
    intro z hz
    exact hR.trans hz
  have hS_R : ∀ z ∈ Set.Ici R, HasDerivAt S (Sprime z) z := by
    intro z hz
    exact hS z (hsubset hz)
  have hSprime_R : ∀ z ∈ Set.Ici R, HasDerivAt Sprime (Ssecond z) z := by
    intro z hz
    exact hSprime z (hsubset hz)
  have hcurv_R : ∀ z ∈ Set.Ici R, Ssecond z * S z - (Sprime z) ^ 2 ≤ 0 := by
    intro z hz
    exact hcurv z (hsubset hz)
  have hSpos : ∀ z ∈ Set.Ici R, 0 < S z := by
    intro z hz
    exact hc.trans_le (hS_lower z hz)
  have hSnz : ∀ z ∈ Set.Ici R, S z ≠ 0 := by
    intro z hz
    exact (hSpos z hz).ne'
  have hratio : AntitoneOn (fun z => Sprime z / S z) (Set.Ici R) :=
    scoreRatio_antitoneOn (convex_Ici R) hS_R hSprime_R hSnz hcurv_R
  by_contra hcontra
  have hge : ∀ z ∈ Set.Ici R, S z ≤ Sprime z / S z := by
    intro z hz
    exact le_of_not_gt (fun hlt => hcontra ⟨z, hz, hlt⟩)
  have hderiv_lower : ∀ z ∈ Set.Ici R, c ^ 2 ≤ Sprime z := by
    intro z hz
    have hsquare_le : S z * S z ≤ Sprime z :=
      (le_div_iff₀ (hSpos z hz)).mp (hge z hz)
    have hcS := hS_lower z hz
    nlinarith
  have hcont : ContinuousOn S (Set.Ici R) := by
    intro z hz
    exact (hS_R z hz).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ S (interior (Set.Ici R)) := by
    intro z hz
    exact (hS_R z (interior_subset hz)).differentiableAt.differentiableWithinAt
  have hderiv_lower_int : ∀ z ∈ interior (Set.Ici R), c ^ 2 ≤ deriv S z := by
    intro z hz
    rw [(hS_R z (interior_subset hz)).deriv]
    exact hderiv_lower z (interior_subset hz)
  let qR : ℝ := Sprime R / S R
  have hRmem : R ∈ Set.Ici R := by simp
  have hRq : S R ≤ qR := by
    simpa [qR] using hge R hRmem
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  let delta : ℝ := qR - S R + 1
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  let x : ℝ := R + delta / (c ^ 2)
  have hRx : R ≤ x := by
    dsimp [x]
    exact le_add_of_nonneg_right (div_nonneg hdelta.le hc2.le)
  have hxmem : x ∈ Set.Ici R := hRx
  have hgrowth : c ^ 2 * (x - R) ≤ S x - S R :=
    (convex_Ici R).mul_sub_le_image_sub_of_le_deriv
      hcont hdiff hderiv_lower_int R hRmem x hxmem hRx
  have hstep : c ^ 2 * (x - R) = delta := by
    dsimp [x]
    field_simp [hc2.ne']
    ring
  have hq_lt_Sx : qR < S x := by
    rw [hstep] at hgrowth
    dsimp [delta] at hgrowth
    linarith
  have hSx_le_qR : S x ≤ qR := by
    have hratio_xR : Sprime x / S x ≤ Sprime R / S R :=
      hratio hRmem hxmem hRx
    exact (hge x hxmem).trans (by simpa [qR] using hratio_xR)
  linarith

end ScoreCurvatureStarOrder
