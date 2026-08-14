import Mathlib
import ScoreCurvatureStarOrder.ScoreRatioWithin
import ScoreCurvatureStarOrder.Tail

namespace ScoreCurvatureStarOrder

open Set

/-- Half-line version of the score-ratio crossing lemma.  On a tail where the
score is bounded below by a positive constant, the logarithmic derivative
`S'/S` must eventually fall strictly below `S`.  Only one-sided regularity on
`[0, ∞)` is assumed; ordinary derivatives are recovered solely at interior
points of the later tail when the convex growth estimate needs `deriv`. -/
theorem exists_scoreRatio_lt_score_on_tail_within
    {S Sprime Ssecond : ℝ → ℝ} {R c : ℝ}
    (hR : 0 ≤ R) (hc : 0 < c)
    (hS_lower : ∀ z ∈ Set.Ici R, c ≤ S z)
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt Sprime (Ssecond z) (Set.Ici (0 : ℝ)) z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ),
      Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    ∃ T ∈ Set.Ici R, Sprime T / S T < S T := by
  have hsubset : Set.Ici R ⊆ Set.Ici (0 : ℝ) := by
    intro z hz
    exact hR.trans hz
  have hcurv_R : ∀ z ∈ Set.Ici R,
      Ssecond z * S z - (Sprime z) ^ 2 ≤ 0 := by
    intro z hz
    exact hcurv z (hsubset hz)
  have hSpos : ∀ z ∈ Set.Ici R, 0 < S z := by
    intro z hz
    exact hc.trans_le (hS_lower z hz)
  have hSnz : ∀ z ∈ Set.Ici R, S z ≠ 0 := by
    intro z hz
    exact (hSpos z hz).ne'
  have hratio : AntitoneOn (fun z => Sprime z / S z) (Set.Ici R) :=
    scoreRatio_antitoneOn_Ici_within hR hS hSprime hSnz hcurv_R
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
    exact (hS z (hsubset hz)).continuousWithinAt.mono hsubset
  have hdiff : DifferentiableOn ℝ S (interior (Set.Ici R)) := by
    intro z hz
    have hzRlt : R < z := by
      simpa only [interior_Ici, mem_Ioi] using hz
    have hzpos : 0 < z := hR.trans_lt hzRlt
    exact
      (hasDerivAt_of_pos_of_hasDerivWithinAt_Ici hzpos (hS z hzpos.le)).
        differentiableAt.differentiableWithinAt
  have hderiv_lower_int : ∀ z ∈ interior (Set.Ici R), c ^ 2 ≤ deriv S z := by
    intro z hz
    have hzRlt : R < z := by
      simpa only [interior_Ici, mem_Ioi] using hz
    have hzpos : 0 < z := hR.trans_lt hzRlt
    have hSat := hasDerivAt_of_pos_of_hasDerivWithinAt_Ici hzpos (hS z hzpos.le)
    rw [hSat.deriv]
    exact hderiv_lower z hzRlt.le
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

/-- Backward-compatible wrapper for the former two-sided assumptions. -/
theorem exists_scoreRatio_lt_score_on_tail
    {S Sprime Ssecond : ℝ → ℝ} {R c : ℝ}
    (hR : 0 ≤ R) (hc : 0 < c)
    (hS_lower : ∀ z ∈ Set.Ici R, c ≤ S z)
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt Sprime (Ssecond z) z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ), Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    ∃ T ∈ Set.Ici R, Sprime T / S T < S T := by
  exact exists_scoreRatio_lt_score_on_tail_within hR hc hS_lower
    (fun z hz => (hS z hz).hasDerivWithinAt)
    (fun z hz => (hSprime z hz).hasDerivWithinAt)
    hcurv

/-- Half-line version of eventual `S' < S²` on a positive-score tail. -/
theorem exists_scoreDeriv_lt_sq_on_tail_within
    {S Sprime Ssecond : ℝ → ℝ} {R c : ℝ}
    (hR : 0 ≤ R) (hc : 0 < c)
    (hS_lower : ∀ z ∈ Set.Ici R, c ≤ S z)
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt Sprime (Ssecond z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ),
      Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    ∃ T ∈ Set.Ici R, ∀ z ∈ Set.Ici T, Sprime z < S z ^ 2 := by
  rcases exists_scoreRatio_lt_score_on_tail_within
      hR hc hS_lower hS hSprime hcurv with
    ⟨T, hTR, hcross⟩
  have hsubset : Set.Ici R ⊆ Set.Ici (0 : ℝ) := by
    intro z hz
    exact hR.trans hz
  have hcurv_R : ∀ z ∈ Set.Ici R,
      Ssecond z * S z - (Sprime z) ^ 2 ≤ 0 := by
    intro z hz
    exact hcurv z (hsubset hz)
  have hSpos : ∀ z ∈ Set.Ici R, 0 < S z := by
    intro z hz
    exact hc.trans_le (hS_lower z hz)
  have hSnz : ∀ z ∈ Set.Ici R, S z ≠ 0 := by
    intro z hz
    exact (hSpos z hz).ne'
  have hratio : AntitoneOn (fun z => Sprime z / S z) (Set.Ici R) :=
    scoreRatio_antitoneOn_Ici_within hR hS hSprime hSnz hcurv_R
  have hcont : ContinuousOn S (Set.Ici R) := by
    intro z hz
    exact (hS z (hsubset hz)).continuousWithinAt.mono hsubset
  have hdiff : DifferentiableOn ℝ S (interior (Set.Ici R)) := by
    intro z hz
    have hzRlt : R < z := by
      simpa only [interior_Ici, mem_Ioi] using hz
    have hzpos : 0 < z := hR.trans_lt hzRlt
    exact
      (hasDerivAt_of_pos_of_hasDerivWithinAt_Ici hzpos (hS z hzpos.le)).
        differentiableAt.differentiableWithinAt
  have hderiv_nonneg : ∀ z ∈ interior (Set.Ici R), 0 ≤ deriv S z := by
    intro z hz
    have hzRlt : R < z := by
      simpa only [interior_Ici, mem_Ioi] using hz
    have hzpos : 0 < z := hR.trans_lt hzRlt
    have hSat := hasDerivAt_of_pos_of_hasDerivWithinAt_Ici hzpos (hS z hzpos.le)
    rw [hSat.deriv]
    exact (hSprime_pos z hzpos.le).le
  have hSmono : MonotoneOn S (Set.Ici R) :=
    monotoneOn_of_deriv_nonneg (convex_Ici R) hcont hdiff hderiv_nonneg
  refine ⟨T, hTR, ?_⟩
  intro z hzT
  have hzR : z ∈ Set.Ici R := by
    change R ≤ z
    exact hTR.trans hzT
  have hratio_z : Sprime z / S z ≤ Sprime T / S T :=
    hratio hTR hzR hzT
  have hSTz : S T ≤ S z := hSmono hTR hzR hzT
  have hphi : Sprime z / S z < S z :=
    lt_of_le_of_lt hratio_z (hcross.trans_le hSTz)
  have hmul : Sprime z < S z * S z :=
    (div_lt_iff₀ (hSpos z hzR)).mp hphi
  simpa [pow_two] using hmul

/-- Backward-compatible wrapper for the former two-sided assumptions. -/
theorem exists_scoreDeriv_lt_sq_on_tail
    {S Sprime Ssecond : ℝ → ℝ} {R c : ℝ}
    (hR : 0 ≤ R) (hc : 0 < c)
    (hS_lower : ∀ z ∈ Set.Ici R, c ≤ S z)
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt Sprime (Ssecond z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ), Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    ∃ T ∈ Set.Ici R, ∀ z ∈ Set.Ici T, Sprime z < S z ^ 2 := by
  exact exists_scoreDeriv_lt_sq_on_tail_within hR hc hS_lower
    (fun z hz => (hS z hz).hasDerivWithinAt)
    (fun z hz => (hSprime z hz).hasDerivWithinAt)
    hSprime_pos hcurv

/-- On a sufficiently late positive-score tail, `S * theta` is antitone under
one-sided half-line differentiability.  The proof uses within-derivatives even
at the left endpoint of the tail; no artificial derivative from the left is
introduced. -/
theorem exists_score_mul_theta_antitoneOn_tail_within
    {theta S Sprime Ssecond : ℝ → ℝ} {R c : ℝ}
    (hR : 0 ≤ R) (hc : 0 < c)
    (hS_lower : ∀ z ∈ Set.Ici R, c ≤ S z)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt Sprime (Ssecond z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ),
      Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    ∃ T ∈ Set.Ici R, AntitoneOn (fun z => S z * theta z) (Set.Ici T) := by
  rcases exists_scoreDeriv_lt_sq_on_tail_within
      hR hc hS_lower hS hSprime hSprime_pos hcurv with
    ⟨T, hTR, hlt⟩
  have hT0 : 0 ≤ T := hR.trans hTR
  have hsubsetT : Set.Ici T ⊆ Set.Ici (0 : ℝ) := by
    intro z hz
    exact hT0.trans hz
  have hcont : ContinuousOn (fun z => S z * theta z) (Set.Ici T) := by
    intro z hz
    have hSc : ContinuousWithinAt S (Set.Ici T) z :=
      (hS z (hsubsetT hz)).continuousWithinAt.mono hsubsetT
    have htc : ContinuousWithinAt theta (Set.Ici T) z :=
      (htheta_deriv z (hsubsetT hz)).continuousWithinAt.mono hsubsetT
    exact hSc.mul htc
  have hinterior_subset : interior (Set.Ici T) ⊆ Set.Ici (0 : ℝ) := by
    intro z hz
    exact hsubsetT (interior_subset hz)
  have hwithin :
      ∀ z ∈ interior (Set.Ici T),
        HasDerivWithinAt (fun y => S y * theta y)
          (theta z * (Sprime z - S z ^ 2)) (interior (Set.Ici T)) z := by
    intro z hz
    have hz0 : z ∈ Set.Ici (0 : ℝ) := hinterior_subset hz
    have hraw :
        HasDerivWithinAt (fun y => S y * theta y)
          (Sprime z * theta z + S z * (-S z * theta z))
          (interior (Set.Ici T)) z :=
      (hS z hz0).mono hinterior_subset |>.mul
        ((htheta_deriv z hz0).mono hinterior_subset)
    have hscalar :
        Sprime z * theta z + S z * (-S z * theta z) =
          theta z * (Sprime z - S z ^ 2) := by
      ring
    rw [hscalar] at hraw
    exact hraw
  have hnonpos :
      ∀ z ∈ interior (Set.Ici T), theta z * (Sprime z - S z ^ 2) ≤ 0 := by
    intro z hz
    have hzT : z ∈ Set.Ici T := interior_subset hz
    have hz0 : z ∈ Set.Ici (0 : ℝ) := hsubsetT hzT
    have hneg : Sprime z - S z ^ 2 < 0 := sub_neg.mpr (hlt z hzT)
    exact (mul_neg_of_pos_of_neg (htheta_pos z hz0) hneg).le
  refine ⟨T, hTR, ?_⟩
  exact antitoneOn_of_hasDerivWithinAt_nonpos
    (convex_Ici T) hcont hwithin hnonpos

/-- Backward-compatible wrapper for the former two-sided assumptions. -/
theorem exists_score_mul_theta_antitoneOn_tail
    {theta S Sprime Ssecond : ℝ → ℝ} {R c : ℝ}
    (hR : 0 ≤ R) (hc : 0 < c)
    (hS_lower : ∀ z ∈ Set.Ici R, c ≤ S z)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt Sprime (Ssecond z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ), Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    ∃ T ∈ Set.Ici R, AntitoneOn (fun z => S z * theta z) (Set.Ici T) := by
  exact exists_score_mul_theta_antitoneOn_tail_within hR hc hS_lower htheta_pos
    (fun z hz => (htheta_deriv z hz).hasDerivWithinAt)
    (fun z hz => (hS z hz).hasDerivWithinAt)
    (fun z hz => (hSprime z hz).hasDerivWithinAt)
    hSprime_pos hcurv

/-- Project-level form of eventual monotonicity of `S * theta` under the
one-sided half-line assumptions. -/
theorem automatic_score_mul_theta_antitoneOn_tail_within
    {theta S Sprime Ssecond : ℝ → ℝ}
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : MeasureTheory.IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt Sprime (Ssecond z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ),
      Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    ∃ T, 0 ≤ T ∧ AntitoneOn (fun z => S z * theta z) (Set.Ici T) := by
  rcases automatic_positive_score_and_exponential_tail_within
      htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨R, c, hR, hc, hS_lower, _htail⟩
  rcases exists_score_mul_theta_antitoneOn_tail_within
      hR hc hS_lower htheta_pos htheta_deriv hS hSprime hSprime_pos hcurv with
    ⟨T, hTR, hanti⟩
  exact ⟨T, hR.trans hTR, hanti⟩

/-- Backward-compatible wrapper for the former project assumptions. -/
theorem automatic_score_mul_theta_antitoneOn_tail
    {theta S Sprime Ssecond : ℝ → ℝ}
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : MeasureTheory.IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt Sprime (Ssecond z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ), Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    ∃ T, 0 ≤ T ∧ AntitoneOn (fun z => S z * theta z) (Set.Ici T) := by
  exact automatic_score_mul_theta_antitoneOn_tail_within htheta_pos
    (fun z hz => (htheta_deriv z hz).hasDerivWithinAt)
    htheta_int
    (fun z hz => (hS z hz).hasDerivWithinAt)
    (fun z hz => (hSprime z hz).hasDerivWithinAt)
    hSprime_pos hcurv

end ScoreCurvatureStarOrder
