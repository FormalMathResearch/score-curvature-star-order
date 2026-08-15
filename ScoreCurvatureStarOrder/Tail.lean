import Mathlib
import ScoreCurvatureStarOrder.HalfLineRegularity

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- A positive integrable kernel whose logarithmic score relation is
`θ' = -S θ` must have positive score somewhere on `[0, ∞)`.

The derivative hypothesis is deliberately formulated *within* `[0, ∞)`, so at
`0` it only requires the mathematically natural right derivative. -/
theorem exists_score_pos_of_integrable
    {theta S : ℝ → ℝ}
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ))) :
    ∃ R ∈ Set.Ici (0 : ℝ), 0 < S R := by
  by_contra hpos
  push_neg at hpos
  have hcont : ContinuousOn theta (Set.Ici (0 : ℝ)) :=
    continuousOn_Ici_of_hasDerivWithinAt htheta_deriv
  have hder :
      ∀ z ∈ interior (Set.Ici (0 : ℝ)),
        HasDerivWithinAt theta (-S z * theta z)
          (interior (Set.Ici (0 : ℝ))) z := by
    intro z hz
    exact (htheta_deriv z (interior_subset hz)).mono interior_subset
  have hmono : MonotoneOn theta (Set.Ici (0 : ℝ)) := by
    exact monotoneOn_of_hasDerivWithinAt_nonneg
      (convex_Ici (0 : ℝ)) hcont hder fun z hz => by
        have hzI : z ∈ Set.Ici (0 : ℝ) := interior_subset hz
        exact mul_nonneg (neg_nonneg.mpr (hpos z hzI)) (htheta_pos z hzI).le
  have hconst_int :
      IntegrableOn (fun _ : ℝ => theta 0) (Set.Ici (0 : ℝ)) := by
    change Integrable (fun _ : ℝ => theta 0) (volume.restrict (Set.Ici (0 : ℝ)))
    apply htheta_int.integrable.mono
    · exact aestronglyMeasurable_const
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      have hle : theta 0 ≤ theta z :=
        hmono (by simp) hz (by simpa using hz)
      have h0pos : 0 < theta 0 := htheta_pos 0 (by simp)
      have hzpos : 0 < theta z := htheta_pos z hz
      simpa [Real.norm_eq_abs, abs_of_pos h0pos, abs_of_pos hzpos] using hle
  have hconst :=
    (integrableOn_const_iff (s := Set.Ici (0 : ℝ)) (μ := volume) (C := theta 0)).1 hconst_int
  rcases hconst with hzero | hfinite
  · have h0pos : 0 < theta 0 := htheta_pos 0 (by simp)
    have h0ne : theta 0 ≠ 0 := ne_of_gt h0pos
    exact h0ne (by simpa using hzero)
  · simpa using hfinite

/-- Under positive score derivative, the score is eventually bounded below by a
strictly positive constant. Score differentiability is only assumed within the
closed positive half-line. -/
theorem exists_positive_score_tail_within
    {theta S Sprime : ℝ → ℝ}
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ∃ R c : ℝ, 0 ≤ R ∧ 0 < c ∧ ∀ x, R ≤ x → c ≤ S x := by
  have hcontS : ContinuousOn S (Set.Ici (0 : ℝ)) :=
    continuousOn_Ici_of_hasDerivWithinAt hS
  have hderS :
      ∀ z ∈ interior (Set.Ici (0 : ℝ)),
        HasDerivWithinAt S (Sprime z) (interior (Set.Ici (0 : ℝ))) z := by
    intro z hz
    exact (hS z (interior_subset hz)).mono interior_subset
  have hmonoS : MonotoneOn S (Set.Ici (0 : ℝ)) := by
    exact monotoneOn_of_hasDerivWithinAt_nonneg
      (convex_Ici (0 : ℝ)) hcontS hderS
      (fun z hz => (hSprime_pos z (interior_subset hz)).le)
  rcases exists_score_pos_of_integrable htheta_pos htheta_deriv htheta_int with
    ⟨R, hR, hSR⟩
  refine ⟨R, S R, hR, hSR, ?_⟩
  intro x hRx
  have hx0 : x ∈ Set.Ici (0 : ℝ) := hR.trans hRx
  exact hmonoS hR hx0 hRx

/-- Compatibility wrapper for the pre-refactor two-sided derivative interface.
Downstream theorems are migrated away from this wrapper incrementally. -/
theorem exists_positive_score_tail
    {theta S Sprime : ℝ → ℝ}
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ∃ R c : ℝ, 0 ≤ R ∧ 0 < c ∧ ∀ x, R ≤ x → c ≤ S x := by
  exact exists_positive_score_tail_within
    htheta_pos
    (fun z hz => (htheta_deriv z hz).hasDerivWithinAt)
    htheta_int
    (fun z hz => (hS z hz).hasDerivWithinAt)
    hSprime_pos

/-- Once `S ≥ c > 0` on a tail, the relation `θ' = -S θ` gives the
exponential tail bound directly via monotonicity of `x ↦ exp(c x) θ(x)`.
The boundary derivative of `theta` is only a within-derivative on `[0, ∞)`. -/
theorem theta_le_exp_tail
    {theta S : ℝ → ℝ} {R c : ℝ}
    (hR : 0 ≤ R) (hc : 0 < c)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (hS_lower : ∀ z, R ≤ z → c ≤ S z) :
    ∀ x, R ≤ x → theta x ≤ theta R * Real.exp (-c * (x - R)) := by
  have hsub : Set.Ici R ⊆ Set.Ici (0 : ℝ) := by
    intro z hz
    exact hR.trans hz
  have hcont : ContinuousOn (fun z => Real.exp (c * z) * theta z) (Set.Ici R) := by
    intro z hz
    have hz0 : z ∈ Set.Ici (0 : ℝ) := hsub hz
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (c * y))
        (Real.exp (c * z) * c) z := by
      simpa using ((hasDerivAt_id z).const_mul c).exp
    have hthetaR :
        HasDerivWithinAt theta (-S z * theta z) (Set.Ici R) z :=
      (htheta_deriv z hz0).mono hsub
    exact (hexp.hasDerivWithinAt.mul hthetaR).continuousWithinAt
  have hsubInt : interior (Set.Ici R) ⊆ Set.Ici (0 : ℝ) := by
    intro z hz
    exact hR.trans (interior_subset hz)
  have hder :
      ∀ z ∈ interior (Set.Ici R),
        HasDerivWithinAt (fun y : ℝ => Real.exp (c * y) * theta y)
          ((Real.exp (c * z) * c) * theta z +
            Real.exp (c * z) * (-S z * theta z))
          (interior (Set.Ici R)) z := by
    intro z hz
    have hz0 : z ∈ Set.Ici (0 : ℝ) := hsubInt hz
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (c * y))
        (Real.exp (c * z) * c) z := by
      simpa using ((hasDerivAt_id z).const_mul c).exp
    exact hexp.hasDerivWithinAt.mul ((htheta_deriv z hz0).mono hsubInt)
  have hnonpos :
      ∀ z ∈ interior (Set.Ici R),
        (Real.exp (c * z) * c) * theta z +
            Real.exp (c * z) * (-S z * theta z) ≤ 0 := by
    intro z hz
    have hzR : R ≤ z := interior_subset hz
    have hz0 : z ∈ Set.Ici (0 : ℝ) := hR.trans hzR
    have hfac : 0 ≤ Real.exp (c * z) * theta z :=
      mul_nonneg (Real.exp_pos _).le (htheta_pos z hz0).le
    have hdiff : c - S z ≤ 0 := sub_nonpos.mpr (hS_lower z hzR)
    have hfactor :
        (Real.exp (c * z) * c) * theta z +
            Real.exp (c * z) * (-S z * theta z) =
          (Real.exp (c * z) * theta z) * (c - S z) := by
      ring
    rw [hfactor]
    exact mul_nonpos_of_nonneg_of_nonpos hfac hdiff
  have hanti : AntitoneOn (fun z => Real.exp (c * z) * theta z) (Set.Ici R) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici R) hcont hder hnonpos
  intro x hx
  have hweighted : Real.exp (c * x) * theta x ≤ Real.exp (c * R) * theta R :=
    hanti (by simp) hx hx
  have hdiv : theta x ≤ (Real.exp (c * R) * theta R) / Real.exp (c * x) := by
    apply (le_div_iff₀ (Real.exp_pos (c * x))).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hweighted
  calc
    theta x ≤ (Real.exp (c * R) * theta R) / Real.exp (c * x) := hdiv
    _ = theta R * (Real.exp (c * R) / Real.exp (c * x)) := by ring
    _ = theta R * Real.exp (c * R - c * x) := by rw [← Real.exp_sub]
    _ = theta R * Real.exp (-c * (x - R)) := by ring_nf

/-- Lemma 2.2 of the manuscript in its mathematically natural half-line form:
integrability and strictly increasing score imply an automatic positive score
tail and exponential decay of the kernel. All differentiability hypotheses are
formulated within `[0, ∞)`. -/
theorem automatic_positive_score_and_exponential_tail_within
    {theta S Sprime : ℝ → ℝ}
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ∃ R c : ℝ, 0 ≤ R ∧ 0 < c ∧
      (∀ x, R ≤ x → c ≤ S x) ∧
      (∀ x, R ≤ x → theta x ≤ theta R * Real.exp (-c * (x - R))) := by
  rcases exists_positive_score_tail_within
      htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨R, c, hR, hc, hS_lower⟩
  refine ⟨R, c, hR, hc, hS_lower, ?_⟩
  exact theta_le_exp_tail hR hc htheta_pos htheta_deriv hS_lower

/-- Backward-compatible version of `automatic_positive_score_and_exponential_tail_within`.
This wrapper keeps the existing development compiling while downstream theorems
are migrated to one-sided half-line regularity. It will not be used by the final
publication theorem. -/
theorem automatic_positive_score_and_exponential_tail
    {theta S Sprime : ℝ → ℝ}
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ∃ R c : ℝ, 0 ≤ R ∧ 0 < c ∧
      (∀ x, R ≤ x → c ≤ S x) ∧
      (∀ x, R ≤ x → theta x ≤ theta R * Real.exp (-c * (x - R))) := by
  exact automatic_positive_score_and_exponential_tail_within
    htheta_pos
    (fun z hz => (htheta_deriv z hz).hasDerivWithinAt)
    htheta_int
    (fun z hz => (hS z hz).hasDerivWithinAt)
    hSprime_pos

end ScoreCurvatureStarOrder
