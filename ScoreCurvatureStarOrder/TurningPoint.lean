import Mathlib
import ScoreCurvatureStarOrder.Tail
import ScoreCurvatureStarOrder.HalfLineRegularity

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- A score with strictly positive derivative on the positive half-line is
strictly increasing there.  The derivative at `0` is only assumed within
`[0, ∞)`; ordinary two-sided differentiability at the boundary is not used. -/
theorem score_strictMonoOn_Ici_within
    {S Sprime : ℝ → ℝ}
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    StrictMonoOn S (Set.Ici (0 : ℝ)) := by
  have hcontS : ContinuousOn S (Set.Ici (0 : ℝ)) :=
    continuousOn_Ici_of_hasDerivWithinAt hS
  have hderS :
      ∀ z ∈ interior (Set.Ici (0 : ℝ)),
        HasDerivWithinAt S (Sprime z) (interior (Set.Ici (0 : ℝ))) z := by
    intro z hz
    exact (hS z (interior_subset hz)).mono interior_subset
  exact strictMonoOn_of_hasDerivWithinAt_pos
    (convex_Ici (0 : ℝ)) hcontS hderS
    (fun z hz => hSprime_pos z (interior_subset hz))

/-- There is a unique positive turning point `x₀` satisfying
`x₀ S(a+x₀) = p+1`.

The proof does **not** assume that `x ↦ x S(a+x)` is increasing on all of
`(0,∞)`, which need not be true while the score is negative.  Existence uses
the automatic positive score tail.  Uniqueness compares two hypothetical
solutions; every such solution has positive score because `p+1>0`, and on that
positive-score region strict increase of `S` makes the product strictly
increase. -/
theorem powerWeightedShift_turningPoint_exists_unique_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ∃! x0 : ℝ, 0 < x0 ∧ x0 * S (a + x0) = p + 1 := by
  have hp1 : 0 < p + 1 := by linarith
  have hstrictS : StrictMonoOn S (Set.Ici (0 : ℝ)) :=
    score_strictMonoOn_Ici_within hS hSprime_pos
  have hSshift : ContinuousOn (fun x : ℝ => S (a + x)) (Set.Ici (0 : ℝ)) :=
    continuousOn_shift_Ici_of_hasDerivWithinAt ha hS
  have hprodcont :
      ContinuousOn (fun x : ℝ => x * S (a + x)) (Set.Ici (0 : ℝ)) :=
    continuousOn_id.mul hSshift
  rcases exists_positive_score_tail_within
      htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨R, c, hR, hc, hSlower⟩
  obtain ⟨X, hXmax⟩ := exists_gt (max R ((p + 1) / c))
  have hRX : R < X := (le_max_left R ((p + 1) / c)).trans_lt hXmax
  have hratioX : (p + 1) / c < X :=
    (le_max_right R ((p + 1) / c)).trans_lt hXmax
  have hXpos : 0 < X := hR.trans_lt hRX
  have hp1Xc : p + 1 < X * c := (div_lt_iff₀ hc).mp hratioX
  have hRaX : R ≤ a + X := by linarith
  have hSc : c ≤ S (a + X) := hSlower (a + X) hRaX
  have hXc_le : X * c ≤ X * S (a + X) :=
    mul_le_mul_of_nonneg_left hSc hXpos.le
  have hp1_lt_prodX : p + 1 < X * S (a + X) := hp1Xc.trans_le hXc_le
  have hcontIcc :
      ContinuousOn (fun x : ℝ => x * S (a + x)) (Set.Icc (0 : ℝ) X) :=
    hprodcont.mono (fun _ hx => hx.1)
  have htarget :
      p + 1 ∈ Set.Icc
        ((0 : ℝ) * S (a + 0))
        (X * S (a + X)) := by
    constructor
    · simpa using hp1.le
    · exact hp1_lt_prodX.le
  have himage := intermediate_value_Icc hXpos.le hcontIcc htarget
  rcases himage with ⟨x0, hx0Icc, hx0eq⟩
  change x0 * S (a + x0) = p + 1 at hx0eq
  have hx0pos : 0 < x0 := by
    by_contra hnot
    have hx0le : x0 ≤ 0 := le_of_not_gt hnot
    have hx0zero : x0 = 0 := le_antisymm hx0le hx0Icc.1
    subst x0
    simp at hx0eq
    linarith
  have hSx0pos : 0 < S (a + x0) := by
    have hmulpos : 0 < x0 * S (a + x0) := by
      rw [hx0eq]
      exact hp1
    rcases (mul_pos_iff.mp hmulpos) with h | h
    · exact h.2
    · linarith
  refine ⟨x0, ⟨hx0pos, hx0eq⟩, ?_⟩
  intro y hy
  rcases hy with ⟨hypos, hyeq⟩
  have hSypos : 0 < S (a + y) := by
    have hmulpos : 0 < y * S (a + y) := by
      rw [hyeq]
      exact hp1
    rcases (mul_pos_iff.mp hmulpos) with h | h
    · exact h.2
    · linarith
  rcases lt_trichotomy y x0 with hyx | hyx | hxy
  · have hay0 : a + y ∈ Set.Ici (0 : ℝ) := add_nonneg ha hypos.le
    have hax0 : a + x0 ∈ Set.Ici (0 : ℝ) := add_nonneg ha hx0pos.le
    have hSlt : S (a + y) < S (a + x0) :=
      hstrictS hay0 hax0 (by linarith)
    have hprod1 : y * S (a + y) < x0 * S (a + y) :=
      mul_lt_mul_of_pos_right hyx hSypos
    have hprod2 : x0 * S (a + y) < x0 * S (a + x0) :=
      mul_lt_mul_of_pos_left hSlt hx0pos
    have hcontra := hprod1.trans hprod2
    rw [hyeq, hx0eq] at hcontra
    exact (lt_irrefl (p + 1) hcontra).elim
  · exact hyx
  · have hax0 : a + x0 ∈ Set.Ici (0 : ℝ) := add_nonneg ha hx0pos.le
    have hay0 : a + y ∈ Set.Ici (0 : ℝ) := add_nonneg ha hypos.le
    have hSlt : S (a + x0) < S (a + y) :=
      hstrictS hax0 hay0 (by linarith)
    have hprod1 : x0 * S (a + x0) < y * S (a + x0) :=
      mul_lt_mul_of_pos_right hxy hSx0pos
    have hprod2 : y * S (a + x0) < y * S (a + y) :=
      mul_lt_mul_of_pos_left hSlt hypos
    have hcontra := hprod1.trans hprod2
    rw [hx0eq, hyeq] at hcontra
    exact (lt_irrefl (p + 1) hcontra).elim

/-- A positive solution `x₀ S(a+x₀)=p+1` is the unique sign-changing point of
`p+1-x S(a+x)`: the denominator is strictly positive to its left and strictly
negative to its right.  No global monotonicity of `x S(a+x)` is assumed. -/
theorem powerWeightedShift_turningPoint_sign_within
    {S Sprime : ℝ → ℝ} {a p x0 : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p) (hx0 : 0 < x0)
    (hroot : x0 * S (a + x0) = p + 1)
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    (∀ x : ℝ, 0 < x → x < x0 → 0 < p + 1 - x * S (a + x)) ∧
    (∀ x : ℝ, x0 < x → p + 1 - x * S (a + x) < 0) := by
  have hp1 : 0 < p + 1 := by linarith
  have hstrictS : StrictMonoOn S (Set.Ici (0 : ℝ)) :=
    score_strictMonoOn_Ici_within hS hSprime_pos
  have hSx0pos : 0 < S (a + x0) := by
    have hmulpos : 0 < x0 * S (a + x0) := by
      rw [hroot]
      exact hp1
    rcases (mul_pos_iff.mp hmulpos) with h | h
    · exact h.2
    · linarith
  constructor
  · intro x hx hxx0
    by_cases hSx : 0 < S (a + x)
    · have hax : a + x ∈ Set.Ici (0 : ℝ) := add_nonneg ha hx.le
      have hax0 : a + x0 ∈ Set.Ici (0 : ℝ) := add_nonneg ha hx0.le
      have hSlt : S (a + x) < S (a + x0) :=
        hstrictS hax hax0 (by linarith)
      have hprod1 : x * S (a + x) < x0 * S (a + x) :=
        mul_lt_mul_of_pos_right hxx0 hSx
      have hprod2 : x0 * S (a + x) < x0 * S (a + x0) :=
        mul_lt_mul_of_pos_left hSlt hx0
      have hlt := hprod1.trans hprod2
      rw [hroot] at hlt
      linarith
    · have hSxle : S (a + x) ≤ 0 := le_of_not_gt hSx
      have hprodle : x * S (a + x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hx.le hSxle
      linarith
  · intro x hx0x
    have hx : 0 < x := hx0.trans hx0x
    have hax0 : a + x0 ∈ Set.Ici (0 : ℝ) := add_nonneg ha hx0.le
    have hax : a + x ∈ Set.Ici (0 : ℝ) := add_nonneg ha hx.le
    have hSlt : S (a + x0) < S (a + x) :=
      hstrictS hax0 hax (by linarith)
    have hprod1 : x0 * S (a + x0) < x * S (a + x0) :=
      mul_lt_mul_of_pos_right hx0x hSx0pos
    have hprod2 : x * S (a + x0) < x * S (a + x) :=
      mul_lt_mul_of_pos_left hSlt hx
    have hlt := hprod1.trans hprod2
    rw [hroot] at hlt
    linarith

/-- Full turning-point package: there is a positive `x₀` with
`x₀ S(a+x₀)=p+1`, the denominator `p+1-x S(a+x)` changes sign strictly there,
and it has no other zero on `(0,∞)`. -/
theorem powerWeightedShift_exists_turningPoint_with_sign_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ∃ x0 : ℝ,
      0 < x0 ∧
      x0 * S (a + x0) = p + 1 ∧
      (∀ x : ℝ, 0 < x → x < x0 → 0 < p + 1 - x * S (a + x)) ∧
      (∀ x : ℝ, x0 < x → p + 1 - x * S (a + x) < 0) ∧
      (∀ x : ℝ, 0 < x →
        (p + 1 - x * S (a + x) = 0 ↔ x = x0)) := by
  rcases powerWeightedShift_turningPoint_exists_unique_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨x0, hx0prop, huniq⟩
  rcases hx0prop with ⟨hx0, hroot⟩
  rcases powerWeightedShift_turningPoint_sign_within
      ha hp hx0 hroot hS hSprime_pos with
    ⟨hleft, hright⟩
  refine ⟨x0, hx0, hroot, hleft, hright, ?_⟩
  intro x hx
  constructor
  · intro hzero
    have hxeq : x * S (a + x) = p + 1 := by linarith
    exact huniq x ⟨hx, hxeq⟩
  · intro hxx0
    subst x
    linarith

end ScoreCurvatureStarOrder
