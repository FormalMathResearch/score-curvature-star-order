import Mathlib
import ScoreCurvatureStarOrder.CumulativeRadialRatio
import ScoreCurvatureStarOrder.TurningPointConsequences
import ScoreCurvatureStarOrder.SlopeQuotient

namespace ScoreCurvatureStarOrder

open Set MeasureTheory
open scoped Interval Topology

/-- On the left side of the unique turning point, the cumulative-radial ratio
`R=A/D` dominates the reduced slope quotient `q=A'/D'`, has nonpositive
derivative, and is antitone.

The comparison `q(x) ≤ R(x)` is obtained from Cauchy's mean value theorem on
`[0,x]`: the exact endpoint identities `A(0)=D(0)=0` produce a point
`c ∈ (0,x)` with `R(x)=q(c)`, and antitonicity of `q` gives `q(x)≤q(c)`.
Thus no comparison crosses the pole at the turning point. -/
theorem powerWeightedShift_left_cumulativeRadialRatio_monotonicity_within
    {theta S Sprime Ssecond : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt Sprime (Ssecond z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ),
      Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    ∃ x0 : ℝ,
      0 < x0 ∧
      x0 * S (a + x0) = p + 1 ∧
      (∀ x : ℝ, 0 < x → x < x0 →
        powerWeightedShiftSlopeQuotient theta S a p x ≤
          powerWeightedShiftCumulativeRadialRatio theta S a p x) ∧
      (∀ x : ℝ, 0 < x → x < x0 →
        deriv (fun y : ℝ =>
          powerWeightedShiftCumulativeRadialRatio theta S a p y) x ≤ 0) ∧
      AntitoneOn
        (fun x : ℝ => powerWeightedShiftCumulativeRadialRatio theta S a p x)
        (Set.Ioo (0 : ℝ) x0) := by
  rcases powerWeightedShift_turningPoint_deriv_sign_and_slope_antitone_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (a := a) (p := p)
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime hSprime_pos hcurv with
    ⟨x0, hx0, hroot, hDleft, _hDright, hqleft, _hqright⟩
  rcases powerWeightedShift_turningPoint_sign_within
      ha hp hx0 hroot hS hSprime_pos with
    ⟨hdenleft, _hdenright⟩

  let A : ℝ → ℝ := fun y =>
    powerWeightedShiftCumulativeShiftNumerator theta S a p y
  let D : ℝ → ℝ := fun y => powerWeightedShiftRadialDensity theta a p y
  let q : ℝ → ℝ := fun y => powerWeightedShiftSlopeQuotient theta S a p y
  let R : ℝ → ℝ := fun y => powerWeightedShiftCumulativeRadialRatio theta S a p y

  have hMpos : 0 < powerWeightedShiftMoment theta a p :=
    powerWeightedShiftMoment_pos_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hdensity_pos : ∀ y : ℝ, 0 < y →
      0 < powerWeightedShiftDensity theta a p y := by
    intro y hy
    have hay : 0 ≤ a + y := by linarith
    dsimp [powerWeightedShiftDensity]
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos hy p) (htheta_pos (a + y) hay)) hMpos

  have hq_le_R : ∀ x : ℝ, 0 < x → x < x0 → q x ≤ R x := by
    intro x hx hxx0
    let G : ℝ := powerWeightedShiftScoreMean theta S a p
    let M : ℝ := powerWeightedShiftMoment theta a p
    let h : ℝ → ℝ := fun t =>
      powerWeightedShiftDensity theta a p t * (G - S (a + t))

    have htheta_shift_Ici :
        ContinuousOn (fun t : ℝ => theta (a + t)) (Set.Ici (0 : ℝ)) :=
      continuousOn_shift_Ici_of_hasDerivWithinAt ha htheta_deriv
    have hS_shift_Ici :
        ContinuousOn (fun t : ℝ => S (a + t)) (Set.Ici (0 : ℝ)) :=
      continuousOn_shift_Ici_of_hasDerivWithinAt ha hS
    have huIcc_sub : [[(0 : ℝ), x]] ⊆ Set.Ici (0 : ℝ) := by
      intro t ht
      rw [uIcc_of_le hx.le] at ht
      exact ht.1
    have htheta_shift_uIcc :
        ContinuousOn (fun t : ℝ => theta (a + t)) [[(0 : ℝ), x]] :=
      htheta_shift_Ici.mono huIcc_sub
    have hS_shift_uIcc :
        ContinuousOn (fun t : ℝ => S (a + t)) [[(0 : ℝ), x]] :=
      hS_shift_Ici.mono huIcc_sub
    have hcoeff_cont :
        ContinuousOn
          (fun t : ℝ => theta (a + t) * M⁻¹ * (G - S (a + t)))
          [[(0 : ℝ), x]] :=
      (htheta_shift_uIcc.mul
        (continuousOn_const : ContinuousOn (fun _ : ℝ => M⁻¹) [[(0 : ℝ), x]])).mul
        ((continuousOn_const : ContinuousOn (fun _ : ℝ => G) [[(0 : ℝ), x]]).sub
          hS_shift_uIcc)
    have hint_raw :
        IntervalIntegrable
          (fun t : ℝ => t ^ p * (theta (a + t) * M⁻¹ * (G - S (a + t))))
          volume 0 x :=
      (intervalIntegral.intervalIntegrable_rpow' hp).mul_continuousOn hcoeff_cont
    have hint : IntervalIntegrable h volume 0 x := by
      simpa [h, G, M, powerWeightedShiftDensity, div_eq_mul_inv, mul_assoc] using hint_raw
    have hAcont0 :
        ContinuousOn (fun y : ℝ => ∫ t : ℝ in 0..y, h t) [[(0 : ℝ), x]] :=
      intervalIntegral.continuousOn_primitive_interval'
        (a := (0 : ℝ)) hint left_mem_uIcc
    have hAcont : ContinuousOn A (Set.Icc (0 : ℝ) x) := by
      rw [← uIcc_of_le hx.le]
      simpa [A, powerWeightedShiftCumulativeShiftNumerator, h, G] using hAcont0

    have hp1 : 0 ≤ p + 1 := by linarith
    have hrpow_cont_Ici :
        ContinuousOn (fun t : ℝ => t ^ (p + 1)) (Set.Ici (0 : ℝ)) :=
      continuousOn_id.rpow_const (by
        intro t ht
        exact Or.inr hp1)
    have hDcont_Ici : ContinuousOn D (Set.Ici (0 : ℝ)) := by
      have hraw :
          ContinuousOn
            (fun t : ℝ => (t ^ (p + 1) * theta (a + t)) * M⁻¹)
            (Set.Ici (0 : ℝ)) :=
        (hrpow_cont_Ici.mul htheta_shift_Ici).mul
          (continuousOn_const : ContinuousOn (fun _ : ℝ => M⁻¹) (Set.Ici (0 : ℝ)))
      simpa [D, powerWeightedShiftRadialDensity, M, div_eq_mul_inv] using hraw
    have hDcont : ContinuousOn D (Set.Icc (0 : ℝ) x) :=
      hDcont_Ici.mono (fun _ ht => ht.1)

    have hAder : ∀ y ∈ Set.Ioo (0 : ℝ) x,
        HasDerivAt A (deriv A y) y := by
      intro y hy
      have hyA := powerWeightedShiftCumulativeShiftNumerator_hasDerivAt_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p) (x := y) ha hp hy.1 htheta_deriv hS
      simpa [A] using hyA.differentiableAt.hasDerivAt
    have hDder : ∀ y ∈ Set.Ioo (0 : ℝ) x,
        HasDerivAt D (deriv D y) y := by
      intro y hy
      have hyD := powerWeightedShiftRadialDensity_hasDerivAt_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p) (x := y)
        ha hp hy.1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
      simpa [D] using hyD.differentiableAt.hasDerivAt

    rcases exists_ratio_hasDerivAt_eq_ratio_slope
        A (fun y => deriv A y) hx hAcont hAder
        D (fun y => deriv D y) hDcont hDder with
      ⟨c, hc, hcauchy⟩
    have hc_x0 : c < x0 := hc.2.trans hxx0
    have hDcpos : 0 < deriv D c := by
      simpa [D] using hDleft c hc.1 hc_x0
    have hDxpos : 0 < D x := by
      simpa [D] using
        (powerWeightedShiftRadialDensity_pos_within
          (theta := theta) (S := S) (Sprime := Sprime)
          (a := a) (p := p) (x := x)
          ha hp hx htheta_pos htheta_deriv htheta_int hS hSprime_pos)
    have hA0 : A 0 = 0 := by
      simpa [A] using
        (powerWeightedShiftCumulativeShiftNumerator_zero
          (theta := theta) (S := S) (a := a) (p := p))
    have hD0 : D 0 = 0 := by
      simpa [D] using
        (powerWeightedShiftRadialDensity_zero
          (theta := theta) (a := a) (p := p) hp)
    rw [hA0, hD0, sub_zero, sub_zero] at hcauchy
    have hratio : A x / D x = deriv A c / deriv D c := by
      apply (div_eq_div_iff hDxpos.ne' hDcpos.ne').2
      nlinarith [hcauchy]
    have hden_c : p + 1 - c * S (a + c) ≠ 0 :=
      (hdenleft c hc.1 hc_x0).ne'
    have hqc : deriv A c / deriv D c = q c := by
      simpa [A, D, q] using
        (powerWeightedShift_APrime_div_DPrime_eq_slopeQuotient_within
          (theta := theta) (S := S) (Sprime := Sprime)
          (a := a) (p := p) (x := c)
          ha hp hc.1 htheta_pos htheta_deriv htheta_int hS hSprime_pos hden_c)
    have hR_eq_qc : R x = q c := by
      calc
        R x = A x / D x := by rfl
        _ = deriv A c / deriv D c := hratio
        _ = q c := hqc
    have hqx_le_qc : q x ≤ q c := by
      simpa [q] using
        hqleft ⟨hc.1, hc_x0⟩ ⟨hx, hxx0⟩ hc.2.le
    rw [hR_eq_qc]
    exact hqx_le_qc

  have hRderiv_nonpos : ∀ x : ℝ, 0 < x → x < x0 → deriv R x ≤ 0 := by
    intro x hx hxx0
    have hqR := hq_le_R x hx hxx0
    have hdenpos : 0 < p + 1 - x * S (a + x) := hdenleft x hx hxx0
    have hDpos : 0 < D x := by
      simpa [D] using
        (powerWeightedShiftRadialDensity_pos_within
          (theta := theta) (S := S) (Sprime := Sprime)
          (a := a) (p := p) (x := x)
          ha hp hx htheta_pos htheta_deriv htheta_int hS hSprime_pos)
    have hqR_expanded :
        (powerWeightedShiftScoreMean theta S a p - S (a + x)) /
            (p + 1 - x * S (a + x)) ≤
          A x / D x := by
      simpa [q, R, A, D, powerWeightedShiftSlopeQuotient,
        powerWeightedShiftCumulativeRadialRatio] using hqR
    have hcross :
        (powerWeightedShiftScoreMean theta S a p - S (a + x)) * D x ≤
          A x * (p + 1 - x * S (a + x)) :=
      (div_le_div_iff₀ hdenpos hDpos).mp hqR_expanded
    have hmul := mul_le_mul_of_nonneg_left hcross (hdensity_pos x hx).le
    have hnum_nonpos :
        ((powerWeightedShiftDensity theta a p x *
            (powerWeightedShiftScoreMean theta S a p - S (a + x))) * D x -
          A x *
            (powerWeightedShiftDensity theta a p x *
              (p + 1 - x * S (a + x)))) ≤ 0 := by
      nlinarith [hmul]
    have hRder := powerWeightedShiftCumulativeRadialRatio_hasDerivAt_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (x := x)
      ha hp hx htheta_pos htheta_deriv htheta_int hS hSprime_pos
    rw [show deriv R x =
        (((powerWeightedShiftDensity theta a p x *
              (powerWeightedShiftScoreMean theta S a p - S (a + x))) * D x -
            A x *
              (powerWeightedShiftDensity theta a p x *
                (p + 1 - x * S (a + x)))) /
          (D x) ^ 2) by
      simpa [R, A, D] using hRder.deriv]
    exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos (sq_nonneg _)

  have hRdiff : ∀ x ∈ Set.Ioo (0 : ℝ) x0, DifferentiableAt ℝ R x := by
    intro x hxI
    have hRx := powerWeightedShiftCumulativeRadialRatio_hasDerivAt_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (x := x)
      ha hp hxI.1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [R] using hRx.differentiableAt
  have hRcont : ContinuousOn R (Set.Ioo (0 : ℝ) x0) := by
    intro x hxI
    exact (hRdiff x hxI).continuousAt.continuousWithinAt
  have hRdiffOn : DifferentiableOn ℝ R (interior (Set.Ioo (0 : ℝ) x0)) := by
    intro x hxInt
    have hxI : x ∈ Set.Ioo (0 : ℝ) x0 := interior_subset hxInt
    exact (hRdiff x hxI).differentiableWithinAt
  have hRanti : AntitoneOn R (Set.Ioo (0 : ℝ) x0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioo (0 : ℝ) x0) hRcont hRdiffOn
    intro x hxInt
    have hxI : x ∈ Set.Ioo (0 : ℝ) x0 := interior_subset hxInt
    exact hRderiv_nonpos x hxI.1 hxI.2

  refine ⟨x0, hx0, hroot, ?_, ?_, ?_⟩
  · intro x hx hxx0
    simpa [q, R] using hq_le_R x hx hxx0
  · intro x hx hxx0
    simpa [R] using hRderiv_nonpos x hx hxx0
  · simpa [R] using hRanti

end ScoreCurvatureStarOrder
