import Mathlib
import ScoreCurvatureStarOrder.QuantileLogDerivative
import ScoreCurvatureStarOrder.GlobalCumulativeRadialRatio

namespace ScoreCurvatureStarOrder

open Set MeasureTheory
open scoped Topology

/-- For two strictly positive shifts `0 < a₁ < a₂`, the canonical quantile
ratio `Q_{p,a₂}(u) / Q_{p,a₁}(u)` is nondecreasing in the probability level
`u ∈ (0,1)`.

The proof differentiates, for fixed `0 < u < v < 1`,

`H(a) = log Q_{p,a}(v) - log Q_{p,a}(u)`.

The logarithmic quantile derivative gives

`H'(a) = R_{p,a}(Q_{p,a}(u)) - R_{p,a}(Q_{p,a}(v)) ≥ 0`,

because the quantile is strictly increasing in its level and the global
cumulative-radial ratio `R` is antitone on the positive half-line.  Monotonicity
of `H` between `a₁` and `a₂` then yields the desired quantile-ratio inequality.
The boundary case `a₁ = 0` is intentionally excluded here and will be obtained
later by a separate `a ↓ 0` continuity argument. -/
theorem powerWeightedShift_quantileRatio_monotoneOn_Ioo_pos_shifts_within
    {theta S Sprime Ssecond : ℝ → ℝ} {a₁ a₂ p : ℝ}
    (ha₁ : 0 < a₁) (ha₁₂ : a₁ < a₂) (hp : -1 < p)
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
    MonotoneOn
      (fun u : ℝ =>
        powerWeightedShiftQuantile theta a₂ p u /
          powerWeightedShiftQuantile theta a₁ p u)
      (Set.Ioo (0 : ℝ) 1) := by
  intro u hu v hv huv

  let Q : ℝ → ℝ → ℝ := fun a w => powerWeightedShiftQuantile theta a p w
  let R : ℝ → ℝ → ℝ := fun a x =>
    powerWeightedShiftCumulativeRadialRatio theta S a p x
  let H : ℝ → ℝ := fun a => Real.log (Q a v) - Real.log (Q a u)

  have hHderiv : ∀ a : ℝ, a ∈ Set.Icc a₁ a₂ →
      HasDerivAt H (R a (Q a u) - R a (Q a v)) a := by
    intro a ha
    have hapos : 0 < a := ha₁.trans_le ha.1
    have huDeriv := powerWeightedShift_logQuantile_hasDerivAt_shift_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (a := a) (p := p) (u := u)
      hapos hp hu.1 hu.2 htheta_pos htheta_deriv htheta_int hS hSprime
      hSprime_pos hcurv
    have hvDeriv := powerWeightedShift_logQuantile_hasDerivAt_shift_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (a := a) (p := p) (u := v)
      hapos hp hv.1 hv.2 htheta_pos htheta_deriv htheta_int hS hSprime
      hSprime_pos hcurv
    have hsub := hvDeriv.sub huDeriv
    simpa [H, Q, R, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsub

  have hHderiv_nonneg : ∀ a ∈ interior (Set.Icc a₁ a₂), 0 ≤ deriv H a := by
    intro a haInt
    have ha : a ∈ Set.Icc a₁ a₂ := interior_subset haInt
    have hapos : 0 < a := ha₁.trans_le ha.1

    have hQmono := powerWeightedShiftQuantile_strictMonoOn_Ioo_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p)
      hapos.le hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
    have hQuv : Q a u < Q a v := by
      simpa [Q] using hQmono hu hv huv

    have hQu := powerWeightedShiftQuantile_pos_and_CDF_eq_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (u := u)
      hapos.le hp hu.1 hu.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos
    have hQv := powerWeightedShiftQuantile_pos_and_CDF_eq_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (u := v)
      hapos.le hp hv.1 hv.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos

    have hRanti := powerWeightedShift_cumulativeRadialRatio_antitoneOn_Ioi_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (a := a) (p := p)
      hapos.le hp htheta_pos htheta_deriv htheta_int hS hSprime hSprime_pos hcurv
    have hRord : R a (Q a v) ≤ R a (Q a u) := by
      apply hRanti
      · simpa [Q] using hQu.1
      · simpa [Q] using hQv.1
      · exact hQuv.le

    rw [(hHderiv a ha).deriv]
    linarith

  have hHcont : ContinuousOn H (Set.Icc a₁ a₂) := by
    intro a ha
    exact (hHderiv a ha).continuousAt.continuousWithinAt

  have hHdiff : DifferentiableOn ℝ H (interior (Set.Icc a₁ a₂)) := by
    intro a haInt
    have ha : a ∈ Set.Icc a₁ a₂ := interior_subset haInt
    exact (hHderiv a ha).differentiableAt.differentiableWithinAt

  have hHmono : MonotoneOn H (Set.Icc a₁ a₂) :=
    monotoneOn_of_deriv_nonneg
      (convex_Icc a₁ a₂) hHcont hHdiff hHderiv_nonneg

  have hHineq : H a₁ ≤ H a₂ :=
    hHmono ⟨le_rfl, ha₁₂.le⟩ ⟨ha₁₂.le, le_rfl⟩ ha₁₂.le

  have hQ₁u := powerWeightedShiftQuantile_pos_and_CDF_eq_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a₁) (p := p) (u := u)
    ha₁.le hp hu.1 hu.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hQ₁v := powerWeightedShiftQuantile_pos_and_CDF_eq_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a₁) (p := p) (u := v)
    ha₁.le hp hv.1 hv.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have ha₂pos : 0 < a₂ := ha₁.trans ha₁₂
  have hQ₂u := powerWeightedShiftQuantile_pos_and_CDF_eq_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a₂) (p := p) (u := u)
    ha₂pos.le hp hu.1 hu.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hQ₂v := powerWeightedShiftQuantile_pos_and_CDF_eq_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a₂) (p := p) (u := v)
    ha₂pos.le hp hv.1 hv.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos

  have hlog :
      Real.log (Q a₂ u) - Real.log (Q a₁ u) ≤
        Real.log (Q a₂ v) - Real.log (Q a₁ v) := by
    dsimp [H] at hHineq
    linarith

  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_sub, Real.exp_sub,
      Real.exp_log (by simpa [Q] using hQ₂u.1),
      Real.exp_log (by simpa [Q] using hQ₁u.1),
      Real.exp_log (by simpa [Q] using hQ₂v.1),
      Real.exp_log (by simpa [Q] using hQ₁v.1)] at hexp
  simpa [Q] using hexp

end ScoreCurvatureStarOrder
