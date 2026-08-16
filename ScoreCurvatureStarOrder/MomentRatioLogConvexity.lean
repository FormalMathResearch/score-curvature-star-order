import Mathlib
import ScoreCurvatureStarOrder.PowerMomentLogVariance
import ScoreCurvatureStarOrder.LogQuantileVarianceMonotonicity

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- **Manuscript Theorem 5.3 (two-shift log-convexity).**

For ordered nonnegative shifts `a₁ < a₂`, the two-shift normalization-moment
ratio is log-convex in the power parameter on `(-1,∞)`:

`q ↦ log (M_q(a₂) / M_q(a₁))`

is convex.  The proof follows the manuscript exactly.  Lemma 5.2 gives the
first and second power derivatives of each `log M_q(aᵢ)`, while manuscript
Theorem 5.1 gives

`Var_{q,a₁}(log X) ≤ Var_{q,a₂}(log X)`.

Hence the second derivative of
`log M_q(a₂) - log M_q(a₁)` is nonnegative.  Positivity of both normalization
moments identifies this difference with the logarithm of their ratio.  No new
differentiation under the integral sign occurs here. -/
theorem powerWeightedShift_momentRatio_log_convexOn_power_within
    {theta S Sprime Ssecond : ℝ → ℝ} {a₁ a₂ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₁₂ : a₁ < a₂)
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
    ConvexOn ℝ (Set.Ioi (-1 : ℝ))
      (fun q : ℝ =>
        Real.log
          (powerWeightedShiftMoment theta a₂ q /
            powerWeightedShiftMoment theta a₁ q)) := by
  have ha₂ : 0 ≤ a₂ := ha₁.trans ha₁₂.le

  let F : ℝ → ℝ := fun q =>
    Real.log (powerWeightedShiftMoment theta a₂ q) -
      Real.log (powerWeightedShiftMoment theta a₁ q)
  let E₂ : ℝ → ℝ :=
    ((fun q : ℝ =>
        ∫ x : ℝ in Set.Ioi 0,
          x ^ q * Real.log x * theta (a₂ + x)) /
      (fun q : ℝ => powerWeightedShiftMoment theta a₂ q))
  let E₁ : ℝ → ℝ :=
    ((fun q : ℝ =>
        ∫ x : ℝ in Set.Ioi 0,
          x ^ q * Real.log x * theta (a₁ + x)) /
      (fun q : ℝ => powerWeightedShiftMoment theta a₁ q))
  let D1 : ℝ → ℝ := E₂ - E₁
  let D2 : ℝ → ℝ := fun q =>
    powerWeightedShiftLogVariance theta a₂ q -
      powerWeightedShiftLogVariance theta a₁ q

  have hD : Convex ℝ (Set.Ioi (-1 : ℝ)) := convex_Ioi _

  have hFcont : ContinuousOn F (Set.Ioi (-1 : ℝ)) := by
    intro q hq
    have h₂ :=
      powerWeightedShiftMoment_log_hasDerivAt_power_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a₂) (p := q)
        ha₂ hq htheta_pos htheta_deriv htheta_int hS hSprime_pos
    have h₁ :=
      powerWeightedShiftMoment_log_hasDerivAt_power_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a₁) (p := q)
        ha₁ hq htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [F] using (h₂.sub h₁).continuousAt.continuousWithinAt

  have hFderiv :
      ∀ q ∈ interior (Set.Ioi (-1 : ℝ)),
        HasDerivWithinAt F (D1 q) (interior (Set.Ioi (-1 : ℝ))) q := by
    intro q hq
    have hq' : -1 < q := by
      simpa only [Set.mem_Ioi] using (interior_subset hq)
    have h₂ :=
      powerWeightedShiftMoment_log_hasDerivAt_power_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a₂) (p := q)
        ha₂ hq' htheta_pos htheta_deriv htheta_int hS hSprime_pos
    have h₁ :=
      powerWeightedShiftMoment_log_hasDerivAt_power_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a₁) (p := q)
        ha₁ hq' htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [F, D1, E₂, E₁] using (h₂.sub h₁).hasDerivWithinAt

  have hD1deriv :
      ∀ q ∈ interior (Set.Ioi (-1 : ℝ)),
        HasDerivWithinAt D1 (D2 q) (interior (Set.Ioi (-1 : ℝ))) q := by
    intro q hq
    have hq' : -1 < q := by
      simpa only [Set.mem_Ioi] using (interior_subset hq)
    have h₂ :=
      powerWeightedShiftMoment_logDerivative_hasDerivAt_logVariance_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a₂) (p := q)
        ha₂ hq' htheta_pos htheta_deriv htheta_int hS hSprime_pos
    have h₁ :=
      powerWeightedShiftMoment_logDerivative_hasDerivAt_logVariance_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a₁) (p := q)
        ha₁ hq' htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [D1, D2, E₂, E₁] using (h₂.sub h₁).hasDerivWithinAt

  have hD2nonneg :
      ∀ q ∈ interior (Set.Ioi (-1 : ℝ)), 0 ≤ D2 q := by
    intro q hq
    have hq' : -1 < q := by
      simpa only [Set.mem_Ioi] using (interior_subset hq)
    have hvarmono :=
      powerWeightedShift_logVariance_mono_within
        (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
        (a₁ := a₁) (a₂ := a₂) (p := q)
        ha₁ ha₁₂ hq' htheta_pos htheta_deriv htheta_int hS hSprime
        hSprime_pos hcurv
    simpa [D2, sub_nonneg] using hvarmono

  have hconvexF : ConvexOn ℝ (Set.Ioi (-1 : ℝ)) F :=
    convexOn_of_hasDerivWithinAt2_nonneg
      hD hFcont hFderiv hD1deriv hD2nonneg

  refine hconvexF.congr ?_
  intro q hq
  have hM₂pos : 0 < powerWeightedShiftMoment theta a₂ q :=
    powerWeightedShiftMoment_pos_within
      ha₂ hq htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hM₁pos : 0 < powerWeightedShiftMoment theta a₁ q :=
    powerWeightedShiftMoment_pos_within
      ha₁ hq htheta_pos htheta_deriv htheta_int hS hSprime_pos
  simpa [F] using (Real.log_div hM₂pos.ne' hM₁pos.ne').symm

end ScoreCurvatureStarOrder
