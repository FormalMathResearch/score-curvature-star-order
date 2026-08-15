import Mathlib
import ScoreCurvatureStarOrder.PowerMomentLogVariance
import ScoreCurvatureStarOrder.QuantileLogVarianceTransport
import ScoreCurvatureStarOrder.LogQuantileStarOrder
import ScoreCurvatureStarOrder.MonotoneCovariance

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- The logarithmic variance of the normalized power-weighted shifted density is
nonnegative.

The proof uses the already verified quantile representation.  On the uniform
unit interval the quantile-side variance is the self-covariance of
`log Q_{p,a}`; its nonnegativity follows from the monotone covariance theorem.
The global first- and second-log-moment transport then identifies this with the
spatial variance `powerWeightedShiftLogVariance`. -/
theorem powerWeightedShift_logVariance_nonneg_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    0 ≤ powerWeightedShiftLogVariance theta a p := by
  let f : ℝ → ℝ := fun u =>
    Real.log (powerWeightedShiftQuantile theta a p u)

  have hf : IntegrableOn f (Set.Ioo (0 : ℝ) 1) := by
    simpa [f] using
      (powerWeightedShift_logQuantile_integrableOn_Ioo_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)

  have hff :
      IntegrableOn (fun u : ℝ => f u * f u) (Set.Ioo (0 : ℝ) 1) := by
    have hsq :=
      powerWeightedShift_logQuantile_sq_integrableOn_Ioo_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [f, pow_two] using hsq

  have hfmono : MonotoneOn f (Set.Ioo (0 : ℝ) 1) := by
    simpa [f] using
      (powerWeightedShift_logQuantile_monotoneOn_Ioo_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)

  have hcov : 0 ≤ unitIntervalCovariance f f :=
    unitIntervalCovariance_nonneg_of_monotoneOn
      hf hf hff hfmono hfmono

  have hqvar :
      0 ≤ powerWeightedShiftLogQuantileVariance theta a p := by
    simpa [unitIntervalCovariance, powerWeightedShiftLogQuantileVariance,
      f, pow_two] using hcov

  have htransport :=
    powerWeightedShift_logQuantileVariance_eq_logVariance_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p)
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  rw [htransport] at hqvar
  exact hqvar

/-- Manuscript Theorem 5.3: for each nonnegative shift `a`, the power moment is
log-convex in the power parameter on `(-1,∞)`.

Equivalently, `p ↦ log M_p(a)` is convex on `(-1,∞)`.  The proof is the direct
second-derivative route from manuscript Lemma 5.2:

`∂ₚ² log M_p(a) = Var_{p,a}(log X) ≥ 0`.

No new differentiation under the integral sign occurs here; both derivatives
are the already verified Lemma 5.2 identities. -/
theorem powerWeightedShiftMoment_log_convexOn_power_within
    {theta S Sprime : ℝ → ℝ} {a : ℝ}
    (ha : 0 ≤ a)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ConvexOn ℝ (Set.Ioi (-1 : ℝ))
      (fun q : ℝ => Real.log (powerWeightedShiftMoment theta a q)) := by
  let F : ℝ → ℝ := fun q =>
    Real.log (powerWeightedShiftMoment theta a q)
  let D1 : ℝ → ℝ :=
    ((fun q : ℝ =>
        ∫ x : ℝ in Set.Ioi 0,
          x ^ q * Real.log x * theta (a + x)) /
      (fun q : ℝ => powerWeightedShiftMoment theta a q))
  let D2 : ℝ → ℝ := fun q => powerWeightedShiftLogVariance theta a q

  have hD : Convex ℝ (Set.Ioi (-1 : ℝ)) := convex_Ioi _

  have hFcont : ContinuousOn F (Set.Ioi (-1 : ℝ)) := by
    intro q hq
    have hderiv :=
      powerWeightedShiftMoment_log_hasDerivAt_power_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := q)
        ha hq htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [F] using hderiv.continuousAt.continuousWithinAt

  have hFderiv :
      ∀ q ∈ interior (Set.Ioi (-1 : ℝ)),
        HasDerivWithinAt F (D1 q) (interior (Set.Ioi (-1 : ℝ))) q := by
    intro q hq
    have hq' : -1 < q := by
      simpa only [Set.mem_Ioi] using (interior_subset hq)
    have hderiv :=
      powerWeightedShiftMoment_log_hasDerivAt_power_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := q)
        ha hq' htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [F, D1] using hderiv.hasDerivWithinAt

  have hD1deriv :
      ∀ q ∈ interior (Set.Ioi (-1 : ℝ)),
        HasDerivWithinAt D1 (D2 q) (interior (Set.Ioi (-1 : ℝ))) q := by
    intro q hq
    have hq' : -1 < q := by
      simpa only [Set.mem_Ioi] using (interior_subset hq)
    have hderiv :=
      powerWeightedShiftMoment_logDerivative_hasDerivAt_logVariance_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := q)
        ha hq' htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [D1, D2] using hderiv.hasDerivWithinAt

  have hD2nonneg :
      ∀ q ∈ interior (Set.Ioi (-1 : ℝ)), 0 ≤ D2 q := by
    intro q hq
    have hq' : -1 < q := by
      simpa only [Set.mem_Ioi] using (interior_subset hq)
    simpa [D2] using
      (powerWeightedShift_logVariance_nonneg_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := q)
        ha hq' htheta_pos htheta_deriv htheta_int hS hSprime_pos)

  have hconvex : ConvexOn ℝ (Set.Ioi (-1 : ℝ)) F :=
    convexOn_of_hasDerivWithinAt2_nonneg
      hD hFcont hFderiv hD1deriv hD2nonneg
  simpa [F] using hconvex

end ScoreCurvatureStarOrder
