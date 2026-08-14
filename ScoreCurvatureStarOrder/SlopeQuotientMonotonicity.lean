import Mathlib
import ScoreCurvatureStarOrder.KernelExpectation

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- Under the score-curvature hypotheses, the derivative of the reduced slope
quotient is nonpositive at every strictly positive point where its denominator
is nonzero.  This combines the exact quotient derivative formula with the
verified nonnegativity of the scalar kernel `K_{p,a}`. -/
theorem powerWeightedShiftSlopeQuotient_deriv_nonpos_within
    {theta S Sprime Ssecond : ℝ → ℝ} {a p x : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p) (hx : 0 < x)
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
      Ssecond z * S z - (Sprime z) ^ 2 ≤ 0)
    (hden : p + 1 - x * S (a + x) ≠ 0) :
    deriv (fun y : ℝ => powerWeightedShiftSlopeQuotient theta S a p y) x ≤ 0 := by
  have hq := powerWeightedShiftSlopeQuotient_hasDerivAt_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p) (x := x) ha hx hS hden
  rw [hq.deriv]
  have hK : 0 ≤ powerWeightedShiftSlopeKernel theta S Sprime a p x :=
    powerWeightedShiftSlopeKernel_nonneg_within
      ha hp hx htheta_pos htheta_deriv htheta_int hS hSprime hSprime_pos hcurv
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hK) (sq_nonneg _)

/-- On every convex positive domain that contains no zero of
`p + 1 - x * S (a+x)`, the reduced slope quotient is antitone.

This is the rigorous interval form of the pointwise derivative-sign argument.
The pole-free hypothesis is imposed on the whole domain, so the theorem never
compares quotient values across a singularity.  Over `ℝ`, convex domains are
the interval domains relevant to the star-order proof. -/
theorem powerWeightedShiftSlopeQuotient_antitoneOn_convex_within
    {theta S Sprime Ssecond : ℝ → ℝ} {a p : ℝ} {D : Set ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (hD : Convex ℝ D)
    (hDpos : D ⊆ Set.Ioi (0 : ℝ))
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
      Ssecond z * S z - (Sprime z) ^ 2 ≤ 0)
    (hden : ∀ x ∈ D, p + 1 - x * S (a + x) ≠ 0) :
    AntitoneOn
      (fun x : ℝ => powerWeightedShiftSlopeQuotient theta S a p x) D := by
  let q : ℝ → ℝ := fun x => powerWeightedShiftSlopeQuotient theta S a p x
  have hqDeriv : ∀ x ∈ D,
      HasDerivAt q
        (-powerWeightedShiftSlopeKernel theta S Sprime a p x /
          (p + 1 - x * S (a + x)) ^ 2) x := by
    intro x hxD
    have hxpos : 0 < x := hDpos hxD
    simpa [q] using
      (powerWeightedShiftSlopeQuotient_hasDerivAt_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p) (x := x) ha hxpos hS (hden x hxD))
  have hqCont : ContinuousOn q D := by
    intro x hxD
    exact (hqDeriv x hxD).continuousAt.continuousWithinAt
  have hqDiff : DifferentiableOn ℝ q (interior D) := by
    intro x hxInt
    have hxD : x ∈ D := interior_subset hxInt
    exact (hqDeriv x hxD).differentiableAt.differentiableWithinAt
  apply antitoneOn_of_deriv_nonpos hD hqCont hqDiff
  intro x hxInt
  have hxD : x ∈ D := interior_subset hxInt
  have hxpos : 0 < x := hDpos hxD
  simpa [q] using
    (powerWeightedShiftSlopeQuotient_deriv_nonpos_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (a := a) (p := p) (x := x)
      ha hp hxpos htheta_pos htheta_deriv htheta_int hS hSprime hSprime_pos hcurv
      (hden x hxD))

end ScoreCurvatureStarOrder
