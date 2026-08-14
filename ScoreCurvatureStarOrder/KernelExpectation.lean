import Mathlib
import ScoreCurvatureStarOrder.GlobalKernelWithin
import ScoreCurvatureStarOrder.Expectation
import ScoreCurvatureStarOrder.ScoreMeanIntegrability
import ScoreCurvatureStarOrder.SlopeQuotient

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- The two-point kernel multiplied by the normalized shifted density is
absolutely integrable.  The proof is an explicit decomposition into the three
already verified observables `X*S`, `S`, and `1`. -/
theorem powerWeightedShift_twoPointKernel_integrableOn_Ioi_within
    {theta S Sprime Ssecond : ℝ → ℝ} {a p x : ℝ}
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
    IntegrableOn
      (fun t : ℝ => twoPointKernel S Sprime a x t *
        powerWeightedShiftDensity theta a p t)
      (Set.Ioi (0 : ℝ)) := by
  have hXS :
      IntegrableOn
        (fun t : ℝ => (t * S (a + t)) * powerWeightedShiftDensity theta a p t)
        (Set.Ioi (0 : ℝ)) :=
    powerWeightedShift_score_expectation_integrableOn_Ioi_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hSmean :
      IntegrableOn
        (fun t : ℝ => S (a + t) * powerWeightedShiftDensity theta a p t)
        (Set.Ioi (0 : ℝ)) :=
    powerWeightedShift_score_mean_integrableOn_Ioi_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime hSprime_pos hcurv
  have hf :
      IntegrableOn (powerWeightedShiftDensity theta a p) (Set.Ioi (0 : ℝ)) :=
    powerWeightedShiftDensity_integrableOn_Ioi_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have h1 := hXS.const_mul (Sprime (a + x))
  have h2 := hSmean.const_mul (Sprime (a + x) * x)
  have h3 := hSmean.const_mul (S (a + x))
  have h4 := hf.const_mul (S (a + x) ^ 2)
  have hlin := ((h1.sub h2).sub h3).add h4
  refine IntegrableOn.congr_fun hlin ?_ measurableSet_Ioi
  intro t ht
  unfold twoPointKernel
  ring

/-- Exact expectation representation of the scalar slope kernel:

`K_{p,a}(x) = ∫ K_a(x,t) f_{p,a}(t) dt`.

Every use of linearity is backed by the explicit integrability theorem above. -/
theorem powerWeightedShiftSlopeKernel_eq_integral_twoPointKernel_within
    {theta S Sprime Ssecond : ℝ → ℝ} {a p x : ℝ}
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
    powerWeightedShiftSlopeKernel theta S Sprime a p x =
      ∫ t : ℝ in Set.Ioi 0,
        twoPointKernel S Sprime a x t * powerWeightedShiftDensity theta a p t := by
  have hXS :
      IntegrableOn
        (fun t : ℝ => (t * S (a + t)) * powerWeightedShiftDensity theta a p t)
        (Set.Ioi (0 : ℝ)) :=
    powerWeightedShift_score_expectation_integrableOn_Ioi_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hSmean :
      IntegrableOn
        (fun t : ℝ => S (a + t) * powerWeightedShiftDensity theta a p t)
        (Set.Ioi (0 : ℝ)) :=
    powerWeightedShift_score_mean_integrableOn_Ioi_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime hSprime_pos hcurv
  have hf :
      IntegrableOn (powerWeightedShiftDensity theta a p) (Set.Ioi (0 : ℝ)) :=
    powerWeightedShiftDensity_integrableOn_Ioi_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have h1 := hXS.const_mul (Sprime (a + x))
  have h2 := hSmean.const_mul (Sprime (a + x) * x)
  have h3 := hSmean.const_mul (S (a + x))
  have h4 := hf.const_mul (S (a + x) ^ 2)
  have h12 := h1.sub h2
  have h123 := h12.sub h3
  have hlin := h123.add h4
  have hXS_id := powerWeightedShift_score_expectation_identity_within
    (theta := theta) (S := S) (Sprime := Sprime) (a := a) (p := p)
    ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hf_id := powerWeightedShiftDensity_integral_eq_one_within
    (theta := theta) (S := S) (Sprime := Sprime) (a := a) (p := p)
    ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hkernel :
      (∫ t : ℝ in Set.Ioi 0,
          twoPointKernel S Sprime a x t * powerWeightedShiftDensity theta a p t) =
        ∫ t : ℝ in Set.Ioi 0,
          (Sprime (a + x) *
              ((t * S (a + t)) * powerWeightedShiftDensity theta a p t) -
            (Sprime (a + x) * x) *
              (S (a + t) * powerWeightedShiftDensity theta a p t) -
            S (a + x) *
              (S (a + t) * powerWeightedShiftDensity theta a p t) +
            S (a + x) ^ 2 * powerWeightedShiftDensity theta a p t) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    unfold twoPointKernel
    ring
  rw [hkernel]
  rw [integral_add h123 h4, integral_sub h12 h3, integral_sub h1 h2]
  simp only [integral_const_mul]
  rw [hXS_id, hf_id]
  change powerWeightedShiftSlopeKernel theta S Sprime a p x =
    Sprime (a + x) * (p + 1) -
      (Sprime (a + x) * x) * powerWeightedShiftScoreMean theta S a p -
      S (a + x) * powerWeightedShiftScoreMean theta S a p +
      S (a + x) ^ 2 * 1
  unfold powerWeightedShiftSlopeKernel
  ring

/-- Under score curvature, the scalar slope kernel is nonnegative at every
strictly positive radial point.  This is obtained by integrating the globally
nonnegative two-point kernel against the positive normalized density. -/
theorem powerWeightedShiftSlopeKernel_nonneg_within
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
      Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    0 ≤ powerWeightedShiftSlopeKernel theta S Sprime a p x := by
  rw [powerWeightedShiftSlopeKernel_eq_integral_twoPointKernel_within
    ha hp htheta_pos htheta_deriv htheta_int hS hSprime hSprime_pos hcurv]
  have hMpos : 0 < powerWeightedShiftMoment theta a p :=
    powerWeightedShiftMoment_pos_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hkernel : 0 ≤ twoPointKernel S Sprime a x t :=
    twoPointKernel_nonneg_of_pos_within
      ha hx ht hS hSprime hSprime_pos hcurv
  have hat0 : 0 ≤ a + t := add_nonneg ha ht.le
  have hdensity : 0 < powerWeightedShiftDensity theta a p t := by
    dsimp [powerWeightedShiftDensity]
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos ht p) (htheta_pos (a + t) hat0)) hMpos
  exact mul_nonneg hkernel hdensity.le

end ScoreCurvatureStarOrder
