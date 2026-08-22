import Mathlib
import ScoreCurvatureStarOrder.QuantileRatioBoundaryMonotonicity

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- The logarithm of the canonical quantile is nondecreasing on `(0,1)`.
This is the first monotonicity input in the quantile-coupling proof of
manuscript Theorem 5.1. -/
theorem powerWeightedShift_logQuantile_monotoneOn_Ioo_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    MonotoneOn
      (fun u : ℝ => Real.log (powerWeightedShiftQuantile theta a p u))
      (Set.Ioo (0 : ℝ) 1) := by
  intro u hu v hv huv
  rcases huv.eq_or_lt with huv_eq | huv_lt
  · subst v
    exact le_rfl
  · have hQstrict := powerWeightedShiftQuantile_strictMonoOn_Ioo_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p)
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
    have hQu := powerWeightedShiftQuantile_pos_and_CDF_eq_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (u := u)
      ha hp hu.1 hu.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos
    exact (Real.log_lt_log hQu.1 (hQstrict hu hv huv_lt)).le

/-- For two ordered nonnegative shifts, the logarithmic quantile increment
`log Q_{p,a₂}(u) - log Q_{p,a₁}(u)` is nondecreasing on `(0,1)`.

This is exactly the second monotonicity input in manuscript Theorem 5.1.  It is
a direct logarithmic reformulation of the already verified full star-order
quantile-ratio theorem, including the boundary case `a₁ = 0`. -/
theorem powerWeightedShift_logQuantileIncrement_monotoneOn_Ioo_within
    {theta S Sprime Ssecond : ℝ → ℝ} {a₁ a₂ p : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₁₂ : a₁ < a₂) (hp : -1 < p)
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
        Real.log (powerWeightedShiftQuantile theta a₂ p u) -
          Real.log (powerWeightedShiftQuantile theta a₁ p u))
      (Set.Ioo (0 : ℝ) 1) := by
  have ha₂ : 0 ≤ a₂ := ha₁.trans ha₁₂.le
  have hratio := powerWeightedShift_quantileRatio_monotoneOn_Ioo_within
    (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
    (a₁ := a₁) (a₂ := a₂) (p := p)
    ha₁ ha₁₂ hp htheta_pos htheta_deriv htheta_int hS hSprime
    hSprime_pos hcurv
  intro u hu v hv huv
  have hratio_le := hratio hu hv huv
  have hQ1u := powerWeightedShiftQuantile_pos_and_CDF_eq_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a₁) (p := p) (u := u)
    ha₁ hp hu.1 hu.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hQ2u := powerWeightedShiftQuantile_pos_and_CDF_eq_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a₂) (p := p) (u := u)
    ha₂ hp hu.1 hu.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hQ1v := powerWeightedShiftQuantile_pos_and_CDF_eq_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a₁) (p := p) (u := v)
    ha₁ hp hv.1 hv.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hQ2v := powerWeightedShiftQuantile_pos_and_CDF_eq_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a₂) (p := p) (u := v)
    ha₂ hp hv.1 hv.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hlog :
      Real.log
          (powerWeightedShiftQuantile theta a₂ p u /
            powerWeightedShiftQuantile theta a₁ p u) ≤
        Real.log
          (powerWeightedShiftQuantile theta a₂ p v /
            powerWeightedShiftQuantile theta a₁ p v) :=
    Real.log_le_log (div_pos hQ2u.1 hQ1u.1) hratio_le
  rw [Real.log_div hQ2u.1.ne' hQ1u.1.ne',
      Real.log_div hQ2v.1.ne' hQ1v.1.ne'] at hlog
  exact hlog

end ScoreCurvatureStarOrder
