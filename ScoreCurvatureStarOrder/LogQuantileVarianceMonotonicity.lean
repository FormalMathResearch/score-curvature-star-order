import Mathlib
import ScoreCurvatureStarOrder.MonotoneCovariance
import ScoreCurvatureStarOrder.QuantileLogVarianceTransport
import ScoreCurvatureStarOrder.LogQuantileStarOrder

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- Variance increases when a nondecreasing function is perturbed by a
nondecreasing increment on the unit probability interval.

This is the algebraic bridge used in manuscript Theorem 5.1.  Writing
`h = g - f`, the proof uses

`Var(g) - Var(f) = 2 Cov(f,h) + Var(h)`.

Both terms on the right are nonnegative by the already verified monotone
covariance theorem.  Square-integrability of `f` and `g` supplies the product
integrability needed for the covariance terms through the `L² × L² ⊆ L¹`
Holder estimate in mathlib. -/
theorem unitInterval_variance_le_of_monotoneOn_increment
    {f g : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Ioo (0 : ℝ) 1))
    (hg : IntegrableOn g (Set.Ioo (0 : ℝ) 1))
    (hfsq : IntegrableOn (fun u : ℝ => (f u) ^ 2) (Set.Ioo (0 : ℝ) 1))
    (hgsq : IntegrableOn (fun u : ℝ => (g u) ^ 2) (Set.Ioo (0 : ℝ) 1))
    (hfmono : MonotoneOn f (Set.Ioo (0 : ℝ) 1))
    (hincmono : MonotoneOn (fun u : ℝ => g u - f u) (Set.Ioo (0 : ℝ) 1)) :
    (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, (f u) ^ 2) -
        (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, f u) ^ 2 ≤
      (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, (g u) ^ 2) -
        (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, g u) ^ 2 := by
  let h : ℝ → ℝ := g - f

  have hh : IntegrableOn h (Set.Ioo (0 : ℝ) 1) := by
    simpa [h] using hg.sub hf

  have hfL2 :
      MemLp f 2 (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    exact (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hfsq
  have hgL2 :
      MemLp g 2 (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    exact (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hgsq
  have hhL2 :
      MemLp h 2 (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    simpa [h] using hgL2.sub hfL2

  have hfh :
      IntegrableOn (fun u : ℝ => f u * h u) (Set.Ioo (0 : ℝ) 1) := by
    have hprod :
        Integrable (f * h) (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
      hfL2.integrable_mul hhL2
    exact hprod.congr (Filter.Eventually.of_forall (fun u => rfl))
  have hhh :
      IntegrableOn (fun u : ℝ => h u * h u) (Set.Ioo (0 : ℝ) 1) := by
    change Integrable (fun u : ℝ => h u * h u)
      (volume.restrict (Set.Ioo (0 : ℝ) 1))
    simpa using hhL2.integrable_mul hhL2

  have hhmono : MonotoneOn h (Set.Ioo (0 : ℝ) 1) := by
    simpa [h] using hincmono

  have hcov : 0 ≤ unitIntervalCovariance f h :=
    unitIntervalCovariance_nonneg_of_monotoneOn
      hf hh hfh hfmono hhmono
  have hvarh : 0 ≤ unitIntervalCovariance h h :=
    unitIntervalCovariance_nonneg_of_monotoneOn
      hh hh hhh hhmono hhmono

  have hmean :
      (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, g u) =
        (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, f u) +
          ∫ u : ℝ in Set.Ioo (0 : ℝ) 1, h u := by
    calc
      (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, g u) =
          ∫ u : ℝ in Set.Ioo (0 : ℝ) 1, f u + h u := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun u => by simp [h])
      _ =
          (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, f u) +
            ∫ u : ℝ in Set.Ioo (0 : ℝ) 1, h u := by
        exact integral_add hf hh

  have hrest :
      IntegrableOn
        (fun u : ℝ => 2 * (f u * h u) + h u * h u)
        (Set.Ioo (0 : ℝ) 1) :=
    (hfh.const_mul (2 : ℝ)).add hhh
  have hsquare :
      (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, (g u) ^ 2) =
        (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, (f u) ^ 2) +
          (2 * (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, f u * h u) +
            ∫ u : ℝ in Set.Ioo (0 : ℝ) 1, h u * h u) := by
    calc
      (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, (g u) ^ 2) =
          ∫ u : ℝ in Set.Ioo (0 : ℝ) 1,
            (f u) ^ 2 + (2 * (f u * h u) + h u * h u) := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun u => by
          dsimp [h]
          ring)
      _ =
          (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, (f u) ^ 2) +
            ∫ u : ℝ in Set.Ioo (0 : ℝ) 1,
              2 * (f u * h u) + h u * h u := by
        exact integral_add hfsq hrest
      _ =
          (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, (f u) ^ 2) +
            ((∫ u : ℝ in Set.Ioo (0 : ℝ) 1, 2 * (f u * h u)) +
              ∫ u : ℝ in Set.Ioo (0 : ℝ) 1, h u * h u) := by
        apply congrArg
          (fun z : ℝ =>
            (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, (f u) ^ 2) + z)
        exact integral_add (hfh.const_mul (2 : ℝ)) hhh
      _ =
          (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, (f u) ^ 2) +
            (2 * (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, f u * h u) +
              ∫ u : ℝ in Set.Ioo (0 : ℝ) 1, h u * h u) := by
        rw [integral_const_mul]

  unfold unitIntervalCovariance at hcov hvarh
  rw [hmean, hsquare]
  nlinarith

/-- Quantile-side variance monotonicity for two ordered nonnegative shifts.

The proof follows the manuscript coupling exactly: `log Q_{a₁}` is
nondecreasing, the increment `log Q_{a₂} - log Q_{a₁}` is nondecreasing by the
full star order, and the global `L²` transport supplies all integrability
requirements. -/
theorem powerWeightedShift_logQuantileVariance_mono_within
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
    powerWeightedShiftLogQuantileVariance theta a₁ p ≤
      powerWeightedShiftLogQuantileVariance theta a₂ p := by
  have ha₂ : 0 ≤ a₂ := ha₁.trans ha₁₂.le

  have hlog₁ :=
    powerWeightedShift_logQuantile_integrableOn_Ioo_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a₁) (p := p)
      ha₁ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hlog₂ :=
    powerWeightedShift_logQuantile_integrableOn_Ioo_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a₂) (p := p)
      ha₂ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hsq₁ :=
    powerWeightedShift_logQuantile_sq_integrableOn_Ioo_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a₁) (p := p)
      ha₁ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hsq₂ :=
    powerWeightedShift_logQuantile_sq_integrableOn_Ioo_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a₂) (p := p)
      ha₂ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos

  have hmono₁ :=
    powerWeightedShift_logQuantile_monotoneOn_Ioo_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a₁) (p := p)
      ha₁ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hincmono :=
    powerWeightedShift_logQuantileIncrement_monotoneOn_Ioo_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (a₁ := a₁) (a₂ := a₂) (p := p)
      ha₁ ha₁₂ hp htheta_pos htheta_deriv htheta_int hS hSprime
      hSprime_pos hcurv

  unfold powerWeightedShiftLogQuantileVariance
  exact unitInterval_variance_le_of_monotoneOn_increment
    hlog₁ hlog₂ hsq₁ hsq₂ hmono₁ hincmono

/-- Manuscript Theorem 5.1: the variance of `log X` under the normalized
power-weighted shifted density is nondecreasing in the shift.

This theorem is obtained from the quantile-side monotone covariance argument
and the already verified global first- and second-log-moment transport.  In
particular, it does not use differentiation of the variance with respect to the
shift. -/
theorem powerWeightedShift_logVariance_mono_within
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
    powerWeightedShiftLogVariance theta a₁ p ≤
      powerWeightedShiftLogVariance theta a₂ p := by
  have ha₂ : 0 ≤ a₂ := ha₁.trans ha₁₂.le
  have hquantile :=
    powerWeightedShift_logQuantileVariance_mono_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (a₁ := a₁) (a₂ := a₂) (p := p)
      ha₁ ha₁₂ hp htheta_pos htheta_deriv htheta_int hS hSprime
      hSprime_pos hcurv
  have htransport₁ :=
    powerWeightedShift_logQuantileVariance_eq_logVariance_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a₁) (p := p)
      ha₁ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have htransport₂ :=
    powerWeightedShift_logQuantileVariance_eq_logVariance_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a₂) (p := p)
      ha₂ hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  rw [htransport₁, htransport₂] at hquantile
  exact hquantile

end ScoreCurvatureStarOrder
