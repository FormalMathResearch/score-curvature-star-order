import Mathlib
import ScoreCurvatureStarOrder.Density

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- The mean score under the normalized power-weighted shifted density. -/
noncomputable def powerWeightedShiftScoreMean
    (theta S : ℝ → ℝ) (a p : ℝ) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0,
    S (a + t) * powerWeightedShiftDensity theta a p t

/-- The cumulative centered-score term that will be identified with the shift derivative
of the distribution function. -/
noncomputable def powerWeightedShiftCumulativeShiftNumerator
    (theta S : ℝ → ℝ) (a p x : ℝ) : ℝ :=
  ∫ t : ℝ in 0..x,
    powerWeightedShiftDensity theta a p t *
      (powerWeightedShiftScoreMean theta S a p - S (a + t))

/-- For `x > 0`, the cumulative centered-score term satisfies
`A'(x) = f_{p,a}(x) (G_{p,a} - S(a+x))`. -/
theorem powerWeightedShiftCumulativeShiftNumerator_hasDerivAt
    {theta S Sprime : ℝ → ℝ} {a p x : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p) (hx : 0 < x)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z) :
    HasDerivAt
      (fun y : ℝ => powerWeightedShiftCumulativeShiftNumerator theta S a p y)
      (powerWeightedShiftDensity theta a p x *
        (powerWeightedShiftScoreMean theta S a p - S (a + x))) x := by
  let G : ℝ := powerWeightedShiftScoreMean theta S a p
  let M : ℝ := powerWeightedShiftMoment theta a p
  let h : ℝ → ℝ := fun t =>
    powerWeightedShiftDensity theta a p t * (G - S (a + t))

  have hrpow_cont : ContinuousOn (fun t : ℝ => t ^ p) (Set.Ioi (0 : ℝ)) :=
    continuousOn_id.rpow_const (by
      intro t ht
      left
      exact ht.ne')
  have htheta_shift_cont :
      ContinuousOn (fun t : ℝ => theta (a + t)) (Set.Ioi (0 : ℝ)) := by
    intro t ht
    have hat0 : 0 ≤ a + t := add_nonneg ha ht.le
    have hshift : ContinuousAt (fun y : ℝ => a + y) t := by fun_prop
    exact ((htheta_deriv (a + t) hat0).continuousAt.comp hshift).continuousWithinAt
  have hS_shift_cont :
      ContinuousOn (fun t : ℝ => S (a + t)) (Set.Ioi (0 : ℝ)) := by
    intro t ht
    have hat0 : 0 ≤ a + t := add_nonneg ha ht.le
    have hshift : ContinuousAt (fun y : ℝ => a + y) t := by fun_prop
    exact ((hS (a + t) hat0).continuousAt.comp hshift).continuousWithinAt
  have hdensity_cont :
      ContinuousOn (fun t : ℝ => powerWeightedShiftDensity theta a p t) (Set.Ioi (0 : ℝ)) := by
    have hraw := (hrpow_cont.mul htheta_shift_cont).mul
      (continuousOn_const : ContinuousOn (fun _ : ℝ => M⁻¹) (Set.Ioi (0 : ℝ)))
    simpa [powerWeightedShiftDensity, M, div_eq_mul_inv, mul_assoc] using hraw
  have hcont : ContinuousOn h (Set.Ioi (0 : ℝ)) := by
    dsimp [h]
    exact hdensity_cont.mul
      ((continuousOn_const : ContinuousOn (fun _ : ℝ => G) (Set.Ioi (0 : ℝ))).sub
        hS_shift_cont)
  have hcontAt : ContinuousAt h x :=
    hcont.continuousAt (Set.Ioi_mem_nhds hx)
  have hmeas : StronglyMeasurableAtFilter h (𝓝 x) :=
    (hcont.aestronglyMeasurable measurableSet_Ioi).stronglyMeasurableAtFilter_of_mem
      (Set.Ioi_mem_nhds hx)

  have htheta_shift_uIcc :
      ContinuousOn (fun t : ℝ => theta (a + t)) [[0, x]] := by
    intro t ht
    rw [uIcc_of_le hx.le] at ht
    have hat0 : 0 ≤ a + t := add_nonneg ha ht.1
    have hshift : ContinuousAt (fun y : ℝ => a + y) t := by fun_prop
    exact ((htheta_deriv (a + t) hat0).continuousAt.comp hshift).continuousWithinAt
  have hS_shift_uIcc :
      ContinuousOn (fun t : ℝ => S (a + t)) [[0, x]] := by
    intro t ht
    rw [uIcc_of_le hx.le] at ht
    have hat0 : 0 ≤ a + t := add_nonneg ha ht.1
    have hshift : ContinuousAt (fun y : ℝ => a + y) t := by fun_prop
    exact ((hS (a + t) hat0).continuousAt.comp hshift).continuousWithinAt
  have hcoeff_cont :
      ContinuousOn
        (fun t : ℝ => theta (a + t) * M⁻¹ * (G - S (a + t))) [[0, x]] :=
    (htheta_shift_uIcc.mul
      (continuousOn_const : ContinuousOn (fun _ : ℝ => M⁻¹) [[0, x]])).mul
      ((continuousOn_const : ContinuousOn (fun _ : ℝ => G) [[0, x]]).sub hS_shift_uIcc)
  have hint_raw :
      IntervalIntegrable
        (fun t : ℝ => t ^ p * (theta (a + t) * M⁻¹ * (G - S (a + t))))
        volume 0 x :=
    (intervalIntegral.intervalIntegrable_rpow' hp).mul_continuousOn hcoeff_cont
  have hint : IntervalIntegrable h volume 0 x := by
    simpa [h, G, M, powerWeightedShiftDensity, div_eq_mul_inv, mul_assoc] using hint_raw

  have hftc := intervalIntegral.integral_hasDerivAt_right hint hmeas hcontAt
  simpa [powerWeightedShiftCumulativeShiftNumerator, h, G] using hftc

end ScoreCurvatureStarOrder
