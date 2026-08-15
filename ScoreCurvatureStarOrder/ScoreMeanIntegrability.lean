import Mathlib
import ScoreCurvatureStarOrder.LocalShiftMajorant
import ScoreCurvatureStarOrder.Density

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- The score itself is absolutely integrable under every normalized
power-weighted shifted density under the mathematically natural one-sided
regularity assumptions on `[0, ∞)`.  This is the integrability needed to treat
`G_{p,a}` as a genuine expectation and to linearize the kernel expectation. -/
theorem powerWeightedShift_score_mean_integrableOn_Ioi_within
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
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ), Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    IntegrableOn
      (fun x : ℝ => S (a + x) * powerWeightedShiftDensity theta a p x)
      (Set.Ioi (0 : ℝ)) := by
  rcases exists_shifted_thetaDeriv_tail_majorant_within
      htheta_pos htheta_deriv htheta_int hS hSprime hSprime_pos hcurv with
    ⟨T₀, hT₀, htail⟩
  let B : ℝ := max T₀ 1
  have hT₀B : T₀ ≤ B := by
    dsimp [B]
    exact le_max_left _ _
  have h1B : 1 ≤ B := by
    dsimp [B]
    exact le_max_right _ _
  have hB0 : 0 ≤ B := zero_le_one.trans h1B
  have hS_shift_Ici : ContinuousOn (fun x : ℝ => S (a + x)) (Set.Ici (0 : ℝ)) :=
    continuousOn_shift_Ici_of_hasDerivWithinAt ha hS
  have htheta_shift_Ici : ContinuousOn (fun x : ℝ => theta (a + x)) (Set.Ici (0 : ℝ)) :=
    continuousOn_shift_Ici_of_hasDerivWithinAt ha htheta_deriv

  have hraw :
      IntegrableOn
        (fun x : ℝ => x ^ p * (-S (a + x) * theta (a + x)))
        (Set.Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi hB0, integrableOn_union]
    constructor
    · rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hB0]
      have hIcc_sub : [[0, B]] ⊆ Set.Ici (0 : ℝ) := by
        intro x hx
        rw [uIcc_of_le hB0] at hx
        exact hx.1
      have hS_shift_cont : ContinuousOn (fun x : ℝ => S (a + x)) [[0, B]] :=
        hS_shift_Ici.mono hIcc_sub
      have htheta_shift_cont :
          ContinuousOn (fun x : ℝ => theta (a + x)) [[0, B]] :=
        htheta_shift_Ici.mono hIcc_sub
      have hscore_cont :
          ContinuousOn (fun x : ℝ => -S (a + x) * theta (a + x)) [[0, B]] :=
        hS_shift_cont.neg.mul htheta_shift_cont
      exact (intervalIntegral.intervalIntegrable_rpow' hp).mul_continuousOn hscore_cont
    · have hscore0 :
          IntegrableOn (fun x : ℝ => x ^ p * S x * theta x) (Set.Ioi (0 : ℝ)) :=
        powerWeightedUnshifted_score_integrableOn_Ioi_within
          hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
      have hscoreB :
          IntegrableOn (fun x : ℝ => x ^ p * S x * theta x) (Set.Ioi B) :=
        hscore0.mono_set (fun x hx => hB0.trans_lt hx)
      have hrpow_cont : ContinuousOn (fun x : ℝ => x ^ p) (Set.Ioi B) :=
        continuousOn_id.rpow_const (by
          intro x hx
          left
          exact (zero_lt_one.trans_le (h1B.trans hx.le)).ne')
      have hIoi_sub : Set.Ioi B ⊆ Set.Ici (0 : ℝ) := by
        intro x hx
        exact (hB0.trans hx.le)
      have hshift_score_cont :
          ContinuousOn (fun x : ℝ => -S (a + x) * theta (a + x)) (Set.Ioi B) :=
        (hS_shift_Ici.mono hIoi_sub).neg.mul (htheta_shift_Ici.mono hIoi_sub)
      have hraw_cont :
          ContinuousOn
            (fun x : ℝ => x ^ p * (-S (a + x) * theta (a + x))) (Set.Ioi B) :=
        hrpow_cont.mul hshift_score_cont
      change Integrable
        (fun x : ℝ => x ^ p * (-S (a + x) * theta (a + x)))
        (volume.restrict (Set.Ioi B))
      refine hscoreB.integrable.mono (hraw_cont.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 ≤ x := hB0.trans hx.le
      have hpow0 : 0 ≤ x ^ p := Real.rpow_nonneg hx0 p
      have hT₀x : T₀ ≤ x := hT₀B.trans hx.le
      have htail' := htail a x ha hT₀x
      have hscore_nonneg : 0 ≤ S x * theta x :=
        (abs_nonneg (-S (a + x) * theta (a + x))).trans htail'
      have hweighted_nonneg : 0 ≤ x ^ p * S x * theta x := by
        nlinarith [hpow0, hscore_nonneg]
      calc
        ‖x ^ p * (-S (a + x) * theta (a + x))‖ =
            x ^ p * |(-S (a + x) * theta (a + x))| := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hpow0, Real.norm_eq_abs]
        _ ≤ x ^ p * (S x * theta x) :=
          mul_le_mul_of_nonneg_left htail' hpow0
        _ = ‖x ^ p * S x * theta x‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hweighted_nonneg]
          ring_nf

  have hscore_raw :
      IntegrableOn
        (fun x : ℝ => x ^ p * S (a + x) * theta (a + x))
        (Set.Ioi (0 : ℝ)) := by
    refine IntegrableOn.congr_fun hraw.neg ?_ measurableSet_Ioi
    intro x hx
    change -(x ^ p * (-S (a + x) * theta (a + x))) =
      x ^ p * S (a + x) * theta (a + x)
    ring
  have hscaled := hscore_raw.const_mul (powerWeightedShiftMoment theta a p)⁻¹
  refine IntegrableOn.congr_fun hscaled ?_ measurableSet_Ioi
  intro x hx
  dsimp [powerWeightedShiftDensity]
  rw [div_eq_mul_inv]
  ring

/-- Backward-compatible wrapper for the former two-sided assumptions. -/
theorem powerWeightedShift_score_mean_integrableOn_Ioi
    {theta S Sprime Ssecond : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt Sprime (Ssecond z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ), Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    IntegrableOn
      (fun x : ℝ => S (a + x) * powerWeightedShiftDensity theta a p x)
      (Set.Ioi (0 : ℝ)) := by
  exact powerWeightedShift_score_mean_integrableOn_Ioi_within ha hp htheta_pos
    (fun z hz => (htheta_deriv z hz).hasDerivWithinAt)
    htheta_int
    (fun z hz => (hS z hz).hasDerivWithinAt)
    (fun z hz => (hSprime z hz).hasDerivWithinAt)
    hSprime_pos hcurv

end ScoreCurvatureStarOrder
