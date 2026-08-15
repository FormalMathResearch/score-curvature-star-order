import Mathlib
import Mathlib.Analysis.MellinTransform
import ScoreCurvatureStarOrder.Tail
import ScoreCurvatureStarOrder.HalfLineRegularity

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter Asymptotics
open scoped Topology

/-- A nonnegative shift of the kernel is locally integrable on the open positive
half-line.  This is only a continuity statement; no global moment estimate is
used here. -/
theorem shiftedTheta_locallyIntegrableOn_Ioi_within
    {theta S : ℝ → ℝ} {a : ℝ}
    (ha : 0 ≤ a)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z) :
    LocallyIntegrableOn (fun x : ℝ => theta (a + x)) (Set.Ioi (0 : ℝ)) := by
  have hcontIci : ContinuousOn (fun x : ℝ => theta (a + x)) (Set.Ici (0 : ℝ)) :=
    continuousOn_shift_Ici_of_hasDerivWithinAt ha htheta_deriv
  exact (hcontIci.mono (fun x hx => hx.le)).locallyIntegrableOn

/-- Near the spatial origin, every nonnegative shift of `theta` is `O(1)`.
This is the precise lower-end asymptotic input needed by the Mellin-transform
power-differentiation machinery. -/
theorem shiftedTheta_isBigO_one_nhdsGT_zero_within
    {theta S : ℝ → ℝ} {a : ℝ}
    (ha : 0 ≤ a)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z) :
    (fun x : ℝ => theta (a + x)) =O[𝓝[>] (0 : ℝ)] (fun _x : ℝ => (1 : ℝ)) := by
  have hcontIci : ContinuousOn (fun x : ℝ => theta (a + x)) (Set.Ici (0 : ℝ)) :=
    continuousOn_shift_Ici_of_hasDerivWithinAt ha htheta_deriv
  have hcontCompact : ContinuousOn (fun x : ℝ => theta (a + x)) (Set.Icc (0 : ℝ) 1) :=
    hcontIci.mono (by
      intro x hx
      exact hx.1)
  rcases isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.mpr (show (0 : ℝ) ≤ 1 by norm_num)) hcontCompact with
    ⟨xmax, hxmax, hxmaximal⟩
  let C : ℝ := theta (a + xmax)
  have hCpos : 0 < C := by
    dsimp [C]
    exact htheta_pos (a + xmax) (add_nonneg ha hxmax.1)
  rw [isBigO_iff]
  refine ⟨C, ?_⟩
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx1 hx0
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx0.le, hx1.le⟩
  have hle : theta (a + x) ≤ C := by
    dsimp [C]
    exact hxmaximal hxIcc
  have hpos : 0 < theta (a + x) :=
    htheta_pos (a + x) (add_nonneg ha hx0.le)
  simpa [Real.norm_eq_abs, abs_of_pos hpos, abs_of_pos hCpos] using hle

/-- The shifted kernel is exponentially bounded at `+∞`, uniformly for one
fixed nonnegative shift. -/
theorem shiftedTheta_isBigO_exp_atTop_within
    {theta S Sprime : ℝ → ℝ} {a : ℝ}
    (ha : 0 ≤ a)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℝ => theta (a + x)) =O[atTop]
        (fun x : ℝ => Real.exp (-c * x)) := by
  rcases automatic_positive_score_and_exponential_tail_within
      htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨R, c, hR, hc, _hS_lower, htail⟩
  let K : ℝ := theta R * Real.exp (c * R)
  have hKpos : 0 < K := by
    dsimp [K]
    exact mul_pos (htheta_pos R hR) (Real.exp_pos _)
  refine ⟨c, hc, ?_⟩
  rw [isBigO_iff]
  refine ⟨K, ?_⟩
  filter_upwards [eventually_ge_atTop R] with x hxR
  have hx0 : 0 ≤ x := hR.trans hxR
  have hax0 : 0 ≤ a + x := add_nonneg ha hx0
  have haxR : R ≤ a + x := by linarith
  have htheta_tail :
      theta (a + x) ≤ theta R * Real.exp (-c * ((a + x) - R)) :=
    htail (a + x) haxR
  have hexp_le :
      Real.exp (-c * ((a + x) - R)) ≤
        Real.exp (c * R) * Real.exp (-c * x) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hca : 0 ≤ c * a := mul_nonneg hc.le ha
    nlinarith
  have hbound : theta (a + x) ≤ K * Real.exp (-c * x) := by
    dsimp [K]
    calc
      theta (a + x) ≤ theta R * Real.exp (-c * ((a + x) - R)) := htheta_tail
      _ ≤ theta R * (Real.exp (c * R) * Real.exp (-c * x)) :=
        mul_le_mul_of_nonneg_left hexp_le (htheta_pos R hR).le
      _ = (theta R * Real.exp (c * R)) * Real.exp (-c * x) := by ring
  have htheta_posx : 0 < theta (a + x) := htheta_pos (a + x) hax0
  have hexppos : 0 < Real.exp (-c * x) := Real.exp_pos _
  simpa [Real.norm_eq_abs, abs_of_pos htheta_posx, abs_of_pos hexppos,
    abs_of_pos hKpos] using hbound

/-- Exponential decay implies decay faster than every reciprocal real power.
This is the upper-end Mellin asymptotic interface. -/
theorem shiftedTheta_isBigO_rpow_atTop_within
    {theta S Sprime : ℝ → ℝ} {a A : ℝ}
    (ha : 0 ≤ a)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    (fun x : ℝ => theta (a + x)) =O[atTop] (fun x : ℝ => x ^ (-A)) := by
  rcases shiftedTheta_isBigO_exp_atTop_within
      ha htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨c, hc, hOexp⟩
  exact hOexp.trans (isLittleO_exp_neg_mul_rpow_atTop hc A).isBigO

end ScoreCurvatureStarOrder
