import Mathlib
import ScoreCurvatureStarOrder.Moments
import ScoreCurvatureStarOrder.CompactParameterMajorants
import ScoreCurvatureStarOrder.HalfLineRegularity

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Topology

/-- Joint continuity of the normalization moment in the power and shift
parameters, including the one-sided shift boundary `a = 0`.

The parameter order is `(p,a)`, matching the manuscript notation `M_p(a)`.
For a fixed admissible point `(p,a)`, choose a compact parameter rectangle
strictly inside `p > -1` and with nonnegative shifts.  The verified compact
parameter majorant dominates the integrand throughout a neighborhood of the
point, while pointwise continuity follows from continuity of the real power in
its exponent and the interior continuity of `theta` at `a+x > 0` for `x > 0`.
Dominated convergence then yields continuity within
`(-1,∞) × [0,∞)`. -/
theorem powerWeightedShiftMoment_continuousWithinAt_parameters_within
    {theta S Sprime : ℝ → ℝ} {p a : ℝ}
    (hp : -1 < p) (ha : 0 ≤ a)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ContinuousWithinAt
      (fun q : ℝ × ℝ => powerWeightedShiftMoment theta q.2 q.1)
      (Set.Ioi (-1 : ℝ) ×ˢ Set.Ici (0 : ℝ)) (p, a) := by
  let p₀ : ℝ := (p - 1) / 2
  let p₁ : ℝ := p + 1
  let A : ℝ := a + 1
  have hp₀ : -1 < p₀ := by
    dsimp [p₀]
    linarith
  have hp₀p : p₀ < p := by
    dsimp [p₀]
    linarith
  have hpp₁ : p < p₁ := by
    dsimp [p₁]
    linarith
  have hp₀₁ : p₀ ≤ p₁ := hp₀p.le.trans hpp₁.le
  have hA : 0 ≤ A := by
    dsimp [A]
    linarith
  have haA : a < A := by
    dsimp [A]
    linarith

  rcases exists_powerWeightedShift_compact_majorant_within
      (theta := theta) (S := S) (Sprime := Sprime)
      hp₀ hp₀₁ hA htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨bound, hbound_int, hbound⟩

  let parameterSet : Set (ℝ × ℝ) :=
    Set.Ioi (-1 : ℝ) ×ˢ Set.Ici (0 : ℝ)

  have hparam_event :
      ∀ᶠ q : ℝ × ℝ in 𝓝[parameterSet] (p, a),
        q.1 ∈ Set.Icc p₀ p₁ ∧ q.2 ∈ Set.Icc (0 : ℝ) A := by
    have hp_lower :
        ∀ᶠ q : ℝ × ℝ in 𝓝[parameterSet] (p, a), p₀ < q.1 := by
      exact mem_nhdsWithin_of_mem_nhds
        ((isOpen_lt continuous_const continuous_fst).mem_nhds hp₀p)
    have hp_upper :
        ∀ᶠ q : ℝ × ℝ in 𝓝[parameterSet] (p, a), q.1 < p₁ := by
      exact mem_nhdsWithin_of_mem_nhds
        ((isOpen_lt continuous_fst continuous_const).mem_nhds hpp₁)
    have ha_upper :
        ∀ᶠ q : ℝ × ℝ in 𝓝[parameterSet] (p, a), q.2 < A := by
      exact mem_nhdsWithin_of_mem_nhds
        ((isOpen_lt continuous_snd continuous_const).mem_nhds haA)
    filter_upwards [eventually_mem_nhdsWithin, hp_lower, hp_upper, ha_upper] with
      q hq hq_lower hq_upper hqa_upper
    exact ⟨⟨hq_lower.le, hq_upper.le⟩, ⟨hq.2, hqa_upper.le⟩⟩

  have hF_meas :
      ∀ᶠ q : ℝ × ℝ in 𝓝[parameterSet] (p, a),
        AEStronglyMeasurable
          (fun x : ℝ => x ^ q.1 * theta (q.2 + x))
          (volume.restrict (Set.Ioi (0 : ℝ))) := by
    filter_upwards [eventually_mem_nhdsWithin] with q hq
    have hint := powerWeightedShift_integrableOn_Ioi_within
      (theta := theta) (S := S) (Sprime := Sprime)
      hq.2 hq.1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
    exact hint.aestronglyMeasurable

  have h_bound :
      ∀ᶠ q : ℝ × ℝ in 𝓝[parameterSet] (p, a),
        ∀ᵐ x : ℝ ∂(volume.restrict (Set.Ioi (0 : ℝ))),
          ‖x ^ q.1 * theta (q.2 + x)‖ ≤ bound x := by
    filter_upwards [hparam_event] with q hq
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hbound q.1 hq.1 q.2 hq.2 x hx

  have h_cont :
      ∀ᵐ x : ℝ ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ContinuousWithinAt
          (fun q : ℝ × ℝ => x ^ q.1 * theta (q.2 + x))
          parameterSet (p, a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := hx
    have hpow : ContinuousAt (fun q : ℝ × ℝ => x ^ q.1) (p, a) := by
      exact (Real.continuous_const_rpow hxpos.ne').continuousAt.comp
        continuous_fst.continuousAt
    have haxpos : 0 < a + x := by linarith
    have htheta_at : ContinuousAt theta (a + x) :=
      (hasDerivAt_of_pos_of_hasDerivWithinAt_Ici haxpos
        (htheta_deriv (a + x) haxpos.le)).continuousAt
    have hshift : ContinuousAt (fun q : ℝ × ℝ => theta (q.2 + x)) (p, a) := by
      have harg : ContinuousAt (fun q : ℝ × ℝ => q.2 + x) (p, a) := by
        fun_prop
      exact htheta_at.comp (p, a) harg
    exact (hpow.mul hshift).continuousWithinAt

  have hDCT := MeasureTheory.continuousWithinAt_of_dominated
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun q : ℝ × ℝ => fun x : ℝ => x ^ q.1 * theta (q.2 + x))
    (x₀ := (p, a)) (s := parameterSet) (bound := bound)
    hF_meas h_bound hbound_int h_cont

  simpa [parameterSet, powerWeightedShiftMoment] using hDCT

/-- The manuscript's joint continuity statement for the normalization moment:
`(p,a) ↦ M_p(a)` is continuous on `(-1,∞) × [0,∞)`. -/
theorem powerWeightedShiftMoment_continuousOn_parameters_within
    {theta S Sprime : ℝ → ℝ}
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ContinuousOn
      (fun q : ℝ × ℝ => powerWeightedShiftMoment theta q.2 q.1)
      (Set.Ioi (-1 : ℝ) ×ˢ Set.Ici (0 : ℝ)) := by
  intro q hq
  exact powerWeightedShiftMoment_continuousWithinAt_parameters_within
    (theta := theta) (S := S) (Sprime := Sprime)
    hq.1 hq.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos

end ScoreCurvatureStarOrder
