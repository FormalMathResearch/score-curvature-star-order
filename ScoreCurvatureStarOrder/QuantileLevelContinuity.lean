import Mathlib
import ScoreCurvatureStarOrder.Quantile

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- For a fixed nonnegative shift and `p > -1`, the canonical quantile is
continuous in its probability level at every `u ∈ (0,1)`.  The proof uses only
strict spatial monotonicity of the CDF and the exact identity `F(Q(u)) = u`;
no derivative of the quantile with respect to `u` is introduced. -/
theorem powerWeightedShiftQuantile_continuousAt_level_within
    {theta S Sprime : ℝ → ℝ} {a p u : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p) (hu0 : 0 < u) (hu1 : u < 1)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ContinuousAt (fun v : ℝ => powerWeightedShiftQuantile theta a p v) u := by
  let Q : ℝ → ℝ := fun v => powerWeightedShiftQuantile theta a p v
  let F : ℝ → ℝ := fun x => powerWeightedShiftCDF theta a p x

  have hQu := powerWeightedShiftQuantile_pos_and_CDF_eq_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p) (u := u)
    ha hp hu0 hu1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hQupos : 0 < Q u := by
    simpa [Q] using hQu.1
  have hFQu : F (Q u) = u := by
    simpa [F, Q] using hQu.2
  have hstrict : StrictMonoOn F (Set.Ioi (0 : ℝ)) := by
    simpa [F] using
      (powerWeightedShiftCDF_strictMonoOn_Ioi_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)

  show Tendsto Q (𝓝 u) (𝓝 (Q u))
  rw [tendsto_order]
  constructor
  · intro l hl
    by_cases hl0 : l ≤ 0
    · filter_upwards [Ioi_mem_nhds hu0, Iio_mem_nhds hu1] with v hv0 hv1
      have hQv := powerWeightedShiftQuantile_pos_and_CDF_eq_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p) (u := v)
        ha hp hv0 hv1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
      exact lt_of_le_of_lt hl0 (by simpa [Q] using hQv.1)
    · have hlpos : 0 < l := lt_of_not_ge hl0
      have hFlt : F l < u := by
        have hmono := hstrict hlpos hQupos hl
        exact hmono.trans_eq hFQu
      filter_upwards [Ioi_mem_nhds hu0, Iio_mem_nhds hu1, Ioi_mem_nhds hFlt] with
          v hv0 hv1 hFlv
      have hQv := powerWeightedShiftQuantile_pos_and_CDF_eq_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p) (u := v)
        ha hp hv0 hv1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
      have hQvpos : 0 < Q v := by
        simpa [Q] using hQv.1
      have hFQv : F (Q v) = v := by
        simpa [F, Q] using hQv.2
      by_contra hnot
      have hQle : Q v ≤ l := le_of_not_gt hnot
      have hmono : F (Q v) ≤ F l :=
        hstrict.monotoneOn hQvpos hlpos hQle
      rw [hFQv] at hmono
      exact (not_lt_of_ge hmono) hFlv
  · intro r hr
    have hrpos : 0 < r := hQupos.trans hr
    have hFgt : u < F r := by
      have hmono := hstrict hQupos hrpos hr
      exact hFQu.symm.trans_lt hmono
    filter_upwards [Ioi_mem_nhds hu0, Iio_mem_nhds hu1, Iio_mem_nhds hFgt] with
        v hv0 hv1 hvFr
    have hQv := powerWeightedShiftQuantile_pos_and_CDF_eq_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (u := v)
      ha hp hv0 hv1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
    have hQvpos : 0 < Q v := by
      simpa [Q] using hQv.1
    have hFQv : F (Q v) = v := by
      simpa [F, Q] using hQv.2
    by_contra hnot
    have hrle : r ≤ Q v := le_of_not_gt hnot
    have hmono : F r ≤ F (Q v) :=
      hstrict.monotoneOn hrpos hQvpos hrle
    rw [hFQv] at hmono
    exact (not_lt_of_ge hmono) hvFr

/-- The canonical quantile is continuous on the full probability interval
`(0,1)` under the one-sided half-line hypotheses. -/
theorem powerWeightedShiftQuantile_continuousOn_Ioo_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ContinuousOn
      (fun u : ℝ => powerWeightedShiftQuantile theta a p u)
      (Set.Ioo (0 : ℝ) 1) := by
  intro u hu
  exact
    (powerWeightedShiftQuantile_continuousAt_level_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (u := u)
      ha hp hu.1 hu.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos).continuousWithinAt

end ScoreCurvatureStarOrder
