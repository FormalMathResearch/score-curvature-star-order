import Mathlib
import ScoreCurvatureStarOrder.CDFShiftBoundaryContinuity
import ScoreCurvatureStarOrder.Quantile

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- For every probability level `u ∈ (0,1)`, the canonical quantile is
right-continuous at the boundary shift `a = 0`.

The proof is an inverse-continuity argument.  At `a=0`, strict spatial
monotonicity of the CDF separates every `l < Q_{p,0}(u) < r` from the level
`u`.  Fixed-endpoint right-continuity of the CDF preserves those strict
inequalities for all sufficiently small nonnegative shifts.  Exact CDF
inversion and strict spatial monotonicity at the nearby shift then trap
`Q_{p,a}(u)` between `l` and `r`.  No implicit-function theorem and no
shift derivative at the boundary are used. -/
theorem powerWeightedShiftQuantile_continuousWithinAt_zero_within
    {theta S Sprime : ℝ → ℝ} {p u : ℝ}
    (hp : -1 < p) (hu0 : 0 < u) (hu1 : u < 1)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ContinuousWithinAt
      (fun a : ℝ => powerWeightedShiftQuantile theta a p u)
      (Set.Ici (0 : ℝ)) 0 := by
  let Q : ℝ → ℝ := fun a => powerWeightedShiftQuantile theta a p u
  let F : ℝ → ℝ → ℝ := fun a x => powerWeightedShiftCDF theta a p x

  have hQ0 := powerWeightedShiftQuantile_pos_and_CDF_eq_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := 0) (p := p) (u := u)
    (by norm_num) hp hu0 hu1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hQ0pos : 0 < Q 0 := by simpa [Q] using hQ0.1
  have hFQ0 : F 0 (Q 0) = u := by simpa [F, Q] using hQ0.2
  have hstrict0 : StrictMonoOn (F 0) (Set.Ioi (0 : ℝ)) := by
    simpa [F] using powerWeightedShiftCDF_strictMonoOn_Ioi_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := 0) (p := p)
      (by norm_num) hp htheta_pos htheta_deriv htheta_int hS hSprime_pos

  show Tendsto Q (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 (Q 0))
  rw [tendsto_order]
  constructor
  · intro l hl
    by_cases hl0 : l ≤ 0
    · filter_upwards [self_mem_nhdsWithin] with a ha
      have hQa := powerWeightedShiftQuantile_pos_and_CDF_eq_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p) (u := u)
        ha hp hu0 hu1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
      exact lt_of_le_of_lt hl0 (by simpa [Q] using hQa.1)
    · have hlpos : 0 < l := lt_of_not_ge hl0
      have hFlt : F 0 l < u := by
        have hmono := hstrict0 hlpos hQ0pos hl
        exact hmono.trans_eq hFQ0
      have hFcont :
          ContinuousWithinAt (fun a : ℝ => F a l) (Set.Ici (0 : ℝ)) 0 := by
        simpa [F] using
          (powerWeightedShiftCDF_continuousWithinAt_zero_within
            (theta := theta) (S := S) (Sprime := Sprime)
            (p := p) (x := l)
            hp hlpos htheta_pos htheta_deriv htheta_int hS hSprime_pos)
      have hevF : ∀ᶠ a : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0, F a l < u :=
        hFcont.eventually (Iio_mem_nhds hFlt)
      filter_upwards [self_mem_nhdsWithin, hevF] with a ha hFla
      have hQa := powerWeightedShiftQuantile_pos_and_CDF_eq_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p) (u := u)
        ha hp hu0 hu1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
      have hstricta : StrictMonoOn (F a) (Set.Ioi (0 : ℝ)) := by
        simpa [F] using powerWeightedShiftCDF_strictMonoOn_Ioi_within
          (theta := theta) (S := S) (Sprime := Sprime)
          (a := a) (p := p)
          ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
      by_contra hnot
      have hQle : Q a ≤ l := le_of_not_gt hnot
      have hmono : F a (Q a) ≤ F a l :=
        hstricta.monotoneOn
          (by simpa [Q] using hQa.1) hlpos hQle
      have hFQa : F a (Q a) = u := by simpa [F, Q] using hQa.2
      rw [hFQa] at hmono
      exact (not_lt_of_ge hmono) hFla
  · intro r hr
    have hrpos : 0 < r := hQ0pos.trans hr
    have hFgt : u < F 0 r := by
      have hmono := hstrict0 hQ0pos hrpos hr
      exact hFQ0.symm.trans_lt hmono
    have hFcont :
        ContinuousWithinAt (fun a : ℝ => F a r) (Set.Ici (0 : ℝ)) 0 := by
      simpa [F] using
        (powerWeightedShiftCDF_continuousWithinAt_zero_within
          (theta := theta) (S := S) (Sprime := Sprime)
          (p := p) (x := r)
          hp hrpos htheta_pos htheta_deriv htheta_int hS hSprime_pos)
    have hevF : ∀ᶠ a : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0, u < F a r :=
      hFcont.eventually (Ioi_mem_nhds hFgt)
    filter_upwards [self_mem_nhdsWithin, hevF] with a ha hFra
    have hQa := powerWeightedShiftQuantile_pos_and_CDF_eq_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (u := u)
      ha hp hu0 hu1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
    have hstricta : StrictMonoOn (F a) (Set.Ioi (0 : ℝ)) := by
      simpa [F] using powerWeightedShiftCDF_strictMonoOn_Ioi_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
    by_contra hnot
    have hrle : r ≤ Q a := le_of_not_gt hnot
    have hmono : F a r ≤ F a (Q a) :=
      hstricta.monotoneOn hrpos (by simpa [Q] using hQa.1) hrle
    have hFQa : F a (Q a) = u := by simpa [F, Q] using hQa.2
    rw [hFQa] at hmono
    exact (not_lt_of_ge hmono) hFra

end ScoreCurvatureStarOrder
