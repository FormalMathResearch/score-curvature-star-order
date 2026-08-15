import Mathlib
import ScoreCurvatureStarOrder.Quantile
import ScoreCurvatureStarOrder.DistributionShiftDerivativeWithin

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- For an interior shift `a > 0` and a probability level `u ∈ (0,1)`, the
canonical quantile depends continuously on the shift parameter.  The proof
uses only fixed-endpoint shift continuity of the CDF and strict spatial
monotonicity; no joint `C¹` hypothesis on `(a,x) ↦ F_{p,a}(x)` is introduced. -/
theorem powerWeightedShiftQuantile_continuousAt_shift_within
    {theta S Sprime Ssecond : ℝ → ℝ} {a p u : ℝ}
    (ha : 0 < a) (hp : -1 < p) (hu0 : 0 < u) (hu1 : u < 1)
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
    ContinuousAt (fun b : ℝ => powerWeightedShiftQuantile theta b p u) a := by
  let Q : ℝ → ℝ := fun b => powerWeightedShiftQuantile theta b p u
  let F : ℝ → ℝ → ℝ := fun b x => powerWeightedShiftCDF theta b p x

  have hQa := powerWeightedShiftQuantile_pos_and_CDF_eq_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p) (u := u)
    ha.le hp hu0 hu1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hQapos : 0 < Q a := by simpa [Q] using hQa.1
  have hFQa : F a (Q a) = u := by simpa [F, Q] using hQa.2
  have hstrict_a : StrictMonoOn (F a) (Set.Ioi (0 : ℝ)) := by
    simpa [F] using powerWeightedShiftCDF_strictMonoOn_Ioi_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p)
      ha.le hp htheta_pos htheta_deriv htheta_int hS hSprime_pos

  show Tendsto Q (𝓝 a) (𝓝 (Q a))
  rw [tendsto_order]
  constructor
  · intro l hl
    by_cases hl0 : l ≤ 0
    · filter_upwards [Ioi_mem_nhds ha] with b hb
      have hQb := powerWeightedShiftQuantile_pos_and_CDF_eq_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := b) (p := p) (u := u)
        hb.le hp hu0 hu1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
      exact lt_of_le_of_lt hl0 hQb.1
    · have hlpos : 0 < l := lt_of_not_ge hl0
      have hFlt : F a l < u := by
        have hmono := hstrict_a hlpos hQapos hl
        exact hmono.trans_eq hFQa
      have hFcont : ContinuousAt (fun b : ℝ => F b l) a := by
        simpa [F] using
          (powerWeightedShiftCDF_hasDerivAt_within
            (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
            (a := a) (p := p) (x := l)
            ha hp hlpos htheta_pos htheta_deriv htheta_int hS hSprime
            hSprime_pos hcurv).continuousAt
      have hevF : ∀ᶠ b : ℝ in 𝓝 a, F b l < u :=
        hFcont.eventually (Iio_mem_nhds hFlt)
      filter_upwards [Ioi_mem_nhds ha, hevF] with b hb hFlb
      have hQb := powerWeightedShiftQuantile_pos_and_CDF_eq_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := b) (p := p) (u := u)
        hb.le hp hu0 hu1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
      have hstrict_b : StrictMonoOn (F b) (Set.Ioi (0 : ℝ)) := by
        simpa [F] using powerWeightedShiftCDF_strictMonoOn_Ioi_within
          (theta := theta) (S := S) (Sprime := Sprime)
          (a := b) (p := p)
          hb.le hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
      by_contra hnot
      have hQle : Q b ≤ l := le_of_not_gt hnot
      have hmono : F b (Q b) ≤ F b l :=
        hstrict_b.monotoneOn (by simpa [Q] using hQb.1) hlpos hQle
      have hFQb : F b (Q b) = u := by simpa [F, Q] using hQb.2
      rw [hFQb] at hmono
      exact (not_lt_of_ge hmono) hFlb
  · intro r hr
    have hrpos : 0 < r := hQapos.trans hr
    have hFgt : u < F a r := by
      have hmono := hstrict_a hQapos hrpos hr
      exact hFQa.symm.trans_lt hmono
    have hFcont : ContinuousAt (fun b : ℝ => F b r) a := by
      simpa [F] using
        (powerWeightedShiftCDF_hasDerivAt_within
          (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
          (a := a) (p := p) (x := r)
          ha hp hrpos htheta_pos htheta_deriv htheta_int hS hSprime
          hSprime_pos hcurv).continuousAt
    have hevF : ∀ᶠ b : ℝ in 𝓝 a, u < F b r :=
      hFcont.eventually (Ioi_mem_nhds hFgt)
    filter_upwards [Ioi_mem_nhds ha, hevF] with b hb hFrb
    have hQb := powerWeightedShiftQuantile_pos_and_CDF_eq_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := b) (p := p) (u := u)
      hb.le hp hu0 hu1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
    have hstrict_b : StrictMonoOn (F b) (Set.Ioi (0 : ℝ)) := by
      simpa [F] using powerWeightedShiftCDF_strictMonoOn_Ioi_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := b) (p := p)
        hb.le hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
    by_contra hnot
    have hrle : r ≤ Q b := le_of_not_gt hnot
    have hmono : F b r ≤ F b (Q b) :=
      hstrict_b.monotoneOn hrpos (by simpa [Q] using hQb.1) hrle
    have hFQb : F b (Q b) = u := by simpa [F, Q] using hQb.2
    rw [hFQb] at hmono
    exact (not_lt_of_ge hmono) hFrb

end ScoreCurvatureStarOrder
