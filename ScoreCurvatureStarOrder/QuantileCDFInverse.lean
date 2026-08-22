import Mathlib
import ScoreCurvatureStarOrder.Quantile

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- At every positive observation point, the normalized CDF takes a genuine
probability level in `(0,1)`.  The lower bound uses strict increase on the
compact segment from `0` to `x`; the upper bound uses strict increase on the
positive half-line together with the already verified limit `F(y) → 1` as
`y → ∞`. -/
theorem powerWeightedShiftCDF_pos_lt_one_within
    {theta S Sprime : ℝ → ℝ} {a p x : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p) (hx : 0 < x)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    0 < powerWeightedShiftCDF theta a p x ∧
      powerWeightedShiftCDF theta a p x < 1 := by
  let F : ℝ → ℝ := fun y => powerWeightedShiftCDF theta a p y

  have hcont_seg : ContinuousOn F (Set.Icc (0 : ℝ) x) := by
    simpa [F] using
      (powerWeightedShiftCDF_continuousOn_Icc_zero_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p) (b := x)
        ha hp hx.le htheta_pos htheta_deriv htheta_int hS hSprime_pos)
  have hderiv_pos_seg :
      ∀ y ∈ interior (Set.Icc (0 : ℝ) x), 0 < deriv F y := by
    intro y hy
    have hyIoo : y ∈ Set.Ioo (0 : ℝ) x := by
      simpa only [interior_Icc] using hy
    have hder := powerWeightedShiftCDF_hasDerivAt_x_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (x := y)
      ha hp hyIoo.1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
    have hdpos := powerWeightedShiftDensity_pos_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (x := y)
      ha hp hyIoo.1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [F, hder.deriv] using hdpos
  have hstrict_seg : StrictMonoOn F (Set.Icc (0 : ℝ) x) :=
    strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) x) hcont_seg hderiv_pos_seg
  have hFpos : 0 < F x := by
    have hlt := hstrict_seg
      (show (0 : ℝ) ∈ Set.Icc 0 x by exact ⟨le_rfl, hx.le⟩)
      (show x ∈ Set.Icc (0 : ℝ) x by exact ⟨hx.le, le_rfl⟩) hx
    simpa [F] using hlt

  have hstrict : StrictMonoOn F (Set.Ioi (0 : ℝ)) := by
    simpa [F] using
      (powerWeightedShiftCDF_strictMonoOn_Ioi_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)
  have hlim : Tendsto F atTop (𝓝 1) := by
    simpa [F] using
      (powerWeightedShiftCDF_tendsto_one_atTop_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)

  let z : ℝ := x + 1
  have hz : 0 < z := by
    dsimp [z]
    linarith
  have hxz : x < z := by
    dsimp [z]
    linarith
  have hFz_le : F z ≤ 1 := by
    apply _root_.ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop z] with y hy
    rcases hy.eq_or_lt with rfl | hzy
    · exact le_rfl
    · exact (hstrict hz (hz.trans hzy) hzy).le
  have hFlt : F x < 1 :=
    (hstrict hx hz hxz).trans_le hFz_le

  exact ⟨by simpa [F] using hFpos, by simpa [F] using hFlt⟩

/-- The canonical quantile is the genuine inverse of the normalized CDF at
every positive spatial point.  This is the inverse identity needed for the
finite-interval substitution `u = F_{p,a}(x)` in the log-moment transport. -/
theorem powerWeightedShiftQuantile_CDF_eq_within
    {theta S Sprime : ℝ → ℝ} {a p x : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p) (hx : 0 < x)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    powerWeightedShiftQuantile theta a p
        (powerWeightedShiftCDF theta a p x) = x := by
  have hlevel := powerWeightedShiftCDF_pos_lt_one_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p) (x := x)
    ha hp hx htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hQ := powerWeightedShiftQuantile_pos_and_CDF_eq_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p) (u := powerWeightedShiftCDF theta a p x)
    ha hp hlevel.1 hlevel.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hstrict := powerWeightedShiftCDF_strictMonoOn_Ioi_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p)
    ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  exact hstrict.injOn hQ.1 hx hQ.2

end ScoreCurvatureStarOrder
