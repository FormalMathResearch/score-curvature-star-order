import Mathlib
import ScoreCurvatureStarOrder.Basic
import ScoreCurvatureStarOrder.TwoPointKernel

namespace ScoreCurvatureStarOrder

theorem scoreRatio_antitoneOn
    {S Sprime Ssecond : ℝ → ℝ} {D : Set ℝ}
    (hD : Convex ℝ D)
    (hS : ∀ z ∈ D, HasDerivAt S (Sprime z) z)
    (hSprime : ∀ z ∈ D, HasDerivAt Sprime (Ssecond z) z)
    (hSnz : ∀ z ∈ D, S z ≠ 0)
    (hcurv : ∀ z ∈ D, Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    AntitoneOn (fun z => Sprime z / S z) D := by
  have hcont : ContinuousOn (fun z => Sprime z / S z) D := by
    intro z hz
    exact
      ((hSprime z hz).div (hS z hz) (hSnz z hz)).continuousAt.continuousWithinAt
  have hder :
      ∀ z ∈ interior D,
        HasDerivWithinAt (fun y => Sprime y / S y)
          ((Ssecond z * S z - Sprime z * Sprime z) / S z ^ 2)
          (interior D) z := by
    intro z hz
    have hzD : z ∈ D := interior_subset hz
    exact
      ((hSprime z hzD).div (hS z hzD) (hSnz z hzD)).hasDerivWithinAt
  have hnonpos :
      ∀ z ∈ interior D,
        (Ssecond z * S z - Sprime z * Sprime z) / S z ^ 2 ≤ 0 := by
    intro z hz
    have hzD : z ∈ D := interior_subset hz
    have hnum : Ssecond z * S z - Sprime z * Sprime z ≤ 0 := by
      simpa [pow_two] using hcurv z hzD
    exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg (S z))
  exact antitoneOn_of_hasDerivWithinAt_nonpos hD hcont hder hnonpos

theorem logScore_concaveOn
    {S Sprime Ssecond : ℝ → ℝ} {D : Set ℝ}
    (hD : Convex ℝ D)
    (hS : ∀ z ∈ D, HasDerivAt S (Sprime z) z)
    (hSprime : ∀ z ∈ D, HasDerivAt Sprime (Ssecond z) z)
    (hSnz : ∀ z ∈ D, S z ≠ 0)
    (hcurv : ∀ z ∈ D, Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    ConcaveOn ℝ D (fun z => Real.log (S z)) := by
  have hratio :
      AntitoneOn (fun z => Sprime z / S z) D :=
    scoreRatio_antitoneOn hD hS hSprime hSnz hcurv
  have hcontS : ContinuousOn S D := by
    intro z hz
    exact (hS z hz).continuousAt.continuousWithinAt
  have hcontLog : ContinuousOn (fun z => Real.log (S z)) D :=
    hcontS.log hSnz
  have hdiffLog :
      DifferentiableOn ℝ (fun z => Real.log (S z)) (interior D) := by
    intro z hz
    have hzD : z ∈ D := interior_subset hz
    exact
      ((hS z hzD).log (hSnz z hzD)).differentiableAt.differentiableWithinAt
  have hantiDeriv :
      AntitoneOn (deriv (fun z => Real.log (S z))) (interior D) := by
    intro u hu v hv huv
    have huD : u ∈ D := interior_subset hu
    have hvD : v ∈ D := interior_subset hv
    have hdu :
        deriv (fun z => Real.log (S z)) u = Sprime u / S u :=
      ((hS u huD).log (hSnz u huD)).deriv
    have hdv :
        deriv (fun z => Real.log (S z)) v = Sprime v / S v :=
      ((hS v hvD).log (hSnz v hvD)).deriv
    rw [hdv, hdu]
    exact hratio huD hvD huv
  exact AntitoneOn.concaveOn_of_deriv hD hcontLog hdiffLog hantiDeriv

theorem logRatio_le_tangent
    {S Sprime : ℝ → ℝ} {D : Set ℝ} {x t : ℝ}
    (hconc : ConcaveOn ℝ D (fun z => Real.log (S z)))
    (hS : ∀ z ∈ D, HasDerivAt S (Sprime z) z)
    (hSnz : ∀ z ∈ D, S z ≠ 0)
    (hx : x ∈ D) (ht : t ∈ D) :
    Real.log (S t / S x) ≤ (Sprime x / S x) * (t - x) := by
  rcases lt_trichotomy x t with hxt | hxt | htx
  · have hslope :=
      hconc.slope_le_of_hasDerivAt hx ht hxt
        ((hS x hx).log (hSnz x hx))
    have hslope' :
        (Real.log (S t) - Real.log (S x)) / (t - x) ≤
          Sprime x / S x := by
      rw [slope_def_field] at hslope
      exact hslope
    have hdiff :
        Real.log (S t) - Real.log (S x) ≤
          (Sprime x / S x) * (t - x) :=
      (div_le_iff₀ (sub_pos.mpr hxt)).mp hslope'
    simpa [Real.log_div (hSnz t ht) (hSnz x hx)] using hdiff
  · subst t
    simp
  · have hslope :=
      hconc.le_slope_of_hasDerivAt ht hx htx
        ((hS x hx).log (hSnz x hx))
    have hslope' :
        Sprime x / S x ≤
          (Real.log (S x) - Real.log (S t)) / (x - t) := by
      rw [slope_def_field] at hslope
      exact hslope
    have hdiffPos :
        (Sprime x / S x) * (x - t) ≤
          Real.log (S x) - Real.log (S t) :=
      (le_div_iff₀ (sub_pos.mpr htx)).mp hslope'
    have hdiff :
        Real.log (S t) - Real.log (S x) ≤
          (Sprime x / S x) * (t - x) := by
      calc
        Real.log (S t) - Real.log (S x) =
            -(Real.log (S x) - Real.log (S t)) := by ring
        _ ≤ -((Sprime x / S x) * (x - t)) := neg_le_neg hdiffPos
        _ = (Sprime x / S x) * (t - x) := by ring
    simpa [Real.log_div (hSnz t ht) (hSnz x hx)] using hdiff

theorem logRatio_le_tangent_of_curvature
    {S Sprime Ssecond : ℝ → ℝ} {D : Set ℝ} {x t : ℝ}
    (hD : Convex ℝ D)
    (hS : ∀ z ∈ D, HasDerivAt S (Sprime z) z)
    (hSprime : ∀ z ∈ D, HasDerivAt Sprime (Ssecond z) z)
    (hSnz : ∀ z ∈ D, S z ≠ 0)
    (hcurv : ∀ z ∈ D, Ssecond z * S z - (Sprime z) ^ 2 ≤ 0)
    (hx : x ∈ D) (ht : t ∈ D) :
    Real.log (S t / S x) ≤ (Sprime x / S x) * (t - x) := by
  exact
    logRatio_le_tangent
      (logScore_concaveOn hD hS hSprime hSnz hcurv)
      hS hSnz hx ht

theorem twoPointKernel_nonneg_of_curvature_on
    {S Sprime Ssecond : ℝ → ℝ} {D : Set ℝ} {a x t : ℝ}
    (hD : Convex ℝ D)
    (hS : ∀ z ∈ D, HasDerivAt S (Sprime z) z)
    (hSprime : ∀ z ∈ D, HasDerivAt Sprime (Ssecond z) z)
    (hSnz : ∀ z ∈ D, S z ≠ 0)
    (hcurv : ∀ z ∈ D, Ssecond z * S z - (Sprime z) ^ 2 ≤ 0)
    (hax : a + x ∈ D) (hat : a + t ∈ D)
    (hr : 0 < S (a + t) / S (a + x)) :
    0 ≤ twoPointKernel S Sprime a x t := by
  have hlog0 :=
    logRatio_le_tangent_of_curvature
      hD hS hSprime hSnz hcurv hax hat
  have hlog :
      Real.log (S (a + t) / S (a + x)) ≤
        (Sprime (a + x) / S (a + x)) * (t - x) := by
    convert hlog0 using 1 <;> ring
  exact
    twoPointKernel_nonneg_of_log_ratio
      (hSnz (a + x) hax) hr hlog

end ScoreCurvatureStarOrder
