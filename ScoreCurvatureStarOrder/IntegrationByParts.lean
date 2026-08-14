import Mathlib
import ScoreCurvatureStarOrder.ScoreIntegrability

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Topology

/-- Integration by parts for the score-weighted shifted moment under the
mathematically natural one-sided differentiability assumptions on `[0, ∞)`.
The ordinary derivatives required by the improper integration-by-parts theorem
are recovered only at the strictly positive interior points where they are
actually used. -/
theorem powerWeightedShift_score_moment_identity_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    (∫ x : ℝ in Set.Ioi 0,
        x ^ (p + 1) * S (a + x) * theta (a + x)) =
      (p + 1) * ∫ x : ℝ in Set.Ioi 0, x ^ p * theta (a + x) := by
  let u : ℝ → ℝ := fun x => x ^ (p + 1)
  let u' : ℝ → ℝ := fun x => (p + 1) * x ^ p
  let v : ℝ → ℝ := fun x => theta (a + x)
  let v' : ℝ → ℝ := fun x => -S (a + x) * theta (a + x)
  have hu : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt u (u' x) x := by
    intro x hx
    have hrpow := Real.hasDerivAt_rpow_const (x := x) (p := p + 1) (Or.inl hx.ne')
    have hexp : p + 1 - 1 = p := by ring
    simpa only [u, u', hexp] using hrpow
  have hv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt v (v' x) x := by
    intro x hx
    have haxpos : 0 < a + x := by linarith [ha, hx]
    simpa [v, v'] using
      (hasDerivAt_shift_of_pos_of_hasDerivWithinAt_Ici haxpos htheta_deriv)
  have hscore :
      IntegrableOn
        (fun x : ℝ => x ^ (p + 1) * S (a + x) * theta (a + x))
        (Set.Ioi (0 : ℝ)) :=
    powerWeightedShift_score_integrableOn_Ioi_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have huv' : IntegrableOn (u * v') (Set.Ioi (0 : ℝ)) := by
    rw [Pi.mul_def]
    refine IntegrableOn.congr_fun hscore.neg ?_ measurableSet_Ioi
    intro x hx
    dsimp [u, v']
    ring
  have hbase :
      IntegrableOn (fun x : ℝ => x ^ p * theta (a + x)) (Set.Ioi (0 : ℝ)) :=
    powerWeightedShift_integrableOn_Ioi_within
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hscaled :
      IntegrableOn (fun x : ℝ => (p + 1) * (x ^ p * theta (a + x)))
        (Set.Ioi (0 : ℝ)) :=
    hbase.const_mul (p + 1)
  have hu'v : IntegrableOn (u' * v) (Set.Ioi (0 : ℝ)) := by
    rw [Pi.mul_def]
    refine IntegrableOn.congr_fun hscaled ?_ measurableSet_Ioi
    intro x hx
    dsimp [u', v]
    ring
  have hzero0 := powerWeightedShift_boundary_zero_within
    (theta := theta) (S := S) (a := a) (p := p) ha hp htheta_deriv
  have hzero : Tendsto (u * v) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [Pi.mul_def]
    simpa [u, v] using hzero0
  have hinfty0 := powerWeightedShift_boundary_atTop_within
    (theta := theta) (S := S) (Sprime := Sprime) (a := a) (p := p)
    ha htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hinfty : Tendsto (u * v) atTop (𝓝 0) := by
    rw [Pi.mul_def]
    simpa [u, v] using hinfty0
  have hibp := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) hu hv huv' hu'v hzero hinfty
  have hleft :
      (∫ x : ℝ in Set.Ioi 0, u x * v' x) =
        -(∫ x : ℝ in Set.Ioi 0,
          x ^ (p + 1) * S (a + x) * theta (a + x)) := by
    calc
      (∫ x : ℝ in Set.Ioi 0, u x * v' x) =
          ∫ x : ℝ in Set.Ioi 0,
            -(x ^ (p + 1) * S (a + x) * theta (a + x)) := by
              refine setIntegral_congr_fun measurableSet_Ioi ?_
              intro x hx
              dsimp [u, v']
              ring
      _ = -(∫ x : ℝ in Set.Ioi 0,
          x ^ (p + 1) * S (a + x) * theta (a + x)) := by
        rw [integral_neg]
  have hright :
      (∫ x : ℝ in Set.Ioi 0, u' x * v x) =
        (p + 1) * ∫ x : ℝ in Set.Ioi 0, x ^ p * theta (a + x) := by
    calc
      (∫ x : ℝ in Set.Ioi 0, u' x * v x) =
          ∫ x : ℝ in Set.Ioi 0, (p + 1) * (x ^ p * theta (a + x)) := by
            refine setIntegral_congr_fun measurableSet_Ioi ?_
            intro x hx
            dsimp [u', v]
            ring
      _ = (p + 1) * ∫ x : ℝ in Set.Ioi 0, x ^ p * theta (a + x) := by
        rw [integral_const_mul]
  rw [hleft, hright] at hibp
  linarith

/-- Backward-compatible wrapper for the former two-sided differentiability
assumptions.  The publication theorem should use
`powerWeightedShift_score_moment_identity_within`. -/
theorem powerWeightedShift_score_moment_identity
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    (∫ x : ℝ in Set.Ioi 0,
        x ^ (p + 1) * S (a + x) * theta (a + x)) =
      (p + 1) * ∫ x : ℝ in Set.Ioi 0, x ^ p * theta (a + x) := by
  exact powerWeightedShift_score_moment_identity_within
    ha hp htheta_pos
    (fun z hz => (htheta_deriv z hz).hasDerivWithinAt)
    htheta_int
    (fun z hz => (hS z hz).hasDerivWithinAt)
    hSprime_pos

end ScoreCurvatureStarOrder
