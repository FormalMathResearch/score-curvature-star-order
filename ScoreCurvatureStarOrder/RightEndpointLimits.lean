import Mathlib
import ScoreCurvatureStarOrder.Boundary
import ScoreCurvatureStarOrder.CumulativeRadialRatio
import ScoreCurvatureStarOrder.ScoreMeanIntegrability

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- At the right endpoint, both quantities entering the cumulative-radial ratio
vanish.  The radial-density limit is inherited from the already verified
exponential-tail boundary estimate.  For the cumulative numerator, the
centered-score integrand is absolutely integrable, its total integral on
`(0,∞)` is exactly zero, and the remaining tail integral tends to zero.

All differentiability hypotheses at the boundary remain one-sided on
`[0,∞)`. -/
theorem powerWeightedShift_cumulative_and_radial_tendsto_atTop_zero_within
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
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ),
      Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    Tendsto
        (fun x : ℝ => powerWeightedShiftCumulativeShiftNumerator theta S a p x)
        atTop (𝓝 0) ∧
      Tendsto
        (fun x : ℝ => powerWeightedShiftRadialDensity theta a p x)
        atTop (𝓝 0) := by
  let G : ℝ := powerWeightedShiftScoreMean theta S a p
  let f : ℝ → ℝ := fun t => powerWeightedShiftDensity theta a p t
  let h : ℝ → ℝ := fun t => f t * (G - S (a + t))
  let A : ℝ → ℝ := fun x =>
    powerWeightedShiftCumulativeShiftNumerator theta S a p x
  let D : ℝ → ℝ := fun x => powerWeightedShiftRadialDensity theta a p x

  have hf : IntegrableOn f (Set.Ioi (0 : ℝ)) := by
    simpa [f] using
      (powerWeightedShiftDensity_integrableOn_Ioi_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)
  have hscore :
      IntegrableOn
        (fun t : ℝ => S (a + t) * f t) (Set.Ioi (0 : ℝ)) := by
    simpa [f] using
      (powerWeightedShift_score_mean_integrableOn_Ioi_within
        (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime hSprime_pos hcurv)
  have hGf := hf.const_mul G
  have hlin := hGf.sub hscore
  have hh : IntegrableOn h (Set.Ioi (0 : ℝ)) := by
    refine IntegrableOn.congr_fun hlin ?_ measurableSet_Ioi
    intro t ht
    dsimp [h]
    change G * f t - S (a + t) * f t = f t * (G - S (a + t))
    ring

  have hf_one : (∫ t : ℝ in Set.Ioi 0, f t) = 1 := by
    simpa [f] using
      (powerWeightedShiftDensity_integral_eq_one_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)
  have htotal : (∫ t : ℝ in Set.Ioi 0, h t) = 0 := by
    have hGfI :
        Integrable (fun t : ℝ => G * f t) (volume.restrict (Set.Ioi (0 : ℝ))) := by
      simpa using hGf
    have hscoreI :
        Integrable (fun t : ℝ => S (a + t) * f t)
          (volume.restrict (Set.Ioi (0 : ℝ))) := by
      simpa using hscore
    have hrepl :
        (∫ t : ℝ in Set.Ioi 0, h t) =
          ∫ t : ℝ in Set.Ioi 0, (G * f t - S (a + t) * f t) := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro t ht
      dsimp [h]
      ring
    rw [hrepl, integral_sub hGfI hscoreI]
    simp only [integral_const_mul]
    rw [hf_one]
    change G * 1 - G = 0
    ring

  have hiInter : (⋂ x : ℝ, Set.Ioi x) = (∅ : Set ℝ) := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro y hy
    have hy' : y + 1 < y := by
      exact (Set.mem_iInter.mp hy) (y + 1)
    linarith

  have htail :
      Tendsto (fun x : ℝ => ∫ t : ℝ in Set.Ioi x, h t) atTop (𝓝 0) := by
    have hanti : Antitone (fun x : ℝ => Set.Ioi x) := by
      intro x y hxy
      intro t ht
      exact hxy.trans_lt ht
    have hlim := tendsto_setIntegral_of_antitone
      (f := h) (μ := volume) (s := fun x : ℝ => Set.Ioi x)
      (fun _ => measurableSet_Ioi) hanti ⟨0, hh⟩
    rw [hiInter] at hlim
    simpa using hlim

  have hA_tail : ∀ x : ℝ, 0 ≤ x → A x = -(∫ t : ℝ in Set.Ioi x, h t) := by
    intro x hx
    have hhx : IntegrableOn h (Set.Ioi x) :=
      hh.mono_set (by
        intro t ht
        exact hx.trans_lt ht)
    have hsplit := intervalIntegral.integral_interval_add_Ioi
      (f := h) (μ := volume) (a := (0 : ℝ)) (b := x) hh hhx
    rw [htotal] at hsplit
    have hinterval : (∫ t : ℝ in 0..x, h t) = -(∫ t : ℝ in Set.Ioi x, h t) := by
      linarith
    simpa [A, h, f, G, powerWeightedShiftCumulativeShiftNumerator] using hinterval

  have hA : Tendsto A atTop (𝓝 0) := by
    have hneg :
        Tendsto (fun x : ℝ => -(∫ t : ℝ in Set.Ioi x, h t)) atTop (𝓝 0) := by
      simpa using htail.neg
    refine hneg.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact (hA_tail x hx).symm

  have hnum :
      Tendsto (fun x : ℝ => x ^ (p + 1) * theta (a + x)) atTop (𝓝 0) :=
    powerWeightedShift_boundary_atTop_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p)
      ha htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hD : Tendsto D atTop (𝓝 0) := by
    have hconst :
        Tendsto
          (fun _ : ℝ => (powerWeightedShiftMoment theta a p)⁻¹)
          atTop (𝓝 ((powerWeightedShiftMoment theta a p)⁻¹)) :=
      tendsto_const_nhds
    have hmul := hnum.mul hconst
    simpa [D, powerWeightedShiftRadialDensity, div_eq_mul_inv] using hmul

  exact ⟨by simpa [A] using hA, by simpa [D] using hD⟩

end ScoreCurvatureStarOrder
