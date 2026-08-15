import Mathlib
import ScoreCurvatureStarOrder.QuantileBoundaryContinuity
import ScoreCurvatureStarOrder.QuantileRatioMonotonicity

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Topology

/-- Full quantile-ratio monotonicity for nonnegative shifts.

For `a₁ > 0` this is the already verified positive-shift theorem.  If `a₁=0`,
we apply that theorem with an auxiliary shift `b ∈ (0,a₂)` and let `b ↓ 0`.
The newly proved right-continuity of each quantile supplies the two quotient
limits, and closedness of the order relation passes the inequality to the
boundary. -/
theorem powerWeightedShift_quantileRatio_monotoneOn_Ioo_within
    {theta S Sprime Ssecond : ℝ → ℝ} {a₁ a₂ p : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₁₂ : a₁ < a₂) (hp : -1 < p)
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
    MonotoneOn
      (fun u : ℝ =>
        powerWeightedShiftQuantile theta a₂ p u /
          powerWeightedShiftQuantile theta a₁ p u)
      (Set.Ioo (0 : ℝ) 1) := by
  by_cases ha₁pos : 0 < a₁
  · exact powerWeightedShift_quantileRatio_monotoneOn_Ioo_pos_shifts_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (a₁ := a₁) (a₂ := a₂) (p := p)
      ha₁pos ha₁₂ hp htheta_pos htheta_deriv htheta_int hS hSprime
      hSprime_pos hcurv

  have ha₁zero : a₁ = 0 := by
    exact le_antisymm (le_of_not_gt ha₁pos) ha₁
  subst a₁
  have ha₂pos : 0 < a₂ := ha₁₂

  intro u hu v hv huv

  let Q : ℝ → ℝ → ℝ := fun a w => powerWeightedShiftQuantile theta a p w
  let l : Filter ℝ := 𝓝[Set.Ioi (0 : ℝ)] 0

  have hQ0u := powerWeightedShiftQuantile_pos_and_CDF_eq_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := 0) (p := p) (u := u)
    (by norm_num) hp hu.1 hu.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hQ0v := powerWeightedShiftQuantile_pos_and_CDF_eq_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := 0) (p := p) (u := v)
    (by norm_num) hp hv.1 hv.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos

  have hQu_cont := powerWeightedShiftQuantile_continuousWithinAt_zero_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (p := p) (u := u)
    hp hu.1 hu.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hQv_cont := powerWeightedShiftQuantile_continuousWithinAt_zero_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (p := p) (u := v)
    hp hv.1 hv.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos

  have hsub : Set.Ioi (0 : ℝ) ⊆ Set.Ici (0 : ℝ) := by
    intro b hb
    exact hb.le
  have hfilter : 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝[Set.Ici (0 : ℝ)] 0 :=
    nhdsWithin_mono 0 hsub

  have hQu_lim_Ici :
      Tendsto (fun b : ℝ => Q b u)
        (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 (Q 0 u)) := by
    simpa [Q] using hQu_cont
  have hQv_lim_Ici :
      Tendsto (fun b : ℝ => Q b v)
        (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 (Q 0 v)) := by
    simpa [Q] using hQv_cont
  have hQu_lim : Tendsto (fun b : ℝ => Q b u) l (𝓝 (Q 0 u)) := by
    exact hQu_lim_Ici.mono_left hfilter
  have hQv_lim : Tendsto (fun b : ℝ => Q b v) l (𝓝 (Q 0 v)) := by
    exact hQv_lim_Ici.mono_left hfilter

  have hconstu : Tendsto (fun _b : ℝ => Q a₂ u) l (𝓝 (Q a₂ u)) :=
    tendsto_const_nhds
  have hconstv : Tendsto (fun _b : ℝ => Q a₂ v) l (𝓝 (Q a₂ v)) :=
    tendsto_const_nhds
  have hleft_lim :
      Tendsto (fun b : ℝ => Q a₂ u / Q b u) l
        (𝓝 (Q a₂ u / Q 0 u)) :=
    hconstu.div hQu_lim (by simpa [Q] using hQ0u.1.ne')
  have hright_lim :
      Tendsto (fun b : ℝ => Q a₂ v / Q b v) l
        (𝓝 (Q a₂ v / Q 0 v)) :=
    hconstv.div hQv_lim (by simpa [Q] using hQ0v.1.ne')

  have hlt_a₂_nhds : ∀ᶠ b : ℝ in 𝓝 (0 : ℝ), b < a₂ :=
    eventually_lt_nhds ha₂pos
  have hlt_a₂ : ∀ᶠ b : ℝ in l, b < a₂ := by
    exact hlt_a₂_nhds.filter_mono nhdsWithin_le_nhds

  have hineq :
      ∀ᶠ b : ℝ in l,
        Q a₂ u / Q b u ≤ Q a₂ v / Q b v := by
    filter_upwards [self_mem_nhdsWithin, hlt_a₂] with b hbpos hba₂
    have hmono := powerWeightedShift_quantileRatio_monotoneOn_Ioo_pos_shifts_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (a₁ := b) (a₂ := a₂) (p := p)
      hbpos hba₂ hp htheta_pos htheta_deriv htheta_int hS hSprime
      hSprime_pos hcurv
    simpa [Q] using hmono hu hv huv

  have hlimit_ineq : Q a₂ u / Q 0 u ≤ Q a₂ v / Q 0 v :=
    le_of_tendsto_of_tendsto hleft_lim hright_lim hineq

  simpa [Q] using hlimit_ineq

end ScoreCurvatureStarOrder
