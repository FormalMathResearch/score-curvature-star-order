import Mathlib
import ScoreCurvatureStarOrder.QuantileBoundaryContinuity
import ScoreCurvatureStarOrder.QuantileRatioMonotonicity

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Topology

/-- **Publication headline theorem (manuscript Theorem 4.8, quantile form).**

Under the one-sided half-line formulation of the admissibility hypotheses, the
power-weighted shift family is star-shaped ordered for every `p > -1`: for
`0 ≤ a₁ < a₂`, the canonical quantile ratio

`u ↦ Q_{p,a₂}(u) / Q_{p,a₁}(u)`

is nondecreasing on `(0,1)`.

This proof is intentionally organized as the manuscript-level end-to-end
argument rather than as one large technical tactic block.  The local
`hpositiveRatio` block invokes the already kernel-checked positive-shift chain
(two-point kernel → scalar kernel → slope quotient → global cumulative-radial
ratio → logarithmic quantile derivative).  The local `hboundaryQuantile` block
records the independently kernel-checked right-continuity `Q_{p,a}(u) →
Q_{p,0}(u)` as `a ↓ 0`.  The remaining local blocks perform exactly the final
boundary passage in the manuscript. -/
theorem powerWeightedShift_starOrder_headline_within
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
  /- The entire interior-shift proof chain, already verified through the
     two-point kernel and the global `R=A/D` theorem. -/
  have hpositiveRatio :
      ∀ {b c : ℝ}, 0 < b → b < c →
        MonotoneOn
          (fun u : ℝ =>
            powerWeightedShiftQuantile theta c p u /
              powerWeightedShiftQuantile theta b p u)
          (Set.Ioo (0 : ℝ) 1) := by
    intro b c hb hbc
    exact powerWeightedShift_quantileRatio_monotoneOn_Ioo_pos_shifts_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (a₁ := b) (a₂ := c) (p := p)
      hb hbc hp htheta_pos htheta_deriv htheta_int hS hSprime
      hSprime_pos hcurv

  /- The only additional analytic input needed at the boundary. -/
  have hboundaryQuantile :
      ∀ {w : ℝ}, w ∈ Set.Ioo (0 : ℝ) 1 →
        ContinuousWithinAt
          (fun a : ℝ => powerWeightedShiftQuantile theta a p w)
          (Set.Ici (0 : ℝ)) 0 := by
    intro w hw
    exact powerWeightedShiftQuantile_continuousWithinAt_zero_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (p := p) (u := w)
      hp hw.1 hw.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos

  by_cases ha₁pos : 0 < a₁
  · exact hpositiveRatio ha₁pos ha₁₂

  /- Since the theorem assumes `a₁ ≥ 0`, the only remaining case is exactly
     the manuscript boundary `a₁ = 0`. -/
  have ha₁zero : a₁ = 0 :=
    le_antisymm (le_of_not_gt ha₁pos) ha₁
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

  have hsub : Set.Ioi (0 : ℝ) ⊆ Set.Ici (0 : ℝ) := by
    intro b hb
    change 0 < b at hb
    exact hb.le
  have hfilter : 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝[Set.Ici (0 : ℝ)] 0 :=
    nhdsWithin_mono 0 hsub

  have hQu_cont := hboundaryQuantile hu
  have hQv_cont := hboundaryQuantile hv
  change Tendsto
      (fun b : ℝ => powerWeightedShiftQuantile theta b p u)
      (𝓝[Set.Ici (0 : ℝ)] 0)
      (𝓝 (powerWeightedShiftQuantile theta 0 p u)) at hQu_cont
  change Tendsto
      (fun b : ℝ => powerWeightedShiftQuantile theta b p v)
      (𝓝[Set.Ici (0 : ℝ)] 0)
      (𝓝 (powerWeightedShiftQuantile theta 0 p v)) at hQv_cont

  have hQu_lim_Ici :
      Tendsto (fun b : ℝ => Q b u)
        (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 (Q 0 u)) := by
    simpa [Q] using hQu_cont
  have hQv_lim_Ici :
      Tendsto (fun b : ℝ => Q b v)
        (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 (Q 0 v)) := by
    simpa [Q] using hQv_cont
  have hQu_lim : Tendsto (fun b : ℝ => Q b u) l (𝓝 (Q 0 u)) :=
    hQu_lim_Ici.mono_left hfilter
  have hQv_lim : Tendsto (fun b : ℝ => Q b v) l (𝓝 (Q 0 v)) :=
    hQv_lim_Ici.mono_left hfilter

  have hleft_lim :
      Tendsto (fun b : ℝ => Q a₂ u / Q b u) l
        (𝓝 (Q a₂ u / Q 0 u)) :=
    tendsto_const_nhds.div hQu_lim (by simpa [Q] using hQ0u.1.ne')
  have hright_lim :
      Tendsto (fun b : ℝ => Q a₂ v / Q b v) l
        (𝓝 (Q a₂ v / Q 0 v)) :=
    tendsto_const_nhds.div hQv_lim (by simpa [Q] using hQ0v.1.ne')

  have hlt_a₂_nhds : ∀ᶠ b : ℝ in 𝓝 (0 : ℝ), b < a₂ :=
    eventually_lt_nhds ha₂pos
  have hlt_a₂ : ∀ᶠ b : ℝ in l, b < a₂ :=
    hlt_a₂_nhds.filter_mono nhdsWithin_le_nhds

  have hpositive_ineq :
      ∀ᶠ b : ℝ in l,
        Q a₂ u / Q b u ≤ Q a₂ v / Q b v := by
    filter_upwards [self_mem_nhdsWithin, hlt_a₂] with b hb hba₂
    change 0 < b at hb
    have hmono := hpositiveRatio hb hba₂
    simpa [Q] using hmono hu hv huv

  have hboundary_ineq : Q a₂ u / Q 0 u ≤ Q a₂ v / Q 0 v :=
    le_of_tendsto_of_tendsto hleft_lim hright_lim hpositive_ineq

  simpa [Q] using hboundary_ineq

end ScoreCurvatureStarOrder
