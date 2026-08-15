import Mathlib
import ScoreCurvatureStarOrder.QuantileShiftContinuity

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- Joint continuity of the normalized density at an interior positive point.
This is the only two-variable continuity needed in the elementary implicit
quantile argument. -/
theorem powerWeightedShiftDensity_continuousAt_prod_within
    {theta S Sprime Ssecond : ℝ → ℝ} {a p x : ℝ}
    (ha : 0 < a) (hp : -1 < p) (hx : 0 < x)
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
    ContinuousAt
      (fun z : ℝ × ℝ => powerWeightedShiftDensity theta z.1 p z.2)
      (a, x) := by
  let M : ℝ → ℝ := fun b => powerWeightedShiftMoment theta b p
  have hMderiv := powerWeightedShiftMoment_hasDerivAt_within
    (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
    (a := a) (p := p) ha hp htheta_pos htheta_deriv htheta_int hS hSprime
    hSprime_pos hcurv
  have hMcont : ContinuousAt M a := by
    simpa [M] using hMderiv.continuousAt
  have hMpos : 0 < M a := by
    dsimp [M]
    exact powerWeightedShiftMoment_pos_within
      ha.le hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hax : 0 < a + x := add_pos ha hx
  have htheta_at : ContinuousAt theta (a + x) :=
    (hasDerivAt_of_pos_of_hasDerivWithinAt_Ici
      hax (htheta_deriv (a + x) hax.le)).continuousAt
  have harg : ContinuousAt (fun z : ℝ × ℝ => z.1 + z.2) (a, x) :=
    continuousAt_fst.add continuousAt_snd
  have htheta_comp :
      ContinuousAt (fun z : ℝ × ℝ => theta (z.1 + z.2)) (a, x) := by
    exact Filter.Tendsto.comp htheta_at harg
  have hpow : ContinuousAt (fun z : ℝ × ℝ => z.2 ^ p) (a, x) :=
    continuousAt_snd.rpow_const (Or.inl hx.ne')
  have hMpair : ContinuousAt (fun z : ℝ × ℝ => M z.1) (a, x) := by
    exact ContinuousAt.comp' hMcont continuousAt_fst
  have hquot := (hpow.mul htheta_comp).div hMpair hMpos.ne'
  change ContinuousAt
    (fun z : ℝ × ℝ => z.2 ^ p * theta (z.1 + z.2) / M z.1) (a, x)
  simpa only [Pi.mul_apply, Pi.div_apply] using hquot

/-- At every interior shift `a>0`, the canonical quantile has the implicit
shift derivative

`Q'(a) = - A_{p,a}(Q(a)) / f_{p,a}(Q(a))`.

The proof uses one-dimensional mean value points between nearby quantiles,
quantile continuity, and joint continuity of the explicit density.  It does
not invoke a bivariate implicit-function theorem and therefore does not add a
continuity assumption on the full partial derivative field `A = ∂ₐF`. -/
theorem powerWeightedShiftQuantile_hasDerivAt_shift_within
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
    HasDerivAt
      (fun b : ℝ => powerWeightedShiftQuantile theta b p u)
      (-powerWeightedShiftCumulativeShiftNumerator theta S a p
          (powerWeightedShiftQuantile theta a p u) /
        powerWeightedShiftDensity theta a p
          (powerWeightedShiftQuantile theta a p u)) a := by
  let Q : ℝ → ℝ := fun b => powerWeightedShiftQuantile theta b p u
  let F : ℝ → ℝ → ℝ := fun b x => powerWeightedShiftCDF theta b p x
  let d : ℝ → ℝ → ℝ := fun b x => powerWeightedShiftDensity theta b p x
  let q : ℝ := Q a
  let A : ℝ := powerWeightedShiftCumulativeShiftNumerator theta S a p q

  have hQa := powerWeightedShiftQuantile_pos_and_CDF_eq_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p) (u := u)
    ha.le hp hu0 hu1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hqpos : 0 < q := by simpa [q, Q] using hQa.1
  have hFaq : F a q = u := by simpa [F, q, Q] using hQa.2

  have hQcont : ContinuousAt Q a := by
    simpa [Q] using powerWeightedShiftQuantile_continuousAt_shift_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (a := a) (p := p) (u := u)
      ha hp hu0 hu1 htheta_pos htheta_deriv htheta_int hS hSprime
      hSprime_pos hcurv

  have hshift : HasDerivAt (fun b : ℝ => F b q) A a := by
    simpa [F, A, q] using
      powerWeightedShiftCDF_hasDerivAt_within
        (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
        (a := a) (p := p) (x := q)
        ha hp hqpos htheta_pos htheta_deriv htheta_int hS hSprime
        hSprime_pos hcurv

  have hdjoint : ContinuousAt (fun z : ℝ × ℝ => d z.1 z.2) (a, q) := by
    simpa [d] using powerWeightedShiftDensity_continuousAt_prod_within
      (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
      (a := a) (p := p) (x := q)
      ha hp hqpos htheta_pos htheta_deriv htheta_int hS hSprime
      hSprime_pos hcurv
  have hdaqpos : 0 < d a q := by
    simpa [d] using powerWeightedShiftDensity_pos_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (x := q)
      ha.le hp hqpos htheta_pos htheta_deriv htheta_int hS hSprime_pos

  have hsec : ∀ b : ℝ, 0 < b → ∃ c : ℝ,
      c ∈ [[q, Q b]] ∧
        d b c * (Q b - q) = F b (Q b) - F b q := by
    intro b hb
    have hQb := powerWeightedShiftQuantile_pos_and_CDF_eq_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := b) (p := p) (u := u)
      hb.le hp hu0 hu1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
    have hQbpos : 0 < Q b := by simpa [Q] using hQb.1
    by_cases heq : Q b = q
    · refine ⟨q, left_mem_uIcc, ?_⟩
      simp [heq]
    · rcases lt_or_gt_of_ne heq with hlt | hgt
      · have hcont : ContinuousOn (F b) (Set.Icc (Q b) q) := by
          intro x hx
          have hxpos : 0 < x := hQbpos.trans_le hx.1
          exact (powerWeightedShiftCDF_hasDerivAt_x_within
            (theta := theta) (S := S) (Sprime := Sprime)
            (a := b) (p := p) (x := x)
            hb.le hp hxpos htheta_pos htheta_deriv htheta_int hS hSprime_pos).continuousAt.continuousWithinAt
        have hder : ∀ x ∈ Set.Ioo (Q b) q, HasDerivAt (F b) (d b x) x := by
          intro x hx
          have hxpos : 0 < x := hQbpos.trans hx.1
          simpa [F, d] using powerWeightedShiftCDF_hasDerivAt_x_within
            (theta := theta) (S := S) (Sprime := Sprime)
            (a := b) (p := p) (x := x)
            hb.le hp hxpos htheta_pos htheta_deriv htheta_int hS hSprime_pos
        rcases exists_hasDerivAt_eq_slope (F b) (d b) hlt hcont hder with
          ⟨c, hc, hcder⟩
        refine ⟨c, ?_, ?_⟩
        · rw [uIcc_of_ge hlt.le]
          exact ⟨hc.1.le, hc.2.le⟩
        · have hden : q - Q b ≠ 0 := sub_ne_zero.mpr hlt.ne'
          have hm : d b c * (q - Q b) = F b q - F b (Q b) :=
            (eq_div_iff hden).mp hcder
          linarith
      · have hcont : ContinuousOn (F b) (Set.Icc q (Q b)) := by
          intro x hx
          have hxpos : 0 < x := hqpos.trans_le hx.1
          exact (powerWeightedShiftCDF_hasDerivAt_x_within
            (theta := theta) (S := S) (Sprime := Sprime)
            (a := b) (p := p) (x := x)
            hb.le hp hxpos htheta_pos htheta_deriv htheta_int hS hSprime_pos).continuousAt.continuousWithinAt
        have hder : ∀ x ∈ Set.Ioo q (Q b), HasDerivAt (F b) (d b x) x := by
          intro x hx
          have hxpos : 0 < x := hqpos.trans hx.1
          simpa [F, d] using powerWeightedShiftCDF_hasDerivAt_x_within
            (theta := theta) (S := S) (Sprime := Sprime)
            (a := b) (p := p) (x := x)
            hb.le hp hxpos htheta_pos htheta_deriv htheta_int hS hSprime_pos
        rcases exists_hasDerivAt_eq_slope (F b) (d b) hgt hcont hder with
          ⟨c, hc, hcder⟩
        refine ⟨c, ?_, ?_⟩
        · rw [uIcc_of_le hgt.le]
          exact ⟨hc.1.le, hc.2.le⟩
        · have hden : Q b - q ≠ 0 := sub_ne_zero.mpr hgt.ne'
          exact (eq_div_iff hden).mp hcder

  have hsecAll : ∀ b : ℝ, ∃ c : ℝ, 0 < b →
      c ∈ [[q, Q b]] ∧ d b c * (Q b - q) = F b (Q b) - F b q := by
    intro b
    by_cases hb : 0 < b
    · rcases hsec b hb with ⟨c, hc⟩
      exact ⟨c, fun _ => hc⟩
    · exact ⟨q, fun hb' => (hb hb').elim⟩
  choose c hc using hsecAll

  have hc_tend : Tendsto c (𝓝 a) (𝓝 q) := by
    have hconstq : Tendsto (fun _ : ℝ => q) (𝓝 a) (𝓝 q) := tendsto_const_nhds
    have hmin : Tendsto (fun b : ℝ => min q (Q b)) (𝓝 a) (𝓝 q) := by
      have h := hconstq.min hQcont
      simpa [q] using h
    have hmax : Tendsto (fun b : ℝ => max q (Q b)) (𝓝 a) (𝓝 q) := by
      have h := hconstq.max hQcont
      simpa [q] using h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hmin hmax
    · filter_upwards [Ioi_mem_nhds ha] with b hb
      have hcb := (hc b hb).1
      change min q (Q b) ≤ c b ∧ c b ≤ max q (Q b) at hcb
      exact hcb.1
    · filter_upwards [Ioi_mem_nhds ha] with b hb
      have hcb := (hc b hb).1
      change min q (Q b) ≤ c b ∧ c b ≤ max q (Q b) at hcb
      exact hcb.2

  have hdpair : Tendsto (fun b : ℝ => d b (c b)) (𝓝 a) (𝓝 (d a q)) := by
    have hpair : Tendsto (fun b : ℝ => (b, c b)) (𝓝 a) (𝓝 (a, q)) :=
      tendsto_id.prodMk_nhds hc_tend
    exact Filter.Tendsto.comp hdjoint hpair

  have hslope_eq :
      (slope Q a) =ᶠ[𝓝[≠] a]
        (fun b : ℝ => -(slope (fun y : ℝ => F y q) a b) / d b (c b)) := by
    have hbpos : ∀ᶠ b : ℝ in 𝓝[≠] a, 0 < b :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ha)
    have hbne : ∀ᶠ b : ℝ in 𝓝[≠] a, b ≠ a := by
      filter_upwards [self_mem_nhdsWithin] with b hb
      simpa using hb
    filter_upwards [hbpos, hbne] with b hb hba
    have hQb := powerWeightedShiftQuantile_pos_and_CDF_eq_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := b) (p := p) (u := u)
      hb.le hp hu0 hu1 htheta_pos htheta_deriv htheta_int hS hSprime_pos
    have hQbpos : 0 < Q b := by simpa [Q] using hQb.1
    have hcb := hc b hb
    have hcpos : 0 < c b := by
      have hmem := hcb.1
      change min q (Q b) ≤ c b ∧ c b ≤ max q (Q b) at hmem
      exact (lt_min hqpos hQbpos).trans_le hmem.1
    have hdbpos : 0 < d b (c b) := by
      simpa [d] using powerWeightedShiftDensity_pos_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := b) (p := p) (x := c b)
        hb.le hp hcpos htheta_pos htheta_deriv htheta_int hS hSprime_pos
    have hFbQ : F b (Q b) = u := by simpa [F, Q] using hQb.2
    have hsec_eq := hcb.2
    rw [hFbQ, ← hFaq] at hsec_eq
    rw [slope_def_field, slope_def_field]
    have hsub : b - a ≠ 0 := sub_ne_zero.mpr hba
    field_simp [hsub, hdbpos.ne']
    linarith

  have hnum_tend :
      Tendsto (fun b : ℝ => -(slope (fun y : ℝ => F y q) a b))
        (𝓝[≠] a) (𝓝 (-A)) :=
    hshift.tendsto_slope.neg
  have hden_tend :
      Tendsto (fun b : ℝ => d b (c b)) (𝓝[≠] a) (𝓝 (d a q)) :=
    hdpair.mono_left inf_le_left
  have hquot :
      Tendsto
        (fun b : ℝ => -(slope (fun y : ℝ => F y q) a b) / d b (c b))
        (𝓝[≠] a) (𝓝 ((-A) / d a q)) :=
    hnum_tend.div hden_tend hdaqpos.ne'
  have hQslope : Tendsto (slope Q a) (𝓝[≠] a) (𝓝 ((-A) / d a q)) :=
    hquot.congr' hslope_eq.symm
  have hQderiv : HasDerivAt Q ((-A) / d a q) a :=
    (hasDerivAt_iff_tendsto_slope).2 hQslope

  simpa [Q, A, d, q, neg_div] using hQderiv

end ScoreCurvatureStarOrder
