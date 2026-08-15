import Mathlib
import ScoreCurvatureStarOrder.Moments
import ScoreCurvatureStarOrder.HalfLineRegularity

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Topology Interval

/-- The normalization moment is right-continuous at the boundary shift `a = 0`.

The proof uses dominated convergence on the natural filter `𝓝[Set.Ici 0] 0`.
Near the spatial origin, continuity of `theta` on a compact interval gives a
uniform bound by a constant multiple of `x^p`; in the tail, the already proved
exponential estimate gives a uniform multiple of `x^p * exp (-c*x)` for all
nonnegative shifts.  Thus no two-sided derivative in the shift parameter at
`0` is introduced. -/
theorem powerWeightedShiftMoment_continuousWithinAt_zero_within
    {theta S Sprime : ℝ → ℝ} {p : ℝ}
    (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    ContinuousWithinAt
      (fun a : ℝ => powerWeightedShiftMoment theta a p)
      (Set.Ici (0 : ℝ)) 0 := by
  rcases automatic_positive_score_and_exponential_tail_within
      htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨R, c, hR, hc, _hS_lower, htail⟩

  let B : ℝ := max R 1
  have hRB : R ≤ B := le_max_left R 1
  have h1B : 1 ≤ B := le_max_right R 1
  have hB0 : 0 ≤ B := zero_le_one.trans h1B
  have hB1 : 0 ≤ B + 1 := by linarith

  have htheta_cont_Ici : ContinuousOn theta (Set.Ici (0 : ℝ)) :=
    continuousOn_Ici_of_hasDerivWithinAt htheta_deriv
  have htheta_cont_compact : ContinuousOn theta (Set.Icc (0 : ℝ) (B + 1)) :=
    htheta_cont_Ici.mono (by
      intro z hz
      exact hz.1)
  rcases isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.mpr hB1) htheta_cont_compact with
    ⟨zmax, hzmax, hzmaximal⟩
  let C : ℝ := theta zmax
  have hCpos : 0 < C := by
    dsimp [C]
    exact htheta_pos zmax hzmax.1

  let K : ℝ := theta R * Real.exp (c * R)
  have hKpos : 0 < K := by
    dsimp [K]
    exact mul_pos (htheta_pos R hR) (Real.exp_pos _)

  let bound : ℝ → ℝ := fun x =>
    if x ≤ B then C * x ^ p else K * (x ^ p * Real.exp (-c * x))

  have hbound_set : IntegrableOn bound (Set.Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi hB0, integrableOn_union]
    constructor
    · have hpow : IntegrableOn (fun x : ℝ => x ^ p) (Set.Ioc 0 B) := by
        rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hB0]
        exact intervalIntegral.intervalIntegrable_rpow' hp
      have hlocal : IntegrableOn (fun x : ℝ => C * x ^ p) (Set.Ioc 0 B) :=
        hpow.const_mul C
      refine IntegrableOn.congr_fun hlocal ?_ measurableSet_Ioc
      intro x hx
      simp [bound, hx.2]
    · have hbase :
          IntegrableOn (fun x : ℝ => x ^ p * Real.exp (-c * x))
            (Set.Ioi (0 : ℝ)) :=
        rpow_mul_exp_neg_integrableOn_Ioi hp hc
      have hbaseB :
          IntegrableOn (fun x : ℝ => x ^ p * Real.exp (-c * x))
            (Set.Ioi B) :=
        hbase.mono_set (fun x hx => hB0.trans_lt hx)
      have htail_int :
          IntegrableOn
            (fun x : ℝ => K * (x ^ p * Real.exp (-c * x)))
            (Set.Ioi B) :=
        hbaseB.const_mul K
      refine IntegrableOn.congr_fun htail_int ?_ measurableSet_Ioi
      intro x hx
      have hxnot : ¬ x ≤ B := not_le.mpr hx
      simp [bound, hxnot]

  let F : ℝ → ℝ → ℝ := fun a x => x ^ p * theta (a + x)

  have hparam :
      ∀ᶠ a : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0, a ∈ Set.Icc (0 : ℝ) 1 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with a ha1 ha0
    exact ⟨ha0, ha1.le⟩

  have hF_meas :
      ∀ᶠ a : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0,
        AEStronglyMeasurable (F a) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    filter_upwards [hparam] with a ha
    have hint := powerWeightedShift_integrableOn_Ioi_within
      (theta := theta) (S := S) (Sprime := Sprime) (a := a) (p := p)
      ha.1 hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [F] using hint.aestronglyMeasurable

  have h_bound :
      ∀ᶠ a : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0,
        ∀ᵐ x ∂volume.restrict (Set.Ioi (0 : ℝ)), ‖F a x‖ ≤ bound x := by
    filter_upwards [hparam] with a ha
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have ha0 : 0 ≤ a := ha.1
    have ha1 : a ≤ 1 := ha.2
    have hx0 : 0 < x := hx
    have hxpow : 0 ≤ x ^ p := Real.rpow_nonneg hx0.le p
    have hax0 : 0 ≤ a + x := add_nonneg ha0 hx0.le
    have hFnonneg : 0 ≤ F a x := by
      dsimp [F]
      exact mul_nonneg hxpow (htheta_pos (a + x) hax0).le
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg hFnonneg]
    by_cases hxB : x ≤ B
    · have haxB1 : a + x ≤ B + 1 := by linarith
      have htheta_le : theta (a + x) ≤ C := by
        dsimp [C]
        exact hzmaximal ⟨hax0, haxB1⟩
      calc
        F a x = x ^ p * theta (a + x) := by rfl
        _ ≤ x ^ p * C := mul_le_mul_of_nonneg_left htheta_le hxpow
        _ = bound x := by simp [bound, hxB]; ring
    · have hBx : B < x := lt_of_not_ge hxB
      have hRx : R ≤ x := hRB.trans hBx.le
      have hRax : R ≤ a + x := by linarith
      have htheta_tail :
          theta (a + x) ≤ theta R * Real.exp (-c * ((a + x) - R)) :=
        htail (a + x) hRax
      have hexp_le :
          Real.exp (-c * ((a + x) - R)) ≤
            Real.exp (c * R) * Real.exp (-c * x) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hca : 0 ≤ c * a := mul_nonneg hc.le ha0
        nlinarith
      have htheta_bound : theta (a + x) ≤ K * Real.exp (-c * x) := by
        dsimp [K]
        calc
          theta (a + x) ≤ theta R * Real.exp (-c * ((a + x) - R)) := htheta_tail
          _ ≤ theta R * (Real.exp (c * R) * Real.exp (-c * x)) :=
            mul_le_mul_of_nonneg_left hexp_le (htheta_pos R hR).le
          _ = (theta R * Real.exp (c * R)) * Real.exp (-c * x) := by ring
      calc
        F a x = x ^ p * theta (a + x) := by rfl
        _ ≤ x ^ p * (K * Real.exp (-c * x)) :=
          mul_le_mul_of_nonneg_left htheta_bound hxpow
        _ = bound x := by simp [bound, hxB]; ring

  have h_lim :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (0 : ℝ)),
        Tendsto (fun a : ℝ => F a x) (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 (F 0 x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := hx
    have hxI : x ∈ Set.Ici (0 : ℝ) := hxpos.le
    have htheta_at : ContinuousAt theta x :=
      (hasDerivAt_of_pos_of_hasDerivWithinAt_Ici
        hxpos (htheta_deriv x hxI)).continuousAt
    have harg_full : Tendsto (fun a : ℝ => a + x) (𝓝 (0 : ℝ)) (𝓝 x) := by
      have hcont : ContinuousAt (fun a : ℝ => a + x) 0 := by fun_prop
      simpa using hcont.tendsto
    have harg :
        Tendsto (fun a : ℝ => a + x) (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 x) :=
      harg_full.mono_left nhdsWithin_le_nhds
    have htheta_lim :
        Tendsto (fun a : ℝ => theta (a + x))
          (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 (theta x)) :=
      htheta_at.tendsto.comp harg
    have hprod := tendsto_const_nhds.mul htheta_lim
    simpa [F] using hprod

  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := F)
    (f := F 0)
    (l := 𝓝[Set.Ici (0 : ℝ)] 0)
    bound hF_meas h_bound hbound_set h_lim

  change Tendsto
    (fun a : ℝ => powerWeightedShiftMoment theta a p)
    (𝓝[Set.Ici (0 : ℝ)] 0)
    (𝓝 (powerWeightedShiftMoment theta 0 p))
  simpa [powerWeightedShiftMoment, F] using hDCT

end ScoreCurvatureStarOrder
