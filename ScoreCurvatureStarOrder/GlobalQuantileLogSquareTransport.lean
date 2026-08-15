import Mathlib
import ScoreCurvatureStarOrder.QuantileLogSquareTransport
import ScoreCurvatureStarOrder.LogDensityIntegrability

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- Technical package for the global squared-log quantile transport.

The proof exhausts both the probability interval `(0,1)` and the spatial half-line
`(0,∞)` by matching CDF windows.  The square is treated first because it is
nonnegative: convergence of its window integrals gives integrability on `(0,1)`
without assuming that integrability in advance. -/
private theorem powerWeightedShift_logQuantile_sq_transport_package_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    IntegrableOn
        (fun u : ℝ => (Real.log (powerWeightedShiftQuantile theta a p u)) ^ 2)
        (Set.Ioo (0 : ℝ) 1) ∧
      (∫ u : ℝ in Set.Ioo (0 : ℝ) 1,
          (Real.log (powerWeightedShiftQuantile theta a p u)) ^ 2) =
        ∫ x : ℝ in Set.Ioi (0 : ℝ),
          (Real.log x) ^ 2 * powerWeightedShiftDensity theta a p x := by
  let F : ℝ → ℝ := fun x => powerWeightedShiftCDF theta a p x
  let Q : ℝ → ℝ := fun u => powerWeightedShiftQuantile theta a p u
  let phi : ℝ → ℝ := fun u => (Real.log (Q u)) ^ 2
  let g : ℝ → ℝ := fun x =>
    (Real.log x) ^ 2 * powerWeightedShiftDensity theta a p x

  -- A single cofinal family with positive finite endpoints.
  let c : ℕ → ℝ := fun n => (n : ℝ) + 2
  let eps : ℕ → ℝ := fun n => 1 / c n
  let R : ℕ → ℝ := c

  have hc_pos (n : ℕ) : 0 < c n := by
    dsimp [c]
    positivity
  have hR_pos (n : ℕ) : 0 < R n := by
    simpa [R] using hc_pos n
  have heps_pos (n : ℕ) : 0 < eps n := by
    dsimp [eps]
    exact div_pos zero_lt_one (hc_pos n)
  have heps_R (n : ℕ) : eps n < R n := by
    have hc2 : 2 ≤ c n := by
      dsimp [c]
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    dsimp [eps, R]
    rw [div_lt_iff₀ (hc_pos n)]
    nlinarith
  have hc_top : Tendsto c atTop atTop := by
    simpa [c] using
      (tendsto_atTop_add_const_right atTop (2 : ℝ)
        (tendsto_natCast_atTop_atTop :
          Tendsto ((↑) : ℕ → ℝ) atTop atTop))
  have hR_top : Tendsto R atTop atTop := by
    simpa [R] using hc_top
  have heps_zero : Tendsto eps atTop (𝓝 0) := by
    simpa [eps, one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hc_top)
  have heps_le_one (n : ℕ) : eps n ≤ 1 := by
    have hc1 : 1 ≤ c n := by
      dsimp [c]
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    dsimp [eps]
    rw [div_le_iff₀ (hc_pos n)]
    simpa using hc1
  have heps_Icc (n : ℕ) : eps n ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(heps_pos n).le, heps_le_one n⟩

  -- The CDF endpoints of these windows tend to 0 and 1.
  have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    simpa [F] using
      (powerWeightedShiftCDF_continuousOn_Icc_zero_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p) (b := (1 : ℝ))
        ha hp zero_le_one htheta_pos htheta_deriv htheta_int hS hSprime_pos)
  have heps_within :
      Tendsto eps atTop (𝓝[Set.Icc (0 : ℝ) 1] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      eps heps_zero (Eventually.of_forall heps_Icc)
  have hF_left : Tendsto (fun n : ℕ => F (eps n)) atTop (𝓝 0) := by
    have h :=
      (hFcont (0 : ℝ) ⟨le_rfl, zero_le_one⟩).tendsto.comp heps_within
    simpa [F, Function.comp_def] using h
  have hF_atTop : Tendsto F atTop (𝓝 1) := by
    simpa [F] using
      (powerWeightedShiftCDF_tendsto_one_atTop_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)
  have hF_right : Tendsto (fun n : ℕ => F (R n)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using hF_atTop.comp hR_top

  have hF_strict : StrictMonoOn F (Set.Ioi (0 : ℝ)) := by
    simpa [F] using
      (powerWeightedShiftCDF_strictMonoOn_Ioi_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)
  have hF_eps (n : ℕ) : F (eps n) ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [F] using
      (powerWeightedShiftCDF_pos_lt_one_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p) (x := eps n)
        ha hp (heps_pos n) htheta_pos htheta_deriv htheta_int hS hSprime_pos)
  have hF_R (n : ℕ) : F (R n) ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [F] using
      (powerWeightedShiftCDF_pos_lt_one_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p) (x := R n)
        ha hp (hR_pos n) htheta_pos htheta_deriv htheta_int hS hSprime_pos)
  have hF_order (n : ℕ) : F (eps n) < F (R n) :=
    hF_strict (heps_pos n) (hR_pos n) (heps_R n)
  have hQwindow_subset (n : ℕ) :
      Set.Ioc (F (eps n)) (F (R n)) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro u hu
    exact ⟨(hF_eps n).1.trans hu.1, hu.2.trans_lt (hF_R n).2⟩

  -- The squared log-quantile is continuous, hence integrable, on every window.
  have hQcont : ContinuousOn Q (Set.Ioo (0 : ℝ) 1) := by
    simpa [Q] using
      (powerWeightedShiftQuantile_continuousOn_Ioo_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)
  have hQne : ∀ u ∈ Set.Ioo (0 : ℝ) 1, Q u ≠ 0 := by
    intro u hu
    have hQu := powerWeightedShiftQuantile_pos_and_CDF_eq_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (u := u)
      ha hp hu.1 hu.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos
    simpa [Q] using hQu.1.ne'
  have hlogQcont :
      ContinuousOn (fun u : ℝ => Real.log (Q u)) (Set.Ioo (0 : ℝ) 1) :=
    hQcont.log hQne
  have hphi_cont : ContinuousOn phi (Set.Ioo (0 : ℝ) 1) := by
    simpa only [phi, pow_two] using hlogQcont.mul hlogQcont
  have hphi_window_integrable :
      ∀ n : ℕ,
        IntegrableOn phi (Set.Ioc (F (eps n)) (F (R n)))
          (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    intro n
    have hsubIcc :
        Set.Icc (F (eps n)) (F (R n)) ⊆ Set.Ioo (0 : ℝ) 1 := by
      intro u hu
      exact ⟨(hF_eps n).1.trans_le hu.1, hu.2.trans_lt (hF_R n).2⟩
    have hcontIcc : ContinuousOn phi (Set.Icc (F (eps n)) (F (R n))) :=
      hphi_cont.mono hsubIcc
    have hvol :
        IntegrableOn phi (Set.Icc (F (eps n)) (F (R n))) :=
      hcontIcc.integrableOn_compact isCompact_Icc
    exact (hvol.mono_set Set.Ioc_subset_Icc_self).restrict

  -- On the spatial side the already verified L²-density integrability gives a
  -- convergent exhaustion by the matching `(eps n, R n]` windows.
  have hg_integrable : IntegrableOn g (Set.Ioi (0 : ℝ)) := by
    simpa [g] using
      (powerWeightedShift_log_sq_density_integrableOn_Ioi_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p)
        ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos)
  have hXcover :
      AECover (volume.restrict (Set.Ioi (0 : ℝ))) (atTop : Filter ℕ)
        (fun n : ℕ => Set.Ioc (eps n) (R n)) := by
    refine MeasureTheory.aecover_restrict_of_ae_imp
      (μ := volume) (l := (atTop : Filter ℕ))
      (s := Set.Ioi (0 : ℝ))
      (φ := fun n : ℕ => Set.Ioc (eps n) (R n))
      measurableSet_Ioi ?_ ?_
    · filter_upwards with x
      intro hx
      have hxpos : (0 : ℝ) < x := hx
      have hlo : ∀ᶠ n : ℕ in atTop, eps n < x :=
        heps_zero.eventually (Iio_mem_nhds hxpos)
      have hhi : ∀ᶠ n : ℕ in atTop, x ≤ R n :=
        hR_top.eventually (eventually_ge_atTop x)
      filter_upwards [hlo, hhi] with n hnlo hnhi
      exact ⟨hnlo, hnhi⟩
    · intro n
      exact measurableSet_Ioc
  have hXset_tendsto :=
    hXcover.integral_tendsto_of_countably_generated hg_integrable
  have hXwindow_subset (n : ℕ) :
      Set.Ioc (eps n) (R n) ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact (heps_pos n).trans hx.1
  have hDensity_window_tendsto :
      Tendsto
        (fun n : ℕ => ∫ x : ℝ in eps n..R n, g x)
        atTop
        (𝓝 (∫ x : ℝ in Set.Ioi (0 : ℝ), g x)) := by
    refine hXset_tendsto.congr' ?_
    filter_upwards with n
    rw [Measure.restrict_restrict_of_subset (hXwindow_subset n)]
    exact (intervalIntegral.integral_of_le (heps_R n).le).symm

  have htransport (n : ℕ) :
      (∫ u : ℝ in F (eps n)..F (R n), phi u) =
        ∫ x : ℝ in eps n..R n, g x := by
    simpa [F, Q, phi, g] using
      (powerWeightedShift_logQuantile_sq_integral_CDF_window_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (p := p) (ε := eps n) (R := R n)
        ha hp (heps_pos n) (heps_R n)
        htheta_pos htheta_deriv htheta_int hS hSprime_pos)

  have hQwindow_eq (n : ℕ) :
      (∫ u : ℝ in Set.Ioc (F (eps n)) (F (R n)), phi u
          ∂(volume.restrict (Set.Ioo (0 : ℝ) 1))) =
        ∫ x : ℝ in eps n..R n, g x := by
    rw [Measure.restrict_restrict_of_subset (hQwindow_subset n)]
    rw [← intervalIntegral.integral_of_le (hF_order n).le]
    exact htransport n

  have hQwindow_norm_eq (n : ℕ) :
      (∫ u : ℝ in Set.Ioc (F (eps n)) (F (R n)), ‖phi u‖
          ∂(volume.restrict (Set.Ioo (0 : ℝ) 1))) =
        ∫ x : ℝ in eps n..R n, g x := by
    rw [Measure.restrict_restrict_of_subset (hQwindow_subset n)]
    rw [← intervalIntegral.integral_of_le (hF_order n).le]
    simp only [phi, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact htransport n

  -- This is the non-circular step: finite window identities plus the spatial
  -- L² bound force integrability of `(log Q)^2` on the whole probability interval.
  have hQnorm_tendsto :
      Tendsto
        (fun n : ℕ =>
          ∫ u : ℝ in Set.Ioc (F (eps n)) (F (R n)), ‖phi u‖
            ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)))
        atTop
        (𝓝 (∫ x : ℝ in Set.Ioi (0 : ℝ), g x)) := by
    refine hDensity_window_tendsto.congr' ?_
    exact Eventually.of_forall fun n => (hQwindow_norm_eq n).symm

  have hQcover :
      AECover (volume.restrict (Set.Ioo (0 : ℝ) 1)) (atTop : Filter ℕ)
        (fun n : ℕ => Set.Ioc (F (eps n)) (F (R n))) :=
    MeasureTheory.aecover_Ioo_of_Ioc
      (μ := volume) (l := (atTop : Filter ℕ))
      (A := (0 : ℝ)) (B := (1 : ℝ)) hF_left hF_right
  have hphi_integrable_restrict :
      Integrable phi (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    hQcover.integrable_of_integral_norm_tendsto
      (∫ x : ℝ in Set.Ioi (0 : ℝ), g x)
      hphi_window_integrable hQnorm_tendsto
  have hphi_integrable : IntegrableOn phi (Set.Ioo (0 : ℝ) 1) :=
    hphi_integrable_restrict

  -- Once integrability is established, the same AE-cover gives the proper
  -- global integral, and uniqueness of limits identifies it with the spatial
  -- second log moment.
  have hQwindow_tendsto_global :=
    hQcover.integral_tendsto_of_countably_generated hphi_integrable_restrict
  have hQwindow_tendsto_density :
      Tendsto
        (fun n : ℕ =>
          ∫ u : ℝ in Set.Ioc (F (eps n)) (F (R n)), phi u
            ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)))
        atTop
        (𝓝 (∫ x : ℝ in Set.Ioi (0 : ℝ), g x)) := by
    refine hDensity_window_tendsto.congr' ?_
    exact Eventually.of_forall fun n => (hQwindow_eq n).symm
  have hglobal :
      (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, phi u) =
        ∫ x : ℝ in Set.Ioi (0 : ℝ), g x := by
    exact tendsto_nhds_unique hQwindow_tendsto_global hQwindow_tendsto_density

  constructor
  · simpa [Q, phi] using hphi_integrable
  · simpa [Q, phi, g] using hglobal

/-- The squared logarithm of the canonical quantile is integrable on `(0,1)`.

This is the L² input needed for the quantile-variance and covariance stages of
the manuscript proof. -/
theorem powerWeightedShift_logQuantile_sq_integrableOn_Ioo_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    IntegrableOn
      (fun u : ℝ => (Real.log (powerWeightedShiftQuantile theta a p u)) ^ 2)
      (Set.Ioo (0 : ℝ) 1) :=
  (powerWeightedShift_logQuantile_sq_transport_package_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p)
    ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos).1

/-- Global second-log-moment transport by the canonical quantile.

`∫₀¹ (log Q_{p,a}(u))² du` equals the second logarithmic moment of the
normalized power-weighted shifted density on `(0,∞)`. -/
theorem powerWeightedShift_logQuantile_sq_integral_Ioo_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    (∫ u : ℝ in Set.Ioo (0 : ℝ) 1,
        (Real.log (powerWeightedShiftQuantile theta a p u)) ^ 2) =
      ∫ x : ℝ in Set.Ioi (0 : ℝ),
        (Real.log x) ^ 2 * powerWeightedShiftDensity theta a p x :=
  (powerWeightedShift_logQuantile_sq_transport_package_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p)
    ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos).2

end ScoreCurvatureStarOrder
