import Mathlib
import Mathlib.Analysis.MellinTransform
import ScoreCurvatureStarOrder.ShiftKernelAsymptotics

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter Asymptotics
open scoped Topology

/-- For every `p > -1` and every nonnegative shift, the first logarithmic
power-weighted moment is absolutely integrable:

`∫ x^p log(x) theta(a+x) dx`.

The proof uses mathlib's Mellin-transform convergence criterion.  The shifted
kernel is locally integrable, `O(1)` at `0+`, and decays faster than every
reciprocal power at `+∞`; multiplying once by `log x` only consumes an
arbitrarily small amount of power at either endpoint. -/
theorem powerWeightedShift_log_integrableOn_Ioi_within
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
      (fun x : ℝ => x ^ p * Real.log x * theta (a + x))
      (Set.Ioi (0 : ℝ)) := by
  let f : ℝ → ℝ := fun x => theta (a + x)
  let d : ℝ := (p + 1) / 2
  have hd0 : 0 < d := by
    dsimp [d]
    linarith
  have hds : d < p + 1 := by
    dsimp [d]
    linarith

  have hfc : LocallyIntegrableOn f (Set.Ioi (0 : ℝ)) := by
    simpa [f] using
      (shiftedTheta_locallyIntegrableOn_Ioi_within
        (theta := theta) (S := S) (a := a) ha htheta_deriv)

  have htop0 :
      f =O[atTop] (fun x : ℝ => x ^ (-(p + 3))) := by
    simpa [f] using
      (shiftedTheta_isBigO_rpow_atTop_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (A := p + 3)
        ha htheta_pos htheta_deriv htheta_int hS hSprime_pos)
  have htop :
      (fun x : ℝ => Real.log x * f x) =O[atTop]
        (fun x : ℝ => x ^ (-(p + 2))) := by
    simpa [smul_eq_mul] using
      (isBigO_rpow_top_log_smul
        (E := ℝ) (a := p + 3) (b := p + 2)
        (f := f) (by linarith) htop0)

  have hbot0 :
      f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    simpa [f] using
      (shiftedTheta_isBigO_one_nhdsGT_zero_within
        (theta := theta) (S := S) (a := a) ha htheta_deriv)
  have hbot :
      (fun x : ℝ => Real.log x * f x) =O[𝓝[>] (0 : ℝ)]
        (fun x : ℝ => x ^ (-d)) := by
    simpa [smul_eq_mul] using
      (isBigO_rpow_zero_log_smul
        (E := ℝ) (a := 0) (b := d)
        (f := f) hd0 hbot0)

  have hlog_local :
      LocallyIntegrableOn (fun x : ℝ => Real.log x * f x) (Set.Ioi (0 : ℝ)) := by
    have hlog_cont : ContinuousOn Real.log (Set.Ioi (0 : ℝ)) :=
      Real.continuousOn_log.mono
        (subset_compl_singleton_iff.mpr self_notMem_Ioi)
    exact hfc.continuousOn_mul hlog_cont isOpen_Ioi.isLocallyClosed

  have hint := mellin_convergent_of_isBigO_scalar
    (a := p + 2) (b := d) (s := p + 1)
    hlog_local htop (by linarith) hbot hds
  simpa [f, mul_assoc] using hint

/-- For every `p > -1` and every nonnegative shift, the second logarithmic
power-weighted moment is absolutely integrable:

`∫ x^p (log x)^2 theta(a+x) dx`.

This is the endpoint control needed for the second derivative in the power
parameter.  It is obtained by applying the same Mellin asymptotic loss twice. -/
theorem powerWeightedShift_log_sq_integrableOn_Ioi_within
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
      (fun x : ℝ => x ^ p * (Real.log x) ^ 2 * theta (a + x))
      (Set.Ioi (0 : ℝ)) := by
  let f : ℝ → ℝ := fun x => theta (a + x)
  let g : ℝ → ℝ := fun x => Real.log x * f x
  let d1 : ℝ := (p + 1) / 3
  let d2 : ℝ := 2 * (p + 1) / 3

  have hd10 : 0 < d1 := by
    dsimp [d1]
    linarith
  have hd12 : d1 < d2 := by
    dsimp [d1, d2]
    linarith
  have hd2s : d2 < p + 1 := by
    dsimp [d2]
    linarith

  have hfc : LocallyIntegrableOn f (Set.Ioi (0 : ℝ)) := by
    simpa [f] using
      (shiftedTheta_locallyIntegrableOn_Ioi_within
        (theta := theta) (S := S) (a := a) ha htheta_deriv)
  have hlog_cont : ContinuousOn Real.log (Set.Ioi (0 : ℝ)) :=
    Real.continuousOn_log.mono
      (subset_compl_singleton_iff.mpr self_notMem_Ioi)
  have hg_local : LocallyIntegrableOn g (Set.Ioi (0 : ℝ)) := by
    simpa [g] using hfc.continuousOn_mul hlog_cont isOpen_Ioi.isLocallyClosed
  have hlogg_local :
      LocallyIntegrableOn (fun x : ℝ => Real.log x * g x) (Set.Ioi (0 : ℝ)) := by
    exact hg_local.continuousOn_mul hlog_cont isOpen_Ioi.isLocallyClosed

  have htop0 :
      f =O[atTop] (fun x : ℝ => x ^ (-(p + 4))) := by
    simpa [f] using
      (shiftedTheta_isBigO_rpow_atTop_within
        (theta := theta) (S := S) (Sprime := Sprime)
        (a := a) (A := p + 4)
        ha htheta_pos htheta_deriv htheta_int hS hSprime_pos)
  have htop1 :
      g =O[atTop] (fun x : ℝ => x ^ (-(p + 3))) := by
    simpa [g, smul_eq_mul] using
      (isBigO_rpow_top_log_smul
        (E := ℝ) (a := p + 4) (b := p + 3)
        (f := f) (by linarith) htop0)
  have htop2 :
      (fun x : ℝ => Real.log x * g x) =O[atTop]
        (fun x : ℝ => x ^ (-(p + 2))) := by
    simpa [smul_eq_mul] using
      (isBigO_rpow_top_log_smul
        (E := ℝ) (a := p + 3) (b := p + 2)
        (f := g) (by linarith) htop1)

  have hbot0 :
      f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    simpa [f] using
      (shiftedTheta_isBigO_one_nhdsGT_zero_within
        (theta := theta) (S := S) (a := a) ha htheta_deriv)
  have hbot1 :
      g =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-d1)) := by
    simpa [g, smul_eq_mul] using
      (isBigO_rpow_zero_log_smul
        (E := ℝ) (a := 0) (b := d1)
        (f := f) hd10 hbot0)
  have hbot2 :
      (fun x : ℝ => Real.log x * g x) =O[𝓝[>] (0 : ℝ)]
        (fun x : ℝ => x ^ (-d2)) := by
    simpa [smul_eq_mul] using
      (isBigO_rpow_zero_log_smul
        (E := ℝ) (a := d1) (b := d2)
        (f := g) hd12 hbot1)

  have hint := mellin_convergent_of_isBigO_scalar
    (a := p + 2) (b := d2) (s := p + 1)
    hlogg_local htop2 (by linarith) hbot2 hd2s
  simpa [f, g, pow_two, mul_assoc] using hint

end ScoreCurvatureStarOrder
