import Mathlib

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter

/-- Covariance of two real-valued functions under the uniform probability
measure on `(0,1)`, written directly as `E[fg] - E[f]E[g]`.

The interval has Lebesgue mass one, so no normalization factor is needed. -/
noncomputable def unitIntervalCovariance (f g : ℝ → ℝ) : ℝ :=
  (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, f u * g u) -
    (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, f u) *
      (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, g u)

/-- Chebyshev's covariance inequality on the unit interval.

If `f` and `g` are nondecreasing on `(0,1)` and the first moments together
with the product are integrable, then their covariance is nonnegative.

The proof is deliberately manuscript-facing: for `x,y ∈ (0,1)`, monotonicity
gives

`(f x - f y) * (g x - g y) ≥ 0`.

We integrate this inequality first in `y` and then in `x`. Expanding the two
integrals yields twice `E[fg] - E[f]E[g]`, hence the desired sign. This avoids
introducing any auxiliary probability-space representation or hidden Fubini
argument. -/
theorem unitIntervalCovariance_nonneg_of_monotoneOn
    {f g : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Ioo (0 : ℝ) 1))
    (hg : IntegrableOn g (Set.Ioo (0 : ℝ) 1))
    (hfg : IntegrableOn (fun u : ℝ => f u * g u) (Set.Ioo (0 : ℝ) 1))
    (hfmono : MonotoneOn f (Set.Ioo (0 : ℝ) 1))
    (hgmono : MonotoneOn g (Set.Ioo (0 : ℝ) 1)) :
    0 ≤ unitIntervalCovariance f g := by
  let F : ℝ := ∫ u : ℝ in Set.Ioo (0 : ℝ) 1, f u
  let G : ℝ := ∫ u : ℝ in Set.Ioo (0 : ℝ) 1, g u
  let H : ℝ := ∫ u : ℝ in Set.Ioo (0 : ℝ) 1, f u * g u

  have hpair (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
      (y : ℝ) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
      0 ≤ (f x - f y) * (g x - g y) := by
    rcases le_total x y with hxy | hyx
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (hfmono hx hy hxy))
        (sub_nonpos.mpr (hgmono hx hy hxy))
    · exact mul_nonneg
        (sub_nonneg.mpr (hfmono hy hx hyx))
        (sub_nonneg.mpr (hgmono hy hx hyx))

  have hinner_nonneg (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
      0 ≤ ∫ y : ℝ in Set.Ioo (0 : ℝ) 1,
        (f x - f y) * (g x - g y) := by
    exact setIntegral_nonneg measurableSet_Ioo (fun y hy => hpair x hx y hy)

  have hinner_eq (x : ℝ) :
      (∫ y : ℝ in Set.Ioo (0 : ℝ) 1,
          (f x - f y) * (g x - g y)) =
        (f x * g x - f x * G) - (F * g x - H) := by
    have hconst :
        Integrable (fun _ : ℝ => f x * g x)
          (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
      integrable_const (f x * g x)
    have hfxg :
        Integrable (fun y : ℝ => f x * g y)
          (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
      hg.const_mul (f x)
    have hfgx :
        Integrable (fun y : ℝ => f y * g x)
          (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
      hf.mul_const (g x)
    calc
      (∫ y : ℝ in Set.Ioo (0 : ℝ) 1,
          (f x - f y) * (g x - g y)) =
          ∫ y : ℝ in Set.Ioo (0 : ℝ) 1,
            (f x * g x - f x * g y) - (f y * g x - f y * g y) := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun y => by ring)
      _ =
          (∫ y : ℝ in Set.Ioo (0 : ℝ) 1, f x * g x - f x * g y) -
            (∫ y : ℝ in Set.Ioo (0 : ℝ) 1, f y * g x - f y * g y) := by
        rw [integral_sub (hconst.sub hfxg) (hfgx.sub hfg)]
      _ =
          ((∫ y : ℝ in Set.Ioo (0 : ℝ) 1, f x * g x) -
              ∫ y : ℝ in Set.Ioo (0 : ℝ) 1, f x * g y) -
            ((∫ y : ℝ in Set.Ioo (0 : ℝ) 1, f y * g x) -
              ∫ y : ℝ in Set.Ioo (0 : ℝ) 1, f y * g y) := by
        rw [integral_sub hconst hfxg, integral_sub hfgx hfg]
      _ = (f x * g x - f x * G) - (F * g x - H) := by
        rw [setIntegral_const, integral_const_mul, integral_mul_const]
        simp [F, G, H, Real.volume_real_Ioo]

  have hpoint (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
      0 ≤ (f x * g x - f x * G) - (F * g x - H) := by
    rw [← hinner_eq x]
    exact hinner_nonneg x hx

  have houter_nonneg :
      0 ≤ ∫ x : ℝ in Set.Ioo (0 : ℝ) 1,
        (f x * g x - f x * G) - (F * g x - H) := by
    exact setIntegral_nonneg measurableSet_Ioo hpoint

  have hfG :
      Integrable (fun x : ℝ => f x * G)
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    hf.mul_const G
  have hFg :
      Integrable (fun x : ℝ => F * g x)
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    hg.const_mul F
  have hconstH :
      Integrable (fun _ : ℝ => H)
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    integrable_const H

  have houter_eq :
      (∫ x : ℝ in Set.Ioo (0 : ℝ) 1,
          (f x * g x - f x * G) - (F * g x - H)) =
        (H - F * G) - (F * G - H) := by
    calc
      (∫ x : ℝ in Set.Ioo (0 : ℝ) 1,
          (f x * g x - f x * G) - (F * g x - H)) =
          (∫ x : ℝ in Set.Ioo (0 : ℝ) 1, f x * g x - f x * G) -
            (∫ x : ℝ in Set.Ioo (0 : ℝ) 1, F * g x - H) := by
        rw [integral_sub (hfg.sub hfG) (hFg.sub hconstH)]
      _ =
          ((∫ x : ℝ in Set.Ioo (0 : ℝ) 1, f x * g x) -
              ∫ x : ℝ in Set.Ioo (0 : ℝ) 1, f x * G) -
            ((∫ x : ℝ in Set.Ioo (0 : ℝ) 1, F * g x) -
              ∫ x : ℝ in Set.Ioo (0 : ℝ) 1, H) := by
        rw [integral_sub hfg hfG, integral_sub hFg hconstH]
      _ = (H - F * G) - (F * G - H) := by
        rw [integral_mul_const, integral_const_mul, setIntegral_const]
        simp [F, G, H, Real.volume_real_Ioo]

  rw [houter_eq] at houter_nonneg
  have hcov : 0 ≤ H - F * G := by
    nlinarith
  simpa [unitIntervalCovariance, F, G, H] using hcov

/-- Equivalent product-integral form of the nonnegative covariance theorem. -/
theorem unitInterval_mul_integrals_le_integral_mul_of_monotoneOn
    {f g : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Ioo (0 : ℝ) 1))
    (hg : IntegrableOn g (Set.Ioo (0 : ℝ) 1))
    (hfg : IntegrableOn (fun u : ℝ => f u * g u) (Set.Ioo (0 : ℝ) 1))
    (hfmono : MonotoneOn f (Set.Ioo (0 : ℝ) 1))
    (hgmono : MonotoneOn g (Set.Ioo (0 : ℝ) 1)) :
    (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, f u) *
        (∫ u : ℝ in Set.Ioo (0 : ℝ) 1, g u) ≤
      ∫ u : ℝ in Set.Ioo (0 : ℝ) 1, f u * g u := by
  have hcov :=
    unitIntervalCovariance_nonneg_of_monotoneOn hf hg hfg hfmono hgmono
  unfold unitIntervalCovariance at hcov
  linarith

end ScoreCurvatureStarOrder
