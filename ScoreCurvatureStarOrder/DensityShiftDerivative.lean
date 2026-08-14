import Mathlib
import ScoreCurvatureStarOrder.MomentLogDerivative

namespace ScoreCurvatureStarOrder

open Set MeasureTheory

/-- At every interior shift and positive observation, the shift derivative of the normalized
density is the density times the centered score. -/
theorem powerWeightedShiftDensity_hasDerivAt
    {theta S Sprime Ssecond : ℝ → ℝ} {a p x : ℝ}
    (ha : 0 < a) (hp : -1 < p) (hx : 0 < x)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt Sprime (Ssecond z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ), Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    HasDerivAt
      (fun b : ℝ => powerWeightedShiftDensity theta b p x)
      (powerWeightedShiftDensity theta a p x *
        ((∫ t : ℝ in Set.Ioi 0,
          S (a + t) * powerWeightedShiftDensity theta a p t) - S (a + x))) a := by
  let D : ℝ := ∫ t : ℝ in Set.Ioi 0,
    t ^ p * (-S (a + t) * theta (a + t))
  let E : ℝ := ∫ t : ℝ in Set.Ioi 0,
    S (a + t) * powerWeightedShiftDensity theta a p t
  let M : ℝ := powerWeightedShiftMoment theta a p

  have hMderiv := powerWeightedShiftMoment_hasDerivAt
    (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
    (a := a) (p := p) ha hp htheta_pos htheta_deriv htheta_int hS hSprime
    hSprime_pos hcurv
  have hMpos : 0 < M := by
    dsimp [M]
    exact powerWeightedShiftMoment_pos
      ha.le hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hMne : M ≠ 0 := hMpos.ne'

  have hrawlog := hMderiv.log hMne
  have hmeanlog := powerWeightedShiftMoment_log_hasDerivAt
    (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
    (a := a) (p := p) ha hp htheta_pos htheta_deriv htheta_int hS hSprime
    hSprime_pos hcurv
  have hDdiv : D / M = -E := by
    calc
      D / M = deriv (fun b : ℝ => Real.log (powerWeightedShiftMoment theta b p)) a := by
        dsimp [D, M]
        exact hrawlog.deriv.symm
      _ = -E := by
        dsimp [E]
        exact hmeanlog.deriv
  have hD : D = (-E) * M := (div_eq_iff hMne).mp hDdiv

  have hax0 : 0 ≤ a + x := add_nonneg ha.le hx.le
  have htheta_shift :
      HasDerivAt (fun b : ℝ => theta (b + x))
        (-S (a + x) * theta (a + x)) a :=
    (htheta_deriv (a + x) hax0).comp_add_const a x
  have hnum := htheta_shift.const_mul (x ^ p)
  have hquot := hnum.fun_div hMderiv hMne

  have hcoef :
      (((x ^ p * (-S (a + x) * theta (a + x))) * M -
          (x ^ p * theta (a + x)) * D) / M ^ 2) =
        powerWeightedShiftDensity theta a p x * (E - S (a + x)) := by
    rw [hD]
    dsimp [powerWeightedShiftDensity, M]
    field_simp [hMne]
    ring

  change HasDerivAt
    (fun b : ℝ => (x ^ p * theta (b + x)) / powerWeightedShiftMoment theta b p)
    (powerWeightedShiftDensity theta a p x * (E - S (a + x))) a
  rw [← hcoef]
  exact hquot

/-- Equivalently, the shift derivative of the log-density is the centered score. -/
theorem powerWeightedShiftDensity_log_hasDerivAt
    {theta S Sprime Ssecond : ℝ → ℝ} {a p x : ℝ}
    (ha : 0 < a) (hp : -1 < p) (hx : 0 < x)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt theta (-S z * theta z) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt S (Sprime z) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt Sprime (Ssecond z) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ), Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    HasDerivAt
      (fun b : ℝ => Real.log (powerWeightedShiftDensity theta b p x))
      ((∫ t : ℝ in Set.Ioi 0,
        S (a + t) * powerWeightedShiftDensity theta a p t) - S (a + x)) a := by
  have hdensity := powerWeightedShiftDensity_hasDerivAt
    (theta := theta) (S := S) (Sprime := Sprime) (Ssecond := Ssecond)
    (a := a) (p := p) (x := x) ha hp hx htheta_pos htheta_deriv htheta_int hS
    hSprime hSprime_pos hcurv
  have hMpos : 0 < powerWeightedShiftMoment theta a p :=
    powerWeightedShiftMoment_pos
      ha.le hp htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hax0 : 0 ≤ a + x := add_nonneg ha.le hx.le
  have hnumpos : 0 < x ^ p * theta (a + x) :=
    mul_pos (Real.rpow_pos_of_pos hx p) (htheta_pos (a + x) hax0)
  have hfdpos : 0 < powerWeightedShiftDensity theta a p x := by
    dsimp [powerWeightedShiftDensity]
    exact div_pos hnumpos hMpos
  have hlog := hdensity.log hfdpos.ne'
  have hcoef :
      (powerWeightedShiftDensity theta a p x *
        ((∫ t : ℝ in Set.Ioi 0,
          S (a + t) * powerWeightedShiftDensity theta a p t) - S (a + x))) /
          powerWeightedShiftDensity theta a p x =
        (∫ t : ℝ in Set.Ioi 0,
          S (a + t) * powerWeightedShiftDensity theta a p t) - S (a + x) := by
    exact mul_div_cancel_left₀ _ hfdpos.ne'
  rw [hcoef] at hlog
  exact hlog

end ScoreCurvatureStarOrder
