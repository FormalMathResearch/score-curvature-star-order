import Mathlib
import ScoreCurvatureStarOrder.QuantileExistence

namespace ScoreCurvatureStarOrder

open Set MeasureTheory Filter
open scoped Interval Topology

/-- Canonical quantile as the generalized inverse of the normalized CDF on the
positive support.  The definition itself is hypothesis-free; under the
one-sided assumptions and for `u ∈ (0,1)` it is proved below to coincide with
the unique positive solution of `F_{p,a}(x)=u`. -/
noncomputable def powerWeightedShiftQuantile
    (theta : ℝ → ℝ) (a p u : ℝ) : ℝ :=
  sInf {x : ℝ | 0 < x ∧ u ≤ powerWeightedShiftCDF theta a p x}

/-- Under the one-sided half-line assumptions, the canonical generalized
inverse is positive and attains the prescribed level exactly. -/
theorem powerWeightedShiftQuantile_pos_and_CDF_eq_within
    {theta S Sprime : ℝ → ℝ} {a p u : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p) (hu0 : 0 < u) (hu1 : u < 1)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    0 < powerWeightedShiftQuantile theta a p u ∧
      powerWeightedShiftCDF theta a p
          (powerWeightedShiftQuantile theta a p u) = u := by
  let E : Set ℝ :=
    {x : ℝ | 0 < x ∧ u ≤ powerWeightedShiftCDF theta a p x}

  rcases existsUnique_pos_powerWeightedShiftCDF_eq_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p) (u := u)
      ha hp hu0 hu1 htheta_pos htheta_deriv htheta_int hS hSprime_pos with
    ⟨q, hq, _huniq⟩

  have hstrict :
      StrictMonoOn
        (fun x : ℝ => powerWeightedShiftCDF theta a p x)
        (Set.Ioi (0 : ℝ)) :=
    powerWeightedShiftCDF_strictMonoOn_Ioi_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p)
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos

  have hqE : q ∈ E := by
    change 0 < q ∧ u ≤ powerWeightedShiftCDF theta a p q
    exact ⟨hq.1, hq.2.ge⟩

  have hq_lower : ∀ x ∈ E, q ≤ x := by
    intro x hx
    change 0 < x ∧ u ≤ powerWeightedShiftCDF theta a p x at hx
    by_contra hqx
    have hxq : x < q := lt_of_not_ge hqx
    have hlt := hstrict hx.1 hq.1 hxq
    change powerWeightedShiftCDF theta a p x <
      powerWeightedShiftCDF theta a p q at hlt
    rw [hq.2] at hlt
    exact (not_lt_of_ge hx.2) hlt

  have hQeq : powerWeightedShiftQuantile theta a p u = q := by
    rw [powerWeightedShiftQuantile]
    change sInf E = q
    apply le_antisymm
    · exact csInf_le ⟨q, hq_lower⟩ hqE
    · exact le_csInf ⟨q, hqE⟩ hq_lower

  rw [hQeq]
  exact hq

/-- The canonical quantile is strictly increasing in its probability level on
`(0,1)`. -/
theorem powerWeightedShiftQuantile_strictMonoOn_Ioo_within
    {theta S Sprime : ℝ → ℝ} {a p : ℝ}
    (ha : 0 ≤ a) (hp : -1 < p)
    (htheta_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < theta z)
    (htheta_deriv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt theta (-S z * theta z) (Set.Ici (0 : ℝ)) z)
    (htheta_int : IntegrableOn theta (Set.Ici (0 : ℝ)))
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z) :
    StrictMonoOn
      (fun u : ℝ => powerWeightedShiftQuantile theta a p u)
      (Set.Ioo (0 : ℝ) 1) := by
  intro u hu v hv huv

  have hQu := powerWeightedShiftQuantile_pos_and_CDF_eq_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p) (u := u)
    ha hp hu.1 hu.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hQv := powerWeightedShiftQuantile_pos_and_CDF_eq_within
    (theta := theta) (S := S) (Sprime := Sprime)
    (a := a) (p := p) (u := v)
    ha hp hv.1 hv.2 htheta_pos htheta_deriv htheta_int hS hSprime_pos
  have hstrict :
      StrictMonoOn
        (fun x : ℝ => powerWeightedShiftCDF theta a p x)
        (Set.Ioi (0 : ℝ)) :=
    powerWeightedShiftCDF_strictMonoOn_Ioi_within
      (theta := theta) (S := S) (Sprime := Sprime)
      (a := a) (p := p)
      ha hp htheta_pos htheta_deriv htheta_int hS hSprime_pos

  by_contra hnot
  have hvleu :
      powerWeightedShiftQuantile theta a p v ≤
        powerWeightedShiftQuantile theta a p u :=
    le_of_not_gt hnot
  rcases hvleu.eq_or_lt with heq | hvlt
  · have huv_eq : u = v := by
      rw [← hQu.2, ← hQv.2, heq]
    exact (ne_of_lt huv) huv_eq
  · have hlt := hstrict hQv.1 hQu.1 hvlt
    change
      powerWeightedShiftCDF theta a p (powerWeightedShiftQuantile theta a p v) <
        powerWeightedShiftCDF theta a p (powerWeightedShiftQuantile theta a p u) at hlt
    rw [hQv.2, hQu.2] at hlt
    exact (not_lt_of_ge huv.le) hlt

end ScoreCurvatureStarOrder
