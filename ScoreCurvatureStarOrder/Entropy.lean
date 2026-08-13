import Mathlib

namespace ScoreCurvatureStarOrder

theorem entropy_nonneg {r : ℝ} (hr : 0 < r) :
    0 ≤ 1 - r + r * Real.log r := by
  have hinv : 0 < r⁻¹ := inv_pos.mpr hr
  have hlog := Real.log_le_sub_one_of_pos hinv
  rw [Real.log_inv] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hr.le
  have hmain : -(r * Real.log r) ≤ 1 - r := by
    calc
      -(r * Real.log r) = r * (-Real.log r) := by ring
      _ ≤ r * (r⁻¹ - 1) := hmul
      _ = 1 - r := by field_simp [hr.ne]
  linarith

end ScoreCurvatureStarOrder
