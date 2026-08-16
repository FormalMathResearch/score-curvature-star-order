import Mathlib
import ScoreCurvatureStarOrder.GlobalKernelWithin

namespace ScoreCurvatureStarOrder

open Set

/-- **Manuscript Theorem 3.1 in the exact half-line form.**

Under the mathematically natural one-sided regularity assumptions on `[0,∞)`,
the two-point kernel is nonnegative for all nonnegative `a`, `x`, and `t`.

The existing interior theorem proves the result for `x,t > 0`.  The endpoint
cases are obtained only by continuity from the positive quadrant.  Thus no
artificial two-sided derivative at the boundary `0` is introduced. -/
theorem twoPointKernel_nonneg_within
    {S Sprime Ssecond : ℝ → ℝ} {a x t : ℝ}
    (ha : 0 ≤ a) (hx0 : 0 ≤ x) (ht0 : 0 ≤ t)
    (hS : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt S (Sprime z) (Set.Ici (0 : ℝ)) z)
    (hSprime : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt Sprime (Ssecond z) (Set.Ici (0 : ℝ)) z)
    (hSprime_pos : ∀ z ∈ Set.Ici (0 : ℝ), 0 < Sprime z)
    (hcurv : ∀ z ∈ Set.Ici (0 : ℝ),
      Ssecond z * S z - (Sprime z) ^ 2 ≤ 0) :
    0 ≤ twoPointKernel S Sprime a x t := by
  have hSshift :
      ContinuousOn (fun y : ℝ => S (a + y)) (Set.Ici (0 : ℝ)) :=
    continuousOn_shift_Ici_of_hasDerivWithinAt ha hS
  have hSpshift :
      ContinuousOn (fun y : ℝ => Sprime (a + y)) (Set.Ici (0 : ℝ)) :=
    continuousOn_shift_Ici_of_hasDerivWithinAt ha hSprime

  have hpospos :
      ∀ {y u : ℝ}, 0 < y → 0 < u →
        0 ≤ twoPointKernel S Sprime a y u := by
    intro y u hy hu
    exact twoPointKernel_nonneg_of_pos_within
      ha hy hu hS hSprime hSprime_pos hcurv

  have hpos_all :
      ∀ {y u : ℝ}, 0 < y → 0 ≤ u →
        0 ≤ twoPointKernel S Sprime a y u := by
    intro y u hy hu
    have hu_cl : u ∈ closure (Set.Ioi (0 : ℝ)) := by
      simpa only [closure_Ioi, Set.mem_Ici] using hu
    have hcont_u :
        ContinuousOn
          (fun v : ℝ => twoPointKernel S Sprime a y v)
          (Set.Ici (0 : ℝ)) := by
      intro v hv
      have hSv :
          ContinuousWithinAt (fun w : ℝ => S (a + w)) (Set.Ici (0 : ℝ)) v :=
        hSshift v hv
      have hSp_const :
          ContinuousWithinAt (fun _ : ℝ => Sprime (a + y)) (Set.Ici (0 : ℝ)) v :=
        continuousWithinAt_const
      have hSy_const :
          ContinuousWithinAt (fun _ : ℝ => S (a + y)) (Set.Ici (0 : ℝ)) v :=
        continuousWithinAt_const
      have hlin :
          ContinuousWithinAt (fun w : ℝ => w - y) (Set.Ici (0 : ℝ)) v :=
        continuousWithinAt_id.sub continuousWithinAt_const
      change ContinuousWithinAt
        (fun w : ℝ =>
          Sprime (a + y) * (w - y) * S (a + w) -
            S (a + y) * (S (a + w) - S (a + y)))
        (Set.Ici (0 : ℝ)) v
      exact ((hSp_const.mul hlin).mul hSv).sub
        (hSy_const.mul (hSv.sub hSy_const))
    have hzero :
        ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Set.Ioi (0 : ℝ)) u :=
      continuousWithinAt_const
    have hk :
        ContinuousWithinAt
          (fun v : ℝ => twoPointKernel S Sprime a y v)
          (Set.Ioi (0 : ℝ)) u :=
      (hcont_u u hu).mono (fun v hv => hv.le)
    exact ContinuousWithinAt.closure_le hu_cl hzero hk (by
      intro v hv
      exact hpospos hy hv)

  have hx_cl : x ∈ closure (Set.Ioi (0 : ℝ)) := by
    simpa only [closure_Ioi] using hx0
  have hcont_x :
      ContinuousOn
        (fun y : ℝ => twoPointKernel S Sprime a y t)
        (Set.Ici (0 : ℝ)) := by
    have hSt_const :
        ContinuousOn (fun _ : ℝ => S (a + t)) (Set.Ici (0 : ℝ)) :=
      continuousOn_const
    have hlin :
        ContinuousOn (fun y : ℝ => t - y) (Set.Ici (0 : ℝ)) :=
      continuousOn_const.sub continuousOn_id
    have hfirst := (hSpshift.mul hlin).mul hSt_const
    have hsecond := hSshift.mul (hSt_const.sub hSshift)
    simpa [twoPointKernel] using hfirst.sub hsecond
  have hzero :
      ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Set.Ioi (0 : ℝ)) x :=
    continuousWithinAt_const
  have hk :
      ContinuousWithinAt
        (fun y : ℝ => twoPointKernel S Sprime a y t)
        (Set.Ioi (0 : ℝ)) x :=
    (hcont_x x hx0).mono (fun y hy => hy.le)
  exact ContinuousWithinAt.closure_le hx_cl hzero hk (by
    intro y hy
    exact hpos_all hy ht0)

end ScoreCurvatureStarOrder
