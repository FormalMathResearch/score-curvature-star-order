# Publication coverage audit — Manuscript Proposition 2.4

Audit baseline: commit `5c0f9ee5bb78832340538a277ef3c7ae49e0462f`

Verification baseline: CI #280 / run `32562527160` — success.

This document records a publication-oriented clause-by-clause audit of Proposition 2.4 in the manuscript. A manuscript clause is marked **covered** only when the current Lean development contains an explicit theorem or a direct theorem chain with the same mathematical content. Separate one-parameter statements are not silently promoted to stronger joint two-parameter statements.

Mathematical policy: Lean verifies the manuscript mathematics. The manuscript statement is not weakened, the shift domain is not altered, and no artificial two-sided derivative at `a = 0` is introduced.

## Manuscript clause audit

| Manuscript clause | Current Lean evidence | Status |
| --- | --- | --- |
| Integrability / finiteness of `M_p(a)` for `p > -1`, `a >= 0` | `powerWeightedShift_integrableOn_Ioi_within` in `Moments.lean` | **COVERED** |
| Strict positivity of `M_p(a)` | `powerWeightedShiftMoment_pos_within` in `Moments.lean` | **COVERED** |
| Integrability of the first and second logarithmic power moments | `powerWeightedShift_log_integrableOn_Ioi_within` and `powerWeightedShift_log_sq_integrableOn_Ioi_within` in `PowerLogMoments.lean` | **COVERED** |
| First derivative in `p`, under the integral sign | `powerWeightedShiftMoment_hasDerivAt_power_within` in `PowerMomentDerivative.lean` | **COVERED** |
| Second derivative in `p`, under the integral sign | `powerWeightedShift_logMoment_hasDerivAt_power_within` in `PowerLogMomentDerivative.lean`, together with the first derivative theorem | **COVERED** |
| Shift derivative on the natural domain `a >= 0`, with right derivative at `a = 0` | `powerWeightedShiftMoment_hasDerivWithinAt_shift_within` in `MomentParameterLocalUniformity.lean`; this packages the interior theorem `powerWeightedShiftMoment_hasDerivAt_within` and the boundary theorem `powerWeightedShiftMoment_hasDerivWithinAt_zero_within` | **COVERED** |
| Right continuity at `a = 0` | `powerWeightedShiftMoment_continuousWithinAt_zero_within` in `ShiftBoundaryContinuity.lean` | **COVERED** |
| Integrable majorant independent of both `(p,a)` on arbitrary compact ranges `p in [p0,p1]`, `a in [0,A]`, for `x^p theta(a+x)` | `exists_powerWeightedShift_compact_majorant_within` in `CompactParameterMajorants.lean` | **COVERED** |
| Integrable majorant independent of both `(p,a)` on the same compact ranges for `x^p |log x| theta(a+x)` | `exists_powerWeightedShift_log_compact_majorant_within` in `CompactParameterLogMajorants.lean` | **COVERED** |
| Integrable majorant independent of both `(p,a)` on the same compact ranges for `x^p |log x|^2 theta(a+x)` | `exists_powerWeightedShift_log_sq_compact_majorant_within` in `CompactParameterLogSqMajorants.lean` | **COVERED** |
| Integrable majorant independent of both `(p,a)` on the same compact ranges for `x^p |theta'(a+x)|` | `exists_powerWeightedShift_thetaDeriv_compact_majorant_within` in `CompactParameterThetaDerivMajorants.lean` | **COVERED** |
| Joint continuity of `(p,a) -> M_p(a)` on `(-1,infinity) x [0,infinity)` | `powerWeightedShiftMoment_continuousOn_parameters_within` in `MomentJointContinuity.lean` | **COVERED** |
| Derivatives may be taken under the integral sign locally uniformly on the joint parameter domain | `exists_powerWeightedShift_parameterDerivative_local_majorants_within` in `MomentParameterLocalUniformity.lean` supplies, around every admissible `(p,a)`, one compact rectangle and parameter-independent integrable majorants for the first and second `p` derivative integrands and the `a` derivative integrand; the corresponding derivative-under-integral identities are supplied by `PowerMomentDerivative.lean`, `PowerLogMomentDerivative.lean`, and `MomentParameterLocalUniformity.lean` | **COVERED** |

## Interpretation of the local-uniform clause

The Lean formalization records the standard sufficient structure used by the manuscript: on a compact parameter rectangle around each admissible point there is a single integrable dominating function for each derivative integrand, independent of the varying parameters, together with the verified pointwise derivative-under-integral identities. This is the local-uniform domination needed to justify differentiating under the integral sign. The formalization does not claim a stronger, unnecessary uniform-convergence statement.

At the boundary `a = 0`, the shift derivative is explicitly a derivative within `[0,infinity)`, i.e. the right derivative. No ambient two-sided derivative at the boundary is asserted.

## Consequence of the audit

With CI #280 green, the clauses of Proposition 2.4 listed above now have explicit publication-facing Lean coverage, including the compact joint-parameter majorants, joint continuity, and the local-uniform differentiation data that were open in the earlier audit.

This closes the Proposition 2.4 publication-coverage gaps identified at CI #263. It does not by itself complete release preparation: the repository still needs the final source-integrity audit, PR consolidation, release metadata review, and a green release-candidate CI before tagging or minting a software DOI.

## Next release-readiness targets

1. Run a repository-wide source-integrity audit for `sorry`, `admit`, unexpected `axiom` declarations, and other proof placeholders, distinguishing deliberate comments/examples from executable Lean declarations.
2. Reconcile the remaining open PR history so the intended proof chain lands cleanly on the release branch without losing the verified boundary and within-domain results.
3. Review README / citation / release metadata and choose the software license before a release is created.
4. Run full release-candidate CI, including leanchecker, on the exact commit intended for the tag.
5. Only after those checks are green: create the GitHub release/tag and archive that exact software version for a Zenodo software DOI.

No release, tag, or Zenodo software DOI should be made before these release-readiness checks are complete.
