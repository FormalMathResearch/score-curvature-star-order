# Publication coverage audit — Manuscript Proposition 2.4

Audit baseline: commit `52d95b087b3e563028d39c2b2bf4cb607384c341`

Verification baseline: CI #263 / run `32554152815` — success.

This document records a publication-oriented clause-by-clause audit of Proposition 2.4 in the manuscript. It is intentionally conservative: a manuscript clause is marked **covered** only when the current Lean development contains an explicit theorem or a direct theorem chain with the same mathematical content. Separate one-parameter statements are not silently promoted to a stronger joint two-parameter statement.

Mathematical policy: Lean verifies the manuscript mathematics. The manuscript statement is not to be weakened, the shift domain is not to be altered, and no artificial two-sided derivative at `a = 0` is to be introduced.

## Manuscript clause audit

| Manuscript clause | Current Lean evidence | Status |
| --- | --- | --- |
| Integrability / finiteness of `M_p(a)` for `p > -1`, `a >= 0` | `powerWeightedShift_integrableOn_Ioi_within` in `Moments.lean` | **COVERED** |
| Strict positivity of `M_p(a)` | `powerWeightedShiftMoment_pos_within` in `Moments.lean` | **COVERED** |
| Integrability of the first and second logarithmic power moments | `powerWeightedShift_log_integrableOn_Ioi_within` and `powerWeightedShift_log_sq_integrableOn_Ioi_within` in `PowerLogMoments.lean` | **COVERED pointwise in `(p,a)`** |
| First derivative in `p`, under the integral sign | `powerWeightedShiftMoment_hasDerivAt_power_within` in `PowerMomentDerivative.lean` | **COVERED** |
| Second derivative in `p`, under the integral sign | combine `powerWeightedShiftMoment_hasDerivAt_power_within` with `powerWeightedShift_logMoment_hasDerivAt_power_within` in `PowerLogMomentDerivative.lean` | **COVERED** |
| Ordinary derivative in shift `a` for `a > 0` | `powerWeightedShiftMoment_hasDerivAt_within` in `DistributionShiftDerivativeWithin.lean` | **COVERED** |
| Right derivative in shift at `a = 0` | `powerWeightedShiftMoment_hasDerivWithinAt_zero_within` in `MomentShiftBoundaryDerivative.lean` | **COVERED** |
| Right continuity at `a = 0` | `powerWeightedShiftMoment_continuousWithinAt_zero_within` in `ShiftBoundaryContinuity.lean` | **COVERED** |
| Integrable majorants independent of **both** `(p,a)` on arbitrary compact ranges `p in [p0,p1]`, `a in [0,A]`, for `x^p |log x|^r theta(a+x)`, `r = 0,1,2` | Current files contain the ingredients and one-parameter dominated bounds, but this audit did not find an explicit theorem with the printed joint compact-parameter uniformity | **OPEN PUBLICATION-COVERAGE GAP** |
| Integrable majorant independent of **both** `(p,a)` on the same compact ranges for `x^p |theta'(a+x)|` | `ShiftDerivativeMajorant.lean` and `LocalShiftMajorant.lean` give shift-uniform ingredients for fixed `p`; the printed joint `(p,a)` theorem is not explicit | **OPEN PUBLICATION-COVERAGE GAP** |
| Joint continuity of `(p,a) -> M_p(a)` on `(-1,infinity) x [0,infinity)` | Continuity/differentiability is established in each parameter with the other fixed, including the one-sided boundary in `a`; no explicit joint two-parameter continuity theorem was identified | **OPEN PUBLICATION-COVERAGE GAP** |
| Derivatives may be taken under the integral sign **locally uniformly on the joint parameter domain** | Existing derivative proofs use local dominated convergence/differentiation in one parameter at a time. The stronger printed joint local-uniform formulation has not yet been packaged as an explicit theorem | **OPEN PUBLICATION-COVERAGE GAP** |

## Consequence of the audit

CI #263 closes the previously open compiler/formalization gap for the natural right derivative at `a = 0`. It does **not**, by itself, justify saying that the entire printed Proposition 2.4 is formalized 1:1.

The remaining work is not to weaken Proposition 2.4. Instead, the next formalization target should encode the compact-parameter uniformity that the manuscript already proves mathematically.

## Next Lean targets

1. Add a theorem (preferably in a dedicated module such as `CompactParameterMajorants.lean`) giving the printed compact-parameter-uniform integrable majorants simultaneously for
   - `x^p |log x|^r theta(a+x)`, for `r = 0,1,2`, and
   - `x^p |theta'(a+x)|`,
   with `p in [p0,p1]`, `a in [0,A]`, `p0 > -1`.
2. Derive an explicit joint continuity theorem for `(p,a) -> M_p(a)` from those majorants.
3. Package the first/second `p` derivatives and the interior/right-boundary `a` derivative into a publication-facing Proposition 2.4 wrapper, including the intended local-uniform differentiation statement.
4. Run full CI and repeat this audit before changing the manuscript wording from “main proof chain” to any stronger formal-verification claim.

No merge, release, tag, or Zenodo software DOI should be made before these publication-coverage gaps are closed and the final audit is green.
