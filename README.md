# score-curvature-star-order

Lean formalization of a score-curvature criterion for star-shaped ordering of power-weighted shift families.

## Status

Formal verification in progress.

## Scope

The project formalizes the proof chain

score curvature
→ nonnegative two-point kernel
→ monotonicity criterion
→ star-shaped ordering
→ monotonicity and log-convexity of two-shift moment ratios.

The repository is intended to provide a reproducible formal-verification companion to the corresponding mathematical manuscript.

## Verification policy

- Lean 4 + mathlib
- pinned toolchain and dependencies
- no `sorry`
- no `admit`
- no additional axioms
- CI build on every relevant commit
- tagged releases for versions cited by the manuscript
