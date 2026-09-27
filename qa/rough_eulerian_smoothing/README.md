# Actual spatial mollification with a stationary Gaussian floor

This scoped checkpoint verifies five new modules, imported by
`SharpWasserstein.RoughEulerianSmoothingLaw`. It is a spatial regularization
stage toward the rough Eulerian transport theorem, not that theorem itself.

The verification script recompiles each source, independently replays its
compiled kernel object, records source/object hashes, and checks the axioms of
every named declaration. Only `propext`, `Classical.choice`, and `Quot.sound`
are permitted. Run from the project root:

```
python3 qa/rough_eulerian_smoothing/verify.py
```

## Construction and hypotheses

Let `μ` be an actual Borel probability measure on the Euclidean space
`WeightedTangent.Point d`. The space uses its canonical inner-product
Lebesgue measure. For `ε > 0`, the kernel is an actual `ContDiffBump` with
inner radius `ε/2`, outer radius `ε`, normalized by its Lebesgue integral.
It is nonnegative, compactly supported, smooth, and has integral one.

For an actual integrable vector field `v`, define

- `density ε hε μ x = ∫ Kε(x-y) dμ(y)`;
- `flux ε hε μ v x = ∫ Kε(x-y) v(y) dμ(y)`;
- `gaussianFloor x = exp(-‖x‖²) / ∫ exp(-‖y‖²) dy`;
- `regularizedDensity = (1-δ) density + δ gaussianFloor`;
- `regularizedVelocity = (1-δ) flux / regularizedDensity`;
- `regularizedLaw = regularizedDensity · volume`.

The floor parameter satisfies `0 < δ ≤ 1`. Positivity, Gaussian
integrability, normalization, smoothness, and its quadratic moment are proved,
not supplied as external hypotheses.

## Main verified statements

`regularizedLaw_probability` proves that the resulting law is a probability
measure. `regularizedVelocity_flux` proves its exact flux identity.

If additionally `∫ ‖v‖² dμ` is finite,
`regularizedLaw_velocity_memLp` establishes that the actual constructed
velocity belongs to `L²(regularizedLaw)`, and
`regularizedLaw_velocity_energy_le` proves

```
∫ ‖regularizedVelocity‖² d regularizedLaw ≤ (1-δ) ∫ ‖v‖² dμ.
```

This is the true Euclidean norm. The coefficient has no dimension loss and
is independent of the support radius, ε, and the original field. The weighted
Jensen proof includes the case of zero original convolved density. Product
integrability, Fubini, and the spatial mass identity are proved on the full
Lebesgue space, not inferred from formal convolution notation.

If the original carrying law satisfies `‖y‖ ≤ R` almost everywhere, the flux
vanishes outside radius `R+ε`. `regularizedVelocity_regular` proves all
iterated derivatives of the velocity globally bounded and proves global
Lipschitz constants for the velocity and its actual first derivative. These
regularity constants may depend on the fixed regularization and the field;
no uniformity as ε or δ tends to zero is asserted.

Under that same bounded-support hypothesis,
`regularizedLaw_quadratic_integrable` proves its finite quadratic moment.
The compressed carrying laws from the preceding checkpoint satisfy the
required support condition, but the time-dependent curve adapter has not yet
been assembled here.

## Remaining transport bridges

This checkpoint does not yet prove the space-time mollified continuity
equation, uniform-in-time regularity for the smoothed velocity, endpoint W₂
convergence for this mollification/floor, or the final length bound. It does
not infer `∫√E` length from a single total-action estimate. Positive-time
truncation remains necessary for an energy profile of order `1/s` near zero.

The five source files contain no `sorry`, custom axioms, `unsafe` proofs, or
assumed dynamic transport estimate. Exact QA results and source/object hashes
are in `verification.json`; per-module compile/replay logs and declaration
axiom output are retained alongside it.
