# Actual smoothed continuity equation

The input is a narrowly continuous probability curve, a genuinely integrable vector field on its joint time-space measure, and the original integrated compact-test flux equation. No pointwise original time derivative is assumed.

`spaceTimeRegularizedLaw_hasDerivAt` derives the actual derivative of every compact-test pairing at strict interior smoothing times. `spaceTimeProbabilityCurve_equation` integrates this derivative and supplies the literal compact-test equation for the actual global probability curve constructed by interior time clamping, spatial convolution, and a stationary positive Gaussian floor. Its velocity is the actual joint flux divided by the actual positive density.

The floor proportion satisfies 0 < δ ≤ 1; both kernel scales are positive. The chosen physical interval [a,b] lies strictly inside [τ,T−τ]. All norm estimates and flux pairings use the true Euclidean norm. This checkpoint does not yet claim the regularization limit or rough Wasserstein bound.

Reproduce using `python3 qa/rough_eulerian_smoothed_equation/verify.py` from the project root. The checker compiles, independently replays the kernel, hashes sources/binaries, and audits every named declaration.
