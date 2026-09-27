# Actual time-mollified weak derivative

This checkpoint has four modules, ending in
`SharpWasserstein.RoughEulerianTimeWeak`. They establish the scalar weak
equation needed for time smoothing; they do not assert that the whole smooth
probability/flux approximation or the final rough transport theorem is done.

`integral_primitive_swap` is triangular Fubini for two actual L¹ functions.
`integral_derivative_mul_weak_curve` derives integration by parts for a
continuous scalar curve `f` satisfying
`f(s)-f(a)=∫_[a,s] g`, where the original source `g` is only L¹. It assumes no
pointwise differentiability of `f` or continuity of `g`.

`timeConvolution_hasDerivAt_source` differentiates the actual convolution
`∫_[a,b] κ(t-s) f(s) ds` and identifies its derivative with
`∫_[a,b] κ(t-s) g(s) ds`. Kernel value/derivative bounds justify differentiation
under the integral; the preceding L¹ integration-by-parts theorem supplies
the source identity. Exact vanishing of the kernel at the interval endpoints
removes the boundary terms.

`timeKernel` is a concrete nonnegative normalized compact C∞ bump of radius
ε, with ε>0. Its integral, support, evenness, value/derivative bounds, and
interior-window normalization are proved. For `a+ε≤t` and `t+ε≤b`,
`timeKernel_hasDerivAt_source` discharges the kernel and boundary hypotheses.

`compact_curve_timeKernel_hasDerivAt` instantiates this result for the genuine
law pairing of `CompactDistributionContinuity μ σ T`. Its hypotheses are
exactly that original compact-test integrated equation, ε>0, and an interior
time `ε≤t`, `t+ε≤T`. No continuity of the source is required.

`compact_curve_timeKernel_hasDerivAt_flux` uses the actual joint L² Riesz
field `curveFlux h`. It additionally takes the actual integrable energy bound
`E` and almost-everywhere test-objective bound from the rough flux checkpoint.
The derivative is the literal time convolution of
`∫ ⟪gradient φ, curveFlux(s,·)⟫ dμ_s`, with the positive divergence-pairing
sign. This does not assume a measurable family of canonical timewise fields.

Reproduction: `python3 qa/rough_eulerian_time_weak/verify.py` from the project
root. The script recompiles each source, independently replays each kernel
object, verifies every named declaration uses only standard axioms, and
records source/object hashes. Exact results are in `verification.json` with
all compile/replay and axiom logs retained.
