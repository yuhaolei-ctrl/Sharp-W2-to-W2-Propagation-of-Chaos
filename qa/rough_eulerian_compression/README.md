# Smooth spatial compression of a rough finite-action curve

All six `RoughEulerianCompression*.lean` modules listed in `verification.json` are frozen. Clean compilation, independent kernel replay, and axiom inspection passed for all 56 named declarations. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Source/object hashes and commands are recorded; all logs are retained. Reproduce with `python3 qa/rough_eulerian_compression/verify.py`.

Import `SharpWasserstein.RoughEulerianCompressionEquation` for the whole group.

## Proved statements

* `bounded_smooth_continuity_equation` extends the actual compact-test equation to every bounded C∞ test with bounded Euclidean gradient. It uses actual compact cutoffs and domination by the integrable norm of the joint L² flux; no velocity continuity/boundedness is assumed.
* `compression R x` is the coordinate map R sin(x_i/R), expressed on genuine Euclidean space. `compression_lipschitz`, `compression_fderiv_norm_le`, and `compression_fderiv_apply_norm_le` prove contraction with constant one, directly by summing coordinate squares. Its range lies in the compact ball of radius sqrt(d)|R|. It is C∞ and tends pointwise to identity for R=k+1.
* `pushedFlux` is constructed by Riesz on the full L² space of an actual pushforward measure. `pushedFlux_pairing` proves its literal vector integral identity for every L² output test vector; `pushedFlux_energy_le` proves action contraction. Conditional expectation or an output representing field is not assumed.
* `compressedFlux` pushes the actual Jacobian field Dθ_R(x)U(t,x) under (t,x)↦(t,θ_R(x)). It is strongly measurable, obeys `compressedFlux_energy_le` with constant one, and is carried by a law supported in the fixed compact spatial ball. This support statement concerns the carrying/vector measure, not an unsupported pointwise assertion about an arbitrary L² representative outside that measure's support.
* `compressedCurve_jointMeasure` identifies the output joint measure with the kernel of the actual compressed probability curve.
* `compressed_curve_joint_equation` and `compressed_curve_continuity_equation` prove the exact integrated compact-test continuity equation for those actual laws and that actual flux, including time integrability and interval endpoints. The sign remains σ=−div(μ U).
* `compressed_curve_action_le` preserves the original supplied integrated energy bound unchanged.
* `configurationCompression_wassersteinSq_tendsto` proves genuine endpoint W₂² convergence for every original probability measure with a second moment, by an explicit graph coupling. Its displacement cost is exactly Euclidean, dominated by 4 times the original unnormalized second moment. `compression_probability_tendsto` needs no moment assumption.

## Hypotheses and constants

The input is the previously proved `CompactDistributionContinuity μ σ T` and its constructed joint flux, with T≥0 and an integrable majorant of every actual quadratic compact-test objective on [0,T]. No time-measurable canonical tangent field is assumed. Compression needs R≠0. Endpoint W₂ convergence alone uses P₂ of the endpoint law; the weak equation and action contraction require no spatial second moment.

Compression and fiber averaging have action constant one. The compact support radius depends on the dimension; that radius is solely an approximation parameter and is not an energy loss. No normalization by particle number or conversion from supremum norm enters the action or endpoint coupling.

## Remaining work

The smoothed positive-density curve and its smooth globally bounded velocity have not yet been constructed here. Space-time smoothing, a positive stationary density, the precise velocity derivative bounds required by `EulerianTransportCompact`, action control under smoothing, and the transport limit remain open. This group does not claim the rough Wasserstein length theorem or the manuscript's final sharp rate.

The finite-action construction applies to intervals where ∫E is finite. The initial-time E(s)≈1/s singularity requires positive-time truncation and a final endpoint-continuity limit. The distinction between total action ∫E and length ∫sqrt(E) must be preserved in the remaining approximation argument.
