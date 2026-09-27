# Actual switch/source derivative verification

All 13 `SwitchSourceDerivative*.lean` modules were compiled and independently replayed by Lean's kernel. All 56 named declarations were inspected with `#print axioms`; only `propext`, `Classical.choice`, and `Quot.sound` occur. Source and object hashes, commands, and exit statuses are in `verification.json`; per-module logs and the complete axiom output are retained here. These source modules are frozen.

The two final imports are `SharpWasserstein.SwitchSourceDerivativePrescribed` and `SharpWasserstein.SwitchSourceDerivativeFlux`.

## Actual statements

For the genuinely constructed switch law P_(T-s) R_s, the ordinary derivative against a bounded C¹ test F with bounded differential is the integral of D(P_(T-s)F) applied to v_ref(s,x)-b(x), under R_s, at every 0<s<T. A right derivative holds for 0≤s<T, and the integrated identity holds on every [s,t] contained in [0,T], including endpoints. The prescribed-reference specialization uses the existing `PrescribedSwitchCurve.law`, a supplied actual `IsLimitEvolution b μ`, and the actual `InitialSourcePermutation.initialCurrent b (μ s)`. Compact C∞ tests require no separate value or derivative bounds.

Final APIs include `prescribed_switch_compact_hasDerivAt`, `prescribed_switch_compact_sub_eq_integral`, `prescribedSourcePairing_eq_current`, `prescribedSourcePairing_eq_generator_difference`, `switch_flux_pairing_integrable`, and `sourcePairing_eq_integral_JV` in namespace `SharpWasserstein.SwitchSourceDerivative`.

The latter identity is the literal random-flow pairing ∫ DF(X_t(x,w)) [J_t(x,w)(v_ref(s,x)-b(x))] dR_s(x) dξ(w), with integrability established before exchanging integrals. The current belongs to actual L². The noise is the previously constructed sqrt(2)-Brownian configuration noise; no Markov, backward C², semigroup derivative, or tangent-PDE conclusion is assumed.

## Hypotheses and constants

The generic particle drift b is autonomous, bounded, uniformly Lipschitz, C∞, with globally bounded iterated derivatives. The reference drift is jointly continuous, bounded, and uniformly spatially Lipschitz; it need not have a time derivative. All laws are actual probability measures, T≥0. This switch identity itself needs no second moment assumption. The particle specialization discharges smoothness and bounded derivative hypotheses from the existing bounded smooth interaction-kernel assumptions and requires N>0 plus the stated nonnegative kernel bounds.

An auxiliary difference-quotient domination is L exp(H T)(M+A), where L bounds DF, H is the full-state particle Lipschitz constant, and M,A bound the reference and particle drifts. This is solely an integrability bound. These modules assert no sharp marginal energy rate and introduce no claimed dimension-free transport estimate. Full Euclidean marginal energy estimates, identification with canonical marginal source representatives, and rough finite-action Eulerian transport remain separate bridges.

## Proof route

Actual common-noise trajectories have a differentiable difference even though each noise path is rough. A genuine time-dependent restart theorem and the autonomous Brownian semigroup convert the finite switch increment to such a synchronous difference. A line-integral formula uses only joint continuity of the actual initial Jacobian and of the propagated C¹ test differential. Dominated convergence differentiates its expectation. Continuity of the resulting source action and the fundamental theorem of calculus produce the ordinary derivative and endpoint integral identity. The already proved flow-Jacobian expectation formula then gives the literal JV flux.
