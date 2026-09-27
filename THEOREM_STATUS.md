# Formalization status

The original main proposition has an unconditional Lean proof:

```lean
theorem SharpWasserstein.main_theorem : SharpWasserstein.MainTheorem
```

`MainTheorem` remains the original definition in `Dynamics.lean`;
`main_theorem` is its proved inhabitant. The final audit passed for
512 files / 3,776 named declarations, including definitions. The aggregate
compile, independent replay, and exact-type/axiom audit are recorded in
`qa/build_SharpWasserstein.json` and `qa/verification.json`; the latter is the
completion certificate, not the inventory count.

## Statement and constants

- The dimension is positive, the time horizon is finite, and the initial
  hierarchy constant and kernel bounds are nonnegative.
- The uniform conclusion constant depends only on dimension, horizon,
  initial hierarchy constant, and the kernel/value first-derivative bounds.
  It is chosen before the kernel, laws, particle number, and marginal level.
- The initial particle laws are arbitrary exchangeable P₂ laws satisfying
  the stated all-level unnormalized squared-Wasserstein estimate.
- The kernel is bounded smooth with bounded derivatives; self-interaction
  is retained. Noise sqrt(2) gives Laplacian coefficient one.
- The target quantifies over the stated weak probability evolutions, with
  continuous compact-test pairings and locally bounded second moments.
  Nonlinear existence/uniqueness is cited background, not a new conclusion.

The initial `Dynamics.lean` hash is checked against the prior checkpoint in
[main_statement_review.md](qa/main_statement_review.md). No main hypothesis
was weakened, and no unproved auxiliary estimate is assumed.

## Manuscript-to-proof map

All names below are under `SharpWasserstein`.

| Revised manuscript component | Actual Lean proof |
| --- | --- |
| Main theorem | `main_theorem`; `main_of_uniform_finite_action_transport` is the intermediate reduction, whose premise is now proved by `RoughEulerianTransport.uniform_finite_action_transport`. |
| True Euclidean W₂² and P₂ endpoints | `wassersteinSq_lt_top`, `coupling_gluing`, `wassersteinSq_root_triangle`, `quadraticProbability_ofReal_dist_sq`; actual couplings and marginal contraction. |
| Gaussian sharpness remark | `GaussianSharpness.particleGaussianLaw_transport_exact`, `gaussian_sharpness_hypotheses`, `gaussian_sharpness_fixed_time`; actual exchangeable common-noise laws and zero-kernel weak evolutions. |
| Weighted negative-Sobolev tangent | `WeightedTangent.existsUnique_tangent`, `energy_eq_integral`, `flux_energy_decomposition`, `extendedEnergy_le_liminf`. |
| Rough finite-action transport | `RoughEulerianTransport.wassersteinSq_le_uniform_action`; constructed spacetime Riesz flux, sine compression, genuine time/space convolution, positive Gaussian floor, exact continuity equation/action, and both actual W₂ endpoint limits. |
| Entropy-cost direction and coefficient | `BrownianEntropy.flow_entropy_le_wassersteinSq`; actual finite Gaussian log-density cost, original-history expectation, chain rule, Euler convergence and KL lower semicontinuity. The coefficient uses the Euclidean Lipschitz constant. |
| Exchangeable entropy increments | `exchangeable_marginal_entropy_second_difference`, `exchangeable_finiteEntropyConditions`; conditional KL superadditivity and chain rules. |
| All-level source estimate | `RegularizedBrownianSource.exists_initial_profile`, `prefixEnergy_le`, `prescribed_marginal_energy_le`; internal bounded-sum estimate, conditional Pinsker, actual source sign and self-term. |
| Finite energy differentiation and cancellation | `PhysicalFourierTrialHierarchy`, `PeriodicMarginalCoefficientEvolutionHierarchy`, `BrownianPeriodicHierarchy`; actual Fourier eigenfunctions, penalized Gram matrix, Brownian coefficient derivatives, Hessian cancellation and explicit approximation gap. |
| Sharp propagated tangent profile | `BrownianEnergyPeriodization.prefixEnergy_quadratic_bound`; finite-energy L¹ recovery, Volterra comparison, all physical period multiples, and original-kernel sine flow/Jacobian limit with the same initial current. |
| Actual switch law and compact continuity equation | `SwitchSourceDerivative.prescribed_marginal_compactDistributionContinuity`; exact cylinder cutoff and source/law identification. |
| Common-label mean-square continuity | `SwitchCurve.jointEndpoint_marginal_cost_tendsto`, `SwitchSourceDerivative.prescribedMarginalCommonLabel`; one initial configuration and two independent Brownian paths. |
| Integrable zero-time singularity | `GeometricEndpointLength.endpoint_of_local_action`; quarter-geometric summation gives `sqrt(C)*(T+3*sqrt(T))*k/N`. |
| Decoupled and final endpoints | `WassersteinEndpoint.propagatedHierarchy_of_switch_lengths`, `SwitchSourceDerivative.prescribed_switch_length_of_finiteAction`; all-level initial data, time zero, reference identification and final uniform constant. |

## Auxiliary scope aligned in the revised note

The entropy lemma is stated for jointly continuous bounded globally Lipschitz
drifts, the case proved and used. Its displayed coefficient is dimension-free
for the genuine Euclidean Lipschitz constant; conversion from the Lean Pi norm
only costs a dimension-dependent factor.

The rough transport lemma states the uniform finite-action estimate under a
common-label mean-square realization. The proof constructs that realization
for the switch curve. It does not assert the broader AGS characterization for
all narrow curves or a measurable selection of timewise minimal fields.

Tangent propagation uses a fixed equivariant L² field. The finite Fourier
argument replaces the previous smooth elliptic optimizer/density argument;
no derivative of the limiting energy is assumed. All-period recovery is
separate from the nonperiodic kernel limit.

The independent full correspondence review is
[manuscript_coverage_audit_2026-09-17.md](qa/manuscript_coverage_audit_2026-09-17.md).
Earlier status snapshots are retained under `qa/history/`.
