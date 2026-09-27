# Formalization status

**Complete manuscript proof: false (not completed).**

Latest aggregate checkpoint: **483 source files / 3,629 named declarations**,
compiled, independently kernel-replayed, and checked for standard-axiom closure.
The smoothing/Jacobian, convolved-source, Eulerian-transport and propagated-flux
components described below are now included. Further work in progress is
excluded. These counts measure verified components, not a completion percentage.

`SharpWasserstein.MainTheorem` in `SharpWasserstein/Dynamics.lean` is only a
definition of the intended proposition. There is no proved inhabitant of that
proposition and no axiom declaring it true. The development supplies actual
proofs of the component results listed below; the remaining rough finite-action transport step has not yet been discharged.
Several newer components carry their own scoped QA records and await the next
aggregate checkpoint.

Build and kernel-replay results are recorded separately under `qa/`. A successful
build verifies the submitted component proofs, not the entire manuscript.

All identifiers below are in namespace `SharpWasserstein`; dotted names such as
`TangentEnergy.dualEnergy_eq_norm_sq` include the indicated subnamespace.

| Manuscript proof step | Exact proved theorem identifiers | Remaining bridge |
| --- | --- | --- |
| Euclidean product transport and marginals | `wassersteinSq_lt_top`, `coupling_gluing`, `wassersteinSq_root_triangle`, `wassersteinSq_sqrt_triangle`, `quadraticProbability_ofReal_dist_sq` and the original self/symmetry/marginal lemmas | Metric separation and general weak/transport convergence; triangle and the P₂ pseudometric are now proved. |
| Particle/McKean–Vlasov setting | `kernel_joint_difference`, `particleDrift_quadratic_difference`, `exists_finiteAdditiveTrajectory`, `BoundedFlow.flow_joint_continuous`, `ParticleFlow.solution_trajectory`, `ParticleFlow.solution_unique`, `BrownianParticle.globalLaw`, `BrownianParticle.globalLaw_eq`, `BrownianParticle.globalLaw_momentBound`, `BrownianParticle.globalLaw_compactExpectation_continuous`, `BrownianParticle.globalLaw_generatorIntegrable`, `BrownianParticle.globalLaw_timeIntegrable`, `BrownianParticle.globalLaw_weakEvolution`, `BrownianParticle.globalLaw_isParticleEvolution` | The actual Brownian particle law satisfies every weak Fokker–Planck condition, including the integrated generator equation, proved by Gaussian one-step calculus and the Euler limit. `BrownianSemigroup` proves the actual independent-increment restart law, and `BrownianForwardDerivative` derives the forward weak derivative. `BrownianParticle.eq_globalLaw_of_weakEvolution` now identifies every stated weak particle evolution with the actual Brownian law. `WeakEvolution.eq_of_same_initial_time_dependent` proves actual time-dependent weak uniqueness; `ReferenceDriftDerivatives` derives all needed uniform spatial bounds from the original kernel. `PrescribedReference.eq_law_of_weakEvolution` and `PrescribedReference.law_tensor_eq_supplied` identify the supplied reference law and its tensor curve with the constructed Brownian flow. |
| Negative-Sobolev Riesz representation | `WeightedTangent.existsUnique_tangent`, `WeightedTangent.representative_divergence`, `WeightedTangent.energy_eq_integral`, `WeightedTangent.flux_energy_decomposition`; `WeightedTangent.extendedEnergy_le_liminf`, `WeightedTangent.exists_tangent_of_weak_limit`; `exists_configurationTangent` | Actual weighted gradient closure, minimal divergence representatives, measurable spacetime Riesz flux, and weighted weak lower semicontinuity are proved. The remaining bridge is rough finite-action transport, not measurable selection of a timewise optimizer. |
| Wasserstein metric speed | `wasserstein_length_of_random_trajectory`, `wassersteinSq_of_l2_integral` and `wassersteinSq_of_pointwise_derivative` | Construct a Lagrangian representation from the general Eulerian continuity equation, including the nonsmooth finite-energy case. The pointwise-to-L² Fubini/FTC and genuine transport-length implication are proved with time-L¹ of L² speed, allowing the endpoint singularity. |
| Entropy–cost regularization | `BrownianEntropy.flow_entropy_le_coupling`, `BrownianEntropy.flow_entropy_le_wassersteinSq`, `BrownianEntropy.flow_entropy_finite`, `BrownianParticle.globalLaw_entropy_le_wassersteinSq` | Complete for the actually constructed continuous, globally bounded, globally Lipschitz Brownian flows, with exact coefficient `(1+LT+L²T²/3)/(4T)` and corrected KL direction. Proof uses genuine Gaussian histories, actual Brownian Euler law identification, deterministic bridge conjugacy, Euler convergence, joint KL lower semicontinuity and coupling optimization. No Girsanov premise remains in these results. The manuscript's broader measurable/unbounded drift lemma is not asserted, and identification for particle laws is now proved in `ParticleWeakIdentification`; the time-dependent reference identification is now proved in `ReferenceWeakIdentification` and `ReferenceTensorIdentification`. |
| Monotone entropy increments | `exchangeable_finiteEntropyConditions`, `exchangeable_marginal_entropy_second_difference`, and the original telescoping lemmas, for the actual `marginalEntropy` of an exchangeable law relative to tensor reference | `regularized_entropy_profile` and `brownianLaw_finiteEntropyConditions` now derive the finite full entropy and quadratic all-level profile from the actual decoupled Brownian regularization. The entropy increments follow from actual KL, disintegration, swap symmetry and chain rules. |
| Sharp source bounds | `internal_source_energy_le_entropy`, `internalCurrentSquare_exp_le`, `internal_source_marginal_energy_le_profile`, `exchangeable_conditional_source_quadratic_bound`, `integral_particleDrift_eq_marginalScalarDrift`, `marginalSourceCurrent_decomposition`, `marginalSourceSquare_integrable_and_le_profile`, `exists_marginalSourceDistribution`, `exists_fullSourceDistribution` | Complete for the actual regularized reference-minus-particle current: `InitialSourceMarginalRegularized` gives one consistent full source and all-level initial energies. Separately audited `RegularizedBrownianSourceSwitch.prescribed_marginal_energy_le` now bounds the actual propagated marginal switch source by C(1+1/s)k²/N² from the original all-level Wasserstein hypothesis. |
| Orthogonal tangent-energy increment | `WeightedGradientApproximation` and `WeightedMarginal`: actual prefix gradient isometry, compact cutoff approximation, closed lifted marginal gradient subspace, canonical marginal representative as orthogonal projection, and exact energy increment | `CylinderWeakEvolution.marginal_weak_generator_identity` now proves the exact weak marginal equation by second-order cutoff approximation. Connect its occupation-measure formulation to the actual time-dependent canonical tangent distribution. The weighted marginal Hilbert construction itself is proved without an independence assumption. |
| Hessian cancellation and residual algebra | `HierarchyAlgebra.symmetric_hessian_pairing`, `HierarchyAlgebra.external_hessian_cancellation`, `HierarchyAlgebra.external_lifted_remainder`, `HierarchyAlgebra.matrixAction_norm_sq_le`, `HierarchyAlgebra.block_pairing_bound`, `HierarchyAlgebra.block_pairing_sq_bound`, `TangentEnergy.two_term_young_absorption` | `WeightedEnergyDerivative.hasDerivAt_weightedTangentEnergy` now proves actual varying-density energy differentiation using Lax–Milgram, including optimizer differentiability. `BochnerIdentity` and `DriftEnergyIdentity` now prove the actual compact-test diffusion and drift energy identities and bounds; `PDEPairings` proves strong-to-weak generator pairings. `PeriodicIntegrationByParts`, `PeriodicFourierTests`, `PeriodicBochner` and `WeightedGalerkin` additionally prove genuine periodic integration by parts, Laplacian-invariant Fourier trial spaces, coercive finite-dimensional optimizer construction and a uniform H² estimate. Match these to the evolving diffusion densities and complete the limiting energy differential inequality. |
| Cooperative hierarchy and quadratic profile | `scalar_comparison`, `finite_cooperative_comparison`, `hasDerivAt_quadraticProfile`, `quadraticProfile_supersolution`, `finite_cooperative_quadratic_bound` | `VolterraFourierSourceHierarchy` removes actual finite Fourier energy gaps in L¹. `BrownianPeriodicHierarchyInitial.brownian_periodic_quadratic_bound_initial_flux` proves the sharp periodic profile using actual Brownian coefficient derivatives, without a limiting derivative premise. `BrownianEnergyPeriodization.prefixEnergy_quadratic_bound` proves full Euclidean propagation for the original nonperiodic kernel. |
| Composed source propagation | `propagated_source_energy`, `propagated_riesz_energy` | The actual original-kernel source propagation is now proved in `BrownianEnergyPeriodization`; separately audited `RegularizedBrownianSourceSwitch` instantiates it with the original Wasserstein data, actual regularized law, and actual initial drift-difference current. Rough transport from the resulting continuity equation remains open. |
| Torus approximation and singular initial laws | `SmoothCutoff`, `WeightedGradientApproximation`, `WeightedTangentLimit`: actual smooth compact approximants, strong L² gradient convergence, and weak-law energy lower semicontinuity | The direct weighted-measure Fourier route avoids assuming a convolved-source commutator estimate. `PeriodicEnergyExhaustion.full_energy_le_of_periodic_multiples` recovers full Euclidean energy from all physical period multiples. `BrownianEnergyPeriodization` applies actual sine-kernel Brownian/Jacobian convergence with the same initial current and source across kernels. Singular initial laws are admitted without a density lower bound. |
| Switch-time interpolation and endpoint singularity | `RegularizationRates.intervalIntegrable_inv_sqrt`, `RegularizationRates.intervalIntegrable_speedRate`, `RegularizationRates.integral_inv_sqrt`, `RegularizationRates.integral_speedRate`, `RegularizationRates.integral_speedRate_le` | Actual switch differentiation, scalar source continuity, and integrated compact-test equations are now proved; the separately audited `PrescribedSwitchMarginalSourceContinuity` handles genuine marginal sources using bounded noncompact cylinders. `GeometricEndpointLength` and the actual metric-curve adapters are separately audited. The needed rough finite-action transport theorem is still open. |
| Decoupled leg and final estimate | `wasserstein_endpoint_assembly`, `DecoupledFlow.law_tensor`, `DecoupledFlow.law_wassersteinSq_le`, `ParticleFlow.law_wassersteinSq_le`, `nonlinearDrift_continuous_curve` | The separately audited `PrescribedDecoupledTransport` and `PrescribedSwitchEndpoint` discharge actual decoupled marginal stability, supplied weak-law endpoint identification, the missing zero initial level, uniform horizon constants, triangle/squaring, and original family quantifiers. `propagatedHierarchy_of_switch_lengths` still requires the true switch length bound, whose remaining analytic input is rough finite-action transport. |
| Gaussian optimality remark | `GaussianSharpness.particleGaussianLaw_transport_exact`, `GaussianSharpness.gaussian_initialHierarchy`, `GaussianSharpness.particleGaussianLaw_fixed_time_lower`, `GaussianSharpness.particleGaussianLaw_heat_convolution`, `GaussianSharpness.gaussian_sharpness_hypotheses`, `GaussianSharpness.gaussian_sharpness_fixed_time` | Complete example: actual Gaussian probability laws, exchangeability, marginal consistency, exact transport cost, C₀=1/4, sharp lower rate, covariance, uniform second moments, and every field of actual `WeakEvolution`, `IsParticleEvolution` and `IsLimitEvolution` are proved. |

The target retains the manuscript's unnormalized Euclidean cost, first-`k`
marginals, self-interaction, diffusion coefficient one, all-level initial
assumption, and uniformity over `0≤t≤T`. Its conclusion constant is quantified
before the kernel and laws, allowing dependence only on
`d,C₀,T,M,L₁,L₂`. The kernel bounds use actual first Fréchet derivatives.

Arbitrary weak solutions now have proved narrow continuity and a derived extension of their weak equation to bounded smooth tests (`WeakEvolutionContinuity`, `WeakEvolutionBoundedTests`). These results use the stated moment and compact-test assumptions and dominated convergence. `WeakAutonomousUniqueness.eq_of_same_initial_autonomous` now proves uniqueness for actual autonomous smooth bounded drifts with bounded derivatives; `ParticleWeakIdentification` derives those conditions from the manuscript kernel and identifies arbitrary weak particle laws. `WeakTimeUniqueness` now proves time-dependent weak uniqueness by actual varying-drift backward Euler tests. `ReferenceDriftDerivatives` discharges its uniform derivative hypotheses from the manuscript kernel, and `ReferenceTensorIdentification` proves the exact supplied tensor-law identity and its complete weak equation.

`DriftApproximation` and `DriftFlowConvergence` prove locally uniform bounded-drift approximation implies narrow, mean-square, and actual Wasserstein convergence of the constructed continuous-input laws. The concrete sine periodization has now been connected to these results, including actual Brownian law convergence. Periodic density smoothing is proved separately; its equation and transport passages still require proof.

No result labeled here as missing is supplied through a new axiom or a
placeholder proof. Detailed semantic checks and the local Mathlib inventory
are in `qa/semantic_audit.md`. In particular, local Mathlib has KL chain-rule,
Brownian-process, and Hoeffding sources; the general diffusion change-of-measure theorem and Eulerian dynamic Wasserstein
representation are still open. Their finite-energy and Lagrangian consequences
listed above are implemented.

## Domain checks

The main target requires `N≥1` and `1≤k≤N`. Auxiliary scalar helpers use
Lean's total division at `N=0`; the hierarchy assertions then have no
admissible levels. Cooperative comparison is used on `a≤b` (an empty interval
is vacuous). Its right-derivative and continuity assumptions are explicit.
The bridge formula requires `s>0`; a Lipschitz interpretation uses `L≥0`.
The speed identities are oriented interval integrals for general real
endpoints and are used as lengths only for `0≤t≤T`. The value assigned to the
inverse-square-root function at zero does not affect its Lebesgue integral.
Gaussian scalar bounds require `a>0`, `r≥0`, and, for the lower bound, `r≤1`.

## Autonomous weak-particle uniqueness checkpoint

`qa/particle_identification_verification.json` records independent kernel
replay and standard-axiom closure for nine additional modules / 18 declarations.
The proof derives a uniform weak-time modulus over bounded Lipschitz test
families, uses actual smooth Gaussian backward Euler tests with common C³
bounds, telescopes the weak/Gaussian errors, takes the mesh to zero, and
separates finite measures using actual sine/cosine characteristic tests.
No backward PDE, SDE uniqueness theorem, or assumed Markov duality is used
as a new hypothesis. This group is included in the 234-source umbrella checkpoint.

## Time-dependent weak-reference identification checkpoint

`qa/reference_identification_verification.json` records independent kernel
replay and standard-axiom closure for 11 additional modules / 42 declarations.
`ProbabilityParameterIntegral` and `TimeGeneratorUniform` derive the required
time modulus from actual narrow continuity and joint drift continuity.
`GaussianTimeBackward` constructs tests with the correct drift at every step;
`WeakTimeBackwardTelescope` and `WeakTimeUniqueness` prove equality of arbitrary
weak solutions by vanishing-mesh comparison. `UniformBoundedDerivatives` proves
that actual probability averaging preserves each derivative bound, uniformly
over the averaging probability law. `ReferenceDriftDerivatives` therefore
derives every auxiliary spatial bound from the original kernel, including for
singular reference laws. `ReferenceWeakIdentification` and
`ReferenceTensorIdentification` identify the supplied reference evolution and
its tensor powers with the constructed Brownian flow. No extra time derivative,
density assumption, or uniqueness premise is added to the manuscript target.

The sharp tangent-energy evolution, switch derivative, Eulerian dynamic
transport theorem, and torus-to-Euclidean transport limit are still open.

## Entropy relative to the supplied reference

`qa/prescribed_entropy_verification.json` independently verifies the additional
`PrescribedEntropyProfile` module / three declarations. The theorem
`PrescribedReference.marginal_klDiv_le_initial_profile` now bounds the actual
regularized marginal KL divergence relative to `tensorLaw (μ t) m`, with the
explicit coefficient `bridgeCost (sqrt d * L₁) t * C₀ * m²/N²`. Both the
Euclidean Lipschitz conversion and identification of the one-particle reference
are derived. This module is now included in the fully kernel-replayed 234-source umbrella
checkpoint (2,009 audited declarations).

## Periodic drift-energy identity

`qa/periodic_drift_energy_verification.json` verifies `PeriodicDriftEnergy`
(one additional module / nine declarations).
`PeriodicDriftEnergy.integral_drift_energy` proves the genuine periodic
integration-by-parts cancellation, leaving precisely the Euclidean Jacobian
quadratic form. The result applies to actual smooth periodic potentials and
drifts; it does not assert the limiting rough-optimizer energy evolution.
The drift Galerkin limit is now proved in the checkpoint below. Actual source
evolution, the sharp marginal hierarchy and rough dynamic transport remain open.

## Actual parabolic optimizer and initial Jacobian checkpoint

`qa/parabolic_flow_verification.json` verifies 11 modules / 82 declarations,
now part of the 234-source umbrella. `PeriodicDriftResidual` derives the exact
finite drift identity and proves that the genuine Galerkin residual vanishes
from an actual smooth source pairing and elliptic H² bound.
`PeriodicCoefficientBounds` derives all auxiliary coefficient bounds from
smooth periodic data; none enters the final energy constant.
`PeriodicJacobianLimit` identifies the actual limiting Jacobian integral.
`PeriodicParabolicEnergy.deriv_energy_le` proves the genuine closed-space
energy inequality `E' ≤ 2 L E + 2 J(U)` from density/source PDEs and time
Banach derivatives. It does not prove those source PDE hypotheses for the
propagated manuscript tangent, nor the sharp marginal external interaction.

`FlowInitialDerivativeSmooth` constructs the actual initial-state derivative
of the autonomous continuous-input flow on every finite horizon and proves
its norm bound `exp(K*t)`. `PeriodicConvolutionWeak` derives the actual
pointwise smoothed-density time derivative from the stated weak evolution.

## Separately verified smoothing and Eulerian flow connections

`qa/smoothing_jacobian_verification.json` records six modules / 49 declarations.
The actual convolution density has a time derivative in the bounded-continuous
sup norm. Arbitrary integrable finite-energy fluxes admit an explicitly
constructed smoothed velocity whose weighted quadratic action contracts;
source pairings converge on continuous periodic fields. The actual flow
Jacobian is jointly continuous in initial point and path at fixed time,
measurable, and preserves Lᵖ with the proved exponential bound.

`qa/eulerian_flow_verification.json` records four modules / 35 declarations.
`WeakContinuity.eq_of_same_initial` proves uniqueness for the first-order weak
continuity equation using genuine backward Euler tests.
`EulerianTransport.flowLaw_weakContinuity` constructs the actual deterministic
flow law and derives that weak equation by pathwise FTC and Fubini. The tested
class currently consists of smooth functions with bounded derivatives; the
compact-test extension and rough finite-action representation remain distinct
obligations. These checks do not establish `MainTheorem`.


## Convolved sources and smooth dynamic transport

The 259-source aggregate checkpoint includes `PeriodicConvolvedOptimizer`:
the actual convolved scalar source is minus the divergence of the convolved
flux, acts correctly on every smooth periodic test, and its constructed
periodic optimizer has energy bounded by the original Euclidean flux energy
with coefficient one. Smoothness is derived for initially merely integrable
fluxes. `PeriodicConvolutionPDE` derives the actual density PDE and exact drift
commutator from the original weak evolution; that commutator has not been
discarded.

`EulerianTransport.CompactWeakContinuity.wasserstein_length_le_action` derives
the actual Wasserstein length bound from the standard compact smooth test
continuity equation for a jointly continuous, spatially smooth bounded velocity
with bounded spatial derivatives. It derives equality to the characteristic
law and propagates second moments. Extension to general finite-action rough
velocities is still open.

`PropagatedFlux.Flow` constructs the tangent distribution transported by the
actual flow Jacobian, identifies its initial value, proves the genuine
semigroup derivative pairing and exponential energy bound. The homogeneous
compact-test propagated-source time equation is now proved in
`PropagatedSourceEquationLaw`. The sharp marginal
hierarchy, switch derivative and limiting tangent-energy argument remain open.


## Actual marginal energy and external interaction

The 268-module aggregate checkpoint includes `PeriodicMarginalLift`, which
proves that actual prefix lifting preserves the closed periodic gradient space,
and `PeriodicMarginalEnergy`, which proves genuine convolved marginal weighted
pairing, optimizer orthogonality and the exact increment `E_full − E_marginal`.
No independence assumption or projection conclusion is added as a premise.

`ExternalInteractionGradient` derives the actual interaction-test gradient bound
with coefficient linear in marginal size; `ExternalInteractionEnergyCancellation`
derives its literal integrated fluctuation/diagonal decomposition and Young
absorption bound. The full weak Hessian is constructed in
`PeriodicHessianDissipation`, and `PeriodicParabolicDissipation` retains the
negative twice-weighted-Hessian term. A combined Galerkin passage to the sharp
marginal hierarchy is in progress; positive Hessian terms cannot be passed to
the weak limit by lower semicontinuity in the wrong direction.

Separately, `qa/propagated_source_equation_verification.json` verifies eight
modules / 42 declarations from the actual Brownian propagated-source equation
through its canonical distribution, initial value and output-law identity.
The compact-test source PDE is derived rather than assumed. The periodic
bounded-test/dual-norm extension is in progress. These components are now included in the 304-module aggregate checkpoint.


## Actual source time differentiation and symmetry

The 304-module / 2,546-declaration aggregate checkpoint includes compilation,
independent kernel replay, and standard-axiom inspection of every declaration.
`PeriodicSourceConvolutionBCF` derives the genuine convolved-source derivative
in bounded-continuous sup norm, including endpoint derivatives within the
time interval, from the actual Brownian weak equation. No source time
regularity hypothesis is inserted. Its extension to the dual gradient norm
is being constructed separately.

`InitialSourcePermutationPropagation` derives both compact source and bounded
source-action permutation invariance from the actual generator discrepancy,
exchangeable initial law and finite source energy. `WeightedSourceSymmetry`
derives equivariance of the canonical minimal-energy representative using
uniqueness and the exact energy decomposition. No assumed representative
equivariance or propagated-source symmetry remains in these results.

`FlowJacobianDriftSmooth` proves convergence of the actual initial-state
Jacobian under locally uniform bounded smooth drift approximation and
moving-point derivative convergence. `PeriodicParticleDerivative` discharges
the derivative convergence for sine-periodized particle drifts.
`PeriodicFluxCommutatorLimit` removes the genuine operator/flux commutator in
weighted quadratic action. Density commutators paired with optimizer Hessians
still require a justified limiting argument.

`ExternalInteractionEnergyLimitEstimate` combines the positive external
Hessian term with negative dissipation before the Galerkin limit. It does not
reverse lower semicontinuity. The differential hierarchy, switch derivative,
and rough Eulerian transport assembly remain open.


## Coefficient-one marginal smoothing and actual source limits

The 326-module / 2,687-declaration aggregate build, independent kernel replay,
and standard-axiom audit are recorded in `qa/verification_checkpoint.json`.
`PeriodicConvolutionMarginalEnergy.marginal_convolved_representative_optimizer_energy_le`
proves that the actual marginal of the smoothed full source has energy bounded
by the original canonical marginal energy, with coefficient one. Its proof
constructs the averaged scalar potential, proves its exact Euclidean gradient,
and uses compact-cutoff marginal consistency on the true periodic closure.

`PeriodicSourceConvolutionDual` now derives the actual source functional's
time derivative in the continuous dual norm. The fixed potential reconstruction
uses the proved periodic Poincare inequality and orthogonal projection onto
the periodic gradient space. Source and derivative mass-zero identities are
derived, including the appropriate positive-horizon endpoint hypothesis.

`ExternalInteractionSymmetryEstimate` derives the external source sum with
coefficient `(N-m)/N` and identifies its actual observed canonical tangent.
`PeriodicParticleTangentLimitIdentification` proves convergence of actual
projected Jacobian-source pairings and carrying laws for sine-periodized
particle drifts. It transfers a supplied periodic energy bound unchanged;
it does not assume or prove that the sharp hierarchy bound has been obtained.

A separately audited mathematical route under development uses a coefficient
penalty in finite Fourier Gram matrices for the actual evolving measure.
The final hierarchy will require a justified positive-kernel integral
comparison; no differentiability of the limiting rough energy is presumed.

## Direct coefficient evolution and periodic tangent checkpoint

The 363-module checkpoint additionally includes the constructed coefficient
Gram operator with positive coefficient penalty, exact energy gap and trial
recovery bound, and the actual finite weighted gradient map.
`FiniteGradientTrial.solution_diffusion_identity` proves the exact negative
Hessian term and the additional dissipative diagonal coefficient term.
`FiniteCoefficientEnergy.brownian_optimizedEnergy_hasDerivWithinAt` derives the
finite optimized energy derivative from the actual Brownian carrying law and
propagated Jacobian source, including horizon endpoints. No density or
differentiated Gram equation is assumed in that result.

`WeightedPeriodicFourier` proves uniform C¹ approximation of every smooth
periodic test by actual finite Fourier sums, and the corresponding closure
inside the true weighted gradient space of an arbitrary finite measure.
`WeightedPeriodicTangent` and `WeightedPeriodicMarginal` construct the genuine
periodic orthogonal representatives and their exact marginal energy increment.
This periodic closure is not identified with the whole compact-gradient
closure. `WeightedPeriodicFourierScale` proves physical-period test scaling,
including the true eigenvalue factor 1/P² and uniform C¹ recovery; physical
weighted-closure wrappers are separate later additions.

`VolterraHierarchy.finite_quadratic_bound` proves the sharp quadratic
comparison directly from positive-kernel integral subsolution inequalities.
The limiting energy need not be continuous or differentiable. Deriving these
inequalities for the actual marginal energies remains necessary.

`SwitchSourceDerivative.prescribed_switch_compact_hasDerivAt` and
`prescribed_switch_compact_sub_eq_integral` now prove the actual prescribed
switch-curve derivative and its integrated identity at endpoints. The source
is exactly reference drift minus particle drift; its literal propagated
Jacobian-flux representation and integrability are proved. The sharp energy
propagation and rough finite-action transport needed to bound this curve's
Wasserstein length remain open.

Later independently audited modules and ongoing work are not counted in this
aggregate checkpoint. `MainTheorem` remains unproved.


## Actual source and finite energy checkpoint (406 modules)

The latest aggregate `qa/verification_checkpoint.json` records 406 source files
and 3,205 named declarations, with independent kernel replay and standard-axiom
closure. These counts include definitions and are not completion percentages.
The earlier table records the original component interfaces; the following
paragraphs supersede its remaining-bridge descriptions where specified.

The actual finite coefficient generator identity and inequality now retain the
negative Hessian dissipation and place auxiliary drift-supremum dependence only
in the true regularized energy gap. Physical-period representatives, exact
periodic marginalization, Fourier recovery, and true physical Laplacian scaling
are included. Periodic closure is still distinguished from full Euclidean
closure; their equality at a fixed period is never assumed.

`InitialSourceMarginal.exists_regularized_weighted_marginal_profile` constructs
one genuine full regularized source and proves the sharp initial profile for
all its literal weighted marginals. `PeriodicMarginalCoefficientEvolution`
derives actual source and Gram coefficient derivatives from the Brownian law,
with exact internal/self-interaction and external `(N-m)/N` terms. The source
symmetry is obtained from the initial exchangeable law and equivariant field.

`RoughEulerianTransportContinuity` constructs jointly measurable spacetime L²
flux from scalar source action and proves the actual continuity equation. The
general rough Eulerian-to-Wasserstein length implication still requires its
smoothing and limiting passage. Additional frozen scoped checks (finite
hierarchy, initial-source consistency extensions, Fourier Volterra assembly,
and spatial compression) are recorded separately until the next aggregate.

The actual finite derivative-to-sharp-profile assembly, periodic-to-full energy
exhaustion, rough metric-length theorem, and final switch/endpoints remain to be
connected. `MainTheorem` is still a proposition without a proved inhabitant.
