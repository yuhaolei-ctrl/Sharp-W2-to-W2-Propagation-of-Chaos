# Semantic audit of the partial Lean development

Audit dates: initial review 2026-09-16; analytic connections updated 2026-09-17. The audited manuscript is
`rethlas/manuscripts/sharp_wasserstein_bounded_kernel_open/sharp_wasserstein_propagation.tex`.
The local library inspected is Mathlib 4.32.0 at
`rethlas/agents/generation/tmp/mathlib4-4.32.0/Mathlib`.

**The complete manuscript theorem is not proved.** `MainTheorem` in
`SharpWasserstein/Dynamics.lean` is a definition of an open proposition. It is
neither an axiom nor a proved theorem. The checked analytic/algebraic modules
below do not supply its missing probabilistic and PDE arguments.

## Target and definition checks

| Item | Audit result |
| --- | --- |
| Particle space | `Configuration d N = Fin N → (Fin d → ℝ)` is a concrete finite-dimensional real coordinate space. The target restricts `d ≥ 1` and `N ≥ 1`. |
| Transport cost | `productCost x y = ∑ i, ∑ a, (x i a - y i a)^2` is the manuscript's **unnormalized** squared Euclidean product cost. There is no factor `1/N`, `1/k`, or `1/d`. The ambient Pi-space sup norm is not substituted for this cost. |
| Couplings | `IsCoupling μ ν γ` requires that `γ` is a probability measure and that its two coordinate pushforwards are exactly `μ` and `ν`. `wassersteinSq` takes the infimum of the actual nonnegative cost integrals over those couplings. Empty coupling families give `∞`, not zero. The diagonal, coordinate-swap, and coordinate-deletion coupling constructions give genuine self-distance, symmetry, and marginal-contraction results. |
| Probability and moments | `WeakEvolution` requires probability measures, actual finite second-moment integrals at every nonnegative time, and a finite second-moment bound on every finite time interval. These conditions contain no chaos estimate. `IsLimitEvolution` separately requires probability of the original one-particle law. |
| Tensor law | `tensorLaw` uses the genuine finite product `Measure.pi`. The requisite probability property follows from Mathlib's product-measure instance once probability of the factor is installed. |
| First `k` marginal | `restrictCoordinates hk` uses `Fin.castLE hk`, preserving the coordinate indices `0,…,k-1`. Thus `marginal hk` is exactly the first-`k` pushforward, not an arbitrary subset or an averaged marginal. |
| Exchangeability | `Exchangeable` requires invariance under every permutation of `Fin N`. `IsParticleEvolution` imposes it at time zero. For the constructed continuous-noise particle flow, permutation covariance and preservation under permutation-invariant noise are now proved in `ParticleFlowPermutation`. Identification with all `WeakEvolution` laws remains open. |
| Self-interaction | `particleDrift` sums over all `j : Fin N`, including `j = i`, with coefficient `(N : ℝ)⁻¹`. No diagonal term is removed. |
| Diffusion coefficient | `laplacian` sums the actual second coordinate derivatives. `generator` is `Δφ + v·∇φ`; its Laplacian coefficient is one, matching noise amplitude `√2`. |
| Derivative meaning | Coordinate derivatives are evaluations of actual Fréchet derivatives on coordinate basis vectors. Although `fderiv` is totalized on nondifferentiable functions, the test class requires actual `ContDiff` smoothness. No arbitrary derivative oracle is used. |
| Weak equation and sign | `WeakEvolution.equation` is `∫φ dP_t - ∫φ dP_0 = ∫₀ᵗ∫(Δφ+v·∇φ)dP_s ds`, the weak form of `∂ₜP=ΔP−div(vP)`. Explicit space/time integrability prevents the equation from relying on undefined integrals. Smooth compact tests are integrable under the required probability measures. |
| Nonlinear drift | `nonlinearDrift b μ x` is the Bochner integral `∫b(x,y)dμ(y)`. Smooth bounded kernels and probability of `μ` supply its intended integrability; `DriftBounds.kernel_integrable`, `nonlinearDrift_bound`, and `nonlinearDrift_lipschitz` now prove this and the required spatial Lipschitz bound. `singletonLaw` transfers the one-particle equation to the `N=1` configuration space. |
| Kernel regularity | `BoundedSmoothKernel` uses actual smoothness of the uncurried kernel and bounds on every iterated Fréchet derivative, including order zero. This matches the manuscript's stated meaning of `C_b^∞`. |
| Constants | The revised target quantifies `d,C₀,T,M,L₁,L₂` **before** `∃ C`, then quantifies the kernel, laws, and particle family **after** `C`. `KernelBounds` uses the actual norms of `b`, `D₁b`, and `D₂b`. Thus `C` is uniform in `N,k`, the initial laws, the kernel within those bounds, and higher derivatives. |
| Norm convention for kernel bounds | Positions and continuous linear maps use the standard Pi-space sup/operator norms. This differs from the manuscript's Euclidean convention but only by factors depending on `d`, which is an allowed constant dependence. `ConfigurationEuclidean` now proves the exact coordinate/cost/gradient conversion; `EuclideanDrift` and `EuclideanFlow` prove the resulting particle-number-independent Euclidean drift and trajectory bounds. |
| Rate and time interval | Initial and final inequalities use `C*k²/N²`, with positive `N,k` and `k≤N`. `PropagatedHierarchy` quantifies every `t∈[0,T]`, including zero; this expresses the manuscript's finite-horizon supremum bound. `ENNReal.ofReal` cannot erase a negative proposed constant because `C₀,C≥0` are explicit. |

## Vacuity and equivalence obligations

No target conclusion is embedded in `WeakEvolution`, `BoundedSmoothKernel`, or
the initial assumptions. The scalar helper theorems do assume their explicitly
stated scalar differential or energy inequalities, and prove consequences of
those inequalities; they do not construct the diffusion quantities satisfying
them.

The target currently concerns all weak Fokker–Planck evolutions in the stated
regularity class. The following bridges are **unproved**, so a proof of the
target alone would still need them to recover the manuscript's SDE statement:

1. Existence and uniqueness of the particle and McKean–Vlasov evolutions for the
   stated initial laws, and the connection between their SDE laws and
   `WeakEvolution`. In particular, no formal evolution witness currently
   certifies nonvacuity of this solution class.
2. The finite-moment, compact-test continuity, and generator-integrability
   properties of those laws. Compact-test continuity plus moment control is
   designed to give narrow continuity in this finite-dimensional setting;
   that implication has not been formalized here.
3. Probability and second-moment preservation under the marginal, tensor, and
   singleton constructions, together with the identification of the
   singleton weak equation with the usual one-particle equation.
4. The custom transport infimum now has finite-cost product couplings,
   genuine disintegration-based gluing, the square-root triangle inequality,
   and a P₂ pseudometric. `DynamicTransport` and `PointwiseTrajectory` prove
   actual Lagrangian transport length from pointwise trajectories. Metric
   separation, general weak convergence properties, and passage from a
   general Eulerian continuity equation to those trajectories remain open.

No contradictory definition was found. The absence of an existence proof is
an explicit outstanding task, not evidence that the assumptions are
inconsistent or that the open proposition has been proved nonvacuously.

## Manuscript-to-Lean proof map

The current complete step-by-step map is maintained in
[`THEOREM_STATUS.md`](../THEOREM_STATUS.md), to avoid divergent copies. The
principal connections checked on 2026-09-17 are:

- The entropy-density orientation is now an equality for Mathlib’s actual
  extended-valued KL divergence. Measurable-map data processing, sharp
  scalar/Hilbert Pinsker, and the integral conditional-KL chain rule are proved.
- Finite full entropy and actual exchangeability now imply the complete
  `FiniteEntropyConditions` for the true prefix entropies. No entropy
  monotonicity assumption is retained in that theorem.
- Tangents are actual L² gradients of compact smooth tests, with divergence
  representation, exact minimal energy, weak-law lower semicontinuity, and
  exact conversion to the manuscript’s coordinate space.
- Smooth cutoffs justify cylinder-gradient inclusion. The actual marginal
  tangent is the orthogonal projection and obeys the exact energy-increment
  identity. Identifying it with a diffusion’s evolving marginal tangent is
  still an analytic obligation.
- Pointwise trajectories with time-L¹ of L² velocity give the genuine
  Wasserstein length estimate by Fubini/FTC and an explicit common-label
  coupling. This does not yet establish the general Eulerian representation.
- Globally bounded Lipschitz drifts have constructed finite-horizon integral
  solutions for every continuous additive input. Initial/noise dependence,
  measurability, uniqueness, moment propagation, and uniform-in-N particle
  Wasserstein stability follow from those equations.

The diffusion change of measure, nonlinear self-consistency, weak-equation
identification/uniqueness, differentiated diffusion tangent hierarchy,
periodization/smoothing, and switch-curve derivative are not supplied by these
connections. They remain genuine outstanding proofs.

## Review of the assembly theorems

`SharpWasserstein.propagated_source_energy` genuinely composes
`source_energy_from_entropy_profile` with
`finite_cooperative_quadratic_bound`: it derives the initial coefficient
`2*K*(1+5*H)` and propagates it with the factor `exp(4*C*(t-a))`.
The entropy-sequence conditions, all-level entropy bound, internal and external
energy inequalities, initial velocity decomposition, and the continuity and
differential inequalities for `E` remain explicit hypotheses. Uniformity of
those constants for an actual family of diffusions is still to be established.

`SharpWasserstein.propagated_riesz_energy` specializes that result to genuine
Hilbert-space variational energies using `TangentEnergy.dualEnergy_eq_norm_sq`.
The newer `WeightedTangent`, `ConfigurationEuclidean`, and `WeightedMarginal`
modules construct the actual weighted gradient spaces and marginal projections.
Identification of their actual diffusion tangents is still open. The level-dependent Hilbert spaces in the statement are
permitted to be abstract; the differential hierarchy is still a hypothesis.

`SharpWasserstein.metric_endpoint_assembly` uses an actual pseudometric triangle
inequality and the proved interval integral, yielding
`(K*(T+2*sqrt T)+exp(L*T)*sqrt C₀)^2*k²/N²`. Its length bound and decoupled-distance
bound are hypotheses. `TransportTriangle` now constructs the actual P₂ pseudometric and
`wasserstein_endpoint_assembly` specializes the estimate to `wassersteinSq`.
Deriving the interpolation length assumption from the actual propagated
diffusion source remains open. Allowing
`N=0` or `k=0` in this general helper does not falsify it: then its distance
hypotheses force zero distances; the manuscript target itself still requires
`1≤k≤N`. No target theorem is assumed by an opaque axiom.

## Local Mathlib foundation inventory

The following findings come from filename and full-source `rg` searches of the
local Mathlib tree. “Not found” means that these searches did not locate a
ready-made result in this checkout; it is not a claim of logical impossibility
or of absence from all external Lean projects.

- **Brownian motion is available in source.**
  `Probability/BrownianMotion/Basic.lean` defines `IsPreBrownianReal` and
  `IsBrownianReal`, with Gaussian-law, covariance, independent-increment, and
  weak-Markov results. These do not supply Girsanov or an SDE solver.
- **SDE/stochastic integral/Girsanov foundations were not found.** Searches for
  `Girsanov`, `Novikov`, `stochastic differential`, `stochastic integral`,
  `Itô`/`ItoFormula`, and `Fokker–Planck` found no relevant development. No
  McKean–Vlasov result was located.
- **Wasserstein/dynamic transport foundations were not found.** Searches for
  `Wasserstein`, `Kantorovich`, `optimal transport`, `Benamou`, and `continuity
  equation` located no relevant library. The project's transport cost is
  consequently defined directly rather than imported as a mature metric API.
- **Relative entropy and a genuine KL chain rule are available in source.**
  `InformationTheory/KullbackLeibler/Basic.lean` defines `klDiv : ℝ≥0∞`, with
  integrability/absolute-continuity characterizations. For probability laws
  the mass-correction terms vanish, giving the manuscript's entropy.
  `ChainRule.lean` proves `InformationTheory.klDiv_compProd_eq_add` for finite
  measures and Markov kernels, and `klDiv_compProd_left`. Its documented TODO
  is the integrated pointwise conditional-KL version. Disintegration tools
  exist under `Probability/Kernel/Disintegration`.
- **KL data processing and Pinsker were not located as ready-made results.**
  Searches of the KL files and full tree found no KL map/kernel-contraction
  theorem or Pinsker theorem. The library's named data-processing theorem for
  Bayes risk is a different result. The KL chain rule and disintegration are
  building blocks used by the now-proved `EntropyDataProcessing`,
  `EntropyObservable`, and `EntropyChainRule` modules.
- **Hoeffding is available in source.**
  `Probability/Moments/SubGaussian.lean` contains
  `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`,
  `hasSubgaussianMGF_of_mem_Icc`, and
  `HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`. These provide the
  scalar bounded-centered/MGF/tail foundation; the manuscript's conditioned
  vector exponential-square estimate has now been derived in `SubGaussianSquare`,
  `BoundedIndependentSum`, `InternalSource` and `InternalSourceProfile`.
- **Source availability is distinct from checked imports.** The local
  copy-on-write bootstrap now builds the required KL, conditional expectation,
  disintegration, Hoeffding, ODE, and other dependency closures. Exact hashes
  are recorded in `mathlib_dependencies.json`; an available source file alone
  is never treated as a proof. The three locally repaired Mathlib elaborations
  are recorded in `mathlib_source_patches.json`. Their statements are unchanged,
  and the root audit verified that the recorded replacements exactly reproduce
  the patched files from the pinned upstream source.
- **External stochastic library audit.** The read-only snapshot
  `formal-mathfin` at commit `fee10f632016a2d72db0d7d68afcd52448205056`
  uses Lean 4.33.0-rc1 and has a scalar natural-filtration Girsanov development.
  This does not directly furnish the arbitrary-dimensional/general-filtration
  theorem required here. No result from that snapshot is imported or counted
  as checked in this project.

The actual continuous bounded-Lipschitz Brownian entropy-cost inequality now
follows from verified Gaussian histories, Brownian Euler identification, exact
meeting bridges, Euler convergence and joint KL lower semicontinuity. Coupling
optimization gives the true Wasserstein bound with the corrected direction;
Girsanov is not a remaining premise of this proof. The next decisive milestones
are identification with weak diffusions and the measure-valued transport/PDE
hierarchy bridges. Proving more scalar corollaries alone would not close the
manuscript theorem.

The pinned Brownian-motion v4.32.0 source closure and its Kolmogorov-extension
dependency (30 modules) have now compiled and passed independent sequential
kernel replay without source modifications. The nine audited core Brownian/Wiener
declarations use only propext, Classical.choice and Quot.sound. See
`brownian_verification.json`; this is not a Girsanov/Itô or full manuscript claim.
