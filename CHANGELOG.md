# Lean formalization changes — 2026-09-16

- Added a concrete measure-theoretic target with unnormalized quadratic
  transport cost, probability couplings, first-coordinate marginals, the
  self-interacting drift, and the weak equation for noise amplitude `√2`.
  The uniform conclusion constant is quantified before the laws and kernel.
- Proved self-distance, symmetry, marginal contraction, and finiteness under
  second moments for the actual quadratic transport infimum.
- Proved finite entropy-increment and source estimates, the Hilbert-space
  variational/projection identities, and Euclidean Hessian cancellation and
  norm estimates.
- Proved finite cooperative comparison and the `exp(4C(t-a))*m²/N²`
  supersolution; composed it with the initial source estimate.
- Proved the corrected reverse log-likelihood identity from an actual
  exponential Radon–Nikodym density and a zero-mean hypothesis under the
  original measure; the Girsanov construction remains open.
- Evaluated the actual bridge and speed integrals with their exact constants;
  proved the scalar Gaussian-mode bounds and conditional metric endpoint
  assembly.
- Added explicit theorem-status and semantic audits, pinned build commands,
  source hashes, an axiom audit, and separate kernel replay.

The main diffusion theorem remains unproved. No theorem has been replaced by
an axiom or a placeholder proof. No change to the mathematical manuscript is
claimed from these component checks, and its PDF is not labeled as formally
verified.

## 2026-09-17 — analytic connections

- Upgraded the entropy-direction correction to the actual KL divergence;
  proved measurable-map data processing, sharp scalar/vector Pinsker, and
  the integrated conditional-KL chain rule.
- Constructed genuine Wasserstein coupling gluing and triangle inequalities;
  specialized the endpoint bound to the manuscript’s transport infimum.
- Realized weighted negative-Sobolev energy in the actual compact-gradient
  closure, including distributional divergence, exact energy/minimality,
  weak-law lower semicontinuity, and explicit Euclidean/configuration conversion.
- Constructed smooth compact cutoffs and proved strong weighted L² gradient
  approximation, marginal gradient inclusion, and exact projection increments.
- Derived transport length from actual pointwise trajectories via Bochner
  Fubini and FTC, retaining time-L¹/label-L² integrability.
- Constructed finite-horizon bounded-drift solutions for continuous additive
  inputs; proved uniqueness, continuous dependence, measurable particle maps,
  moment propagation and genuine Wasserstein stability uniform in particle number.
- Made the build bootstrap the Mathlib imports of the selected proof closure
  automatically; preserved sequential independent kernel replay.

These additions do not yet prove `MainTheorem` or certify the full manuscript.

## 2026-09-17 — concrete source, variational, Gaussian and noise results

- Proved the actual exchangeable conditional external-source estimate and the
  internal empirical-source estimate including the diagonal self-term, deriving
  the exponential-square moment from product Hoeffding and a Gaussian mixture.
- Proved density-dependent elliptic invertibility by Lax–Milgram and derived
  the optimizer derivative and the exact derivative of weighted tangent energy.
- Constructed consistent exchangeable Gaussian laws, proved their exact
  quadratic transport cost, all-level initial bound C₀=1/4, matching lower rate,
  moments/covariance and heat convolution identity.
- Proved exact tensor preservation for constructed decoupled random flows,
  narrow continuity of particle laws and joint continuity of the genuine
  mean-field drift along narrowly continuous probability curves.
- Compiled and independently kernel-replayed the pinned Lean 4.32 Brownian
  construction and its 30-module source closure. Core constructor axiom checks
  contain only Lean's standard axioms; no stochastic change-of-measure theorem
  is claimed from this result.

The remaining PDE, entropy-cost limiting, interpolation and approximation
bridges are tracked in THEOREM_STATUS.md; the full theorem remains unproved.

- Connected independent continuous Brownian coordinate laws to the constructed
  particle flow, proving its genuine initial law, finite second moments,
  exchangeability, narrow continuity and dimension-controlled transport
  stability. The noise variance and total quadratic moment are exactly
  `2t` and `2Nd t`; weak Fokker–Planck identification is still separate.

- Completed the Gaussian example through every weak Fokker–Planck condition,
  using Gaussian integration by parts, dominated parameter differentiation and
  time FTC; assembled actual particle/limit evolution and sharpness hypotheses.
- Proved scalar/vector Gaussian KL and the exact entropy chain for constructed
  finite Gaussian histories, with cost integrated under the first history law.
- Derived Euler consistency from the actual trajectory integral and uniform
  continuity, proved endpoint convergence, and obtained narrow and mean-square
  convergence of measurable Euler laws by deterministic bounded-drift domination.
- Proved actual compact-test diffusion and drift energy identities, including
  Schwarz symmetry, the Euclidean Bochner identity and the Jacobian norm bound.

## 2026-09-17 — continuous entropy cost and actual source identification

- Proved the corrected entropy-cost inequality for actual continuous bounded
  Lipschitz Brownian flows: exact Gaussian transition KL, finite meeting bridge,
  actual Brownian Euler law, narrow limit, KL lower semicontinuity and infimum
  over P₂ couplings. The coefficient is `(1+LT+L²T²/3)/(4T)`; the particle
  specialization uses a Lipschitz constant independent of particle number.
- Proved horizon consistency and assembled actual global particle laws, with
  compact-time uniform second moments and all weak-evolution regularity fields
  except the integrated generator equation.
- Identified the actual disintegrated marginal particle drift with the internal
  and external currents; constructed its finite-energy distributional source
  and proved the quadratic profile bound, retaining the diagonal and treating
  the full-particle endpoint directly.

The interacting weak equation, tangent-energy evolution, dynamic transport
representation, switch curve and approximation passage remain open.


## 2026-09-17 — actual weak particle equation and approximation stability

- Proved the integrated weak generator equation for the constructed Brownian
  particle law by exact Gaussian one-step calculus, quantitative consistency,
  telescoping, and convergence of expected Euler Riemann sums. Assembled every
  field of `WeakEvolution` and `IsParticleEvolution`.
- Derived narrow continuity and the bounded smooth test equation from the
  original compact-test weak-evolution hypotheses and uniform second moments.
- Proved the all-level entropy profile and finite-energy signed source bound
  for the actual Brownian regularization, including the full-particle endpoint
  and the coefficient bounded by C(1+1/s).
- Constructed genuine coercive Galerkin optimizers and proved periodic
  integration by parts, Fourier Laplacian invariance, and the uniform Hessian
  estimate. No smooth limiting optimizer is assumed.
- Proved drift approximation stability along actual trajectories and locally
  uniform bounded-drift convergence of the true Wasserstein cost.

The full propagation theorem remains unproved; the remaining bridges are
listed in THEOREM_STATUS.md. Component verification does not certify the full
manuscript.

## 2026-09-17 — actual switch curve, periodic approximation, and smoothing

- Constructed the composed Brownian switch curve from arbitrary P₂ input,
  proved its exact particle/reference endpoints and W₂ continuity, including
  every marginal and both endpoints. No sharp speed estimate is assumed.
- Constructed smooth periodic sine approximations preserving precisely the
  original M,L₁,L₂ bounds, proved bounded derivatives of every order, and
  derived convergence of the actual Brownian particle laws in W₂.
- Proved Fourier density in the periodic gradient closure and constructed
  genuine weak L² Hessian entries for the limiting elliptic optimizer.
- Constructed normalized strictly positive product periodic kernels and their
  actual smooth convolution densities for arbitrary, possibly singular laws.
- Proved actual Brownian semigroup restart and forward weak differentiation;
  developed smooth backward Gaussian Euler tests with uniform derivative
  bounds for the still-open arbitrary weak-solution uniqueness argument.

The audited umbrella checkpoint contains 168 modules and 1634 declarations.
Later independently audited component groups have separate QA ledgers. The
main propagation theorem is still a proposition awaiting a complete proof.

## 2026-09-17 — removing the drift smoothing error

- Proved actual concentration of the positive periodic kernels using their
  unique cosine-potential maximum on the quotient torus, and convergence of
  smoothed laws against every continuous periodic test.
- Identified the genuine convolution drift commutator, proved its weighted
  quadratic bound without an inverse minimum-density constant, established
  action integrability, and proved the integrated action tends to zero.
- Proved exact equality between the prefix marginal of the smoothed law and
  the smoothed prefix marginal of the original law.
- Proved weak convergence of actual Galerkin Hessian entries and admissibility
  of products with the limiting optimizer.

The new full umbrella checkpoint passed compilation, sequential independent
kernel replay, and standard-axiom audit for 201 modules / 1855 declarations.
The tangent-source error and the remaining main-theorem bridges stay explicit.

## 2026-09-17 — identifying arbitrary weak particle laws

- Proved uniqueness for the stated weak Fokker–Planck evolution with an
  autonomous smooth bounded drift whose derivatives of every order are
  bounded. The proof derives the common test-family time modulus, compares
  actual Gaussian Euler backward tests, telescopes, and removes the mesh.
- Proved that smooth bounded tests with bounded derivatives separate finite
  measures by actual sine/cosine characteristic functions.
- Derived all particle-drift smoothness hypotheses from the manuscript's
  bounded smooth kernel and identified every weak particle evolution with
  its constructed Brownian law.

This additional group passed independent kernel replay and standard-axiom
audit (9 modules / 18 declarations). Time-dependent reference uniqueness and
the main tangent-energy/transport bridges remain open.

## 2026-09-17 — time-dependent reference identification

- Derived the generator's uniform time modulus from the stated weak-law
  continuity and joint continuity of the bounded drift.
- Constructed actual varying-drift backward Gaussian Euler tests with uniform
  first-three-derivative bounds, and proved uniqueness of arbitrary weak
  time-dependent evolutions by telescoping and vanishing mesh.
- Proved probability averaging preserves each spatial derivative bound
  uniformly over the law; derived all reference-drift regularity from the
  original bounded smooth kernel, with no density assumption.
- Identified the supplied nonlinear reference law and its exact tensor powers
  with the constructed Brownian reference flow, including the full weak
  equation at every particle level.
- Independently kernel-replayed and axiom-audited 11 new modules / 42
  declarations (`qa/reference_identification_verification.json`). The sharp
  tangent-energy and dynamic-transport passages remain unproved.

- Additionally connected the entropy regularization to the manuscript's
  supplied reference `μ_t`, deriving the Euclidean drift constant `sqrt d * L₁`
  and the actual marginal KL bound. Three declarations were independently
  kernel-replayed and axiom-audited in
  `qa/prescribed_entropy_verification.json`.

- Proved the actual periodic drift-energy cancellation by fundamental-domain
  integration by parts, with the exact Euclidean Jacobian quadratic form.
  Nine declarations passed independent replay and axiom inspection; the
  rough-optimizer limit remains open.
- Updated the aggregate checkpoint to 221 source files / 1,915 declarations.
  The separately audited entropy-reference and periodic-drift modules bring
  the verified total to 223 files / 1,927 declarations. `MainTheorem` is still
  an unproved proposition; these counts do not certify the full manuscript.

## 2026-09-17 — actual parabolic and Eulerian connections

- Proved the periodic drift Galerkin residual tends to zero using derived
  elliptic regularity and compact coefficient bounds. Identified the true
  limiting Jacobian integral and obtained the closed-space parabolic energy
  inequality without assuming smoothness of the optimizer.
- Constructed the actual initial-state flow Jacobian on every finite horizon,
  proved its exponential norm bound, fixed-time joint continuity/measurability,
  and genuine Lᵖ propagation bounds.
- Derived the smoothed density time derivative directly from weak evolution,
  including its derivative in the bounded-continuous sup norm.
- Constructed smoothed velocities for arbitrary integrable finite-energy
  fluxes, proved action contraction and convergence of actual test pairings.
- Proved first-order weak continuity uniqueness with actual Euler tests and
  derived the weak equation for the genuine deterministic characteristic law.

The complete 234-module entry point passes independent kernel replay and
standard-axiom closure (2,009 named declarations). Two further audit groups
verify 10 modules / 84 declarations. The sharp marginal hierarchy, switch
source derivative, and rough transport connection are still open; no claim
of complete manuscript certification is made.


## 2026-09-17 — convolved source and genuine smooth transport

- Identified the actual smoothed scalar source as negative flux divergence;
  proved its periodic elliptic optimizer energy is at most the original true
  Euclidean flux energy, with coefficient one and no initial flux smoothness.
- Derived the smoothed-density PDE from the weak equation, keeping its exact
  drift commutator explicit.
- Derived the genuine Wasserstein length/action bound from compact-test weak
  continuity for smooth bounded velocities, through actual flow uniqueness.
- Constructed the flow-Jacobian tangent distribution and proved its actual
  semigroup derivative pairing and exponential energy bound.
- Passed aggregate compilation, independent kernel replay and standard-axiom
  audit for **259 modules / 2,225 named declarations**. The manuscript main
  theorem remains unproved; rough transport and sharp marginal propagation
  are not included as completed results.


## 2026-09-17 — exact marginal energy and retained dissipation

- Proved actual periodic prefix lifting and convolved marginal weighted
  pairing, then optimizer orthogonality and exact Pythagorean energy increment.
- Derived the actual external interaction gradient bound with linear marginal
  dependence and the exact D₁b cancellation; proved its integrated fluctuation
  bound with tunable Hessian absorption.
- Constructed the full weighted weak Hessian and proved lower semicontinuity;
  retained the negative twice-Hessian dissipation in parabolic energy estimates.
- Passed aggregate replay/axiom audit for **268 modules / 2,322 declarations**.
  An additional eight-module / 42-declaration audit proves the actual Brownian
  propagated-source PDE, initial source and carrying-law identity. Full sharp
  hierarchy assembly and the manuscript main theorem remain open.


## 2026-09-17 — actual source evolution and symmetry

- Derived the propagated-source PDE from the actual Brownian primal equation
  and constructed its bounded-continuous time derivative after convolution.
- Derived initial generator-source symmetry and canonical representative
  equivariance; propagated them through the actual particle flow and noise.
- Proved the actual Jacobian variation equation and drift-approximation limit;
  verified moving-point derivative convergence for sine-periodized kernels.
- Proved weighted-action disappearance of the actual operator/flux commutator.
- Passed the external Galerkin bound only after combining its positive Hessian
  contribution with negative dissipation, preserving the inequality direction.
- Passed the aggregate build, independent replay and axiom audit for
  **304 modules / 2,546 declarations**. These are component counts;
  `MainTheorem` is still unproved and the PDF is not formally certified.


## 2026-09-17 — marginal smoothing and source limit connections

- Proved coefficient-one preservation of every actual marginal energy under
  smoothing the full canonical source, with the full/marginal source identity.
- Constructed the fixed periodic potential reconstruction and derived true
  dual-norm source differentiation and zero-mean derivative compatibility.
- Proved actual source external-coordinate averaging with `(N-m)/N`.
- Proved sine-periodized particle Jacobian-source and marginal carrying-law
  convergence, preserving any eventual uniform energy bound.
- Aggregate verification now covers **326 modules / 2,687 declarations**.
  Sharp hierarchy assembly, switch differentiation and rough transport
  remain unfinished; the manuscript main proposition is not yet proved.

## Direct weighted-measure coefficient route (363-module checkpoint)

- Constructed the actual finite weighted gradient map and coercive coefficient
  Gram inverse; proved the exact residual-plus-penalty energy gap.
- Proved exact negative Hessian diffusion dissipation with a correctly signed
  coefficient penalty, valid for singular finite carrying measures.
- Derived actual Brownian Gram/source derivatives and the finite optimized
  energy derivative, including time endpoints.
- Proved uniform C¹ Fourier recovery, true weighted periodic projection, and
  the exact periodic marginal energy increment; distinguished periodic from
  the full Euclidean gradient closure.
- Proved positive-period test scaling with eigenvalue factor 1/P².
- Added Volterra quadratic comparison so no differentiability of limiting
  tangent energy is silently assumed.
- Proved the actual prescribed switch-time derivative, its endpoint integrated
  identity, and its exact reference-minus-particle Jacobian source.
- Aggregate validation: 363 modules and 2,938 named declarations, independent
  kernel replay and standard-axiom audit passed. The manuscript theorem is
  still incomplete; no claim of full formal verification is made.


## Actual source profile and finite generator checkpoint (406 modules)

- Proved the initial sharp energy profile for genuine marginals of one full
  regularized source, preserving the reference-minus-particle sign.
- Identified finite coefficient derivatives with literal generator integrals;
  absorbed drift/Hessian residuals into dissipation and the vanishing energy gap.
- Constructed physical-period tangent projections, exact marginal pairings,
  Fourier recovery, and scaled physical Laplacian eigenvalues.
- Derived actual Brownian marginal source/Gram derivatives with diagonal
  self-interactions and exact external coefficient `(N-m)/N`.
- Constructed jointly measurable spacetime flux from scalar finite-energy
  source actions; no measurable family of pointwise Riesz choices was assumed.
- Aggregate compilation, independent replay, and standard-axiom audit passed
  for 406 modules / 3,205 named declarations. The main theorem remains open.

## Original-kernel sharp propagation (453-module checkpoint)

- Proved actual finite Brownian coefficient inequalities and their Volterra
  limit; no derivative of the limiting tangent energy is assumed.
- Recovered full Euclidean energy from bounds at all physical period multiples
  using explicit smooth periodic approximants and dominated convergence.
- Transferred the sharp all-level profile through genuine sine-periodized
  Brownian flow/Jacobian limits to the original nonperiodic interaction, with
  one unchanged initial current and no particle-number-dependent constant.
- Constructed compact spatial convolution with a positive Gaussian floor,
  smooth bounded velocity, and exact action contraction.
- Aggregate validation: 453 modules / 3,484 named declarations, compilation,
  independent kernel replay, and standard-axiom audit passed. Full manuscript
  status remains incomplete; newer separately audited additions are tracked
  under qa/ and are excluded from this aggregate count.

## Actual switch curve and endpoint preparation (483-module checkpoint)

- Identified the literal marginal switch source and proved its compact-test
  continuity equation, including the cylinder-to-marginal cutoff argument.
- Derived the actual local energy bound from the original initial Wasserstein
  hierarchy and proved independent P₂/Wasserstein continuity of the curve.
- Proved geometric endpoint summation for the zero-time energy singularity;
  the resulting root-cost factor is `T + 3 sqrt(T)`.
- Proved the actual reference endpoint transport and final hierarchy assembly
  conditional on the switch length estimate, preserving the main constants'
  independence from the particle number and the particular kernel.
- Proved spatial regularization endpoint couplings and the true time-convolution
  weak derivative from the integrated compact continuity equation.
- Aggregate validation passed for 483 modules / 3,629 named declarations,
  including independent kernel replay and standard-axiom closure. The rough
  finite-action transport theorem and unconditional main theorem remain open.

## Completion of the original main target (2026-09-17)

- Proved the actual common-label mean-square switch realization using the
  same initial configuration and two Brownian paths at every switch time.
- Constructed and removed all rough continuity-equation regularizations,
  deriving the genuine coefficient-one finite-action bound from the actual
  source objective. No optimal-coupling selection or smooth-law premise is
  assumed in the resulting rough theorem.
- Added `main_theorem : MainTheorem`, discharging the last premise of the
  unchanged original propagation target.
- Aligned the manuscript's six auxiliary lemmas and Gaussian sharpness proof
  with their actual Lean statements; recorded the narrower used entropy and
  common-label transport scopes, same-field Fourier/Volterra route, and
  `T+3sqrt(T)` endpoint factor.
- Added exact-original-type verification to the full audit with
  `python3 scripts/audit.py --require-main`. Final aggregate evidence is
  `qa/verification.json`; earlier incomplete checkpoints remain historical.

Final verification passed: 512 modules / 3,776 named declarations; exact
original target type, unchanged target source, independent kernel replay and
standard-only axiom closure. No project source is excluded from the full audit.
