# Gaussian sharpness verification

The Gaussian example is proved through the project's actual weak-PDE evolution
predicates. The eight modules `RankOneTransport`, `GaussianSharpness`,
`GaussianCovariance`, `GaussianHeat`, `GaussianMoments`, `GaussianStein`,
`GaussianHeatCalculus`, and `GaussianHeatWeak` compile without warnings and pass
independent kernel replay. All 135 definitions/theorems audited in
`GaussianAxioms.lean` use only `propext`, `Classical.choice`, and `Quot.sound`;
see `gaussian_axioms.log` and `gaussian_verification.json`.

The transport definition is the project's actual ENNReal infimum over probability
couplings with the unnormalized sum of squared coordinate displacements. The
proof constructs a common-label coupling and proves its optimality by projecting
**every** admissible coupling onto the normalized all-ones direction and applying
the L² triangle inequality. No Gaussian transport formula or optimality statement
is assumed.

The explicit law `particleGaussianLaw N a` is the law of
`Xi = sqrt(a) Zi + sqrt(1/N) Z0` under a finite product of standard scalar Gaussian
probability measures. Its Gaussian classification is proved through characteristic
functionals. The means are zero; covariance is `a I + (1/N) 11ᵀ` for `a ≥ 0`.
The laws are exchangeable and their first k coordinates have the corresponding
k-dimensional common-noise law.

Key exported statements (namespace `SharpWasserstein.GaussianSharpness`):

- `particleGaussianLaw_transport_exact`: for `0 < k ≤ N` and `a > 0`, the actual
  k-marginal squared transport cost is `(k/N)² / (sqrt(a+k/N)+sqrt(a))²`.
- `particleGaussianLaw_initial_allLevels` and `gaussian_initialHierarchy`: one
  family of exchangeable N-particle initial laws satisfies the exact main
  target's all-level initial condition with `C₀ = 1/4`.
- `gaussian_sharpness_fixed_time`: for every `t ≥ 0`, a strictly positive
  constant independent of k and N gives the matching `(k/N)²` lower rate.
- `particleGaussianLaw_marginal_covariance`: exact coordinate covariance integral
  of each actual marginal.
- `particleGaussianLaw_probability`, `particleGaussianLaw_secondMoment`, and
  `particleGaussianLaw_uniform_momentBound`: probability and genuine Euclidean
  second moments, including uniform boundedness on compact time intervals.
- `particleGaussianLaw_heat_convolution`: variance `1+2t` is the convolution of
  the initial law with the independent Gaussian product of variance `2t`.
- `commonNoiseLaw_expectation_hasDerivAt`: for every actual compact smooth test,
  its expected time derivative is the expected genuine Laplacian.
- `commonNoiseLaw_weakEvolution`: every field of `Dynamics.WeakEvolution` is
  proved, including test continuity, generator and time integrability, moment
  bounds, and the integrated weak PDE with diffusion coefficient one.
- `particleGaussianLaw_isParticleEvolution` and
  `oneParticleGaussian_isLimitEvolution`: actual zero-interaction particle and
  limit evolutions, with the one-particle law identified exactly.
- `gaussian_sharpness_hypotheses`: assembles kernel smoothness and uniform bounds,
  both evolution predicates, exchangeability, and the initial hierarchy.

The weak heat equation follows from integration by parts against the explicit
scalar Gaussian density, finite-product Fubini, explicit label derivatives,
dominated differentiation under the integral, and the fundamental theorem of
calculus. No assumed weak equation, Stein identity, or transport speed is used.

The Gaussian sharpness example is complete relative to the project's exact
weak-PDE target. The main interacting propagation theorem remains unproved by
these modules; `MainTheorem` is still an open definition elsewhere in the project.
