# Actual Brownian semigroup and generator bridges

These modules establish component theorems; they do not constitute a complete proof of the manuscript or of `MainTheorem`.

- `ContinuousPathLaw`: the continuous-path Borel sigma-algebra is the evaluation sigma-algebra. Equality and independence of actual function-process laws therefore transfer to the concrete continuous-path spaces.
- `BrownianSplit`: the pinned Brownian constructor's proved shift law and independent past/future processes imply `BrownianNoise.configurationLaw_split`. The complete particle path, split at time S into its past and restarted future, has exactly the product of the configuration Brownian laws over S and T. Spatial and particle independence are transported through finite product measures. The scalar Brownian scale remains sqrt(2).
- `FlowSemigroup`: `FiniteAdditiveTrajectory.shift_autonomous` follows by splitting and translating the Bochner integral. Pathwise uniqueness gives `BoundedFlow.flow_add` for the constructed flow, without a stochastic or PDE uniqueness assumption.
- `BrownianSemigroup`: `BrownianFlow.globalLaw_add` and `BrownianParticle.globalLaw_add` combine the actual product path law and deterministic composition. They apply to any probability initial law and S,T >= 0, including zero; neither moments nor exchangeability are needed. `globalLaw_add_integral` gives the bounded continuous test version.
- `BrownianForwardDerivative`: genuine compact-test generator expectations are continuous and have their actual time derivative, including the initial right derivative. It also refines `WeakEvolutionTimeTests` to the boundary for bounded smooth Euclidean tests. `transition_iterated_hasDerivWithinAt_zero` derives the right derivative of P_s(P_T phi) as P_T(L phi) from the actual semigroup. This alone does not prove spatial regularity of P_T phi or the backward PDE.
- `ConstantDriftLaw`: `BrownianFlow.globalLaw_constant_dirac` identifies the actual point-started constant-drift flow with `FrozenGaussian.transitionLaw`, with mean x+tu and covariance 2t I, including t=0. The genuine bounded-smooth weak identity yields `FrozenGaussian.timeExpectation_sub_eq_integral_bounded_smooth`.
- `BoundedConfigurationTests`: actual bounded iterated Fréchet derivatives survive the configuration/Euclidean linear equivalence. Bounds on derivatives of orders zero, one and two give global value, gradient and Laplacian bounds. `WeakEvolution.equation_bounded_configuration` and `FrozenGaussian.timeExpectation_sub_eq_integral_bounded_configuration` apply the established identities directly to these configuration-space tests, without compact support.

Each chain has a localized audit script and a JSON verification report:

- `audit_brownian_semigroup.py` / `brownian_semigroup_verification.json`
- `audit_brownian_forward_derivative.py` / `brownian_forward_derivative_verification.json`
- `audit_constant_drift_law.py` / `constant_drift_law_verification.json`
- `audit_bounded_configuration_tests.py` / `bounded_configuration_tests_verification.json`

The scripts scan listed project modules for forbidden tokens after removing nested comments and strings, independently replay their compiled modules through the Lean kernel, and check every extracted declaration's axiom closure against `propext`, `Classical.choice`, and `Quot.sound`. Source and compiled-object hashes are recorded. They do not replace the project's final complete dependency-closure audit.
