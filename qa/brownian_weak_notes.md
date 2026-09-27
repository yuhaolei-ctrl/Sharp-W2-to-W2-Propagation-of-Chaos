# Brownian weak-evolution bridge

The component proof is complete; the manuscript's `MainTheorem` remains an open target.

- `EulerWeakLimit.brownian_trajectory_weak_equation` derives the actual compact-test generator equation from Gaussian Euler history laws, uniform one-step errors, endpoint convergence, and expected Riemann-sum convergence. No stochastic generator identity is assumed.
- `BrownianParticle.globalLaw_weakEvolution` and `globalLaw_isParticleEvolution` supply every field of the manuscript predicates for the constructed self-inclusive particle dynamics. The diffusion term is exactly the coordinate Laplacian, from the actual independent sqrt-two Brownian law. The initial law must be a probability with a second moment; the particle predicate also requires its exchangeability.
- `EulerTimeWeak.brownian_trajectory_weak_equation` extends the argument to jointly continuous, uniformly bounded, uniformly spatially Lipschitz time-dependent drifts. No drift time derivative or spatial smoothness is assumed. `TimeGenerator` derives the uniform test-generator bounds used in the limit.
- `BrownianFlow.globalLaw_weakEvolution` assembles the genuine global evolution for that general time-dependent drift, including horizon independence, compact-time moment bounds and time integrability.
- `PrescribedReference.law_weakEvolution` obtains a prescribed mean-field drift directly from any supplied `IsLimitEvolution`. Its regularity follows from proved narrow continuity, and the original drift is used at every nonnegative time. `law_eq_decoupled` identifies this construction with the existing independent-coordinate flow; `law_tensor` proves its actual tensor factorization. Identifying the constructed one-particle reference with the supplied limit curve still requires weak-solution uniqueness.

Independent replay and declaration-axiom checks are reproducible with `qa/audit_brownian_weak.py`, `qa/audit_brownian_time_weak.py`, and `qa/audit_prescribed_reference.py`. Their JSON reports contain exact source/object hashes, scan scopes, and declaration closures. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
