# Sharp Wasserstein propagation: partial Lean formalization

**The complete manuscript proof is not yet formalized.** This project contains
kernel-checkable component proofs and a concrete statement of the intended
measure-theoretic theorem. `SharpWasserstein.MainTheorem` is a definition of a
proposition, **not a theorem**, and no axiom is used to assert it. The remaining rough continuity-equation transport and final assembly are
not yet proved. Sharp tangent-energy propagation for the original kernel is
now proved from the actual initial source profile.

The source manuscript is
[`sharp_wasserstein_propagation.tex`](../../rethlas/manuscripts/sharp_wasserstein_bounded_kernel_open/sharp_wasserstein_propagation.tex).
The latest aggregate checkpoint verifies 483 source files / 3,629 named
declarations, including definitions, by compilation, independent kernel replay,
and axiom inspection. Further work in progress is excluded from this count.
See [THEOREM_STATUS.md](THEOREM_STATUS.md) for the correspondence between every
manuscript step, exact Lean declarations, and open proof obligations.

## What is proved

- The actual quadratic transport infimum: probability couplings, moments,
  marginal contraction, gluing, square-root triangle inequality, and P₂
  pseudometric; endpoint assembly uses this actual cost.
- The corrected exponential-density KL identity, arbitrary measurable-map
  data processing, entropy variational estimates, scalar and Hilbert-valued
  Pinsker inequalities, and the integrated conditional-KL chain rule.
- Actual compact-test weighted L² tangent representatives, divergence
  pairings, exact/minimal energy, explicit configuration coordinate change,
  weak-law lower semicontinuity, and cutoff-based marginal projection.
- Genuine Lagrangian transport length from pointwise integral/differential
  trajectories, including the mixed time-L¹/label-L² Fubini bridge.
- Finite-horizon continuous-forcing solutions for bounded Lipschitz drifts,
  uniqueness, dependence on initial data and noise, measurable particle
  solution maps, second-moment propagation, and actual Wasserstein stability
  with constants independent of particle number.
- Actual internal and conditional external source estimates, including the
  diagonal self-term, from product concentration and genuine marginal entropy.
- Lax–Milgram construction of varying-density optimizers and the exact
  derivative of the actual weighted tangent energy.
- Consistent exchangeable Gaussian laws with exact optimal transport cost,
  the all-level initial bound, sharp lower rate, covariance and heat convolution.
- Pinned Brownian/Wiener construction and actual independent sqrt(2) path
  inputs for constructed particle laws, with zero initial noise, moments and
  permutation invariance.
- Actual weak-particle uniqueness and identification with the Brownian law;
  time-dependent weak-reference uniqueness, exact identification of the supplied
  reference tensor laws, and their full weak Fokker–Planck equations.
- Entropy–cost regularization of actual bounded Lipschitz Brownian flows, with
  the corrected KL direction and explicit bridge coefficient.
- Symmetric-Hessian cancellations, cooperative hierarchy comparison and
  exact bridge/speed integrals.

The transport cost is `∑ i, ∑ a, (x i a - y i a)^2`, with no normalization by
particle number. The target uses genuine probability measures, finite moments,
product laws, marginals, Fréchet derivatives, and the integrated weak
Fokker–Planck equation with Laplacian coefficient one. The conclusion constant
is independent of particle number and initial laws. These definitions avoid
replacing the analytic objects by uninterpreted symbols.

## Reproduce the checks in this workspace

The checked toolchain is Lean **4.32.0** and the corresponding local Mathlib
source/cache. No network access or global Lean installation is required:

```sh
cd /Users/tudou/Desktop/research/lean/sharp_wasserstein
python3 build.py --fresh --replay --jobs 2
python3 scripts/audit.py
```

`lean_local.py` locates the existing runtime and dependencies under
`rethlas/agents/generation/`. `scripts/bootstrap_mathlib.py` compiles additional
Mathlib sources into a local copy-on-write cache overlay; it does not modify
the shared cache. `scripts/bootstrap_brownian.py` builds and replays the pinned external Brownian
and Kolmogorov source closure when needed; its source provenance and license
files are retained under `external_sources/`. `lakefile.toml` records the local
Mathlib path dependency; use the workspace build script for this combined
development. This is a
workspace-local build configuration, not a self-contained distribution of
Lean and Mathlib.

The build recompiles each project module and `--replay` invokes the unchanged
`LeanChecker.replayFromImports` function sequentially, including private module
parts. This avoids the stock CLI's concurrent prefix expansion. The generated
wrapper is `qa/KernelReplay.lean`. The audit checks source tokens, prints
the axioms used by project declarations, and records source hashes. Only the
standard foundational axioms `propext`, `Classical.choice`, and `Quot.sound`
are allowed. Successful checking establishes the written statements under
their stated hypotheses; it does not discharge the missing analytic bridges.

During parallel development, `python3 scripts/audit.py --checked-closure`
audits only the source-hash-matched last checked umbrella closure and explicitly
lists excluded in-progress files in `qa/verification_checkpoint.json`. The
default full audit still requires every project module.

Reports and logs are under [`qa/`](qa/), including the independent
[semantic audit](qa/semantic_audit.md). The reports explicitly retain
`complete_manuscript_proof: false`.

The exact checked module closure and source hashes are recorded in
[`qa/build_SharpWasserstein.json`](qa/build_SharpWasserstein.json). Individual
new component audits are also retained under `qa/`. Work-in-progress files
outside a checked closure are not certified by that report.

## Remaining work

The actual continuous Brownian entropy-cost inequality and the identification
of source bounds with disintegrated diffusion currents are now proved. The
Gaussian sharpness example satisfies every weak-evolution hypothesis.
The actual Brownian particle law now satisfies the full weak generator equation.
Arbitrary weak solutions have proved narrow continuity and a bounded smooth test
extension. The main missing developments are identification with all weak
Fokker–Planck solutions, tangent-energy evolution,
the general Eulerian continuity-equation representation, the switch-time
construction, and the torus/smoothing argument for singular initial laws. The exact evolving
list is in `THEOREM_STATUS.md`. No gap is supplied by `sorry`, a new axiom,
or an assumed copy of the main theorem.
