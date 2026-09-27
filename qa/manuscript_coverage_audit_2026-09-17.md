# Manuscript-to-Lean coverage audit, 2026-09-17

Final read-only review after mathematical alignment. This supersedes the earlier pre-alignment version of this audit. No manuscript or frozen Lean source was edited by this review.

## Reviewed snapshot

- Manuscript: `rethlas/manuscripts/sharp_wasserstein_bounded_kernel_open/sharp_wasserstein_propagation.tex`.
- SHA-256: `b9b05c4498b9e4d70c7366e2f9b6d3188adf56b45ad3dbf45581438376314330`.
- 981 lines; 59 unique labels; no duplicate labels or undefined references.
- 12 cited bibliography entries; no undefined citations or unused entries. Bibliographic metadata and external source verification belong to the separate reference audit; this check verifies internal citation consistency.
- Checked at `2026-09-18T02:00:59.436655+00:00`.

## Main theorem status

`SharpWasserstein.main_theorem : SharpWasserstein.MainTheorem` is now present in `Main.lean`. It applies the original reduction to the proved `RoughEulerianTransport.uniform_finite_action_transport`; no rough transport, hierarchy, density regularity, entropy, or independence premise remains in the theorem.

The target preserves arbitrary correlated initial laws, finite second moments, all positive marginal levels, self-interaction, unnormalized Euclidean sum-of-squares cost, and constants chosen before the kernel, particle number and initial laws. The rough theorem has passed scoped compilation, independent kernel replay and standard-axiom verification in `qa/rough_finite_action/verification.json`. The root agent reports that the main declaration has passed compilation and exact-type/standard-axiom checking; the final aggregate replay is managed separately. This textual coverage audit does not substitute for that aggregate certificate.

## Theorem and remark correspondence

| Manuscript item | Actual formalized content |
| --- | --- |
| Main theorem and scope remark | `Main.lean`, `MainTheorem` in `Dynamics.lean`, and `MainFiniteActionReduction.lean`: finite-horizon all-level propagation for supplied weak evolutions and the original initial hierarchy. |
| Gaussian optimality remark | `GaussianCovariance.lean`, `RankOneTransport.lean`, `GaussianHeatWeak.lean`: genuine common-noise Gaussian laws, exchangeability, all marginals, exact rank-one transport by an explicit upper coupling and a lower bound for every coupling, actual zero-kernel weak evolution, initial constant 1/4, and positive matching fixed-time lower constant. |
| Weighted H⁻¹ lemma | `WeightedTangent.lean` and `WeightedTangentLimit.lean`: actual compact smooth gradients in weighted L², unique Riesz field, minimal energy, and variational lower semicontinuity. `RoughFiniteAction.lean` supplies the common-label uniform-action transport statement through one space-time Riesz field, actual compression/smoothing, smooth-flow transport and explicit endpoint couplings. |
| Entropy-cost lemma | `BrownianEntropy.flow_entropy_le_wassersteinSq`: actual finite Gaussian bridge densities, chain rule, endpoint data processing, Brownian Euler convergence, KL lower semicontinuity and the exact bridge coefficient. |
| Entropy increment lemma | `exchangeable_marginal_entropy_second_difference` and the subsequent increment bounds: disintegration, finite marginal KL, conditional KL superadditivity and exchangeability. |
| Source lemma | `RegularizedBrownianSourceData/Bound/Switch.lean`: actual generator-difference current, conditional Pinsker, internal bounded-sum estimate, self-term, equivariance, exact marginal source, and the singular source profile derived from initial W₂ bounds. |
| Tangent propagation lemma | `BrownianEnergyPeriodization.prefixEnergy_quadratic_bound` and `projectedSource_quadratic_bound`: genuine finite Fourier Gram/source differentiation, exact finite energy gap, marginal Pythagoras, Hessian cancellation, all-level finite differential bound, scalar L¹ recovery and Volterra comparison, all-period exhaustion, and original-kernel flow/Jacobian limits with the same initial field. |
| Interpolation lemma and final endpoint argument | `PrescribedSwitchMarginalSourceContinuity.lean`, `RegularizedBrownianSourceSwitch.lean`, `PrescribedSwitchCommonLabel.lean`, `GeometricEndpointLength.lean` and the main reduction: exact marginal switch equation and source, actual common-label mean-square continuity, finite-action bound on positive-time intervals, quarter-geometric summation, and decoupled endpoint transport through arbitrary couplings. |

## Resolved alignment findings

1. **Entropy direction and assumptions.** The drift is now jointly continuous, globally bounded and uniformly Euclidean-Lipschitz, exactly the proved scope. The first entropy measure is explicitly the controlled finite Gaussian history and the cost is expected under that measure. No unproved continuous-time Girsanov or Novikov argument remains.

2. **Exact entropy coefficient and norms.** The factor `(1+L s+L²s²/3)/(4s)` uses the genuine Euclidean Lipschitz constant L. The coordinatewise tensor drift has the same L, independently of marginal level. Lean's `KernelBounds` uses finite Pi sup norms, so the prescribed-drift specialization takes L=√d L₁. Conversion from the manuscript's physical Euclidean kernel norms changes only dimension-dependent constants; the stated main constant allows precisely that dependence. No hidden N-dependent norm conversion enters the sharp rate.

3. **Rough transport scope.** The manuscript now states the actually used uniform energy estimate with common labels. It constructs one jointly measurable space-time flux, rather than assuming a measurable choice of pointwise optimizers. Sine compression, compact smoothing, the floor with 0<δ<1 and the explicit endpoint couplings match the proof. Translation of an interval and constant clamping of its common labels express the finite-interval statement in the all-real curve convention used in Lean; the actual switch curve is already globally clamped. No general metric-speed theorem is claimed.

4. **Finite Fourier hierarchy.** The revised proof uses nested finite subsets of one real Fourier eigenfunction family, with nonnegative Laplacian eigenvalues and time-independent positive coefficient penalty. These are the conditions needed for the exact negative penalty term. The genuine approximation gap, fixed-horizon bound on its coefficient, continuous finite energies, measurable limiting energies and dominated time L¹ passage are stated. Infinite-dimensional optimizer smoothness and pointwise differentiability are no longer asserted.

5. **Marginals, constants and endpoints.** The periodic minimal fields are used inside the finite calculation; initial periodic energy is bounded by full energy. The coefficient (N−m)/N and terminal level are retained. The actual proved external coefficient is bounded by C_b m; the unused stronger squared-factor claim has been removed. All-period recovery precedes the sine-kernel limit at fixed N, leaving only the permitted dimension/kernel dependence. The terminal summation is the proved t+3√t estimate.

6. **Initial tangent and weak-law conventions.** Propagation is defined from the same fixed a.e. equivariant L² field throughout, with the actual generator current supplying it in the application. No unrestricted independence-of-representation assertion on arbitrary bounded C¹ tests remains. The setting now specifies a narrowly continuous weak solution with locally bounded second moments. The final decoupled argument uses arbitrary couplings and an infimum, matching the actual transport proof.

## Explicit scope boundaries

Nonlinear McKean–Vlasov fixed-point existence and uniqueness are cited background, not an additional conclusion of `MainTheorem`; the actual prescribed weak-law identification needed for the rate is proved. General AGS metric-speed results, continuous-time Girsanov, and C∞ spatial regularity of the infinite-dimensional weighted elliptic optimizer are neither needed nor claimed by the revised proof. Introductory literature comparisons are supported by the separate reference audit, not by Lean.

No remaining substantive mathematical coverage gap was found in the revised theorem, its six auxiliary lemmas, or its Gaussian sharpness remark. No new Gaussian algebra, law, moment or coupling module was required.
