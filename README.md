# Sharp Wasserstein propagation of chaos from correlated initial data

[![CI](https://github.com/yuhaolei-ctrl/Sharp-W2-to-W2-Propagation-of-Chaos/actions/workflows/ci.yml/badge.svg)](https://github.com/yuhaolei-ctrl/Sharp-W2-to-W2-Propagation-of-Chaos/actions/workflows/ci.yml)

A complete Lean 4 proof, checked against Mathlib, of Theorem 2.1 of

> Yuhao Lei, *Sharp Wasserstein propagation of chaos from correlated initial data*.

The manuscript is in [`paper/`](paper/) ([PDF](paper/sharp_wasserstein_chaos.pdf), [LaTeX](paper/sharp_wasserstein_chaos.tex)); equation and lemma numbers below refer to it.

Consider `N` particles in `ℝᵈ`,

```
dXᵢ = (a(Xᵢ) + N⁻¹ ∑ⱼ K(Xᵢ, Xⱼ)) dt + √2 dWᵢ,      1 ≤ i ≤ N,
```

with independent Brownian motions and an exchangeable initial law `P_{N,0}`, and the
McKean–Vlasov equation `dX = (a(X) + ∫ K(X, y) μ_t(dy)) dt + √2 dW`, `μ_t = Law(X_t)`.
Assume that `a` is `L_a`-Lipschitz and that `K` is bounded by `M` and satisfies
`|K(x,y) − K(x',y')| ≤ L₁|x − x'| + L₂|y − y'|` (Euclidean norms). If

```
W₂²(P^{(k)}_{N,0}, μ₀^{⊗k}) ≤ C₀ k²/N²        for 1 ≤ k ≤ N,
```

then for every `T > 0`

```
W₂²(P^{(k)}_{N,t}, μ_t^{⊗k}) ≤ C_T k²/N²       for 0 ≤ t ≤ T, 1 ≤ k ≤ N,
```

with the explicit constant `C_T = (e^{LT}√C₀ + e^{ωT/2}(A₀T + 2A₁√T))²` of the paper, where
`L = L_a + L₁`, `Λ = L_a + L₁ + L₂`, `L_c = 2L₁ + L₂`, `G = 2L₁² + L₂² + 2M²`, `λ = 2G`,
`D = 2Λ + 2L₁ + 1`, `ω = D + 3λ`, `D_T = (1 + LT + L²T²/3)/4`, `A₀ = 2M + L_c e^{LT}√C₀`,
`A₁ = √8 M √(C₀ D_T)`. The constant depends neither on `N` nor on the dimension `d`. The initial
law may be correlated and singular; no entropy bound, transport inequality or independence of the
initial particles is assumed.

## The statement

[`Challenge.lean`](Challenge.lean) imports only Mathlib. It defines Assumption A, the squared
quadratic Wasserstein distance (infimum of `∑ᵢ ‖xᵢ − yᵢ‖²` over couplings), marginals,
exchangeability, standard Brownian motions in `ℝᵈ` (coordinates are independent Mathlib
`ProbabilityTheory.IsBrownianReal` processes), strong solutions of the particle system and of the
McKean–Vlasov equation (integral form, almost surely continuous paths, noise independent of the
initial value), and the constant `SharpChaos.sharpConstant` (formulas (2.6)–(2.9) of the paper).
It then states

```lean
theorem SharpChaos.sharp_propagation_of_chaos … :
    ∀ t ∈ Icc 0 T, ∀ k (hk : k ≤ N), 1 ≤ k →
      wassersteinSq (marginal hk (P.map (X t))) (Measure.pi fun _ : Fin k => P'.map (Y t)) ≤
        ENNReal.ofReal (sharpConstant C₀ T La L₁ L₂ M * k ^ 2 / N ^ 2)
```

for all `d`, all `N ≥ 1`, all `a`, `K` satisfying Assumption A, all exchangeable initial laws
with finite second moments satisfying the initial hierarchy, and all strong solutions on arbitrary
probability spaces (the particle system and the McKean–Vlasov process may live on different
spaces). [`Solution.lean`](Solution.lean) proves the same statement; the definitions it uses are
those of [`SharpWasserstein/Statement.lean`](SharpWasserstein/Statement.lean), generated verbatim
from `Challenge.lean` by [`scripts/sync-statement.py`](scripts/sync-statement.py).
[`comparator.json`](comparator.json) lists the compared theorem and the permitted axioms
`propext`, `Quot.sound` and `Classical.choice`.

## Build and verify

```sh
lake exe cache get
lake build                       # the development, Challenge and Solution
python3 scripts/check-lean-sources.py
python3 scripts/sync-statement.py --check
./scripts/verify-comparator.sh   # Linux with bubblewrap: the toolchain's `lake comparator`
```

The toolchain is `leanprover/lean4:v4.35.0-rc3` with Mathlib `v4.35.0-rc3`. `verify-comparator.sh`
runs the `lake comparator` that ships with the toolchain, replaying the proof in Lean's kernel and
in the bundled independent kernels (NanoDa and con-ron), as the Palomar registry does. CI runs all
of these checks on every push.

## How the proof is organised

The proof follows the paper. Paths are relative to `SharpWasserstein/`.

| Paper | Lean |
| --- | --- |
| Theorem 2.1 | `Solution.lean`; reduction to smooth coefficients in `Sharp/Final/Reduction.lean`, smooth case `Sharp.smoothSharpCase` in `Sharp/SmoothSharpCaseProof.lean` |
| Constants (2.6)–(2.9) | `Sharp/Constants.lean` |
| Lemma 3.1 (dynamics, Jacobian bound) | `BoundedFlow`, `BrownianFlow*`, `BrownianParticle*`, `FlowInitialDerivative*`; existence for bounded coefficients by Picard iteration in `Sharp/McKeanVlasovPicard.lean`; pathwise estimates in `Sharp/PathwiseEstimates.lean` |
| Lemmas 3.2–3.3 (tangent energies) | `WeightedTangent`, `WeightedMarginal` |
| Lemma 3.4 (transport length) | `Rough*` (continuity equation with finite action), `Sharp/EndpointLength.lean`, `Sharp/Endpoint/SwitchLength.lean` |
| Lemma 3.5 (reference law) | `Sharp/Source/ReferenceTransport.lean`, `Sharp/Source/ReferenceBound.lean` |
| Proposition 3.6 (source) | `Sharp/Source/Proposition.lean` |
| Proposition 3.7 (profile) | `Sharp/Hierarchy/Main.lean` |
| Lemma 3.8, Section 6 (interpolating curve) | `SwitchCurve*`, `SwitchSourceDerivative*`, `PrescribedSwitch*` |
| Lemma 4.1 (entropy–cost) | `BrownianEntropyTransport` and its import closure |
| Lemma 4.2 (increments) | `ExchangeableEntropy` |
| Lemma 4.3 | `Sharp/Source/EntropyProfile.lean` |
| Lemma 4.4 (representation) | `MarginalParticleCurrent`, `InitialSourceMarginalCurrent` |
| Lemma 4.5 (internal source) | `Sharp/InternalMoment.lean`, `Sharp/Source/Internal.lean` |
| Lemma 4.6 (external source) | `ExchangeableConditionalSource`, `Sharp/Source/External.lean` |
| Lemmas 5.1–5.3, Proposition 5.4, Section 5.4 | `Sharp/Hierarchy/*` with the Galerkin machinery (`RegularizedTrial*`, `FiniteGradientTrial*`, `PeriodicMarginalCoefficientEvolution*`, `Volterra*`) |
| Appendix A (Galerkin approximation) | `RegularizedTrial*`, `PeriodicEnergyExhaustion` |
| Section 3.4, smooth case | `Sharp/Endpoint/SmoothCase.lean` |
| Lemma 7.1 (mollification) | `Sharp/Mollify.lean`, `Sharp/ConvolutionDerivBounds.lean` |
| Lemma 7.2 (stability) | `Sharp/ApproxParticle.lean`, `Sharp/ApproxMcKeanVlasov.lean` |

Two bridges connect the public statement with the development, whose positions are coordinate
vectors `Fin d → ℝ` and whose laws are constructed on a canonical Brownian space:
`Sharp/EuclideanBridge.lean` identifies the two Wasserstein distances, marginals and tensor
powers, and `Sharp/Transfer/*` shows that the laws of strong solutions on an arbitrary probability
space coincide with the constructed laws (hence satisfy the weak Fokker–Planck equations used by
the proof).

Some lemmas are proved by a different route than in the paper; the statement is unaffected:

* the entropy–cost inequality (Lemma 4.1) is proved with Euler schemes, an explicit Gaussian
  bridge and lower semicontinuity of relative entropy, instead of Girsanov's theorem;
* the tangent hierarchy is first proved for sine-periodized interactions with periodic Galerkin
  energies and then transferred to the original interaction and the full energy; all constants
  are those of the paper (`D`, `λ`, `ω`), and the periodization never enters them;
* the continuity-equation characterization behind Lemma 3.4 is proved for the curves needed here
  (with a common-label realization), not in the generality of Ambrosio–Gigli–Savaré;
* well-posedness is proved only where the proof uses it: existence by Picard iteration for the
  bounded smooth approximations, and pathwise uniqueness for Lipschitz drifts.

## Dependencies

The proof uses Mathlib and vendored copies of two Apache-2.0 formalizations, adapted to the pinned
Mathlib (only their import closure is kept; modified files say so in their headers):

* [`BrownianMotion/`](BrownianMotion/UPSTREAM.md): the construction of Brownian motion from
  [RemyDegenne/brownian-motion](https://github.com/RemyDegenne/brownian-motion);
* [`KolmogorovExtension4/`](KolmogorovExtension4/UPSTREAM.md): the Kolmogorov extension theorem
  from [RemyDegenne/kolmogorov_extension4](https://github.com/RemyDegenne/kolmogorov_extension4).

`Challenge.lean` depends on Mathlib only.

## Authorship and AI use

The mathematics is Yuhao Lei's. The Lean formalization was produced with AI agents under the
author's direction; [`formalization.yaml`](formalization.yaml) records the details. No AI system is
listed as an author.

## Licence

Apache 2.0, see [`LICENSE`](LICENSE). The vendored libraries retain their own Apache 2.0 licences.
