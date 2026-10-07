# Sharp Wasserstein propagation of chaos from correlated initial data

[![CI](https://github.com/yuhaolei-ctrl/Sharp-W2-to-W2-Propagation-of-Chaos/actions/workflows/ci.yml/badge.svg)](https://github.com/yuhaolei-ctrl/Sharp-W2-to-W2-Propagation-of-Chaos/actions/workflows/ci.yml)

A Lean 4 formalization, checked against Mathlib, of the main theorem of

> Yuhao Lei, *Sharp Wasserstein propagation of chaos from correlated initial data*
> ([PDF](paper/sharp_wasserstein_chaos.pdf), [LaTeX](paper/sharp_wasserstein_chaos.tex)).

## The theorem

Consider $N$ particles in $\mathbb R^d$ and the McKean–Vlasov equation

$$
dX_i = \Big(a(X_i) + \frac1N\sum_{j=1}^N K(X_i,X_j)\Big)\,dt + \sqrt2\,dW_i,
\qquad
dX = \Big(a(X) + \int K(X,y)\,\mu_t(dy)\Big)\,dt + \sqrt2\,dW,\quad \mu_t = \mathrm{Law}(X_t),
$$

where $a$ is $L_a$-Lipschitz, $|K|\le M$ and
$|K(x,y)-K(x',y')|\le L_1|x-x'|+L_2|y-y'|$. Let $P_{N,t}$ be the law of the particle system,
started from an exchangeable law $P_{N,0}$ with finite second moment, and $P^{(k)}_{N,t}$ the law of
its first $k$ particles.

**Theorem 2.1.** If
$W_2^2\big(P^{(k)}_{N,0},\mu_0^{\otimes k}\big)\le C_0\,k^2/N^2$ for $1\le k\le N$, then for every
$T>0$

$$
W_2^2\big(P^{(k)}_{N,t},\mu_t^{\otimes k}\big)\le C_T\,\frac{k^2}{N^2},
\qquad 0\le t\le T,\ 1\le k\le N,
$$

with

$$
C_T=\Big(e^{LT}\sqrt{C_0}+e^{\omega T/2}\big(A_0T+2A_1\sqrt T\big)\Big)^2,
$$

where $L=L_a+L_1$, $\Lambda=L_a+L_1+L_2$, $G=2L_1^2+L_2^2+2M^2$, $\omega=2\Lambda+2L_1+1+6G$,
$D_T=(1+LT+L^2T^2/3)/4$, $A_0=2M+(2L_1+L_2)e^{LT}\sqrt{C_0}$ and $A_1=\sqrt8\,M\sqrt{C_0D_T}$.
The constant depends neither on $N$ nor on $d$, and the initial law may be correlated and singular.

## Lean statement

[`Challenge.lean`](Challenge.lean) uses only Mathlib. Positions lie in
`EuclideanSpace ℝ (Fin d)`, $W_2^2$ is the infimum of $\sum_i \lVert x_i-y_i\rVert^2$ over couplings,
the noise consists of independent Mathlib Brownian motions (`ProbabilityTheory.IsBrownianReal`)
independent of the initial value, and solutions are strong solutions in integral form. The theorem
is `SharpChaos.sharp_propagation_of_chaos`, with the constant `SharpChaos.sharpConstant`.
[`Solution.lean`](Solution.lean) proves it, using only the axioms `propext`, `Quot.sound` and
`Classical.choice`.

## Building and checking

The project uses `leanprover/lean4:v4.35.0-rc3` and Mathlib `v4.35.0-rc3`.

```sh
lake exe cache get
lake build
./scripts/verify-comparator.sh   # Linux with bubblewrap
```

The last command runs the toolchain's `lake comparator`, which checks that `Solution.lean` proves
the statement of `Challenge.lean` and replays the proof in Lean's kernel and in the NanoDa and
con-ron kernels. CI runs it on every push.

## Structure of the proof

The proof follows the paper. Its main parts, under `SharpWasserstein/`:

| Paper | Lean |
| --- | --- |
| Theorem 2.1, reduction to smooth coefficients (§3.4, §7) | `Sharp/Final/`, `Sharp/Mollify.lean`, `Sharp/ApproxParticle.lean`, `Sharp/ApproxMcKeanVlasov.lean` |
| Smooth case (§3.4) | `Sharp/SmoothSharpCaseProof.lean`, `Sharp/Endpoint/` |
| Source estimate (Prop. 3.6, §4) | `Sharp/Source/`, `BrownianEntropy*`, `ExchangeableEntropy*` |
| Tangent hierarchy (Prop. 3.7, §5, App. A) | `Sharp/Hierarchy/` and the Galerkin files |
| Transport length (Lemma 3.4) | `Rough*`, `Sharp/EndpointLength.lean` |
| Interpolating curve (Lemma 3.8, §6) | `SwitchCurve*`, `PrescribedSwitch*` |
| Strong solutions and their laws | `Sharp/McKeanVlasovPicard.lean`, `Sharp/Transfer/` |

A few lemmas are proved differently from the paper: the entropy–cost inequality uses Euler
schemes and Gaussian bridges instead of Girsanov's theorem, and the tangent hierarchy is first
proved for periodized interactions and then passed to the limit. The constants are those of the
paper.

The construction of Brownian motion and the Kolmogorov extension theorem are vendored from
[RemyDegenne/brownian-motion](https://github.com/RemyDegenne/brownian-motion) and
[RemyDegenne/kolmogorov_extension4](https://github.com/RemyDegenne/kolmogorov_extension4)
(Apache 2.0; see `BrownianMotion/UPSTREAM.md` and `KolmogorovExtension4/UPSTREAM.md`).

## Authorship and licence

The mathematics is by Yuhao Lei. The formalization was carried out with AI assistance under the
author's direction, as recorded in [`formalization.yaml`](formalization.yaml).
Licensed under Apache 2.0 ([`LICENSE`](LICENSE)).
