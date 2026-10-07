/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.RegularizedBrownianSourceBound
public import SharpWasserstein.Sharp.Constants
public import SharpWasserstein.Sharp.SmoothCoefficients

/-!
# The two quantitative inputs of the smooth case of Theorem 2.1

The proof of the smooth case of Theorem 2.1 (`thm:main`) in Section 3.4 (`sec:proof-main`) of
the paper combines two quantitative estimates with the length lemma (Lemma 3.4, `lem:length`),
the interpolation lemma (Lemma 3.8, `lem:switch`) and the triangle inequality. This file states
these two estimates as propositions, in terms of the objects of the development, so that the
final assembly (`SharpWasserstein.Sharp.Endpoint.SmoothCase`) can be proved now and the estimates
can be supplied independently.

Let `a`, `K` be smooth coefficients with the Euclidean constants `L_a, L₁, L₂, M` of
Assumption A (`IsSmoothCoefficients`), driving the dynamics of the development through the
kernel `kernelOf a K`. Let `μ` be the limit evolution, `P₀` the initial law of the particle
system with `N` particles, `C₀` the constant of the initial hierarchy (`eq:initial`) and `T` the
horizon. The constants `A₀`, `A₁`, `ω`, `L` are `sourceA₀`, `sourceA₁`, `omega`, `lipL`
(`eq:const1`–`eq:const3`).

* `SharpSourceEnergyBound`: Propositions 3.6 (`prop:source`) and 3.7 (`prop:profile`) combined,
  as they are used in Section 3.4. For a switch time `0 < t ≤ T` and `0 < s ≤ t`, the tangent
  energy `E^{[s]}_k(t - s)` of the `k`-th marginal of the source `ζ^N_s = -div(R^N_s U_s)`,
  transported by the linearized particle flow for the time `t - s`, satisfies
  `E^{[s]}_k(t - s) ≤ (A₀ + A₁/√s)² e^{ω(t-s)} k²/N²`.
  In the development this energy is `BrownianEnergyPeriodization.prefixEnergy` of the Euclidean
  reference law `R^N_s = PrescribedReference.law … N P₀ s` and of the Euclidean form of the
  current `U_s = InitialSourcePermutation.initialCurrent b (μ s)`, exactly the object bounded by
  the old estimate `RegularizedBrownianSource.prefixEnergy_le` (whose conclusion had the
  non-sharp constant `propagationConstant d M L₁ L₂ C₀ t * (1 + 1/s)`). By
  `RegularizedBrownianSource.prescribed_marginal_energy_eq_prefix` it is the tangent energy of the
  derivative of the marginal interpolating curve `s ↦ ν^{N,t,(k)}_s` (`eq:switch-derivative`).
* `SharpReferenceBound`: Lemma 3.5 (`lem:reference-W`) in squared form,
  `W²(R^{(k)}_t, μ_t^{⊗k}) ≤ e^{2Lt} C₀ k²/N²` for `0 < t ≤ T`.

The objects of the development carry qualitative data: a proof of `BoundedSmoothKernel` and
sup-norm bounds `KernelBounds b Mb Lb₁ Lb₂` for the kernel `b = kernelOf a K`. These data never
enter the estimates, so both propositions quantify universally over them; in the same way they
quantify over the (proof-irrelevant) hypotheses on `μ` and `P₀` needed to form the objects.
Neither proposition assumes the initial hierarchy, exchangeability or smoothness: whoever proves
them states these assumptions as hypotheses of the theorem concluding the proposition.

## Main definitions

* `SharpSourceEnergyBound a K La L₁ L₂ M C₀ T μ P₀`: the source and profile estimate.
* `SharpReferenceBound a K La L₁ C₀ T μ P₀`: the reference estimate.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace SharpWasserstein.Sharp.Endpoint

open RegularizedBrownianSource InitialSourcePermutation

variable {d N : ℕ}

/-- **Propositions 3.6 and 3.7, as used in Section 3.4.** For every switch time `0 < t ≤ T`,
every `0 < s ≤ t` and every level `1 ≤ k ≤ N`, the tangent energy at time `t - s` of the
`k`-th marginal of the source `ζ^N_s`, carried by the reference law `R^N_s` and transported by
the linearized particle flow, is at most `(A₀ + A₁/√s)² e^{ω(t-s)} k²/N²`, where `A₀`, `A₁`
are the constants of the horizon `T`.

The energy is `BrownianEnergyPeriodization.prefixEnergy` with the switch time `t` as horizon,
the Euclidean reference law `euclideanLaw (PrescribedReference.law … N P₀ s)`, the Euclidean
current `euclideanFlux (initialCurrent (kernelOf a K) (μ s))` and the propagation time `t - s`,
exactly as in the old `RegularizedBrownianSource.prefixEnergy_le`. The statement quantifies over
the qualitative data needed to form these objects (smoothness of the kernel, sup-norm kernel
bounds `Mb, Lb₁, Lb₂`, the limit evolution, and the probability and second moment of `P₀`). -/
def SharpSourceEnergyBound (a : Position d → Position d)
    (K : Position d → Position d → Position d) (La L₁ L₂ M C₀ T : ℝ)
    (μ : ℝ → Measure (Position d)) (P₀ : Measure (Configuration d N)) : Prop :=
  ∀ (hN : 0 < N) (hb : BoundedSmoothKernel (kernelOf a K)) (Mb Lb₁ Lb₂ : ℝ)
    (hbound : KernelBounds (kernelOf a K) Mb Lb₁ Lb₂) (hMb : 0 ≤ Mb) (hLb₁ : 0 ≤ Lb₁)
    (hLb₂ : 0 ≤ Lb₂) (hμ : IsLimitEvolution (kernelOf a K) μ)
    (_ : IsProbabilityMeasure P₀) (hP₀ : HasSecondMoment P₀)
    (t : ℝ) (ht : 0 < t), t ≤ T → ∀ (s : ℝ) (hs : 0 < s), s ≤ t →
    ∀ (k : ℕ) (hk : k ≤ N), 1 ≤ k →
      letI : IsProbabilityMeasure (PrescribedReference.law hb hbound hMb hLb₁ hμ N P₀ s) :=
        law_probability hb hbound hMb hLb₁ hμ P₀ hP₀ hs.le
      BrownianEnergyPeriodization.prefixEnergy hN hb hbound hMb hLb₁ hLb₂ ht.le
          (euclideanLaw (PrescribedReference.law hb hbound hMb hLb₁ hμ N P₀ s)) hk
          (euclideanFlux (initialCurrent (kernelOf a K) (μ s)))
          (current_memLp hb hbound hMb hLb₁ hμ P₀ hP₀ hN hs.le) (t - s) ≤
        (sourceA₀ C₀ T La L₁ L₂ M + sourceA₁ C₀ T La L₁ M / Real.sqrt s) ^ 2 *
          Real.exp (omega La L₁ L₂ M * (t - s)) * (k : ℝ) ^ 2 / (N : ℝ) ^ 2

/-- **Lemma 3.5 (`lem:reference-W`), squared.** For `0 < t ≤ T` and `1 ≤ k ≤ N`, the `k`-th
marginal of the reference law `R^N_t = P₀ Q_{0,t}^{⊗N}` (`PrescribedReference.law … N P₀ t`)
satisfies `W²(R^{(k)}_t, μ_t^{⊗k}) ≤ e^{2Lt} C₀ k²/N²`, with `L = L_a + L₁`. The statement
quantifies over the qualitative data needed to form the reference law. -/
def SharpReferenceBound (a : Position d → Position d)
    (K : Position d → Position d → Position d) (La L₁ C₀ T : ℝ)
    (μ : ℝ → Measure (Position d)) (P₀ : Measure (Configuration d N)) : Prop :=
  ∀ (hb : BoundedSmoothKernel (kernelOf a K)) (Mb Lb₁ Lb₂ : ℝ)
    (hbound : KernelBounds (kernelOf a K) Mb Lb₁ Lb₂) (hMb : 0 ≤ Mb) (hLb₁ : 0 ≤ Lb₁)
    (hμ : IsLimitEvolution (kernelOf a K) μ) (t : ℝ), 0 < t → t ≤ T →
    ∀ (k : ℕ) (hk : k ≤ N), 1 ≤ k →
      wassersteinSq (marginal hk (PrescribedReference.law hb hbound hMb hLb₁ hμ N P₀ t))
          (tensorLaw (μ t) k) ≤
        ENNReal.ofReal (Real.exp (lipL La L₁ * t) ^ 2 * C₀ * (k : ℝ) ^ 2 / (N : ℝ) ^ 2)

end SharpWasserstein.Sharp.Endpoint
