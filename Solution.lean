/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.Final.Reduction
public import SharpWasserstein.Sharp.SmoothSharpCaseProof

/-!
# Solution: sharp Wasserstein propagation of chaos

The statement of `Challenge.lean`, proved from the development. The definitions it uses are those
of `SharpWasserstein.Statement`, which are copied verbatim from `Challenge.lean`.

The proof has two steps, as in Section 3.4 of the paper:
* `SharpWasserstein.Sharp.smoothSharpCase`: the estimate for smooth bounded coefficients with
  bounded derivatives, from the source estimate (Proposition 3.6), the tangent hierarchy
  (Proposition 3.7), the transport length lemma (Lemma 3.4), the reference estimate (Lemma 3.5)
  and the interpolating curve (Lemma 3.8);
* `SharpWasserstein.Sharp.Final.sharp_propagation_of_chaos_of_smoothSharpCase`: the reduction of
  the general case by smooth approximation (Lemmas 7.1 and 7.2).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SharpChaos

/-- **Theorem 2.1.** Under Assumption A, let `X` solve the particle system (1.1) with an
exchangeable initial law `P_{N,0} ∈ 𝒫₂((ℝᵈ)ᴺ)`, and let `Y` solve the McKean–Vlasov equation (1.2)
with `μ₀ = Law(Y(0)) ∈ 𝒫₂(ℝᵈ)`. If `W₂²(P^{(k)}_{N,0}, μ₀^{⊗k}) ≤ C₀ k²/N²` for `1 ≤ k ≤ N`, then
for every `T > 0`, all `0 ≤ t ≤ T` and `1 ≤ k ≤ N`,
`W₂²(P^{(k)}_{N,t}, μ_t^{⊗k}) ≤ C_T k²/N²` (2.5), where `C_T = sharpConstant C₀ T L_a L₁ L₂ M`. -/
theorem sharp_propagation_of_chaos {d N : ℕ} (hN : 1 ≤ N)
    {a : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {La L₁ L₂ M : ℝ} (hA : AssumptionA a K La L₁ L₂ M)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ → Ω → Fin N → EuclideanSpace ℝ (Fin d)}
    {W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : IsParticleSolution a K X W P)
    (hX₀ : MemLp (X 0) 2 P) (hexch : Exchangeable (P.map (X 0)))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : ℝ → Ω' → EuclideanSpace ℝ (Fin d)} {B : ℝ≥0 → Ω' → EuclideanSpace ℝ (Fin d)}
    (hY : IsMcKeanVlasovSolution a K Y B P') (hY₀ : MemLp (Y 0) 2 P')
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hinit : ∀ k (hk : k ≤ N), 1 ≤ k →
      wassersteinSq (marginal hk (P.map (X 0))) (Measure.pi fun _ : Fin k => P'.map (Y 0)) ≤
        ENNReal.ofReal (C₀ * k ^ 2 / N ^ 2))
    {T : ℝ} (hT : 0 < T) :
    ∀ t ∈ Icc 0 T, ∀ k (hk : k ≤ N), 1 ≤ k →
      wassersteinSq (marginal hk (P.map (X t))) (Measure.pi fun _ : Fin k => P'.map (Y t)) ≤
        ENNReal.ofReal (sharpConstant C₀ T La L₁ L₂ M * k ^ 2 / N ^ 2) :=
  SharpWasserstein.Sharp.Final.sharp_propagation_of_chaos_of_smoothSharpCase
    SharpWasserstein.Sharp.smoothSharpCase hN hA hX hX₀ hexch hY hY₀ hC₀ hinit hT

end SharpChaos
