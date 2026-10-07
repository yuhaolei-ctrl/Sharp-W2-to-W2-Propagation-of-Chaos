/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.Source.ReferenceTransport
public import SharpWasserstein.Sharp.Endpoint.Hypotheses

/-!
# The reference bound of the endpoint assembly

This file supplies the hypothesis `SharpWasserstein.Sharp.Endpoint.SharpReferenceBound` of the
smooth case of Theorem 2.1 (Section 3.4, `sec:proof-main`): the squared form
`W²(R^{(k)}_t, μ_t^{⊗k}) ≤ e^{2Lt} C₀ k²/N²` of the reference estimate of Lemma 3.5
(`lem:reference-W`), for `0 < t ≤ T` and `1 ≤ k ≤ N`, under the initial hierarchy
(`eq:initial`). It is
`marginal_wassersteinSq_le_sharp` with the qualitative data quantified universally.

It also records that the initial hierarchy, stated for levels `1 ≤ k ≤ N` as in Theorem 2.1,
extends to the level `k = 0`, where both laws live on a one-point space.

## Main statements

* `sharpReferenceBound`: `SharpReferenceBound a K La L₁ C₀ T μ P₀` under the initial hierarchy.
* `initialHierarchy_all`: the initial hierarchy at all levels `0 ≤ k ≤ N`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace SharpWasserstein.Sharp.Source

variable {d N : ℕ}

/-- Two probability laws of configurations of zero particles are at distance zero. -/
theorem wassersteinSq_eq_zero_of_zero (μ ν : Measure (Configuration d 0)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : wassersteinSq μ ν = 0 := by
  refine le_antisymm ((wassersteinSq_le_cost (product_isCoupling μ ν)).trans_eq ?_) bot_le
  simp [transportCost, productCost]

/-- The initial hierarchy `eq:initial`, assumed for `1 ≤ k ≤ N` as in Theorem 2.1, holds at all
levels `0 ≤ k ≤ N`. -/
theorem initialHierarchy_all {P : Measure (Configuration d N)} [IsProbabilityMeasure P]
    {r : Measure (Position d)} [IsProbabilityMeasure r] {C₀ : ℝ}
    (hinit : ∀ k (hk : k ≤ N), 1 ≤ k →
      wassersteinSq (marginal hk P) (tensorLaw r k) ≤
        ENNReal.ofReal (C₀ * (k : ℝ) ^ 2 / (N : ℝ) ^ 2)) :
    ∀ k, ∀ hk : k ≤ N, wassersteinSq (marginal hk P) (tensorLaw r k) ≤
      ENNReal.ofReal (C₀ * (k : ℝ) ^ 2 / (N : ℝ) ^ 2) := by
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have : IsProbabilityMeasure (marginal hk P) :=
      Measure.isProbabilityMeasure_map (measurable_restrictCoordinates hk).aemeasurable
    have : IsProbabilityMeasure (tensorLaw r 0) := by
      unfold tensorLaw
      infer_instance
    rw [wassersteinSq_eq_zero_of_zero]
    exact zero_le
  · exact hinit k hk hk0

/-- **Lemma 3.5 (`lem:reference-W`) in the form of the endpoint assembly.** Under the initial
hierarchy `W²(P₀^{(k)}, μ_0^{⊗k}) ≤ C₀ k²/N²` for `1 ≤ k ≤ N`, the reference law satisfies
`W²(R^{(k)}_t, μ_t^{⊗k}) ≤ e^{2Lt} C₀ k²/N²` for `0 < t ≤ T` and `1 ≤ k ≤ N`, for every choice
of the qualitative data. -/
theorem sharpReferenceBound {a : Position d → Position d}
    {K : Position d → Position d → Position d} {La L₁ L₂ M : ℝ}
    (hS : IsSmoothCoefficients a K La L₁ L₂ M) {μ : ℝ → Measure (Position d)}
    {P₀ : Measure (Configuration d N)} [IsProbabilityMeasure P₀] {C₀ : ℝ}
    (hinit : ∀ k (hk : k ≤ N), 1 ≤ k →
      wassersteinSq (marginal hk P₀) (tensorLaw (μ 0) k) ≤
        ENNReal.ofReal (C₀ * (k : ℝ) ^ 2 / (N : ℝ) ^ 2)) (T : ℝ) :
    Endpoint.SharpReferenceBound a K La L₁ C₀ T μ P₀ := by
  intro hb Mb Lb₁ Lb₂ hbound hMb hLb₁ hμ t ht _ k hk hk1
  exact marginal_wassersteinSq_le_sharp hS hb hbound hMb hLb₁ hμ P₀ ht.le hk (hinit k hk hk1)

end SharpWasserstein.Sharp.Source
