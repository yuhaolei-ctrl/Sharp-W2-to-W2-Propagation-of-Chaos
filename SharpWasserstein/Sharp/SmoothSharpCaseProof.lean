/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.SmoothSharpCase
public import SharpWasserstein.Sharp.Source.Proposition
public import SharpWasserstein.Sharp.Hierarchy.Main
public import SharpWasserstein.Sharp.Endpoint.SmoothCase

/-!
# Proof of the smooth case of Theorem 2.1

This file assembles the smooth case of Theorem 2.1 (Section 3.4 of the paper):

* Proposition 3.6 (`Source.exists_initial_profile_sharp`) bounds the tangent energies of the
  marginal sources at the switching time `s` by `(A₀ + A₁ / √s)² m² / N²`;
* Proposition 3.7 (`Hierarchy.prefixEnergy_quadratic_bound_sharp`) propagates this profile along
  the particle flow with the rate `ω = D + 3λ`;
* together they give the energy hypothesis `Endpoint.SharpSourceEnergyBound`, and Lemma 3.5
  (`Source.sharpReferenceBound`) gives `Endpoint.SharpReferenceBound`;
* `Endpoint.smooth_case` then yields the bound `W₂² ≤ C_T k² / N²`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace SharpWasserstein.Sharp

open RegularizedBrownianSource

variable {d N : ℕ} {a : Position d → Position d} {K : Position d → Position d → Position d}
  {La L₁ L₂ M : ℝ}

/-- Propositions 3.6 and 3.7 combined: the energy hypothesis of the endpoint argument. -/
theorem sharpSourceEnergyBound (hS : IsSmoothCoefficients a K La L₁ L₂ M)
    {μ : ℝ → Measure (Position d)} {P₀ : Measure (Configuration d N)} (hex : Exchangeable P₀)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hinit : ∀ k (hk : k ≤ N), 1 ≤ k →
      wassersteinSq (marginal hk P₀) (tensorLaw (μ 0) k) ≤
        ENNReal.ofReal (C₀ * (k : ℝ) ^ 2 / (N : ℝ) ^ 2)) (T : ℝ) :
    Endpoint.SharpSourceEnergyBound a K La L₁ L₂ M C₀ T μ P₀ := by
  intro hN hb Mb Lb₁ Lb₂ hbound hMb hLb₁ hLb₂ hμ hP hP₀ t ht htT s hs hst k hk hkpos
  have := law_probability hb hbound hMb hLb₁ hμ P₀ hP₀ hs.le
  obtain ⟨σ₀, hσ₀, -, hprof⟩ := Source.exists_initial_profile_sharp hb hbound hMb hLb₁ hμ P₀
    hP₀ hS hN hex hC₀ hs (hst.trans htT) hinit
  exact Hierarchy.prefixEnergy_quadratic_bound_sharp hN hb hbound hMb hLb₁ hLb₂ ht.le
    (PrescribedReference.law hb hbound hMb hLb₁ hμ N P₀ s)
    (law_secondMoment hb hbound hMb hLb₁ hμ P₀ hP₀ hs.le)
    (current_memLp hb hbound hMb hLb₁ hμ P₀ hP₀ hN hs.le) hS
    (law_exchangeable hb hbound hMb hLb₁ hμ P₀ hex hs)
    (current_covariant hb hbound hMb hLb₁ hμ P₀ s) (sq_nonneg _) σ₀ hσ₀ hprof hkpos hk
    ⟨sub_nonneg.mpr hst, sub_le_self _ hs.le⟩

/-- **Theorem 2.1, smooth case.** For smooth bounded coefficients with bounded derivatives
satisfying Assumption A, the sharp propagation estimate holds with the constant `C_T`. -/
theorem smoothSharpCase : SmoothSharpCase := by
  intro d N a K La L₁ L₂ M hS hN μ hμ P hP C₀ hC₀ hinit T hT
  have := hP.1.probability 0 le_rfl
  exact Endpoint.smooth_case hS hN hμ hP hC₀ hinit hT
    (sharpSourceEnergyBound hS hP.2 hC₀ hinit T) (Source.sharpReferenceBound hS hinit T)

end SharpWasserstein.Sharp
