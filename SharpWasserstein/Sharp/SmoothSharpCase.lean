/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.Constants
public import SharpWasserstein.Sharp.SmoothCoefficients

/-!
# The smooth case of Theorem 2.1

`SmoothSharpCase` is the statement of Theorem 2.1 for smooth bounded coefficients with bounded
derivatives (the first paragraph of Section 3.4 of the paper), in the language of the development:
the laws are weak Fokker–Planck evolutions of the particle system and of the McKean–Vlasov
equation for the kernel `kernelOf a K`, positions are coordinate vectors, and the constant is the
explicit `sharpC` of the paper. It is proved from the source estimate, the tangent hierarchy and
the interpolating curve, and the general case of Theorem 2.1 is reduced to it by smooth
approximation.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace SharpWasserstein.Sharp

/-- Theorem 2.1 for smooth coefficients, with the explicit constant `sharpC`. -/
def SmoothSharpCase : Prop :=
  ∀ {d N : ℕ} {a : Position d → Position d} {K : Position d → Position d → Position d}
    {La L₁ L₂ M : ℝ}, IsSmoothCoefficients a K La L₁ L₂ M → 1 ≤ N →
    ∀ {μ : ℝ → Measure (Position d)}, IsLimitEvolution (kernelOf a K) μ →
    ∀ {P : ℝ → Measure (Configuration d N)}, IsParticleEvolution (kernelOf a K) P →
    ∀ {C₀ : ℝ}, 0 ≤ C₀ →
    (∀ k (hk : k ≤ N), 1 ≤ k →
      wassersteinSq (marginal hk (P 0)) (tensorLaw (μ 0) k) ≤
        ENNReal.ofReal (C₀ * (k : ℝ) ^ 2 / (N : ℝ) ^ 2)) →
    ∀ {T : ℝ}, 0 < T →
    ∀ t ∈ Set.Icc 0 T, ∀ k (hk : k ≤ N), 1 ≤ k →
      wassersteinSq (marginal hk (P t)) (tensorLaw (μ t) k) ≤
        ENNReal.ofReal (sharpC C₀ T La L₁ L₂ M * (k : ℝ) ^ 2 / (N : ℝ) ^ 2)

end SharpWasserstein.Sharp
