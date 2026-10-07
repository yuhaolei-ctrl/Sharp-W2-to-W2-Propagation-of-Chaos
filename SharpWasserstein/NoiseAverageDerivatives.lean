module

public import SharpWasserstein.Compat
public import SharpWasserstein.BoundedNoiseAverage
public import Mathlib.Analysis.Calculus.ContDiff.Comp

@[expose] public section

/-! Genuine second and third derivative regularity for probability translation
averages. Derivative identities and Lipschitz bounds are proved for the actual
Bochner integrals, and can be used in backward Euler test estimates. -/
noncomputable section
open MeasureTheory
open scoped Topology NNReal
namespace SharpWasserstein.NoiseAverage
variable {Ω E F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Ω → E) (hξ : StronglyMeasurable ξ)

include hξ

theorem fderiv_average {f : E → F} (hf : ContDiff ℝ 1 f) {L : ℝ≥0} (hL : LipschitzWith L f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    fderiv ℝ (average μ ξ f) = average μ ξ (fderiv ℝ f) :=
  funext fun x ↦ (hasFDerivAt_average μ ξ hξ hf hL hC x).fderiv

theorem lipschitz_fderiv_average {f : E → F} (hf : ContDiff ℝ 1 f) {L L₁ : ℝ≥0}
    (hL : LipschitzWith L f) (hL₁ : LipschitzWith L₁ (fderiv ℝ f))
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    LipschitzWith L₁ (fderiv ℝ (average μ ξ f)) := by
  rw [fderiv_average μ ξ hξ hf hL hC]
  exact lipschitz_average μ ξ hξ hL₁ (fun _ ↦ norm_fderiv_le_of_lipschitz ℝ hL)

theorem contDiff_two_average {f : E → F} (hf : ContDiff ℝ 2 f) {L L₁ : ℝ≥0}
    (hL : LipschitzWith L f) (hL₁ : LipschitzWith L₁ (fderiv ℝ f))
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) : ContDiff ℝ 2 (average μ ξ f) := by
  have hf₁ : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  change ContDiff ℝ ((1 : WithTop ℕ∞) + 1) (average μ ξ f)
  apply contDiff_succ_iff_fderiv.mpr
  refine ⟨fun x ↦ (hasFDerivAt_average μ ξ hξ hf₁ hL hC x).differentiableAt, by norm_num, ?_⟩
  rw [fderiv_average μ ξ hξ hf₁ hL hC]
  exact contDiff_one_average μ ξ hξ (hf.fderiv_right (by norm_num)) hL₁
    (fun _ ↦ norm_fderiv_le_of_lipschitz ℝ hL)

theorem secondFDeriv_average {f : E → F} (hf : ContDiff ℝ 2 f) {L L₁ : ℝ≥0}
    (hL : LipschitzWith L f) (hL₁ : LipschitzWith L₁ (fderiv ℝ f))
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    fderiv ℝ (fderiv ℝ (average μ ξ f)) = average μ ξ (fderiv ℝ (fderiv ℝ f)) := by
  rw [fderiv_average μ ξ hξ (hf.of_le (by norm_num)) hL hC]
  exact fderiv_average μ ξ hξ (hf.fderiv_right (by norm_num)) hL₁
    (fun _ ↦ norm_fderiv_le_of_lipschitz ℝ hL)

theorem lipschitz_secondFDeriv_average {f : E → F} (hf : ContDiff ℝ 2 f) {L L₁ L₂ : ℝ≥0}
    (hL : LipschitzWith L f) (hL₁ : LipschitzWith L₁ (fderiv ℝ f))
    (hL₂ : LipschitzWith L₂ (fderiv ℝ (fderiv ℝ f)))
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    LipschitzWith L₂ (fderiv ℝ (fderiv ℝ (average μ ξ f))) := by
  rw [secondFDeriv_average μ ξ hξ hf hL hL₁ hC]
  exact lipschitz_average μ ξ hξ hL₂ (fun _ ↦ norm_fderiv_le_of_lipschitz ℝ hL₁)

theorem contDiff_three_average {f : E → F} (hf : ContDiff ℝ 3 f) {L L₁ L₂ : ℝ≥0}
    (hL : LipschitzWith L f) (hL₁ : LipschitzWith L₁ (fderiv ℝ f))
    (hL₂ : LipschitzWith L₂ (fderiv ℝ (fderiv ℝ f)))
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) : ContDiff ℝ 3 (average μ ξ f) := by
  have hf₁ : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  change ContDiff ℝ ((2 : WithTop ℕ∞) + 1) (average μ ξ f)
  apply contDiff_succ_iff_fderiv.mpr
  refine ⟨fun x ↦ (hasFDerivAt_average μ ξ hξ hf₁ hL hC x).differentiableAt, by norm_num, ?_⟩
  rw [fderiv_average μ ξ hξ hf₁ hL hC]
  exact contDiff_two_average μ ξ hξ (hf.fderiv_right (by norm_num)) hL₁ hL₂
    (fun _ ↦ norm_fderiv_le_of_lipschitz ℝ hL)

end SharpWasserstein.NoiseAverage
