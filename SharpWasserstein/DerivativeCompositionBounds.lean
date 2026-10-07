module

public import SharpWasserstein.Compat
public import SharpWasserstein.NoiseAverageDerivatives
public import Mathlib.Analysis.Normed.Operator.Mul

@[expose] public section

/-! Quantitative chain-rule bounds for genuine Fréchet derivatives. -/
noncomputable section
open scoped NNReal
namespace SharpWasserstein
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The true derivative of a composition is Lipschitz with the second-order
chain-rule coefficient. All four constants bound actual functions or derivatives. -/
theorem lipschitz_fderiv_comp {f : E → F} {g : D → E} {L₀ L₁ K₀ K₁ : ℝ≥0}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hf₀ : LipschitzWith L₀ f) (hf₁ : LipschitzWith L₁ (fderiv ℝ f))
    (hg₀ : LipschitzWith K₀ g) (hg₁ : LipschitzWith K₁ (fderiv ℝ g)) :
    LipschitzWith (L₁*K₀^2 + L₀*K₁) (fderiv ℝ (f ∘ g)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, fderiv_comp x (hf _) (hg x), fderiv_comp y (hf _) (hg y)]
  have heq : (fderiv ℝ f (g x)).comp (fderiv ℝ g x) -
      (fderiv ℝ f (g y)).comp (fderiv ℝ g y) =
      (fderiv ℝ f (g x) - fderiv ℝ f (g y)).comp (fderiv ℝ g x) +
      (fderiv ℝ f (g y)).comp (fderiv ℝ g x - fderiv ℝ g y) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  rw [heq]
  have hfx := hf₁.norm_sub_le (g x) (g y)
  have hgxy := hg₀.norm_sub_le x y
  have hdfy : ‖fderiv ℝ f (g y)‖ ≤ L₀ := norm_fderiv_le_of_lipschitz ℝ hf₀
  have hdgx : ‖fderiv ℝ g x‖ ≤ K₀ := norm_fderiv_le_of_lipschitz ℝ hg₀
  have hDgxy := hg₁.norm_sub_le x y
  calc
    _ ≤ ‖(fderiv ℝ f (g x) - fderiv ℝ f (g y)).comp (fderiv ℝ g x)‖ +
      ‖(fderiv ℝ f (g y)).comp (fderiv ℝ g x - fderiv ℝ g y)‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ f (g x) - fderiv ℝ f (g y)‖ * ‖fderiv ℝ g x‖ +
      ‖fderiv ℝ f (g y)‖ * ‖fderiv ℝ g x - fderiv ℝ g y‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ ((L₁ : ℝ) * ((K₀ : ℝ) * ‖x-y‖)) * K₀ + L₀ * ((K₁ : ℝ) * ‖x-y‖) := by
      apply add_le_add
      · exact mul_le_mul (hfx.trans (mul_le_mul_of_nonneg_left hgxy L₁.coe_nonneg)) hdgx
          (norm_nonneg _) (by positivity)
      · exact mul_le_mul hdfy hDgxy (norm_nonneg _) L₀.coe_nonneg
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, dist_eq_norm]; ring

end SharpWasserstein
