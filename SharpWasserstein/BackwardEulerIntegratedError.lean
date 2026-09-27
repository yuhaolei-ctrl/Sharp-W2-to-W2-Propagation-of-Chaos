import SharpWasserstein.FrozenGaussianBoundedError

/-! The actual backward Euler Gaussian consistency estimate integrated
against an arbitrary probability law, including singular and correlated laws. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ContDiff
namespace SharpWasserstein.BackwardEuler
open WeightedTangent NoiseAverage
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]

theorem integral_step_error_bound {b : Configuration d N → Configuration d N}
    {K M L L₁ L₂ : ℝ≥0} (hb : LipschitzWith K b) (hM : ∀ x, ‖b x‖ ≤ M)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hB : AllDerivativesBounded φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    (hL₂ : LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ)))
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (δ : ℝ≥0) :
    ‖(∫ x, step b δ φ x ∂μ)-(∫ x, φ x ∂μ)-(δ:ℝ)*(∫ x, generator b φ x ∂μ)‖ ≤
      (δ:ℝ)*((N*d:ℕ)*(L₂:ℝ)+L₁*M)*((M:ℝ)*δ+Real.sqrt (2*δ)*FrozenGaussian.noiseFirstMoment d N) := by
  obtain ⟨A,_,hA⟩ := hB.bounded
  have hφ₂ : ContDiff ℝ 2 φ := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hGL := generator_lipschitz_of_derivatives hφ₂ hL hL₁ hL₂ hb hM
  have hGn := generator_norm_le_of_derivatives hφ₂ hL hL₁ hM
  have hiφ : Integrable φ μ := Integrable.of_bound hφ.continuous.aestronglyMeasurable A
    (Eventually.of_forall hA)
  have hiG : Integrable (generator b φ) μ := Integrable.of_bound hGL.continuous.aestronglyMeasurable
    ((N*d:ℕ)*(L₁:ℝ)+L*M) (Eventually.of_forall hGn)
  have hist : Integrable (step b δ φ) μ := Integrable.of_bound
    (lipschitz_step hb δ hL hA).continuous.aestronglyMeasurable A
    (Eventually.of_forall (norm_step_le b δ hA))
  have he : (∫ x, step b δ φ x ∂μ)-(∫ x, φ x ∂μ)-(δ:ℝ)*(∫ x, generator b φ x ∂μ) =
      ∫ x, step b δ φ x-φ x-(δ:ℝ)*generator b φ x ∂μ := by
    have hs := integral_sub (hist.sub hiφ) (hiG.const_mul (δ:ℝ))
    simp only [Pi.sub_apply] at hs
    rw [hs,integral_sub hist hiφ,integral_const_mul]
  rw [he]
  have hpoint (x : Configuration d N) :
      ‖step b δ φ x-φ x-(δ:ℝ)*generator b φ x‖ ≤
        (δ:ℝ)*((N*d:ℕ)*(L₂:ℝ)+L₁*M)*((M:ℝ)*δ+Real.sqrt (2*δ)*FrozenGaussian.noiseFirstMoment d N) := by
    rw [step_eq_integral_transitionLaw b δ hφ.continuous,FrozenGaussian.integral_transitionLaw hφ.continuous]
    exact FrozenGaussian.step_error_bound_bounded hφ hB hL hL₁ hL₂ x (b x) (hM x) δ.coe_nonneg
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hpoint)

end SharpWasserstein.BackwardEuler
