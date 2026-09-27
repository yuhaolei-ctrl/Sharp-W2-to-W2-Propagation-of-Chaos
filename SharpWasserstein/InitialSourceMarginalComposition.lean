import SharpWasserstein.InitialSourceMarginalPairing

/-! Successive genuine linear source marginals agree with the composed
observation. The intermediate canonical tangent is eliminated using the
proved bounded-cylinder cutoff pairing. -/
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff
namespace SharpWasserstein.InitialSourceMarginal
open WeightedTangent
variable {n m k : ℕ}
  [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  [MeasurableSpace (Point m)] [BorelSpace (Point m)]
  [MeasurableSpace (Point k)] [BorelSpace (Point k)]

theorem imageSource_comp (μ : Measure (Point n)) [IsFiniteMeasure μ]
    (σ : Test n →ₗ[ℝ] ℝ) (E : Point n →L[ℝ] Point m) (A : Point m →L[ℝ] Point k) :
    imageSource (μ.map E) (imageSource μ σ E) A = imageSource μ σ (A.comp E) := by
  ext φ
  rw [imageSource_apply,imageSource_apply]
  obtain ⟨hf,hfa,hfb⟩ := cylinder_bounds A φ
  have hh := PropagatedFlux.representative_bounded_smooth_pairing μ E E.continuous.measurable
    (E.compLpₗ 2 μ (representative μ σ).val) hf hfa hfb
  change (∫ x,⟪gradient (φ.val ∘ A) x,
      (representative (μ.map E) (imageSource μ σ E)).val x⟫_ℝ ∂μ.map E) = _ at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards [E.coeFn_compLp (representative μ σ).val] with x hx
  change ⟪gradient (φ.val ∘ A) (E x),E.compLp (representative μ σ).val x⟫_ℝ = _
  rw [hx,inner_gradient_left,inner_gradient_left]
  have he : φ.val ∘ ⇑(A.comp E) = (φ.val ∘ A) ∘ E := rfl
  rw [he,fderiv_comp x (hf.differentiable (by simp) _) E.differentiableAt,
    ContinuousLinearMap.fderiv]
  rfl

end SharpWasserstein.InitialSourceMarginal
