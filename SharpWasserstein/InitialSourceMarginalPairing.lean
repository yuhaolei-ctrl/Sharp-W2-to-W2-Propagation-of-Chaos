module

public import SharpWasserstein.Compat
public import SharpWasserstein.PropagatedFluxSmoothPairing
public import SharpWasserstein.WeightedMarginal

@[expose] public section

/-! Genuine linear-image marginals of one finite-energy source. The canonical
representative is projected as an actual L² field. Compact cutoff density
proves that any other representing flux gives the same cylinder pairing. -/
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff
namespace SharpWasserstein.InitialSourceMarginal
open WeightedTangent
variable {n m : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  [MeasurableSpace (Point m)] [BorelSpace (Point m)]

/-- Compact-test equality extends to bounded smooth tests by actual weighted
compact-cutoff approximation, without a density or product-law hypothesis. -/
theorem representative_bounded_pairing (μ : Measure (Point n)) [IsFiniteMeasure μ]
    (σ : Test n →ₗ[ℝ] ℝ) (V : Lp (Point n) 2 μ)
    (hV : ∀ φ : Test n, σ φ = ∫ x, ⟪gradient φ.val x,V x⟫_ℝ ∂μ)
    {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfa : ∃ A : ℝ,∀ x,|f x| ≤ A) (hfb : ∃ B : ℝ,∀ x,‖gradient f x‖ ≤ B) :
    (∫ x,⟪gradient f x,(representative μ σ).val x⟫_ℝ ∂μ) =
      ∫ x,⟪gradient f x,V x⟫_ℝ ∂μ := by
  have hg := bounded_smooth_gradient_memLp μ f hf hfb
  let w : gradientClosure μ :=
    ⟨hg.toLp (gradient f),bounded_smooth_gradient_memClosure μ f hf hfa hfb hg⟩
  have h := flux_residual_orthogonal μ σ V hV w
  rw [inner_sub_left,sub_eq_zero] at h
  have hp (U : Lp (Point n) 2 μ) :
      ⟪U,w.val⟫_ℝ = ∫ x,⟪gradient f x,U x⟫_ℝ ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    change ⟪U x,hg.toLp (gradient f) x⟫_ℝ = _
    rw [hx,real_inner_comm]
  rw [hp,hp] at h
  exact h.symm

/-- Actual pushforward distribution, defined from the canonical full tangent. -/
def imageSource (μ : Measure (Point n)) [IsFiniteMeasure μ]
    (σ : Test n →ₗ[ℝ] ℝ) (A : Point n →L[ℝ] Point m) : Test m →ₗ[ℝ] ℝ :=
  PropagatedFlux.source μ A A.continuous.measurable
    (A.compLpₗ 2 μ (representative μ σ).val)

theorem imageSource_finite (μ : Measure (Point n)) [IsFiniteMeasure μ]
    (σ : Test n →ₗ[ℝ] ℝ) (A : Point n →L[ℝ] Point m) :
    FiniteEnergy (μ.map A) (imageSource μ σ A) :=
  PropagatedFlux.source_finiteEnergy _ _ _ _

theorem imageSource_apply (μ : Measure (Point n)) [IsFiniteMeasure μ]
    (σ : Test n →ₗ[ℝ] ℝ) (A : Point n →L[ℝ] Point m) (φ : Test m) :
    imageSource μ σ A φ =
      ∫ x,⟪gradient (φ.val ∘ A) x,(representative μ σ).val x⟫_ℝ ∂μ := by
  rw [imageSource,PropagatedFlux.source_apply]
  apply integral_congr_ae
  filter_upwards [A.coeFn_compLp (representative μ σ).val] with x hx
  change ⟪gradient φ.val (A x),A.compLp (representative μ σ).val x⟫_ℝ = _
  rw [hx,inner_gradient_left,inner_gradient_left,
    fderiv_comp x (test_differentiable φ _) A.differentiableAt,
    ContinuousLinearMap.fderiv]
  rfl

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  [MeasurableSpace (Point m)] [BorelSpace (Point m)] in
/-- A compact test composed with any continuous linear map is bounded and has
a bounded gradient, even when its cylinder is not compactly supported. -/
theorem cylinder_bounds (A : Point n →L[ℝ] Point m) (φ : Test m) :
    ContDiff ℝ ∞ (φ.val ∘ A) ∧
    (∃ C : ℝ,∀ x,|(φ.val ∘ A) x| ≤ C) ∧
    (∃ C : ℝ,∀ x,‖gradient (φ.val ∘ A) x‖ ≤ C) := by
  refine ⟨φ.property.1.comp A.contDiff,?_,?_⟩
  · obtain ⟨C,hC⟩ := φ.property.2.exists_bound_of_continuous φ.property.1.continuous
    exact ⟨C,fun x => by simpa only [Real.norm_eq_abs,Function.comp_apply] using hC (A x)⟩
  · obtain ⟨C,hC⟩ := (compactSupport_test_gradient φ).exists_bound_of_continuous
      (continuous_test_gradient φ)
    refine ⟨C*‖A‖,fun x => ?_⟩
    rw [SmoothCutoff.norm_gradient_eq_fderiv,
      fderiv_comp x (test_differentiable φ _) A.differentiableAt,
      ContinuousLinearMap.fderiv]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [← SmoothCutoff.norm_gradient_eq_fderiv]
    exact hC (A x)

/-- The genuine marginal is independent of the choice of representing flux. -/
theorem imageSource_eq_flux_pairing (μ : Measure (Point n)) [IsFiniteMeasure μ]
    (σ : Test n →ₗ[ℝ] ℝ) (V : Lp (Point n) 2 μ)
    (hV : ∀ φ : Test n, σ φ = ∫ x,⟪gradient φ.val x,V x⟫_ℝ ∂μ)
    (A : Point n →L[ℝ] Point m) (φ : Test m) :
    imageSource μ σ A φ = ∫ x,⟪gradient (φ.val ∘ A) x,V x⟫_ℝ ∂μ := by
  rw [imageSource_apply]
  obtain ⟨hf,hfa,hfb⟩ := cylinder_bounds A φ
  exact representative_bounded_pairing μ σ V hV hf hfa hfb

/-- For the ordinary prefix projection this is exactly the existing genuine
`marginalDistribution`, not a separately chosen marginal source. -/
theorem imageSource_prefix_eq {p q : ℕ}
    [MeasurableSpace (Point (p+q))] [BorelSpace (Point (p+q))]
    [MeasurableSpace (Point p)] [BorelSpace (Point p)]
    (μ : Measure (Point (p+q))) [IsFiniteMeasure μ] (σ : Test (p+q) →ₗ[ℝ] ℝ) :
    imageSource μ σ (WeightedMarginal.prefixProjection p q) =
      WeightedMarginal.marginalDistribution μ σ := by
  ext φ
  rw [imageSource_apply,WeightedMarginal.marginalDistribution_integral]

end SharpWasserstein.InitialSourceMarginal
