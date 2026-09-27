import SharpWasserstein.PeriodicConvolutionCoordinateLaw
import SharpWasserstein.PeriodicMarginalEnergy

/-! Actual convolution of the full canonical source has exactly the same
periodic marginal test action as convolution of its canonical marginal source.
This is a source identity, not only marginal consistency of the density. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace SharpWasserstein.PeriodicConvolution
open WeightedTangent WeightedMarginal PeriodicIntegrationByParts PeriodicPositiveKernel PeriodicBochner
open PeriodicGalerkin PeriodicGradientClosure PeriodicSmoothGradient PeriodicMarginalLift PeriodicMarginalEnergy
variable {n m : ℕ}

theorem euclideanGradient_prefix {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f)
    (x : Coordinates (n+m)) :
    euclideanGradient (f ∘ prefixCoords n m) x =
      prefixEmbedding n m (euclideanGradient f (prefixCoords n m x)) := by
  change gradient ((f ∘ coordinateEquiv n) ∘ prefixProjection n m) ((coordinateEquiv (n+m)).symm x) = _
  rw [gradient_comp_prefixProjection ((hf.comp (coordinateEquiv n).contDiff).differentiable (by simp))]
  rfl

variable [MeasurableSpace (Point n)] [BorelSpace (Point n)]

theorem convolvedRepresentative_gradient (κ : ℝ) (μ : Measure (Point n)) [IsProbabilityMeasure μ]
    (σ : Test n →ₗ[ℝ] ℝ) {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    convolvedFunctional κ (coordinateLaw μ) (coordinateRepresentative μ σ)
      (coordinateRepresentative_integrable μ σ) (gradientVector f hf) =
    ∫ y, ⟪∫ x, kernel κ (x-coordinateEquiv n y) • euclideanGradient f x ∂cube n,
      (representative μ σ).val y⟫_ℝ ∂μ := by
  rw [convolvedFunctional_gradient _ _ _ _ hf hp,
    integral_fluxSource_convolved_test _ _ (coordinateRepresentative_integrable μ σ) hf hp,
    integral_coordinateLaw]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    simp only [coordinateRepresentative,ContinuousLinearEquiv.symm_apply_apply]

variable [MeasurableSpace (Point (n+m))] [BorelSpace (Point (n+m))]
  (μ : Measure (Point (n+m))) [IsProbabilityMeasure μ]

instance marginalLaw_probability : IsProbabilityMeasure (marginalLaw (n := n) (m := m) μ) :=
  Measure.isProbabilityMeasure_map (prefixProjection n m).continuous.measurable.aemeasurable

omit [IsProbabilityMeasure μ] in
theorem coordinateLaw_marginal :
    (coordinateLaw μ).map (prefixCoords n m) = coordinateLaw (marginalLaw μ) := by
  rw [coordinateLaw,Measure.map_map (prefix_continuous n m).measurable
    (coordinateEquiv (n+m)).continuous.measurable,
    coordinateLaw,marginalLaw,Measure.map_map (coordinateEquiv n).continuous.measurable
      (prefixProjection n m).continuous.measurable]
  rfl

theorem marginalFunctional_convolvedRepresentative_gradient (κ : ℝ)
    (σ : Test (n+m) →ₗ[ℝ] ℝ) {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    marginalFunctional (convolvedFunctional κ (coordinateLaw μ) (coordinateRepresentative μ σ)
      (coordinateRepresentative_integrable μ σ)) (gradientVector f hf) =
    convolvedFunctional κ (coordinateLaw (marginalLaw μ))
      (coordinateRepresentative (marginalLaw μ) (marginalDistribution μ σ))
      (coordinateRepresentative_integrable (marginalLaw μ) (marginalDistribution μ σ))
      (gradientVector f hf) := by
  change convolvedFunctional _ _ _ _ (gradientLift (m := m) (gradientVector f hf)) = _
  rw [gradientLift_gradientVector,convolvedRepresentative_gradient _ _ _
    (hf.comp (prefix_smooth n m)) (prefix_periodic hp),
    convolvedRepresentative_gradient _ _ _ hf hp]
  obtain ⟨C,_,hC⟩ := PeriodicSmoothBounds.norm_bound
    (euclideanGradient_periodic hp) (euclideanGradient_continuous hf)
  simp_rw [euclideanGradient_prefix hf]
  simp_rw [integral_kernel_prefixEmbedding (euclideanGradient_continuous hf) hC,
    inner_prefixEmbedding]
  exact marginal_representative_testAverage_pairing μ σ κ hf hp

end SharpWasserstein.PeriodicConvolution
