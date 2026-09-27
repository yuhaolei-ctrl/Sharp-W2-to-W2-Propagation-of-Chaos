import SharpWasserstein.PeriodicConvolutionMarginalSource
import SharpWasserstein.PeriodicConvolvedOptimizer

/-! The coordinate law and vector field used by periodic smoothing are the
actual pushforwards of a Euclidean law and its weighted tangent representative.
The coordinate map is never treated as an isometry. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace SharpWasserstein.PeriodicConvolution
open WeightedTangent WeightedMarginal PeriodicBochner PeriodicIntegrationByParts
variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

def coordinateLaw (μ : Measure (Point n)) : Measure (Coordinates n) :=
  μ.map (coordinateEquiv n)

instance coordinateLaw_probability (μ : Measure (Point n)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (coordinateLaw μ) :=
  Measure.isProbabilityMeasure_map (coordinateEquiv n).continuous.measurable.aemeasurable

theorem coordinateLaw_symm_measurePreserving (μ : Measure (Point n)) :
    MeasurePreserving (coordinateEquiv n).symm (coordinateLaw μ) μ := by
  refine ⟨(coordinateEquiv n).symm.continuous.measurable,?_⟩
  rw [coordinateLaw,Measure.map_map (coordinateEquiv n).symm.continuous.measurable
    (coordinateEquiv n).continuous.measurable]
  simp only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply]
  exact Measure.map_id

theorem integral_coordinateLaw (μ : Measure (Point n)) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Coordinates n → E) :
    (∫ x,f x ∂coordinateLaw μ) = ∫ y,f (coordinateEquiv n y) ∂μ :=
  integral_map_equiv (coordinateEquiv n).toHomeomorph.toMeasurableEquiv f

def coordinateRepresentative (μ : Measure (Point n)) [IsFiniteMeasure μ]
    (σ : Test n →ₗ[ℝ] ℝ) (x : Coordinates n) : Coordinates n :=
  coordinateEquiv n ((representative μ σ).val ((coordinateEquiv n).symm x))

theorem coordinateRepresentative_integrable (μ : Measure (Point n)) [IsFiniteMeasure μ]
    (σ : Test n →ₗ[ℝ] ℝ) : Integrable (coordinateRepresentative μ σ) (coordinateLaw μ) := by
  have hi := (Lp.memLp (representative μ σ).val).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hj := (coordinateEquiv n).toContinuousLinearMap.integrable_comp hi
  exact ((coordinateLaw_symm_measurePreserving μ).integrable_comp hj.aestronglyMeasurable).mpr hj

theorem coordinateRepresentative_sq_integrable (μ : Measure (Point n)) [IsFiniteMeasure μ]
    (σ : Test n →ₗ[ℝ] ℝ) :
    Integrable (fun x => ‖(coordinateEquiv n).symm (coordinateRepresentative μ σ x)‖^2)
      (coordinateLaw μ) := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.memLp (representative μ σ).val).aestronglyMeasurable).mp
    (Lp.memLp (representative μ σ).val)
  convert ((coordinateLaw_symm_measurePreserving μ).integrable_comp hi.aestronglyMeasurable).mpr hi using 1
  funext x
  simp only [coordinateRepresentative,ContinuousLinearEquiv.symm_apply_apply,Function.comp_def]

theorem coordinateRepresentative_energy (μ : Measure (Point n)) [IsFiniteMeasure μ]
    (σ : Test n →ₗ[ℝ] ℝ) (hσ : FiniteEnergy μ σ) :
    (∫ x, ‖(coordinateEquiv n).symm (coordinateRepresentative μ σ x)‖^2 ∂coordinateLaw μ) =
      energy μ σ := by
  rw [integral_coordinateLaw,energy_eq_norm_sq μ σ hσ]
  change _ = ‖(representative μ σ).val‖^2
  rw [lp_norm_sq_eq_integral]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [coordinateRepresentative,ContinuousLinearEquiv.symm_apply_apply]

/-- Smoothing the actual canonical representative contracts its true
Euclidean tangent energy with coefficient one. -/
theorem convolved_representative_optimizer_energy_le (κ : ℝ)
    (μ : Measure (Point n)) [IsProbabilityMeasure μ]
    (σ : Test n →ₗ[ℝ] ℝ) (hσ : FiniteEnergy μ σ) :
    convolvedFunctional κ (coordinateLaw μ) (coordinateRepresentative μ σ)
      (coordinateRepresentative_integrable μ σ)
      (PeriodicGradientClosure.optimizer (densityBCF κ (coordinateLaw μ))
        (convolvedFunctional κ (coordinateLaw μ) (coordinateRepresentative μ σ)
          (coordinateRepresentative_integrable μ σ))) ≤ energy μ σ := by
  exact (convolved_optimizer_energy_le κ (coordinateLaw μ) (coordinateRepresentative μ σ)
    (coordinateRepresentative_integrable μ σ) (coordinateRepresentative_sq_integrable μ σ)).trans_eq
      (coordinateRepresentative_energy μ σ hσ)

end SharpWasserstein.PeriodicConvolution
