import SharpWasserstein.PeriodicConvolutionMarginalFunctional
import SharpWasserstein.PeriodicOptimizerFunctionalCongruence

/-! Product-kernel smoothing preserves every genuine marginal initial energy
bound with coefficient one. The marginal is taken after smoothing the full
canonical source; its action is identified with smoothing the original
canonical marginal on the true periodic gradient closure. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ContDiff BoundedContinuousFunction
namespace SharpWasserstein.PeriodicConvolution
open WeightedTangent WeightedMarginal PeriodicBochner PeriodicIntegrationByParts
open PeriodicGalerkin PeriodicGradientClosure PeriodicSmoothGradient PeriodicMarginalEnergy
variable {n m : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  [MeasurableSpace (Point (n+m))] [BorelSpace (Point (n+m))]
  (μ : Measure (Point (n+m))) [IsProbabilityMeasure μ]

local instance : IsProbabilityMeasure ((coordinateLaw μ).map (prefixCoords n m)) :=
  Measure.isProbabilityMeasure_map (prefix_continuous n m).measurable.aemeasurable

theorem marginalFunctional_convolvedRepresentative_periodic (κ : ℝ)
    (σ : Test (n+m) →ₗ[ℝ] ℝ) (w : periodicSpace (n := n)) :
    marginalFunctional (convolvedFunctional κ (coordinateLaw μ) (coordinateRepresentative μ σ)
      (coordinateRepresentative_integrable μ σ)) w =
    convolvedFunctional κ (coordinateLaw (marginalLaw μ))
      (coordinateRepresentative (marginalLaw μ) (marginalDistribution μ σ))
      (coordinateRepresentative_integrable (marginalLaw μ) (marginalDistribution μ σ)) w := by
  apply functional_eq_on_periodicSpace_of_smooth
  intro f hf hp
  exact marginalFunctional_convolvedRepresentative_gradient μ κ σ hf hp

/-- The energy of each actual marginal of the convolved full source is at
most the original marginal energy. No full-energy replacement loses the
quadratic marginal profile. -/
theorem marginal_convolved_representative_optimizer_energy_le (κ : ℝ)
    (σ : Test (n+m) →ₗ[ℝ] ℝ) :
    let ℓ := convolvedFunctional κ (coordinateLaw μ) (coordinateRepresentative μ σ)
      (coordinateRepresentative_integrable μ σ)
    marginalFunctional ℓ
      (optimizer (densityBCF κ ((coordinateLaw μ).map (prefixCoords n m))) (marginalFunctional ℓ)) ≤
      energy (marginalLaw μ) (marginalDistribution μ σ) := by
  dsimp only
  have hρ : densityBCF κ ((coordinateLaw μ).map (prefixCoords n m)) =
      densityBCF κ (coordinateLaw (marginalLaw μ)) := by
    ext x
    change density κ ((coordinateLaw μ).map (prefixCoords n m)) (coordinateEquiv n x) =
      density κ (coordinateLaw (marginalLaw μ)) (coordinateEquiv n x)
    rw [coordinateLaw_marginal]
  rw [hρ]
  let ℓ := marginalFunctional (convolvedFunctional κ (coordinateLaw μ) (coordinateRepresentative μ σ)
    (coordinateRepresentative_integrable μ σ))
  let ℓ' := convolvedFunctional κ (coordinateLaw (marginalLaw μ))
    (coordinateRepresentative (marginalLaw μ) (marginalDistribution μ σ))
    (coordinateRepresentative_integrable (marginalLaw μ) (marginalDistribution μ σ))
  have he := optimizer_energy_eq_of_functional_eq_on_periodicSpace
    (densityBCF κ (coordinateLaw (marginalLaw μ))) ℓ ℓ'
    (densityBCF_positive_lower κ n (coordinateLaw (marginalLaw μ)))
    (Eventually.of_forall (densityBCF_lower κ (coordinateLaw (marginalLaw μ))))
    (marginalFunctional_convolvedRepresentative_periodic μ κ σ)
  exact he.trans_le (convolved_representative_optimizer_energy_le κ (marginalLaw μ)
    (marginalDistribution μ σ) (marginalDistribution_finite μ σ))

end SharpWasserstein.PeriodicConvolution
