import SharpWasserstein.ExternalInteractionEnergyCancellation
import SharpWasserstein.PeriodicMarginalEnergy

/-! Genuine convolved periodic Galerkin fluctuations. Strong convergence follows
from the actual marginal Galerkin construction and coordinate lift. Their
weighted square converges to the exact optimizer energy increment. -/
noncomputable section
namespace SharpWasserstein.ExternalInteractionEnergyLimit
open MeasureTheory Filter WeightedTangent WeightedMarginal WeightedDensity
open PeriodicIntegrationByParts PeriodicBochner PeriodicFourierTests PeriodicGalerkin
open PeriodicGradientClosure PeriodicSmoothGradient PeriodicOptimizerProducts
open PeriodicMarginalLift PeriodicMarginalEnergy PeriodicConvolution
open scoped Topology InnerProductSpace ContDiff BoundedContinuousFunction
variable {n k : ℕ}
  [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  [MeasurableSpace (Point (n+k))] [BorelSpace (Point (n+k))]
  (κ : ℝ) (μ : Measure (Coordinates (n+k))) [IsProbabilityMeasure μ]
  (ℓ : gradientClosure (cubePoint (n := n+k)) →L[ℝ] ℝ)

local instance marginal_probability : IsProbabilityMeasure (μ.map (prefixCoords n k)) :=
  Measure.isProbabilityMeasure_map (prefix_continuous n k).measurable.aemeasurable

/-- The actual full optimizer minus the lifted finite-dimensional marginal optimizer. -/
def galerkinResidual (s : Finset ((Fin n → ℤ) × Bool)) :
    gradientClosure (cubePoint (n := n+k)) :=
  (optimizer (densityBCF κ μ) ℓ : gradientClosure (cubePoint (n := n+k)))-
    gradientLift (m := k) (vector (densityBCF κ (μ.map (prefixCoords n k))) (marginalFunctional ℓ) s)

/-- The actual full optimizer minus the lifted limiting marginal optimizer. -/
def optimizerResidual : gradientClosure (cubePoint (n := n+k)) :=
  (optimizer (densityBCF κ μ) ℓ : gradientClosure (cubePoint (n := n+k)))-
    gradientLift (m := k) (optimizer (densityBCF κ (μ.map (prefixCoords n k))) (marginalFunctional ℓ) :
      gradientClosure (cubePoint (n := n)))

/-- The real Galerkin fluctuation converges strongly in the actual full cube `L²`. -/
theorem galerkinResidual_tendsto :
    Tendsto (galerkinResidual κ μ ℓ) atTop (𝓝 (optimizerResidual κ μ ℓ)) := by
  apply tendsto_const_nhds.sub
  exact (gradientLift (n := n) (m := k)).continuous.continuousAt.tendsto.comp
    (vector_tendsto (densityBCF κ (μ.map (prefixCoords n k))) (marginalFunctional ℓ)
      (densityBCF_positive_lower κ n (μ.map (prefixCoords n k)))
      (Eventually.of_forall (densityBCF_lower κ (μ.map (prefixCoords n k)))))

/-- The density-weighted norm convergence is a consequence of bounded actual
multiplication by the convolution density, not a norm-convergence premise. -/
theorem galerkinResidual_weighted_square_tendsto :
    Tendsto (fun s => ∫ y, densityBCF κ μ y*
      ‖(galerkinResidual κ μ ℓ s : Lp (Point (n+k)) 2 cubePoint) y‖^2 ∂cubePoint) atTop
      (𝓝 (∫ y, densityBCF κ μ y*
        ‖(optimizerResidual κ μ ℓ : Lp (Point (n+k)) 2 cubePoint) y‖^2 ∂cubePoint)) := by
  have hv := galerkinResidual_tendsto κ μ ℓ
  have hh := ((weightedOperator cubePoint (densityBCF κ μ)).continuous.continuousAt.tendsto.comp hv).inner
    (𝕜 := ℝ) hv
  simpa only [Function.comp_apply,weightedOperator_inner,real_inner_self_eq_norm_sq] using hh

/-- The actual Galerkin fluctuation energy tends to the exact energy increment
of the two genuine convolved-law optimizers. -/
theorem galerkinResidual_energy_increment_tendsto :
    Tendsto (fun s => ∫ y, densityBCF κ μ y*
      ‖(galerkinResidual κ μ ℓ s : Lp (Point (n+k)) 2 cubePoint) y‖^2 ∂cubePoint) atTop
      (𝓝 (ℓ (optimizer (densityBCF κ μ) ℓ)-
        marginalFunctional ℓ (optimizer (densityBCF κ (μ.map (prefixCoords n k))) (marginalFunctional ℓ)))) := by
  have hh := galerkinResidual_weighted_square_tendsto κ μ ℓ
  have he := optimizer_energy_increment_integral κ μ ℓ
  dsimp only at he
  simpa only [optimizerResidual,he] using hh

/-- Almost-everywhere identification with the literal full-minus-lifted fields. -/
theorem galerkinResidual_ae (s : Finset ((Fin n → ℤ) × Bool)) :
    (galerkinResidual κ μ ℓ s : Lp (Point (n+k)) 2 cubePoint) =ᵐ[cubePoint]
      (fun y => ((optimizer (densityBCF κ μ) ℓ : gradientClosure (cubePoint (n := n+k))) :
        Lp (Point (n+k)) 2 cubePoint) y-
        prefixEmbedding n k
          ((vector (densityBCF κ (μ.map (prefixCoords n k))) (marginalFunctional ℓ) s :
            Lp (Point n) 2 cubePoint) (prefixProjection n k y))) := by
  filter_upwards [Lp.coeFn_sub
      ((optimizer (densityBCF κ μ) ℓ : gradientClosure (cubePoint (n := n+k))) : Lp (Point (n+k)) 2 cubePoint)
      ((gradientLift (m := k) (vector (densityBCF κ (μ.map (prefixCoords n k))) (marginalFunctional ℓ) s) :
        gradientClosure (cubePoint (n := n+k))) : Lp (Point (n+k)) 2 cubePoint),
    liftLinear_ae (m := k)
      (vector (densityBCF κ (μ.map (prefixCoords n k))) (marginalFunctional ℓ) s : Lp (Point n) 2 cubePoint)]
      with y hy hz
  exact hy.trans (congrArg (fun v =>
    ((optimizer (densityBCF κ μ) ℓ : gradientClosure (cubePoint (n := n+k))) : Lp (Point (n+k)) 2 cubePoint) y-v) hz)

/-- The exact increment limit written entirely as genuine density-weighted
squares of the actual field difference. -/
theorem literal_galerkin_fluctuation_energy_tendsto :
    Tendsto (fun s => ∫ y, densityBCF κ μ y*
      ‖((optimizer (densityBCF κ μ) ℓ : gradientClosure (cubePoint (n := n+k))) :
        Lp (Point (n+k)) 2 cubePoint) y-
        prefixEmbedding n k
          ((vector (densityBCF κ (μ.map (prefixCoords n k))) (marginalFunctional ℓ) s :
            Lp (Point n) 2 cubePoint) (prefixProjection n k y))‖^2 ∂cubePoint) atTop
      (𝓝 (ℓ (optimizer (densityBCF κ μ) ℓ)-
        marginalFunctional ℓ (optimizer (densityBCF κ (μ.map (prefixCoords n k))) (marginalFunctional ℓ)))) := by
  apply (galerkinResidual_energy_increment_tendsto κ μ ℓ).congr'
  exact Eventually.of_forall (fun s => integral_congr_ae ((galerkinResidual_ae κ μ ℓ s).mono
    (fun y hy => by dsimp only at hy ⊢; rw [hy])))

end SharpWasserstein.ExternalInteractionEnergyLimit
