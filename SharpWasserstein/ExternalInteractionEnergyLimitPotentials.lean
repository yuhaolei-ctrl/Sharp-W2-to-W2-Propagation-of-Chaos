import SharpWasserstein.ExternalInteractionEnergyLimitWeighted

/-! The actual smooth marginal Galerkin potentials realize the convergent
periodic tangent fields and fluctuation energies under the full convolved law. -/
noncomputable section
namespace SharpWasserstein.ExternalInteractionEnergyLimit
open MeasureTheory Filter WeightedTangent WeightedMarginal WeightedDensity
open PeriodicIntegrationByParts PeriodicBochner PeriodicFourierTests PeriodicGalerkin
open PeriodicGradientClosure PeriodicSmoothGradient PeriodicOptimizerProducts
open PeriodicMarginalLift PeriodicMarginalEnergy PeriodicConvolution
open scoped Topology InnerProductSpace ContDiff BoundedContinuousFunction
variable {n k : ℕ}
  [MeasurableSpace (Point n)] [BorelSpace (Point n)]

/-- The periodic Hilbert field is the genuine smooth gradient almost everywhere. -/
theorem gradientVector_field_ae (f : Coordinates n → ℝ) (hf : ContDiff ℝ ∞ f) :
    (gradientVector f hf : Lp (Point n) 2 cubePoint) =ᵐ[cubePoint] gradient (pullback f) := by
  filter_upwards [testGradient_ae cubePoint (compactTest f hf),cubePoint_ae_mem (n := n)] with y hy hc
  have hh := compactTest_gradient_on_cube f hf hc
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hh
  change testGradient cubePoint (compactTest f hf) y = gradient (pullback f) y
  exact hy.trans hh

variable [MeasurableSpace (Point (n+k))] [BorelSpace (Point (n+k))]
  (κ : ℝ) (μ : Measure (Coordinates (n+k))) [IsProbabilityMeasure μ]
  (ℓ : gradientClosure (cubePoint (n := n+k)) →L[ℝ] ℝ)

local instance potential_marginal_probability : IsProbabilityMeasure (μ.map (prefixCoords n k)) :=
  Measure.isProbabilityMeasure_map (prefix_continuous n k).measurable.aemeasurable

/-- The genuine Euclidean potential selected by the lower-dimensional Fourier solve. -/
def marginalPotential (s : Finset ((Fin n → ℤ) × Bool)) : Point n → ℝ :=
  pullback (potential (densityBCF κ (μ.map (prefixCoords n k))) (marginalFunctional ℓ) s).val

theorem marginalPotential_smooth (s : Finset ((Fin n → ℤ) × Bool)) :
    ContDiff ℝ ∞ (marginalPotential κ μ ℓ s) :=
  (frequencySpace_properties s
    (potential (densityBCF κ (μ.map (prefixCoords n k))) (marginalFunctional ℓ) s).property).1.comp
    (coordinateEquiv n).contDiff

/-- The actual finite marginal gradient is its solved Hilbert vector. -/
theorem marginalPotential_gradient_ae (s : Finset ((Fin n → ℤ) × Bool)) :
    (vector (densityBCF κ (μ.map (prefixCoords n k))) (marginalFunctional ℓ) s :
      Lp (Point n) 2 cubePoint) =ᵐ[cubePoint] gradient (marginalPotential κ μ ℓ s) := by
  let f := potential (densityBCF κ (μ.map (prefixCoords n k))) (marginalFunctional ℓ) s
  have hf := (frequencySpace_properties s f.property).1
  rw [← gradient_potential]
  change (gradientVector f.val hf : Lp (Point n) 2 cubePoint) =ᵐ[cubePoint] gradient (pullback f.val)
  exact gradientVector_field_ae f.val hf

/-- The same identity holds at actual visible coordinates of the full cube. -/
theorem marginalPotential_prefix_gradient_ae (s : Finset ((Fin n → ℤ) × Bool)) :
    (fun y : Point (n+k) =>
      (vector (densityBCF κ (μ.map (prefixCoords n k))) (marginalFunctional ℓ) s :
        Lp (Point n) 2 cubePoint) (prefixProjection n k y)) =ᵐ[cubePoint]
      (fun y => gradient (marginalPotential κ μ ℓ s) (prefixProjection n k y)) := by
  have hh : ∀ᵐ y ∂(cubePoint (n := n+k)).map (prefixProjection n k),
      (vector (densityBCF κ (μ.map (prefixCoords n k))) (marginalFunctional ℓ) s :
        Lp (Point n) 2 cubePoint) y = gradient (marginalPotential κ μ ℓ s) y := by
    rw [cubePoint_prefix_map]
    exact marginalPotential_gradient_ae κ μ ℓ s
  exact ae_of_ae_map (prefixProjection n k).continuous.measurable.aemeasurable hh

/-- The strong Galerkin residual is literally the smooth-potential fluctuation. -/
theorem galerkinResidual_potential_ae (s : Finset ((Fin n → ℤ) × Bool)) :
    (galerkinResidual κ μ ℓ s : Lp (Point (n+k)) 2 cubePoint) =ᵐ[cubePoint]
      (fun y => ((optimizer (densityBCF κ μ) ℓ : gradientClosure (cubePoint (n := n+k))) :
        Lp (Point (n+k)) 2 cubePoint) y-
        prefixEmbedding n k (gradient (marginalPotential κ μ ℓ s) (prefixProjection n k y))) := by
  filter_upwards [galerkinResidual_ae κ μ ℓ s,marginalPotential_prefix_gradient_ae κ μ ℓ s] with y hy hz
  rw [hy,hz]

/-- The actual smooth-potential fluctuation energies converge to the true
optimizer energy increment, without a Hessian convergence assumption. -/
theorem potential_fluctuation_energy_tendsto :
    Tendsto (fun s => ∫ y,densityBCF κ μ y*
      ‖((optimizer (densityBCF κ μ) ℓ : gradientClosure (cubePoint (n := n+k))) :
        Lp (Point (n+k)) 2 cubePoint) y-
        prefixEmbedding n k (gradient (marginalPotential κ μ ℓ s) (prefixProjection n k y))‖^2 ∂cubePoint)
      atTop (𝓝 (ℓ (optimizer (densityBCF κ μ) ℓ)-
        marginalFunctional ℓ (optimizer (densityBCF κ (μ.map (prefixCoords n k))) (marginalFunctional ℓ)))) := by
  apply (galerkinResidual_energy_increment_tendsto κ μ ℓ).congr'
  exact Eventually.of_forall (fun s => integral_congr_ae ((galerkinResidual_potential_ae κ μ ℓ s).mono
    (fun y hy => by dsimp only at hy ⊢; rw [hy])))

/-- The actual marginal gradient energy, integrated against the full density,
converges to the genuine lower-dimensional optimizer energy. -/
theorem potential_marginal_energy_tendsto :
    Tendsto (fun s => ∫ y,densityBCF κ μ y*
      ‖gradient (marginalPotential κ μ ℓ s) (prefixProjection n k y)‖^2 ∂cubePoint)
      atTop (𝓝 (marginalFunctional ℓ
        (optimizer (densityBCF κ (μ.map (prefixCoords n k))) (marginalFunctional ℓ)))) := by
  let ρ := densityBCF κ (μ.map (prefixCoords n k))
  let ℓm := marginalFunctional ℓ
  have hp : ∀ᵐ y ∂cubePoint, (Real.exp (-|κ|)/PeriodicPositiveKernel.normalizer κ)^n ≤ ρ y :=
    Eventually.of_forall (densityBCF_lower κ (μ.map (prefixCoords n k)))
  have ha := densityBCF_positive_lower κ n (μ.map (prefixCoords n k))
  have hv := vector_tendsto ρ ℓm ha hp
  have hh := ((weightedOperator cubePoint ρ).continuous.continuousAt.tendsto.comp hv).inner (𝕜 := ℝ) hv
  rw [optimizer_equation ρ ℓm ha hp] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro s
  dsimp only [Function.comp_apply,ρ]
  rw [← densityPairing_lift κ μ,weightedOperator_inner]
  apply integral_congr_ae
  filter_upwards [liftLinear_ae (m := k) (vector ρ ℓm s : Lp (Point n) 2 cubePoint),
    marginalPotential_prefix_gradient_ae κ μ ℓ s] with y hy hz
  change densityBCF κ μ y*⟪liftLinear (m := k) (vector ρ ℓm s : Lp (Point n) 2 cubePoint) y,
    liftLinear (m := k) (vector ρ ℓm s : Lp (Point n) 2 cubePoint) y⟫_ℝ = _
  rw [hy,hz,real_inner_self_eq_norm_sq,LinearIsometry.norm_map]

/-- Prefix integration against the actual full convolution density is exactly
integration against its genuine convolved marginal density. -/
theorem integral_densityBCF_prefix (F : Point n → ℝ) (hF : Continuous F) :
    (∫ y,densityBCF κ μ y*F (prefixProjection n k y) ∂cubePoint) =
      ∫ y,densityBCF κ (μ.map (prefixCoords n k)) y*F y ∂cubePoint := by
  rw [integral_densityBCF κ μ,integral_densityBCF κ (μ.map (prefixCoords n k))]
  change (∫ x,(F ∘ (coordinateEquiv n).symm) (prefixCoords n k x) ∂smoothLaw κ μ) = _
  rw [← smoothLaw_prefix κ μ]
  exact (integral_map (prefix_continuous n k).measurable.aemeasurable
    (hF.comp (coordinateEquiv n).symm.continuous).aestronglyMeasurable).symm

end SharpWasserstein.ExternalInteractionEnergyLimit
