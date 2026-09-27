import SharpWasserstein.InitialSourceMarginalPairing
import SharpWasserstein.InitialSourcePermutation
import SharpWasserstein.PeriodicParticleTangentLimitMarginal

/-! Particle-coordinate marginals of the actual full discrepancy source.
The source is defined by projecting its canonical tangent, and then identified
with the actual reference-minus-particle flux on cylinder tests. -/
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff BigOperators
namespace SharpWasserstein.InitialSourceMarginal
open WeightedTangent PeriodicParticleTangentLimit InitialSourcePermutation
variable {d k N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point (k*d))] [BorelSpace (Point (k*d))]

/-- The projected carrying law is the actual particle marginal. -/
theorem map_marginalProjection (hk : k ≤ N) (μ : Measure (Configuration d N)) :
    (euclideanLaw μ).map (marginalProjection hk) = euclideanLaw (marginal hk μ) := by
  unfold euclideanLaw marginal
  rw [Measure.map_map (marginalProjection hk).continuous.measurable
    (configurationEuclidean d N).continuous.measurable,
    Measure.map_map (configurationEuclidean d k).continuous.measurable
    (measurable_restrictCoordinates hk)]
  congr 1
  funext x
  exact marginalProjection_coordinates hk x

/-- One full source determines all its genuine particle marginal sources. -/
def configurationMarginalSource (hk : k ≤ N) (μ : Measure (Configuration d N))
    [IsFiniteMeasure μ] (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) : ConfigurationTest d k →ₗ[ℝ] ℝ :=
  (imageSource (euclideanLaw μ) (euclideanDistribution σ) (marginalProjection hk)).comp
    (configurationTestEuclidean d k).toLinearMap

theorem euclideanDistribution_configurationMarginalSource (hk : k ≤ N)
    (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) :
    euclideanDistribution (configurationMarginalSource hk μ σ) =
      imageSource (euclideanLaw μ) (euclideanDistribution σ) (marginalProjection hk) := by
  ext φ
  simp only [euclideanDistribution,configurationMarginalSource,LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap,LinearEquiv.apply_symm_apply]

theorem configurationMarginalSource_finite (hk : k ≤ N)
    (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) :
    ConfigurationFiniteEnergy (marginal hk μ) (configurationMarginalSource hk μ σ) := by
  rw [configurationFiniteEnergy_iff,euclideanDistribution_configurationMarginalSource,
    ← map_marginalProjection]
  exact imageSource_finite _ _ _

/-- The bounded actual discrepancy current is a genuine weighted L² field,
including its diagonal self-interaction term. -/
theorem initialCurrent_memLp (hN : 0 < N)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (q : Measure (Position d)) [IsProbabilityMeasure q]
    {b : Position d → Position d → Position d} {B : ℝ}
    (hb : Measurable (Function.uncurry b)) (hbnd : ∀ u w a,|b u w a| ≤ B) :
    MemLp (euclideanFlux (initialCurrent b q)) 2 (euclideanLaw μ) := by
  have he (x : Configuration d N) (i : Fin N) (a : Fin d) :
      initialCurrent b q x i a = -(N:ℝ)⁻¹ * internalScalarCurrent q (fun u w => b u w a) i x := by
    have hh := fullSourceCurrent_eq_internal hN q hb hbnd x i a
    change nonlinearDrift b q (x i) a - particleDrift b x i a = _
    linarith
  apply memLp_euclideanFlux μ
  · apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro a
    simp_rw [he]
    exact measurable_const.mul (measurable_internalScalarCurrent (r := q)
      (b := fun u w => b u w a) ((measurable_pi_apply a).comp hb) i)
  · simp_rw [he,mul_pow,← Finset.mul_sum]
    exact (integrable_finsetSum _ (fun i _ => integrable_internalCurrentSquare hb hbnd i μ)).const_mul _

/-- The full discrepancy distribution equals the actual current's flux
functional, with the manuscript's reference-minus-particle sign. -/
theorem source_eq_configurationFlux (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (q : Measure (Position d)) (b : Position d → Position d → Position d)
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ)
    (hσ : ∀ φ : ConfigurationTest d N,σ φ = ∫ x,
      generator (fun z i => nonlinearDrift b q (z i)) φ.val x -
        generator (particleDrift b) φ.val x ∂μ)
    (hv : MemLp (euclideanFlux (initialCurrent b q)) 2 (euclideanLaw μ)) :
    σ = configurationFluxFunctional μ (initialCurrent b q) hv := by
  ext φ
  rw [hσ,configurationFluxFunctional_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [generator_difference,fderiv_eq_sum_coordinateDerivative]

/-- Genuine marginal action is the cylinder differential of the actual full
current. The replacement of the canonical tangent is proved by cutoff density. -/
theorem configurationMarginalSource_apply_current (hk : k ≤ N)
    (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (q : Measure (Position d)) (b : Position d → Position d → Position d)
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ)
    (hσ : ∀ φ : ConfigurationTest d N,σ φ = ∫ x,
      generator (fun z i => nonlinearDrift b q (z i)) φ.val x -
        generator (particleDrift b) φ.val x ∂μ)
    (hv : MemLp (euclideanFlux (initialCurrent b q)) 2 (euclideanLaw μ))
    (φ : ConfigurationTest d k) :
    configurationMarginalSource hk μ σ φ = ∫ x,
      fderiv ℝ φ.val (restrictCoordinates hk x)
        (restrictCoordinates hk (initialCurrent b q x)) ∂μ := by
  have hflux := source_eq_configurationFlux μ q b σ hσ hv
  have hV (ψ : Test (N*d)) : euclideanDistribution σ ψ =
      ∫ y,⟪gradient ψ.val y,hv.toLp (euclideanFlux (initialCurrent b q)) y⟫_ℝ ∂euclideanLaw μ := by
    rw [hflux,euclideanDistribution_configurationFluxFunctional,fluxFunctional_apply]
  change imageSource _ _ _ (configurationTestEuclidean d k φ) = _
  rw [imageSource_eq_flux_pairing _ _ _ hV]
  calc
    _ = ∫ y,⟪gradient ((euclideanTest φ.val) ∘ marginalProjection hk) y,
        euclideanFlux (initialCurrent b q) y⟫_ℝ ∂euclideanLaw μ := by
      apply integral_congr_ae
      filter_upwards [hv.coeFn_toLp] with y hy
      rw [hy]
      rfl
    _ = _ := by
      rw [integral_euclideanLaw]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [inner_gradient_left,
        fderiv_comp _ (show DifferentiableAt ℝ (euclideanTest φ.val) _ from
          ((smoothCompactTest_euclidean φ.property).1.differentiable (by simp) _))
          (marginalProjection hk).differentiableAt,ContinuousLinearMap.fderiv]
      simp only [ContinuousLinearMap.comp_apply,euclideanFlux,
        ContinuousLinearEquiv.symm_apply_apply,marginalProjection_coordinates]
      rw [← inner_gradient_left,euclideanTest_gradient_pairing]

/-- The top-level genuine marginal is the original full source. -/
theorem configurationMarginalSource_self
    (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (q : Measure (Position d)) (b : Position d → Position d → Position d)
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ)
    (hσ : ∀ φ : ConfigurationTest d N,σ φ = ∫ x,
      generator (fun z i => nonlinearDrift b q (z i)) φ.val x -
        generator (particleDrift b) φ.val x ∂μ)
    (hv : MemLp (euclideanFlux (initialCurrent b q)) 2 (euclideanLaw μ)) :
    configurationMarginalSource (le_refl N) μ σ = σ := by
  ext φ
  rw [configurationMarginalSource_apply_current (le_refl N) μ q b σ hσ hv,hσ]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [generator_difference]
  rfl

end SharpWasserstein.InitialSourceMarginal
