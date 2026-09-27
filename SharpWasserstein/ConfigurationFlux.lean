import SharpWasserstein.ConfigurationEuclidean

/-! Actual configuration vector fluxes define weighted negative-Sobolev sources.
The norm used below is always the Euclidean coordinate square sum. -/

noncomputable section
namespace SharpWasserstein
open MeasureTheory Set
open scoped ENNReal BigOperators InnerProductSpace

variable {d N : ℕ} [MeasurableSpace (WeightedTangent.Point (N * d))]
  [BorelSpace (WeightedTangent.Point (N * d))]

/-- Transport a concrete configuration vector field to genuine Euclidean coordinates. -/
def euclideanFlux (v : Configuration d N → Configuration d N)
    (y : WeightedTangent.Point (N * d)) : WeightedTangent.Point (N * d) :=
  configurationEuclidean d N (v ((configurationEuclidean d N).symm y))

theorem measurable_euclideanFlux {v : Configuration d N → Configuration d N}
    (hv : Measurable v) : Measurable (euclideanFlux v) :=
  (configurationEuclidean d N).continuous.measurable.comp
    (hv.comp (configurationEuclidean d N).symm.continuous.measurable)

/-- Integrability of the actual Euclidean square gives the genuine weighted `L²` flux. -/
theorem memLp_euclideanFlux (μ : Measure (Configuration d N))
    {v : Configuration d N → Configuration d N} (hv : Measurable v)
    (hsq : Integrable (fun x => ∑ i, ∑ a, (v x i a) ^ 2) μ) :
    MemLp (euclideanFlux v) 2 (euclideanLaw μ) := by
  apply (memLp_map_measure_iff (measurable_euclideanFlux hv).aestronglyMeasurable
    (configurationEuclidean d N).continuous.measurable.aemeasurable).mpr
  apply (memLp_two_iff_integrable_sq_norm
    (((measurable_euclideanFlux hv).comp
      (configurationEuclidean d N).continuous.measurable).aestronglyMeasurable)).mpr
  simpa only [Function.comp_apply, euclideanFlux, ContinuousLinearEquiv.symm_apply_apply,
    configurationEuclidean_norm_sq] using hsq

variable (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]

/-- The source is constructed from the actual field, not postulated through a variational bound. -/
def configurationFluxFunctional (v : Configuration d N → Configuration d N)
    (hv : MemLp (euclideanFlux v) 2 (euclideanLaw μ)) : ConfigurationTest d N →ₗ[ℝ] ℝ :=
  (WeightedTangent.fluxFunctional (euclideanLaw μ) (hv.toLp (euclideanFlux v))).comp
    (configurationTestEuclidean d N).toLinearMap

/-- Exact weak divergence pairing in the original particle coordinates. -/
theorem configurationFluxFunctional_apply (v : Configuration d N → Configuration d N)
    (hv : MemLp (euclideanFlux v) 2 (euclideanLaw μ)) (φ : ConfigurationTest d N) :
    configurationFluxFunctional μ v hv φ =
      ∫ x, ∑ i, ∑ a, v x i a * coordinateDerivative φ.val i a x ∂μ := by
  change WeightedTangent.fluxFunctional (euclideanLaw μ) (hv.toLp (euclideanFlux v))
    (configurationTestEuclidean d N φ) = _
  rw [WeightedTangent.fluxFunctional_apply]
  calc
    _ = ∫ y, ⟪gradient (euclideanTest φ.val) y, euclideanFlux v y⟫_ℝ ∂euclideanLaw μ := by
      apply integral_congr_ae
      filter_upwards [hv.coeFn_toLp] with y hy
      rw [hy]
      rfl
    _ = ∫ x, ⟪gradient (euclideanTest φ.val) (configurationEuclidean d N x),
        configurationEuclidean d N (v x)⟫_ℝ ∂μ := by
      rw [integral_euclideanLaw]
      simp only [euclideanFlux, ContinuousLinearEquiv.symm_apply_apply]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [euclideanTest_gradient_pairing, fderiv_eq_sum_coordinateDerivative]

theorem euclideanDistribution_configurationFluxFunctional
    (v : Configuration d N → Configuration d N)
    (hv : MemLp (euclideanFlux v) 2 (euclideanLaw μ)) :
    euclideanDistribution (configurationFluxFunctional μ v hv) =
      WeightedTangent.fluxFunctional (euclideanLaw μ) (hv.toLp (euclideanFlux v)) := by
  ext φ
  simp only [euclideanDistribution, configurationFluxFunctional, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]

/-- Actual source existence and the minimum-energy bound for every square-integrable flux. -/
theorem configurationFluxFunctional_finiteEnergy_and_le
    (v : Configuration d N → Configuration d N)
    (hv : MemLp (euclideanFlux v) 2 (euclideanLaw μ)) :
    ConfigurationFiniteEnergy μ (configurationFluxFunctional μ v hv) ∧
    configurationTangentEnergy μ (configurationFluxFunctional μ v hv) ≤
      ∫ x, ∑ i, ∑ a, (v x i a) ^ 2 ∂μ := by
  rw [configurationFiniteEnergy_iff, configurationTangentEnergy_eq,
    euclideanDistribution_configurationFluxFunctional]
  refine ⟨WeightedTangent.finiteEnergy_of_divergence _ _ _
    (WeightedTangent.fluxFunctional_apply _ _), ?_⟩
  calc
    _ ≤ ∫ y, ‖(hv.toLp (euclideanFlux v)) y‖ ^ 2 ∂euclideanLaw μ :=
      WeightedTangent.energy_le_flux_integral _ _ _ (WeightedTangent.fluxFunctional_apply _ _)
    _ = ∫ y, ‖euclideanFlux v y‖ ^ 2 ∂euclideanLaw μ := by
      apply integral_congr_ae
      filter_upwards [hv.coeFn_toLp] with y hy
      rw [hy]
    _ = _ := by
      rw [integral_euclideanLaw]
      simp only [euclideanFlux, ContinuousLinearEquiv.symm_apply_apply,
        configurationEuclidean_norm_sq]

end SharpWasserstein
