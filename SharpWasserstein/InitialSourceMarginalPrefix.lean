import SharpWasserstein.InitialSourceMarginalComposition
import SharpWasserstein.InitialSourceMarginalConfiguration

/-! Exact identification with the existing prefix `marginalDistribution`.
Only the arithmetic dimension reindexing N*d = k*d+(N-k)*d is used; all
Euclidean norms and source signs are preserved. -/
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff
namespace SharpWasserstein.InitialSourceMarginal
open WeightedTangent WeightedMarginal PeriodicParticleTangentLimit

/-- Arithmetic reindexing only, preserving every flattened coordinate. -/
def dimensionReindex {d k N : ℕ} (hk : k ≤ N) :
    Point (N*d) ≃ₗᵢ[ℝ] Point (k*d+(N-k)*d) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    { toFun := Fin.cast (by rw [← Nat.add_mul,Nat.add_sub_of_le hk])
      invFun := Fin.cast (by rw [← Nat.add_mul,Nat.add_sub_of_le hk])
      left_inv := fun _ => by apply Fin.ext; rfl
      right_inv := fun _ => by apply Fin.ext; rfl }

theorem prefix_comp_dimensionReindex {d k N : ℕ} (hk : k ≤ N) :
    (prefixProjection (k*d) ((N-k)*d)).comp
      (dimensionReindex (d := d) hk).toContinuousLinearEquiv.toContinuousLinearMap =
      marginalProjection hk := by
  ext y j
  obtain ⟨x,rfl⟩ := (configurationEuclidean d N).surjective y
  rw [ContinuousLinearMap.comp_apply,marginalProjection_coordinates]
  obtain ⟨⟨i,a⟩,rfl⟩ := finProdFinEquiv.surjective j
  change configurationEuclidean d N x
      (Fin.cast (by rw [← Nat.add_mul,Nat.add_sub_of_le hk])
        ((finProdFinEquiv (i,a)).castAdd ((N-k)*d))) =
    configurationEuclidean d k (restrictCoordinates hk x) (finProdFinEquiv (i,a))
  have hi : Fin.cast (by rw [← Nat.add_mul,Nat.add_sub_of_le hk])
      ((finProdFinEquiv (i,a)).castAdd ((N-k)*d)) =
      finProdFinEquiv (Fin.castLE hk i,a) := by
    apply Fin.ext
    rfl
  rw [hi,configurationEuclidean_apply_coordinate,configurationEuclidean_apply_coordinate]
  rfl

/-- Literal standard-prefix marginal of the arithmetically reindexed full
source is the already constructed genuine configuration marginal. -/
theorem marginalDistribution_reindexed_eq {d k N : ℕ} (hk : k ≤ N)
    [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
    [MeasurableSpace (Point (k*d))] [BorelSpace (Point (k*d))]
    [MeasurableSpace (Point (k*d+(N-k)*d))] [BorelSpace (Point (k*d+(N-k)*d))]
    (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) :
    marginalDistribution
      ((euclideanLaw μ).map (dimensionReindex (d := d) hk))
      (imageSource (euclideanLaw μ) (euclideanDistribution σ)
        (dimensionReindex (d := d) hk).toContinuousLinearEquiv.toContinuousLinearMap) =
      euclideanDistribution (configurationMarginalSource hk μ σ) := by
  rw [← imageSource_prefix_eq]
  change imageSource
    ((euclideanLaw μ).map (dimensionReindex (d := d) hk).toContinuousLinearEquiv.toContinuousLinearMap)
    (imageSource (euclideanLaw μ) (euclideanDistribution σ)
      (dimensionReindex (d := d) hk).toContinuousLinearEquiv.toContinuousLinearMap)
    (prefixProjection (k*d) ((N-k)*d)) = _
  rw [imageSource_comp,prefix_comp_dimensionReindex,
    euclideanDistribution_configurationMarginalSource]

/-- The carrying measure in the standard-prefix identity is the actual
configuration marginal, with no product-law assumption. -/
theorem marginalLaw_reindexed_eq {d k N : ℕ} (hk : k ≤ N)
    [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
    [MeasurableSpace (Point (k*d))] [BorelSpace (Point (k*d))]
    [MeasurableSpace (Point (k*d+(N-k)*d))] [BorelSpace (Point (k*d+(N-k)*d))]
    (μ : Measure (Configuration d N)) :
    marginalLaw ((euclideanLaw μ).map (dimensionReindex (d := d) hk)) =
      euclideanLaw (marginal hk μ) := by
  unfold marginalLaw
  rw [Measure.map_map (prefixProjection (k*d) ((N-k)*d)).continuous.measurable
    (dimensionReindex (d := d) hk).continuous.measurable]
  change (euclideanLaw μ).map ((prefixProjection (k*d) ((N-k)*d)).comp
    (dimensionReindex (d := d) hk).toContinuousLinearEquiv.toContinuousLinearMap) = _
  rw [prefix_comp_dimensionReindex,map_marginalProjection]

/-- The actual weighted prefix energy is exactly the configuration marginal
energy used in the sharp source estimate. -/
theorem marginal_energy_reindexed_eq {d k N : ℕ} (hk : k ≤ N)
    [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
    [MeasurableSpace (Point (k*d))] [BorelSpace (Point (k*d))]
    [MeasurableSpace (Point (k*d+(N-k)*d))] [BorelSpace (Point (k*d+(N-k)*d))]
    (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) :
    energy (marginalLaw ((euclideanLaw μ).map (dimensionReindex (d := d) hk)))
      (marginalDistribution ((euclideanLaw μ).map (dimensionReindex (d := d) hk))
        (imageSource (euclideanLaw μ) (euclideanDistribution σ)
          (dimensionReindex (d := d) hk).toContinuousLinearEquiv.toContinuousLinearMap)) =
      configurationTangentEnergy (marginal hk μ) (configurationMarginalSource hk μ σ) := by
  rw [marginalLaw_reindexed_eq,marginalDistribution_reindexed_eq,configurationTangentEnergy_eq]

end SharpWasserstein.InitialSourceMarginal
