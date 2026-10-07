module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicMarginalCoefficientEvolutionLaw
public import SharpWasserstein.InitialSourceMarginalComposition

@[expose] public section

/-! Exact consistency of the next-particle observation and the prefix source.
The current law, canonical source, periodic projection, and finite trial energy
therefore refer to one and the same genuine marginal. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.PeriodicMarginalCoefficientEvolution
open WeightedTangent WeightedMarginal PeriodicParticleTangentLimit ExternalInteractionSymmetry
variable {d m N : ℕ}

/-- Taking the prefix of the genuine next-particle observation is exactly
the original particle marginal projection. -/
theorem prefix_comp_observation (hm : m ≤ N) (j : Fin N) :
    (prefixProjection (m*d) d).comp (observation (d := d) hm j) = marginalProjection hm := by
  ext x k
  obtain ⟨z,rfl⟩ := (configurationEuclidean d N).surjective x
  exact congrArg (fun y : Point (m*d) => y k)
    ((observation_prefix hm j z).trans (marginalProjection_coordinates hm z).symm)

theorem prefix_observation (hm : m ≤ N) (j : Fin N) (x : Point (N*d)) :
    prefixProjection (m*d) d (observation hm j x) = marginalProjection hm x :=
  congrArg (fun L : Point (N*d) →L[ℝ] Point (m*d) => L x) (prefix_comp_observation hm j)

variable [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
  [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]

/-- Prefix of the true observed law, with no density or independence premise. -/
theorem marginalLaw_observation (hm : m ≤ N) (j : Fin N) (μ : Measure (Point (N*d))) :
    marginalLaw (μ.map (observation hm j)) = μ.map (marginalProjection hm) := by
  unfold marginalLaw
  rw [Measure.map_map (prefixProjection (m*d) d).continuous.measurable
    (observation hm j).continuous.measurable]
  change μ.map ((prefixProjection (m*d) d).comp (observation hm j)) = _
  rw [prefix_comp_observation]

/-- Canonical marginalization of the actual observed source equals the source
of the original projected flux. The intermediate representative is eliminated
by the proved bounded-cylinder cutoff pairing. -/
theorem marginalDistribution_observedSource (hm : m ≤ N) (j : Fin N)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ] (U : Lp (Point (N*d)) 2 μ) :
    marginalDistribution (μ.map (observation hm j)) (observedSource hm j μ U) =
      prefixSource hm μ U := by
  ext φ
  rw [marginalDistribution_integral]
  obtain ⟨hs,hA,hB⟩ := cylinder_test_smooth_bounded (m := d) φ
  have hi := randomSource_bounded_pairing μ (observation hm j) (observation hm j).continuous.measurable
    (observedVelocity hm j μ U) (φ.val ∘ prefixProjection (m*d) d) hs hA hB
  change (∫ z,⟪gradient (φ.val ∘ prefixProjection (m*d) d) (observation hm j z),
    observedVelocity hm j μ U z⟫_ℝ ∂μ) =
      ∫ y,⟪gradient (φ.val ∘ prefixProjection (m*d) d) y,
        (representative (μ.map (observation hm j)) (observedSource hm j μ U)).val y⟫_ℝ
        ∂μ.map (observation hm j) at hi
  rw [← hi,prefixSource,PropagatedFlux.source_apply]
  apply integral_congr_ae
  filter_upwards [observedVelocity_ae hm j μ U,(marginalProjection hm).coeFn_compLp U] with x hx hy
  rw [hx,ContinuousLinearMap.compLpₗ_apply,hy,
    gradient_comp_prefixProjection (test_differentiable φ),inner_prefixEmbedding,
    prefix_observation,prefix_observation]

omit [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))] in
/-- In the canonical full-source case, the observed distribution is exactly
the existing linear-image source API. -/
theorem observedSource_eq_imageSource (hm : m ≤ N) (j : Fin N)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ] (σ : Test (N*d) →ₗ[ℝ] ℝ) :
    observedSource hm j μ (representative μ σ).val =
      InitialSourceMarginal.imageSource μ σ (observation hm j) := rfl

omit [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))] in
theorem prefixSource_eq_imageSource (hm : m ≤ N)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ] (σ : Test (N*d) →ₗ[ℝ] ℝ) :
    prefixSource hm μ (representative μ σ).val =
      InitialSourceMarginal.imageSource μ σ (marginalProjection hm) := rfl

/-- The periodic marginal energy used by the true next-particle Pythagorean
identity is exactly the periodic energy appearing in the coefficient equation. -/
theorem periodic_marginalEnergy_observedSource (P : ℝ) (hm : m ≤ N) (j : Fin N)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ] (U : Lp (Point (N*d)) 2 μ) :
    WeightedPeriodicTangentPhysical.energy P (marginalLaw (μ.map (observation hm j)))
      (marginalDistribution (μ.map (observation hm j)) (observedSource hm j μ U)) =
    WeightedPeriodicTangentPhysical.energy P (μ.map (marginalProjection hm)) (prefixSource hm μ U) := by
  simp only [marginalDistribution_observedSource,marginalLaw_observation]

end SharpWasserstein.PeriodicMarginalCoefficientEvolution
