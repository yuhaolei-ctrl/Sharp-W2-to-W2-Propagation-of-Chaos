module

public import SharpWasserstein.Compat
public import SharpWasserstein.BrownianSourceInitialFlux

@[expose] public section

/-! The bounded initial drift defect used by the switch derivative is exactly
the initial source for the sharp propagated hierarchy. Its actual field is
permutation covariant; no canonical-field propagation identity is needed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff InnerProductSpace
namespace SharpWasserstein.InitialSourcePermutation
open WeightedTangent PropagatedSourcePermutation PropagatedSourceEquation NoiseAverage
variable {d N : ℕ}

theorem euclidean_initialCurrent_covariant (b : Position d → Position d → Position d)
    (q : Measure (Position d)) (e : Equiv.Perm (Fin N)) (y : Point (N*d)) :
    euclideanFlux (initialCurrent b q) (euclideanPermutation e y) =
      euclideanPermutation e (euclideanFlux (initialCurrent b q) y) := by
  obtain ⟨x,rfl⟩ := (configurationEuclidean d N).surjective y
  simp [euclideanFlux,initialCurrent_covariant]

variable [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Position d → Position d → Position d} {M' K' : ℝ≥0}
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) (particleDrift b))))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) (particleDrift b) y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) (particleDrift b)))
  {T : ℝ} (hT : 0 ≤ T) (hbs : BoundedSmoothKernel b)
  (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
  (q : Measure (Position d))

/-- Genuine full generator-source identification at time zero, in the actual
Euclidean coordinates used by the coefficient energy calculation. -/
theorem current_sourceAt_zero (σ : ConfigurationTest d N →ₗ[ℝ] ℝ)
    (hσ : ∀ φ : ConfigurationTest d N,σ φ = ∫ x,
      generator (fun z i => nonlinearDrift b q (z i)) φ.val x -
        generator (particleDrift b) φ.val x ∂μ)
    (hu : MemLp (euclideanFlux (initialCurrent b q)) 2 (euclideanLaw μ)) :
    Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs) (particleDrift_allDerivativesBounded hbs)
      (euclideanLaw μ) (euclideanFlux (initialCurrent b q)) hu 0 = euclideanDistribution σ := by
  apply Brownian.sourceAt_zero_of_divergence
  intro φ
  rw [InitialSourceMarginal.source_eq_configurationFlux μ q b σ hσ hu,
    euclideanDistribution_configurationFluxFunctional,fluxFunctional_apply]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx]

end SharpWasserstein.InitialSourcePermutation
