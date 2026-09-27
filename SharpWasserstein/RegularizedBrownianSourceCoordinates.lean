import SharpWasserstein.InitialSourceMarginalRegularized
import SharpWasserstein.BrownianPeriodicHierarchyInitial
import SharpWasserstein.InitialCurrentBrownianSource

/-! Exact coordinate conversion of the one-source regularized initial profile.
The source sign is the actual reference-minus-particle current, and every
level is a marginal of that same distribution. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal
namespace SharpWasserstein.RegularizedBrownianSource
open WeightedTangent InitialSourceMarginal InitialSourcePermutation
open BrownianPeriodicHierarchy PeriodicParticleTangentLimit

/-- Equality of carrying measures preserves the actual variational energy. -/
theorem energy_measure_congr {n : ℕ} (ν τ : Measure (Point n))
    [IsFiniteMeasure ν] [IsFiniteMeasure τ] (h : ν=τ) (σ : Test n →ₗ[ℝ] ℝ) :
    energy ν σ = energy τ σ := by
  subst τ
  rfl

/-- The Euclidean total level family has exactly the configuration marginal
energy already controlled by entropy regularization. -/
theorem levelEnergy_eq_configurationMarginal {d N m : ℕ} (hm : m ≤ N)
    (R : Measure (Configuration d N)) [IsFiniteMeasure R]
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) :
    energy (levelLaw d N (euclideanLaw R) m)
      (levelSource d N (euclideanLaw R) (euclideanDistribution σ) m) =
    configurationTangentEnergy (marginal hm R) (configurationMarginalSource hm R σ) := by
  letI : IsFiniteMeasure (marginal hm R) := Measure.isFiniteMeasure_map _ _
  have hh := congrArg (fun A : Point (N*d) →L[ℝ] Point (m*d) =>
    energy ((euclideanLaw R).map A) (imageSource (euclideanLaw R) (euclideanDistribution σ) A))
    (levelProjection_eq hm)
  calc
    _ = energy ((euclideanLaw R).map (marginalProjection hm))
        (imageSource (euclideanLaw R) (euclideanDistribution σ) (marginalProjection hm)) := hh
    _ = _ := by
      rw [configurationTangentEnergy_eq,euclideanDistribution_configurationMarginalSource]
      exact energy_measure_congr _ _ (map_marginalProjection hm R) _

/-- Actual Euclidean divergence pairing, with no replacement of the current
by a different propagated canonical field. -/
theorem initialCurrent_distribution_pairing {d N : ℕ}
    (R : Measure (Configuration d N)) [IsFiniteMeasure R]
    (q : Measure (Position d)) (b : Position d → Position d → Position d)
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ)
    (hσ : ∀ φ : ConfigurationTest d N,σ φ = ∫ x,
      generator (fun z i => nonlinearDrift b q (z i)) φ.val x-
        generator (particleDrift b) φ.val x ∂R)
    (hu : MemLp (euclideanFlux (initialCurrent b q)) 2 (euclideanLaw R)) (φ : Test (N*d)) :
    euclideanDistribution σ φ = ∫ x,⟪gradient φ.val x,euclideanFlux (initialCurrent b q) x⟫_ℝ
      ∂euclideanLaw R := by
  rw [source_eq_configurationFlux R q b σ hσ hu,
    euclideanDistribution_configurationFluxFunctional,fluxFunctional_apply]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx]

end SharpWasserstein.RegularizedBrownianSource
