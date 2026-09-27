import SharpWasserstein.PeriodicParticleTangentLimitMarginal

/-! Identify the full random-flux source used for approximation with the
previously proved actual Brownian source evolution. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology
namespace SharpWasserstein.PeriodicParticleTangentLimit
open WeightedTangent PropagatedSourceEquation
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) {T : ℝ} (hT : 0 ≤ T)
  (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]

/-- The approximation's full source is exactly the constructed Brownian
source already proved to satisfy the homogeneous weak equation. -/
theorem fullSource_eq_brownianSourceAt
    (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    source hN hb hbound hM hL₁ hL₂ hT (euclideanBrownianPathLaw d N T) μ
      (ContinuousLinearMap.id ℝ (Point (N*d))) ht u hu =
    Brownian.sourceAt
      ((drift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
      (fun _ => drift_norm_le hN hbound hM) (fun _ => drift_lipschitz hN hb hbound hL₁ hL₂)
      hT (particleDrift_smooth hb) (particleDrift_allDerivativesBounded hb) μ u hu t := by
  ext φ
  rw [source_apply]
  simp only [Brownian.sourceAt,projIcc_of_mem _ ht,PropagatedFlux.Flow.source_apply,
    ContinuousLinearMap.id_apply]
  rfl

/-- Test convergence for the very Brownian source evolution used elsewhere
in the proof chain, with no replacement distribution. -/
theorem brownianSourceAt_tendsto
    (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ) {t : ℝ} (ht : t ∈ Icc 0 T) (φ : Test (N*d)) :
    Tendsto (fun n => Brownian.sourceAt
      ((drift_lipschitz hN (PeriodicParticle.interaction_smooth hb n)
        (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hL₁ hL₂).continuous.comp continuous_snd)
      (fun _ => drift_norm_le hN (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM)
      (fun _ => drift_lipschitz hN (PeriodicParticle.interaction_smooth hb n)
        (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hL₁ hL₂)
      hT (particleDrift_smooth (PeriodicParticle.interaction_smooth hb n))
      (particleDrift_allDerivativesBounded (PeriodicParticle.interaction_smooth hb n)) μ u hu t φ)
      atTop (𝓝 (Brownian.sourceAt
        ((drift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
        (fun _ => drift_norm_le hN hbound hM) (fun _ => drift_lipschitz hN hb hbound hL₁ hL₂)
        hT (particleDrift_smooth hb) (particleDrift_allDerivativesBounded hb) μ u hu t φ)) := by
  convert source_tendsto hN hb hbound hM hL₁ hL₂ hT (euclideanBrownianPathLaw d N T) μ
    (ContinuousLinearMap.id ℝ (Point (N*d))) ht u hu φ using 1
  · funext n
    exact congrArg (fun σ : Test (N*d) →ₗ[ℝ] ℝ => σ φ)
      (fullSource_eq_brownianSourceAt hN (PeriodicParticle.interaction_smooth hb n)
        (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT μ u hu ht).symm
  · exact congrArg (fun σ : Test (N*d) →ₗ[ℝ] ℝ => 𝓝 (σ φ))
      (fullSource_eq_brownianSourceAt hN hb hbound hM hL₁ hL₂ hT μ u hu ht).symm

end SharpWasserstein.PeriodicParticleTangentLimit
