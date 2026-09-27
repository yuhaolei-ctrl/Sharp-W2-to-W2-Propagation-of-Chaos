import SharpWasserstein.PeriodicParticleTangentLimitPairing
import SharpWasserstein.PeriodicParticleTangentLimitLaw

/-! Actual particle-coordinate marginals of the JV carrying laws and sources.
The projection contracts the full Euclidean norm, and the original quadratic
Wasserstein marginal limit identifies the limiting carrying measure. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology
namespace SharpWasserstein.PeriodicParticleTangentLimit
open WeightedTangent PropagatedSourceEquation

/-- The exact particle-coordinate restriction as a continuous linear map. -/
def configurationRestriction {d k N : ℕ} (hk : k ≤ N) : Configuration d N →L[ℝ] Configuration d k :=
  ContinuousLinearMap.pi fun i : Fin k => ContinuousLinearMap.proj (Fin.castLE hk i)

/-- The genuine coordinate marginal projection in Euclidean coordinates. -/
def marginalProjection {d k N : ℕ} (hk : k ≤ N) : Point (N*d) →L[ℝ] Point (k*d) :=
  (configurationEuclidean d k).toContinuousLinearMap.comp
    ((configurationRestriction (d := d) hk).comp (configurationEuclidean d N).symm.toContinuousLinearMap)

theorem marginalProjection_coordinates {d k N : ℕ} (hk : k ≤ N) (x : Configuration d N) :
    marginalProjection hk (configurationEuclidean d N x) =
      configurationEuclidean d k (restrictCoordinates hk x) := by
  simp only [marginalProjection,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- Marginalization has operator norm at most one in the true Euclidean norm. -/
theorem marginalProjection_norm_le_one {d k N : ℕ} (hk : k ≤ N) :
    ‖marginalProjection (d := d) hk‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  obtain ⟨x,rfl⟩ := (configurationEuclidean d N).surjective y
  rw [marginalProjection_coordinates,one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hh := productCost_restrict_le hk x 0
  have hz : restrictCoordinates (d := d) hk (0 : Configuration d N) = 0 := rfl
  simpa only [hz,productCost_eq_configurationEuclidean_dist_sq,map_zero,sub_zero] using hh

variable {d k N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point (k*d))] [BorelSpace (Point (k*d))]
  {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) {T : ℝ} (hT : 0 ≤ T)
  (hk : k ≤ N)

/-- The source carrying law is literally the manuscript's k-particle marginal. -/
theorem marginalLaw_eq_map_particleMarginal
    (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (ξ : Measure C(Icc 0 T,Configuration d N)) [IsProbabilityMeasure ξ]
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    law hN hb hbound hM hL₁ hL₂ hT (ξ.map (equivPath (configurationEuclidean d N)))
      (μ.map (configurationEuclidean d N)) (marginalProjection hk) (t := t) =
      (marginal hk (ParticleFlow.law hN hb hbound hM hL₁ hL₂ hT μ ξ t)).map (configurationEuclidean d k) := by
  rw [law_eq_map_particleLaw hN hb hbound hM hL₁ hL₂ hT μ ξ _ ht,
    marginal,Measure.map_map (configurationEuclidean d k).continuous.measurable (measurable_restrictCoordinates hk)]
  congr 1
  funext x
  exact marginalProjection_coordinates hk x

/-- Exact inverse-coordinate identification for the marginal carrying law. -/
theorem marginalLaw_map_symm_eq_particleMarginal
    (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (ξ : Measure C(Icc 0 T,Configuration d N)) [IsProbabilityMeasure ξ]
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (law hN hb hbound hM hL₁ hL₂ hT (ξ.map (equivPath (configurationEuclidean d N)))
      (μ.map (configurationEuclidean d N)) (marginalProjection hk) (t := t)).map
      (configurationEuclidean d k).symm = marginal hk (ParticleFlow.law hN hb hbound hM hL₁ hL₂ hT μ ξ t) := by
  rw [marginalLaw_eq_map_particleMarginal hN hb hbound hM hL₁ hL₂ hT hk μ ξ ht,
    Measure.map_map (configurationEuclidean d k).symm.continuous.measurable
      (configurationEuclidean d k).continuous.measurable]
  simp only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply]
  change Measure.map id (marginal hk (ParticleFlow.law hN hb hbound hM hL₁ hL₂ hT μ ξ t)) = _
  exact Measure.map_id

/-- The carrying marginals have the genuine existing quadratic transport limit. -/
theorem marginalCarryingLaw_wassersteinSq_tendsto
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (ξ : Measure C(Icc 0 T,Configuration d N)) [IsProbabilityMeasure ξ]
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => wassersteinSq
      ((law hN (PeriodicParticle.interaction_smooth hb n)
        (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT
          (ξ.map (equivPath (configurationEuclidean d N))) (μ.map (configurationEuclidean d N))
          (marginalProjection hk) (t := t)).map (configurationEuclidean d k).symm)
      ((law hN hb hbound hM hL₁ hL₂ hT (ξ.map (equivPath (configurationEuclidean d N)))
        (μ.map (configurationEuclidean d N)) (marginalProjection hk) (t := t)).map
          (configurationEuclidean d k).symm)) atTop (𝓝 0) := by
  simp_rw [marginalLaw_map_symm_eq_particleMarginal _ _ _ _ _ _ _ hk μ ξ ht]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (PeriodicParticle.law_wassersteinSq_tendsto hN hb hbound hM hL₁ hL₂ hT μ ξ ht)
  · intro n
    exact bot_le
  · intro n
    exact wassersteinSq_marginal_le hk _ _

/-- Every compact marginal-test source pairing converges for the actual
periodized flows under the original finite-energy initial field. -/
theorem marginalSource_tendsto
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    (ξ : Measure C(Icc 0 T,Point (N*d))) [IsProbabilityMeasure ξ]
    (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (φ : Test (k*d)) :
    Tendsto (fun n => source hN (PeriodicParticle.interaction_smooth hb n)
      (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT ξ μ (marginalProjection hk) ht u hu φ)
      atTop (𝓝 (source hN hb hbound hM hL₁ hL₂ hT ξ μ (marginalProjection hk) ht u hu φ)) :=
  source_tendsto hN hb hbound hM hL₁ hL₂ hT ξ μ (marginalProjection hk) ht u hu φ

/-- A separately established uniform marginal energy bound passes to the
actual unperiodized source, after the two genuine convergence proofs. -/
theorem marginalEnergy_bound_of_periodic_bounds
    (μ : Measure (Point (N*d))) [IsProbabilityMeasure μ]
    (ξ : Measure C(Icc 0 T,Point (N*d))) [IsProbabilityMeasure ξ]
    (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ) {t : ℝ} (ht : t ∈ Icc 0 T) {C : ℝ}
    (hC : ∀ᶠ n in atTop,
      energy (law hN (PeriodicParticle.interaction_smooth hb n)
        (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT ξ μ (marginalProjection hk) (t := t))
        (source hN (PeriodicParticle.interaction_smooth hb n)
          (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT ξ μ (marginalProjection hk) ht u hu) ≤ C) :
    FiniteEnergy (law hN hb hbound hM hL₁ hL₂ hT ξ μ (marginalProjection hk) (t := t))
      (source hN hb hbound hM hL₁ hL₂ hT ξ μ (marginalProjection hk) ht u hu) ∧
    energy (law hN hb hbound hM hL₁ hL₂ hT ξ μ (marginalProjection hk) (t := t))
      (source hN hb hbound hM hL₁ hL₂ hT ξ μ (marginalProjection hk) ht u hu) ≤ C :=
  energy_bound_of_periodic_bounds hN hb hbound hM hL₁ hL₂ hT ξ μ (marginalProjection hk) ht u hu hC

/-- Brownian specialization under the original configuration law; the source
uses the actually constructed independent Brownian paths. -/
theorem brownianMarginalSource_tendsto
    (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 (μ.map (configurationEuclidean d N)))
    {t : ℝ} (ht : t ∈ Icc 0 T) (φ : Test (k*d)) :
    Tendsto (fun n => source hN (PeriodicParticle.interaction_smooth hb n)
      (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT
      (euclideanBrownianPathLaw d N T) (μ.map (configurationEuclidean d N)) (marginalProjection hk) ht u hu φ)
      atTop (𝓝 (source hN hb hbound hM hL₁ hL₂ hT (euclideanBrownianPathLaw d N T)
        (μ.map (configurationEuclidean d N)) (marginalProjection hk) ht u hu φ)) :=
  marginalSource_tendsto hN hb hbound hM hL₁ hL₂ hT hk (μ.map (configurationEuclidean d N))
    (euclideanBrownianPathLaw d N T) u hu ht φ

end SharpWasserstein.PeriodicParticleTangentLimit
