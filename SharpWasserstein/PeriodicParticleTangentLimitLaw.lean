import SharpWasserstein.PeriodicParticleTangentLimitSource

/-! The carrying laws of the projected JV sources are the actual particle
laws already used in the Wasserstein approximation theorem. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology
namespace SharpWasserstein.PeriodicParticleTangentLimit
open WeightedTangent PropagatedSourceEquation
variable {d N m : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point m)] [BorelSpace (Point m)]
  {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) {T : ℝ} (hT : 0 ≤ T)

omit [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))] in
/-- Exact selected-flow conjugacy, including the true Euclidean norm. -/
theorem flow_eq_particleSolution (x : Configuration d N) (w : C(Icc 0 T,Configuration d N))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    flow hN hb hbound hM hL₁ hL₂ hT (configurationEuclidean d N x)
      (equivPath (configurationEuclidean d N) w) t =
        configurationEuclidean d N (ParticleFlow.solution hN hb hbound hM hL₁ hL₂ hT x w t) := by
  exact flow_equiv (configurationEuclidean d N)
    (M := NNReal.mk M hM) ((particleDrift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (fun _ => particleDrift_norm_bound hN hbound hM) (fun _ => particleDrift_lipschitz hN hb hbound hL₁ hL₂)
    ((drift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (fun _ => drift_norm_le hN hbound hM) (fun _ => drift_lipschitz hN hb hbound hL₁ hL₂) hT x w ht

/-- The actual projected JV carrying law is the projected particle law. -/
theorem law_eq_map_particleLaw
    (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (ξ : Measure C(Icc 0 T,Configuration d N)) [IsProbabilityMeasure ξ]
    (A : Point (N*d) →L[ℝ] Point m) {t : ℝ} (ht : t ∈ Icc 0 T) :
    law hN hb hbound hM hL₁ hL₂ hT (ξ.map (equivPath (configurationEuclidean d N)))
      (μ.map (configurationEuclidean d N)) A (t := t) =
        (ParticleFlow.law hN hb hbound hM hL₁ hL₂ hT μ ξ t).map
          (fun x => A (configurationEuclidean d N x)) := by
  let L := configurationEuclidean d N
  have hL : Measurable L := L.continuous.measurable
  have hP := (equivPath_continuous (T := T) L).measurable
  have hAE : Measurable (fun q => A (endpoint hN hb hbound hM hL₁ hL₂ hT (t := t) q)) :=
    (A.continuous.comp (endpoint_continuous hN hb hbound hM hL₁ hL₂ hT ht)).measurable
  rw [law,Measure.map_prod_map μ ξ hL hP,Measure.map_map hAE (hL.prodMap hP)]
  have hAL : Measurable (fun x => A (configurationEuclidean d N x)) :=
    (A.continuous.comp L.continuous).measurable
  rw [ParticleFlow.law,randomMapLaw,Measure.map_map hAL
    (ParticleFlow.solution_measurable hN hb hbound hM hL₁ hL₂ hT ht)]
  congr 1
  funext p
  exact congrArg A (flow_eq_particleSolution hN hb hbound hM hL₁ hL₂ hT p.1 p.2 ht)

/-- In particular this is the genuine Brownian particle marginal law. -/
theorem law_eq_map_brownianLaw (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (A : Point (N*d) →L[ℝ] Point m) {t : ℝ} (ht : t ∈ Icc 0 T) :
    law hN hb hbound hM hL₁ hL₂ hT (euclideanBrownianPathLaw d N T)
      (μ.map (configurationEuclidean d N)) A (t := t) =
        (BrownianParticle.law hN hb hbound hM hL₁ hL₂ hT μ t).map
          (fun x => A (configurationEuclidean d N x)) :=
  law_eq_map_particleLaw hN hb hbound hM hL₁ hL₂ hT μ (BrownianNoise.configurationLaw d N T) A ht

/-- Undoing the exact Euclidean coordinates identifies the full carrying law
with the actual particle law used by the quadratic transport theorem. -/
theorem fullLaw_map_symm_eq_particleLaw
    (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (ξ : Measure C(Icc 0 T,Configuration d N)) [IsProbabilityMeasure ξ]
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (law hN hb hbound hM hL₁ hL₂ hT (ξ.map (equivPath (configurationEuclidean d N)))
      (μ.map (configurationEuclidean d N)) (ContinuousLinearMap.id ℝ (Point (N*d))) (t := t)).map
      (configurationEuclidean d N).symm = ParticleFlow.law hN hb hbound hM hL₁ hL₂ hT μ ξ t := by
  rw [law_eq_map_particleLaw hN hb hbound hM hL₁ hL₂ hT μ ξ _ ht]
  simp only [ContinuousLinearMap.id_apply]
  rw [Measure.map_map (configurationEuclidean d N).symm.continuous.measurable
      (configurationEuclidean d N).continuous.measurable]
  simp only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply]
  change Measure.map id (ParticleFlow.law hN hb hbound hM hL₁ hL₂ hT μ ξ t) = _
  exact Measure.map_id

/-- The identified full carrying laws satisfy the previously proved actual
quadratic Wasserstein limit in the manuscript's configuration cost. -/
theorem carryingLaw_wassersteinSq_tendsto
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (ξ : Measure C(Icc 0 T,Configuration d N)) [IsProbabilityMeasure ξ]
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => wassersteinSq
      ((law hN (PeriodicParticle.interaction_smooth hb n)
        (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT
          (ξ.map (equivPath (configurationEuclidean d N))) (μ.map (configurationEuclidean d N))
          (ContinuousLinearMap.id ℝ (Point (N*d))) (t := t)).map (configurationEuclidean d N).symm)
      ((law hN hb hbound hM hL₁ hL₂ hT (ξ.map (equivPath (configurationEuclidean d N)))
        (μ.map (configurationEuclidean d N)) (ContinuousLinearMap.id ℝ (Point (N*d))) (t := t)).map
          (configurationEuclidean d N).symm)) atTop (𝓝 0) := by
  simp_rw [fullLaw_map_symm_eq_particleLaw _ _ _ _ _ _ _ μ ξ ht]
  exact PeriodicParticle.law_wassersteinSq_tendsto hN hb hbound hM hL₁ hL₂ hT μ ξ ht

end SharpWasserstein.PeriodicParticleTangentLimit
