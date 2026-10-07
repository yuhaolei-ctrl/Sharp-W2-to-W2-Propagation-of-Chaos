module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicMarginalCoefficientEvolutionAverage

@[expose] public section

/-! Physical periodic coefficient equations for the actual Brownian particle
source. Law exchangeability and source covariance are propagated from the
initial data; neither a marginal PDE nor a marginal source identity is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal BigOperators
namespace SharpWasserstein.PeriodicMarginalCoefficientEvolution
open WeightedTangent NoiseAverage PropagatedSourceEquation PeriodicSourceConvolution
open PeriodicParticleTangentLimit WeightedPeriodicCoefficientEvolution
open ExternalInteractionPeriodic ExternalInteractionSymmetry PropagatedSourcePermutation
open WeightedPeriodicFourierScale (PeriodicOf)

variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Position d → Position d → Position d} {M' K' : ℝ≥0}
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) (particleDrift b))))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) (particleDrift b) y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) (particleDrift b)))
  {T : ℝ} (hT : 0 ≤ T)

/-- The exact carrying law used by the differentiated source preserves the
actual Euclidean particle permutation invariance of the initial measure. -/
theorem brownian_lawAt_permutation (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    (e : Equiv.Perm (Fin N)) (hμ : μ.map (euclideanPermutation e)=μ) (t : ℝ) :
    (Brownian.lawAt hv' hb' hl' hT μ t).map (euclideanPermutation e) =
      Brownian.lawAt hv' hb' hl' hT μ t := by
  let L := euclideanPermutation (d := d) e
  let ξ := euclideanBrownianPathLaw d N T
  let F := PropagatedFlux.Flow.endpoint hv' hb' hl' hT (t := projIcc 0 T hT t)
  have hF := PropagatedFlux.Flow.endpoint_measurable hv' hb' hl' hT (projIcc 0 T hT t).property
  have hL := L.continuous.measurable
  have hW := (equivPath_continuous (T := T) L).measurable
  have hpair : (μ.prod ξ).map (Prod.map L (equivPath L)) = μ.prod ξ := by
    rw [← Measure.map_prod_map μ ξ hL hW,hμ,euclideanBrownianPathLaw_permutation]
  change ((μ.prod ξ).map F).map L = (μ.prod ξ).map F
  rw [Measure.map_map hL hF]
  have hfun : L ∘ F = F ∘ Prod.map L (equivPath L) := by
    funext p
    exact (flow_covariant hv' hb' hl' hT L (particle_equivDrift_covariant b e)
      p.1 p.2 (projIcc 0 T hT t).property).symm
  rw [hfun,← Measure.map_map hF (hL.prodMap hW),hpair]

variable {m : ℕ} [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
  [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]
  {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => (particleDrift b : Configuration d N → _))))
  (hb : ∀ _ : ℝ,∀ x : Configuration d N,‖particleDrift b x‖ ≤ M)
  (hl : ∀ _ : ℝ,LipschitzWith K (particleDrift b : Configuration d N → _))
  (hbs : BoundedSmoothKernel b)
  (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]

omit [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))] in
/-- The actual Brownian source coefficient equals the literal pairing with
its constructed physical-periodic marginal representative. -/
theorem brownian_marginal_periodic_source_pairing {P : ℝ} (hP : 0 < P) (hm : m ≤ N)
    {u : Point (N*d) → Point (N*d)}
    (hu : MemLp u 2 (μ.map (configurationEuclidean d N)))
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PeriodicOf P (f ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    let ν := Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t
    let σ := Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
      (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu t
    let U := (WeightedTangent.representative ν σ).val
    action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (μ.map (configurationEuclidean d N)) u
      (cylinder hm f) t =
      ∫ y,⟪gradient f y,
        ((WeightedPeriodicTangentPhysical.representative P (ν.map (marginalProjection hm))
          (prefixSource hm ν U) : gradientClosure (ν.map (marginalProjection hm))) :
          Lp (Point (m*d)) 2 (ν.map (marginalProjection hm))) y⟫_ℝ ∂ν.map (marginalProjection hm) := by
  dsimp only
  rw [Brownian.action_eq_representative_pairing hv' hb' hl' hT
    (particleDrift_smooth hbs) (particleDrift_allDerivativesBounded hbs)
    (μ.map (configurationEuclidean d N)) hu (cylinder_smooth hm hf)
    (cylinder_allDerivativesBounded hm hf (physical_allDerivativesBounded hP hf hp)) ht]
  simpa only [pairing,inner_gradient_left] using prefixSource_periodic_pairing hm
    (Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t)
    (WeightedTangent.representative _ (Brownian.sourceAt hv' hb' hl' hT
      (particleDrift_smooth hbs) (particleDrift_allDerivativesBounded hbs)
      (μ.map (configurationEuclidean d N)) u hu t)).val hP hf hp

include hv hb hl in
/-- The genuine marginal source coefficient satisfies the exact internal and
averaged external derivative equation. Its symmetry is derived from exchangeable
initial data and an equivariant initial L² source field, and all periodic tests
are admitted through the actual gradient closure. -/
theorem brownian_marginal_periodic_source_hasDerivWithinAt
    {P : ℝ} (hP : 0 < P) (hm : m < N) (hex : Exchangeable μ)
    (hx : ∀ a x y,b (x+Pi.single a P) y=b x y)
    (hy : ∀ a x y,b x (y+Pi.single a P)=b x y)
    {u : Point (N*d) → Point (N*d)}
    (hu : MemLp u 2 (μ.map (configurationEuclidean d N)))
    (hue : ∀ e : Equiv.Perm (Fin N),∀ᵐ x ∂μ.map (configurationEuclidean d N),
      u (euclideanPermutation e x)=euclideanPermutation e (u x))
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PeriodicOf P (f ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    let ν := Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t
    let σ := Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
      (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu t
    let U := (WeightedTangent.representative ν σ).val
    HasDerivWithinAt
      (action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (μ.map (configurationEuclidean d N)) u
        (cylinder hm.le f))
      ((∫ y,⟪gradient (internalGenerator N b f) y,
        ((WeightedPeriodicTangentPhysical.representative P (ν.map (marginalProjection hm.le))
          (prefixSource hm.le ν U) : gradientClosure (ν.map (marginalProjection hm.le))) :
          Lp (Point (m*d)) 2 (ν.map (marginalProjection hm.le))) y⟫_ℝ
          ∂ν.map (marginalProjection hm.le)) +
      (((N:ℝ)-m)/N)*(∫ y,⟪gradient (ExternalInteraction.interaction b f) y,
        ((WeightedPeriodicTangentPhysical.representative P (ν.map (observation hm.le ⟨m,hm⟩))
          (observedSource hm.le ⟨m,hm⟩ ν U) : gradientClosure (ν.map (observation hm.le ⟨m,hm⟩))) :
          Lp (Point (m*d+d)) 2 (ν.map (observation hm.le ⟨m,hm⟩))) y⟫_ℝ
          ∂ν.map (observation hm.le ⟨m,hm⟩))) (Icc 0 T) t := by
  let ν := Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t
  let σ := Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
    (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu t
  have hν (e : Equiv.Perm (Fin N)) : ν.map (euclideanPermutation e)=ν :=
    brownian_lawAt_permutation hv' hb' hl' hT _ e (euclideanLaw_permutation μ hex e) t
  have hσ (e : Equiv.Perm (Fin N)) (φ : Test (N*d)) :
      σ (pullTest (euclideanPermutation e) φ)=σ φ :=
    particle_sourceAt_invariant hbs hv' hb' hl' hT _ e (euclideanLaw_permutation μ hex e)
      u hu (hue e) t φ
  have hσE : FiniteEnergy ν σ :=
    (Brownian.sourceAt_finiteEnergy_and_energy_le hv' hb' hl' hT
      (particleDrift_smooth hbs) (particleDrift_allDerivativesBounded hbs)
      (μ.map (configurationEuclidean d N)) u hu ht).1
  have hd := brownian_marginal_source_pairing_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs μ hm.le
    hu hf (physical_allDerivativesBounded hP hf hp) ht
  have he := canonical_splitGenerator_periodic_pairing hP hm ν hν σ hσE hσ hbs hx hy hf hp
  dsimp only at hd he ⊢
  rw [he] at hd
  exact hd

end SharpWasserstein.PeriodicMarginalCoefficientEvolution
