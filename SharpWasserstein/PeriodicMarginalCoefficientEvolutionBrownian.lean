module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicMarginalCoefficientEvolutionCalculus
public import SharpWasserstein.WeightedPeriodicCoefficientEvolutionBrownian
public import SharpWasserstein.BrownianSourceSmoothPairing

@[expose] public section

/-! Genuine marginal Gram and source scalar derivatives under the constructed
full Brownian particle evolution. Marginal laws are actual pushforwards;
noncompact cylinders are justified by the full bounded smooth test equations. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal BigOperators
namespace SharpWasserstein.PeriodicMarginalCoefficientEvolution
open WeightedTangent NoiseAverage PropagatedSourceEquation PeriodicSourceConvolution
open PeriodicParticleTangentLimit WeightedPeriodicCoefficientEvolution
open ExternalInteractionPeriodic ExternalInteractionSymmetry

variable {d m N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
  {b : Position d → Position d → Position d} {M K M' K' : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => (particleDrift b : Configuration d N → _))))
  (hb : ∀ _ : ℝ,∀ x : Configuration d N,‖particleDrift b x‖ ≤ M)
  (hl : ∀ _ : ℝ,LipschitzWith K (particleDrift b : Configuration d N → _))
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) (particleDrift b))))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) (particleDrift b) y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) (particleDrift b)))
  {T : ℝ} (hT : 0 ≤ T) (hbs : BoundedSmoothKernel b)
  (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (hμ : HasSecondMoment μ)
  (hm : m ≤ N)

/-- The actual full particle generator after retaining m particle coordinates. -/
def splitGenerator (hm : m ≤ N) (b : Position d → Position d → Position d)
    (f : Point (m*d) → ℝ) (x : Point (N*d)) : ℝ :=
  cylinder hm (fun y => PDEPairings.laplacian f y + ⟪internalDrift N b y,gradient f y⟫_ℝ) x +
    (N:ℝ)⁻¹ * ∑ j : Fin N with m ≤ j.val,particleInteraction hm j b f x

omit [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))] in
theorem splitGenerator_eq (hm : m ≤ N) (b : Position d → Position d → Position d)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ 2 f) :
    splitGenerator hm b f = euclideanGenerator (particleDrift b) (cylinder hm f) :=
  funext fun x => (particle_generator_cylinder hm b hf x).symm

include hv hb hl hbs hμ

/-- Every bounded smooth marginal observable differentiates with the exact
particle generator split. Its carrying law is literally the coordinate marginal. -/
theorem brownian_marginal_observable_hasDerivWithinAt
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f) (hBf : AllDerivativesBounded f)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt
      (fun s => ∫ y,f y ∂(Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) s).map
        (marginalProjection hm))
      (∫ x,splitGenerator hm b f x
        ∂Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t) (Icc 0 T) t := by
  rw [splitGenerator_eq hm b (BochnerIdentity.contDiff_two_of_smooth hf)]
  have hd := brownian_observable_hasDerivWithinAt hv hb hl hv' hb' hl' hT
    (particleDrift_smooth hbs) μ hμ (cylinder_smooth hm hf)
    (cylinder_allDerivativesBounded hm hf hBf) ht
  apply hd.congr_of_mem _ ht
  intro s hs
  exact (integral_map (marginalProjection hm).continuous.measurable.aemeasurable
    hf.continuous.aestronglyMeasurable)

/-- The Gram entry uses genuine lower-dimensional Euclidean gradients and
the actual marginal measure, not a assumed finite matrix evolution. -/
theorem brownian_marginal_gramEntry_hasDerivWithinAt
    {f g : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hBf : AllDerivativesBounded f) (hBg : AllDerivativesBounded g)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt
      (fun s => gramEntry ((Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) s).map
        (marginalProjection hm)) f g)
      (∫ x,splitGenerator hm b (gramTest f g) x
        ∂Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t) (Icc 0 T) t :=
  brownian_marginal_observable_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs μ hμ hm
    (gramTest_smooth hf hg) (gramTest_allDerivativesBounded hf hg hBf hBg) ht

omit hμ [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))] in
/-- The actual propagated source coefficient of a cylinder differentiates
into the same exact internal/diffusive/external generator decomposition. -/
theorem brownian_marginal_source_hasDerivWithinAt
    {u : Point (N*d) → Point (N*d)}
    (hu : MemLp u 2 (μ.map (configurationEuclidean d N)))
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f) (hBf : AllDerivativesBounded f)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt
      (action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (μ.map (configurationEuclidean d N)) u
        (cylinder hm f))
      (action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (μ.map (configurationEuclidean d N)) u
        (splitGenerator hm b f) t) (Icc 0 T) t := by
  rw [splitGenerator_eq hm b (BochnerIdentity.contDiff_two_of_smooth hf)]
  exact brownian_action_hasDerivWithinAt hv hb hl hv' hb' hl' hT
    (particleDrift_smooth hbs) (particleDrift_allDerivativesBounded hbs)
    (μ.map (configurationEuclidean d N)) hu (cylinder_smooth hm hf)
    (cylinder_allDerivativesBounded hm hf hBf) ht

omit hμ in
/-- The source derivative is the literal differential pairing of the true
split generator with the full canonical tangent at the same time. -/
theorem brownian_marginal_source_pairing_hasDerivWithinAt
    {u : Point (N*d) → Point (N*d)}
    (hu : MemLp u 2 (μ.map (configurationEuclidean d N)))
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f) (hBf : AllDerivativesBounded f)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    let ν := Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t
    let σ := Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
      (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu t
    HasDerivWithinAt
      (action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (μ.map (configurationEuclidean d N)) u
        (cylinder hm f))
      (pairing ν (WeightedTangent.representative ν σ).val (splitGenerator hm b f)) (Icc 0 T) t := by
  dsimp only
  have hd := brownian_marginal_source_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs μ hm hu hf hBf ht
  have hs : ContDiff ℝ ∞ (splitGenerator hm b f) := by
    rw [splitGenerator_eq hm b (BochnerIdentity.contDiff_two_of_smooth hf)]
    exact euclideanGenerator_smooth (particleDrift_smooth hbs) (cylinder_smooth hm hf)
  have hB : AllDerivativesBounded (splitGenerator hm b f) := by
    rw [splitGenerator_eq hm b (BochnerIdentity.contDiff_two_of_smooth hf)]
    exact euclideanGenerator_bounded (particleDrift_smooth hbs) (particleDrift_allDerivativesBounded hbs)
      (cylinder_smooth hm hf) (cylinder_allDerivativesBounded hm hf hBf)
  rw [Brownian.action_eq_representative_pairing hv' hb' hl' hT
    (particleDrift_smooth hbs) (particleDrift_allDerivativesBounded hbs)
    (μ.map (configurationEuclidean d N)) hu hs hB ht] at hd
  simpa only [pairing,inner_gradient_left] using hd

/-- All coefficients of any finite marginal trial family have genuine scalar
derivatives along the actual full Brownian evolution. -/
theorem brownian_marginal_coefficients_hasDerivWithinAt
    {ι : Type*} (a : ι → Point (m*d) → ℝ)
    (ha : ∀ i,ContDiff ℝ ∞ (a i)) (hBa : ∀ i,AllDerivativesBounded (a i))
    {u : Point (N*d) → Point (N*d)}
    (hu : MemLp u 2 (μ.map (configurationEuclidean d N)))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∀ i j,HasDerivWithinAt
      (fun s => gramEntry ((Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) s).map
        (marginalProjection hm)) (a i) (a j))
      (∫ x,splitGenerator hm b (gramTest (a i) (a j)) x
        ∂Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t) (Icc 0 T) t) ∧
    (∀ i,HasDerivWithinAt
      (action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (μ.map (configurationEuclidean d N)) u
        (cylinder hm (a i)))
      (action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (μ.map (configurationEuclidean d N)) u
        (splitGenerator hm b (a i)) t) (Icc 0 T) t) := by
  exact ⟨fun i j => brownian_marginal_gramEntry_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs μ hμ hm
    (ha i) (ha j) (hBa i) (hBa j) ht,
    fun i => brownian_marginal_source_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs μ hm
      hu (ha i) (hBa i) ht⟩

end SharpWasserstein.PeriodicMarginalCoefficientEvolution
