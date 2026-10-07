module

public import SharpWasserstein.Compat
public import SharpWasserstein.WeightedPeriodicCoefficientEvolution
public import SharpWasserstein.PropagatedSourceEquationLaw

@[expose] public section

/-! Gram and source coefficient equations on the very same constructed
Brownian carrying law. This supplies literal scalar derivatives for finite
Galerkin systems without assuming a density or a matrix evolution equation. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal Topology
namespace SharpWasserstein.WeightedPeriodicCoefficientEvolution
open WeightedTangent NoiseAverage PropagatedSourceEquation PeriodicSourceConvolution

variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Configuration d N → Configuration d N} {M K M' K' : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ,∀ x,‖b x‖ ≤ M) (hl : ∀ _ : ℝ,LipschitzWith K b)
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) b)))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) b y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) b))
  {T : ℝ} (hT : 0 ≤ T) (hbs : ContDiff ℝ ∞ b)
  (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (hμ : HasSecondMoment μ)
include hv hb hl hbs hμ

/-- A bounded smooth observable of the source's actual carrying law has the
true Euclidean generator derivative, including both horizon endpoints. -/
theorem brownian_observable_hasDerivWithinAt
    {F : Point (N*d) → ℝ} (hF : ContDiff ℝ ∞ F) (hBF : AllDerivativesBounded F)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt
      (fun s => ∫ x,F x ∂Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) s)
      (∫ x,euclideanGenerator b F x
        ∂Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t) (Icc 0 T) t := by
  have hd := (observable_hasDerivWithinAt
    (BrownianFlow.globalLaw_weakEvolution hv hb hl μ hμ) hv hl hb hF hBF ht.1).mono
      (show Icc (0:ℝ) T ⊆ Ici 0 from fun _ hs => hs.1)
  have he (s : ℝ) (hs : s ∈ Icc 0 T) :
      (∫ x,F x ∂Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) s) =
        ∫ x,F x ∂(BrownianFlow.globalLaw hv hb hl μ s).map (configurationEuclidean d N) := by
    rw [Brownian.lawAt_eq_map_globalLaw hv hb hl hv' hb' hl' hT μ hs]
  have hG : Continuous (euclideanGenerator b F) := (euclideanGenerator_smooth hbs hF).continuous
  have hgen : (∫ x,euclideanGenerator b F x
      ∂Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t) =
      ∫ x,generator b (F ∘ configurationEuclidean d N) x ∂BrownianFlow.globalLaw hv hb hl μ t := by
    rw [Brownian.lawAt_eq_map_globalLaw hv hb hl hv' hb' hl' hT μ ht,
      integral_map_euclidean _ hG]
    simp only [euclideanGenerator,Function.comp_def,ContinuousLinearEquiv.symm_apply_apply]
  rw [hgen]
  exact hd.congr_of_mem he ht

theorem brownian_observable_hasDerivAt
    {F : Point (N*d) → ℝ} (hF : ContDiff ℝ ∞ F) (hBF : AllDerivativesBounded F)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt
      (fun s => ∫ x,F x ∂Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) s)
      (∫ x,euclideanGenerator b F x
        ∂Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t) t :=
  (brownian_observable_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs μ hμ hF hBF
    ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- Actual weighted Gram coefficients, with no absolute continuity of the
carrying probability measure required. -/
theorem brownian_gramEntry_hasDerivWithinAt
    {f g : Point (N*d) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hBf : AllDerivativesBounded f) (hBg : AllDerivativesBounded g)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt
      (fun s => gramEntry (Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) s) f g)
      (∫ x,euclideanGenerator b (gramTest f g) x
        ∂Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t) (Icc 0 T) t :=
  brownian_observable_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs μ hμ
    (gramTest_smooth hf hg) (gramTest_allDerivativesBounded hf hg hBf hBg) ht

theorem brownian_gramEntry_hasDerivAt
    {f g : Point (N*d) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hBf : AllDerivativesBounded f) (hBg : AllDerivativesBounded g)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt
      (fun s => gramEntry (Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) s) f g)
      (∫ x,euclideanGenerator b (gramTest f g) x
        ∂Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t) t :=
  (brownian_gramEntry_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs μ hμ hf hg hBf hBg
    ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- The exact derivative of a Brownian Gram coefficient is continuous on
the whole finite horizon, including its endpoint values. -/
theorem brownian_gramEntry_derivative_continuousOn
    {f g : Point (N*d) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hBf : AllDerivativesBounded f) (hBg : AllDerivativesBounded g) :
    ContinuousOn (fun t => ∫ x,euclideanGenerator b (gramTest f g) x
      ∂Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t) (Icc 0 T) := by
  have hc := (gramEntry_derivative_continuousOn
    (BrownianFlow.globalLaw_weakEvolution hv hb hl μ hμ) hv hl hb hf hg hBf hBg).mono
      (show Icc (0:ℝ) T ⊆ Ici 0 from fun _ hs => hs.1)
  apply hc.congr
  intro t ht
  dsimp only
  rw [Brownian.lawAt_eq_map_globalLaw hv hb hl hv' hb' hl' hT μ ht,
    integral_map_euclidean _ (euclideanGenerator_smooth hbs (gramTest_smooth hf hg)).continuous]
  simp only [euclideanGenerator,Function.comp_def,ContinuousLinearEquiv.symm_apply_apply]

omit hμ in
/-- The exact source-coefficient derivative is continuous, by a second
application of the actual source equation to the genuine generator test. -/
theorem brownian_source_derivative_continuousOn
    (hB : AllDerivativesBounded b)
    {u : Point (N*d) → Point (N*d)}
    (hu : MemLp u 2 (μ.map (configurationEuclidean d N)))
    {F : Point (N*d) → ℝ} (hF : ContDiff ℝ ∞ F) (hBF : AllDerivativesBounded F) :
    ContinuousOn
      (action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (μ.map (configurationEuclidean d N)) u
        (euclideanGenerator b F)) (Icc 0 T) := by
  obtain ⟨C,hC⟩ := brownian_action_lipschitzOn hv hb hl hv' hb' hl' hT hbs hB
    (μ.map (configurationEuclidean d N)) hu
    (euclideanGenerator_smooth hbs hF) (euclideanGenerator_bounded hbs hB hF hBF)
  exact hC.continuousOn

/-- Every entry of a finite Galerkin system differentiates along the actual
Brownian measure and its genuine propagated Jacobian source. The formula
works for any family of bounded smooth potentials, in particular Fourier atoms. -/
theorem brownian_coefficients_hasDerivWithinAt
    (hB : AllDerivativesBounded b) {ι : Type*} (a : ι → Point (N*d) → ℝ)
    (ha : ∀ i,ContDiff ℝ ∞ (a i)) (hBa : ∀ i,AllDerivativesBounded (a i))
    {u : Point (N*d) → Point (N*d)}
    (hu : MemLp u 2 (μ.map (configurationEuclidean d N)))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∀ i j,HasDerivWithinAt
      (fun s => gramEntry (Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) s) (a i) (a j))
      (∫ x,euclideanGenerator b (gramTest (a i) (a j)) x
        ∂Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t) (Icc 0 T) t) ∧
    (∀ i,HasDerivWithinAt
      (action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (μ.map (configurationEuclidean d N)) u (a i))
      (action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (μ.map (configurationEuclidean d N)) u
        (euclideanGenerator b (a i)) t) (Icc 0 T) t) := by
  constructor
  · intro i j
    exact brownian_gramEntry_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs μ hμ
      (ha i) (ha j) (hBa i) (hBa j) ht
  · intro i
    exact brownian_action_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs hB
      (μ.map (configurationEuclidean d N)) hu (ha i) (hBa i) ht

end SharpWasserstein.WeightedPeriodicCoefficientEvolution
