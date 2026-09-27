import SharpWasserstein.PeriodicSourceConvolutionTime

/-! Actual scalar Gram coefficients for a weighted Fourier/Galerkin problem.
All derivatives of gradient products are proved bounded from those of the
potentials. Their time derivatives follow from the genuine weak evolution;
no differentiated Gram equation or time modulus is an assumption. Periodicity
is deliberately unnecessary for this local coefficient theorem. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal Topology
namespace SharpWasserstein.WeightedPeriodicCoefficientEvolution
open WeightedTangent NoiseAverage PropagatedSourceEquation

variable {n : ℕ}

/-- The genuine Euclidean gradient preserves bounds of every derivative order. -/
theorem gradient_allDerivativesBounded {f : Point n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hB : AllDerivativesBounded f) :
    AllDerivativesBounded (gradient f) := by
  exact hB.fderiv.linear_comp (contDiff_infty_iff_fderiv.mp hf).2
    (InnerProductSpace.toDual ℝ (Point n)).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- The literal scalar integrand of the weighted Gram matrix. -/
def gramTest (f g : Point n → ℝ) (x : Point n) : ℝ :=
  ⟪gradient f x, gradient g x⟫_ℝ

theorem gramTest_smooth {f g : Point n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (gramTest f g) :=
  (BochnerIdentity.smooth_gradient hf).inner ℝ (BochnerIdentity.smooth_gradient hg)

/-- Bounds on actual derivatives of the test potentials suffice for the
entire gradient-product test, including all derivatives used by the generator. -/
theorem gramTest_allDerivativesBounded {f g : Point n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hBf : AllDerivativesBounded f) (hBg : AllDerivativesBounded g) :
    AllDerivativesBounded (gramTest f g) := by
  have hdg := BochnerIdentity.smooth_gradient hg
  have hbg := gradient_allDerivativesBounded hg hBg
  have he : gramTest f g = fun x => fderiv ℝ f x (gradient g x) := by
    funext x
    exact inner_gradient_left
  rw [he]
  exact hBf.fderiv.clm_apply (contDiff_infty_iff_fderiv.mp hf).2 hdg hbg

/-- This is an actual weighted Lebesgue integral, valid also for singular laws. -/
def gramEntry [MeasurableSpace (Point n)] (μ : Measure (Point n))
    (f g : Point n → ℝ) : ℝ := ∫ x,gramTest f g x ∂μ

/-- Bounded gradient products are integrable against any finite measure,
so Gram coefficients do not rely on the totalized nonintegrable integral. -/
theorem gramTest_integrable [MeasurableSpace (Point n)] [BorelSpace (Point n)]
    (μ : Measure (Point n)) [IsFiniteMeasure μ]
    {f g : Point n → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hBf : AllDerivativesBounded f) (hBg : AllDerivativesBounded g) :
    Integrable (gramTest f g) μ := by
  obtain ⟨C,_,hC⟩ := (gramTest_allDerivativesBounded hf hg hBf hBg).bounded
  exact Integrable.of_bound (gramTest_smooth hf hg).continuous.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

section Weak
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {v : ℝ → Configuration d N → Configuration d N}
  {P : ℝ → Measure (Configuration d N)}

/-- Exact transport of a continuous scalar observable to Euclidean coordinates. -/
theorem integral_map_euclidean (μ : Measure (Configuration d N))
    {F : Point (N*d) → ℝ} (hF : Continuous F) :
    (∫ x,F x ∂μ.map (configurationEuclidean d N)) =
      ∫ x,F (configurationEuclidean d N x) ∂μ :=
  integral_map (configurationEuclidean d N).continuous.measurable.aemeasurable
    hF.aestronglyMeasurable

/-- The right derivative, including time zero, of every bounded smooth
observable of the actual Euclidean pushforward of a weak evolution. -/
theorem observable_hasDerivWithinAt (h : WeakEvolution v P)
    {K M : ℝ≥0} (hv : Continuous (Function.uncurry v))
    (hl : ∀ t,LipschitzWith K (v t)) (hb : ∀ t x,‖v t x‖ ≤ M)
    {F : Point (N*d) → ℝ} (hF : ContDiff ℝ ∞ F) (hBF : AllDerivativesBounded F)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt
      (fun s => ∫ x,F x ∂(P s).map (configurationEuclidean d N))
      (∫ x,generator (v t) (F ∘ configurationEuclidean d N) x ∂P t) (Ici 0) t := by
  have hp := hF.comp (configurationEuclidean d N).contDiff
  have hBp := hBF.comp_linear hF (configurationEuclidean d N).toContinuousLinearMap
  simpa only [integral_map_euclidean _ hF.continuous, Function.comp_def] using
    WeakEvolution.hasDerivWithinAt_bounded_configuration h hv hl hb hp hBp ht

/-- Positive-time scalar differentiability of the same actual observable. -/
theorem observable_hasDerivAt (h : WeakEvolution v P)
    {K M : ℝ≥0} (hv : Continuous (Function.uncurry v))
    (hl : ∀ t,LipschitzWith K (v t)) (hb : ∀ t x,‖v t x‖ ≤ M)
    {F : Point (N*d) → ℝ} (hF : ContDiff ℝ ∞ F) (hBF : AllDerivativesBounded F)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s => ∫ x,F x ∂(P s).map (configurationEuclidean d N))
      (∫ x,generator (v t) (F ∘ configurationEuclidean d N) x ∂P t) t :=
  (observable_hasDerivWithinAt h hv hl hb hF hBF ht.le).hasDerivAt (Ici_mem_nhds ht)

/-- A genuine weighted Gram entry obeys the forward generator equation at
all nonnegative times, with the one-sided initial derivative. -/
theorem gramEntry_hasDerivWithinAt (h : WeakEvolution v P)
    {K M : ℝ≥0} (hv : Continuous (Function.uncurry v))
    (hl : ∀ t,LipschitzWith K (v t)) (hb : ∀ t x,‖v t x‖ ≤ M)
    {f g : Point (N*d) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hBf : AllDerivativesBounded f) (hBg : AllDerivativesBounded g)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt
      (fun s => gramEntry ((P s).map (configurationEuclidean d N)) f g)
      (∫ x,generator (v t) (gramTest f g ∘ configurationEuclidean d N) x ∂P t) (Ici 0) t :=
  observable_hasDerivWithinAt h hv hl hb (gramTest_smooth hf hg)
    (gramTest_allDerivativesBounded hf hg hBf hBg) ht

theorem gramEntry_hasDerivAt (h : WeakEvolution v P)
    {K M : ℝ≥0} (hv : Continuous (Function.uncurry v))
    (hl : ∀ t,LipschitzWith K (v t)) (hb : ∀ t x,‖v t x‖ ≤ M)
    {f g : Point (N*d) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hBf : AllDerivativesBounded f) (hBg : AllDerivativesBounded g)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s => gramEntry ((P s).map (configurationEuclidean d N)) f g)
      (∫ x,generator (v t) (gramTest f g ∘ configurationEuclidean d N) x ∂P t) t :=
  (gramEntry_hasDerivWithinAt h hv hl hb hf hg hBf hBg ht.le).hasDerivAt (Ici_mem_nhds ht)

/-- The derivative of each Gram coefficient is continuous; this is obtained
from the actual weak law and generator, not an assumed matrix regularity. -/
theorem gramEntry_derivative_continuousOn (h : WeakEvolution v P)
    {K M : ℝ≥0} (hv : Continuous (Function.uncurry v))
    (hl : ∀ t,LipschitzWith K (v t)) (hb : ∀ t x,‖v t x‖ ≤ M)
    {f g : Point (N*d) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hBf : AllDerivativesBounded f) (hBg : AllDerivativesBounded g) :
    ContinuousOn
      (fun t => ∫ x,generator (v t) (gramTest f g ∘ configurationEuclidean d N) x ∂P t) (Ici 0) := by
  have hs := gramTest_smooth hf hg
  have hB := gramTest_allDerivativesBounded hf hg hBf hBg
  exact WeakEvolution.bounded_generatorExpectation_continuousOn h hv hl hb
    (hs.comp (configurationEuclidean d N).contDiff)
    (hB.comp_linear hs (configurationEuclidean d N).toContinuousLinearMap)

end Weak
end SharpWasserstein.WeightedPeriodicCoefficientEvolution
