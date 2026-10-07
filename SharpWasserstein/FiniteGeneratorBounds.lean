module

public import SharpWasserstein.Compat
public import SharpWasserstein.FiniteGeneratorCalculus
public import SharpWasserstein.ConfigurationGeneratorEuclidean

@[expose] public section

/-! Genuine global derivative bounds for the physical Euclidean generator;
these discharge the integrability in the finite coefficient identities. -/
noncomputable section
open MeasureTheory
open scoped ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.FiniteGeneratorCalculus
open WeightedTangent NoiseAverage BochnerIdentity PDEPairings
variable {n : ℕ}

theorem directionDeriv_allDerivativesBounded {f : Point n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hB : AllDerivativesBounded f) (v : Point n) :
    AllDerivativesBounded (directionDeriv v f) :=
  hB.fderiv.linear_comp (contDiff_infty_iff_fderiv.mp hf).2 (ContinuousLinearMap.apply ℝ ℝ v)

theorem laplacian_allDerivativesBounded {f : Point n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hB : AllDerivativesBounded f) :
    AllDerivativesBounded (PDEPairings.laplacian f) :=
  AllDerivativesBounded.sum Finset.univ
    (fun _i _ => smooth_directionDeriv (smooth_directionDeriv hf _) _)
    (fun _i _ => directionDeriv_allDerivativesBounded (smooth_directionDeriv hf _)
      (directionDeriv_allDerivativesBounded hf hB _) _)

theorem generator_eq (b : Point n → Point n) (f : Point n → ℝ) :
    generator b f = fun x => PDEPairings.laplacian f x+fderiv ℝ f x (b x) := by
  funext x
  simp only [generator,inner_gradient_right,RCLike.conj_to_real]

theorem generator_smooth {b : Point n → Point n} (hb : ContDiff ℝ ∞ b)
    {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (generator b f) :=
  (smooth_laplacian hf).add (hb.inner ℝ (smooth_gradient hf))

theorem generator_allDerivativesBounded {b : Point n → Point n} (hb : ContDiff ℝ ∞ b)
    (hBb : AllDerivativesBounded b) {f : Point n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hBf : AllDerivativesBounded f) :
    AllDerivativesBounded (generator b f) := by
  rw [generator_eq]
  exact (laplacian_allDerivativesBounded hf hBf).add (smooth_laplacian hf)
    ((contDiff_infty_iff_fderiv.mp hf).2.clm_apply hb)
    (hBf.fderiv.clm_apply (contDiff_infty_iff_fderiv.mp hf).2 hb hBb)

/-- This physical operator is exactly the Brownian configuration generator,
with diffusion coefficient one and no factor of the particle count. -/
theorem euclideanGenerator_eq {d N : ℕ} (b : Configuration d N → Configuration d N)
    (f : Point (N*d) → ℝ) : PropagatedSourceEquation.euclideanGenerator b f =
      generator (PropagatedSourceEquation.equivDrift (configurationEuclidean d N) b) f := by
  funext x
  have h := SharpWasserstein.generator_pullback f b ((configurationEuclidean d N).symm x)
  simpa only [PropagatedSourceEquation.euclideanGenerator,Function.comp_apply,
    ContinuousLinearEquiv.apply_symm_apply,BoundedWeakTests.generator,generator,
    PropagatedSourceEquation.equivDrift] using h

variable [MeasurableSpace (Point n)] [BorelSpace (Point n)]

theorem generator_integrable (μ : Measure (Point n)) [IsFiniteMeasure μ]
    {b : Point n → Point n} (hb : ContDiff ℝ ∞ b) (hBb : AllDerivativesBounded b)
    {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f) (hBf : AllDerivativesBounded f) :
    Integrable (generator b f) μ := by
  obtain ⟨C,_,hC⟩ := (generator_allDerivativesBounded hb hBb hf hBf).bounded
  exact Integrable.of_bound (generator_smooth hb hf).continuous.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

end SharpWasserstein.FiniteGeneratorCalculus
