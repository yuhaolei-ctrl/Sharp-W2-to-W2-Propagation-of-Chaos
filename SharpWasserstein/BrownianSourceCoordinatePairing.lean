import SharpWasserstein.BrownianSourceInitialFlux
import SharpWasserstein.PropagatedSourceEquationConjugacy

/-! Exact coordinate bridge from the actual Euclidean Brownian JV source
to the configuration semigroup/current pairing used by the switch curve. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff InnerProductSpace
namespace SharpWasserstein.PropagatedSourceEquation.Brownian
open WeightedTangent NoiseAverage FlowSemigroupDerivative
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Configuration d N → Configuration d N} {M K M' K' : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ,∀ x,‖b x‖ ≤ M) (hl : ∀ _ : ℝ,LipschitzWith K b)
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) b)))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) b y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) b))
  {T : ℝ} (hT : 0 ≤ T) (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]

/-- The propagated actual current in Euclidean coordinates acts exactly as
the original configuration semigroup derivative, with no change in sign. -/
theorem sourceAt_configuration_pairing {v : Configuration d N → Configuration d N}
    (hvL : MemLp (euclideanFlux v) 2 (euclideanLaw μ)) {t : ℝ} (ht : t ∈ Icc 0 T)
    (φ : Test (N*d)) :
    sourceAt hv' hb' hl' hT hbs hB (euclideanLaw μ) (euclideanFlux v) hvL t φ =
      ∫ x,fderiv ℝ (expectation hv hb hl hT (BrownianNoise.configurationLaw d N T)
        (t := t) ((φ : Point (N*d) → ℝ) ∘ configurationEuclidean d N)) x (v x) ∂μ := by
  rw [sourceAt_apply,clampedExpectation_of_mem hv' hb' hl' hT _ _ ht,integral_euclideanLaw]
  have he : (expectation hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (t := t)
      (φ : Point (N*d) → ℝ)) ∘ configurationEuclidean d N =
      expectation hv hb hl hT (BrownianNoise.configurationLaw d N T) (t := t)
        ((φ : Point (N*d) → ℝ) ∘ configurationEuclidean d N) := by
    funext x
    exact expectation_equiv (configurationEuclidean d N) hv hb hl hv' hb' hl' hT
      (BrownianNoise.configurationLaw d N T) x ht φ.property.1.continuous
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [(configurationEuclidean d N).comp_right_fderiv]
  simp only [euclideanFlux,ContinuousLinearEquiv.symm_apply_apply,ContinuousLinearMap.comp_apply]
  rfl

end SharpWasserstein.PropagatedSourceEquation.Brownian
