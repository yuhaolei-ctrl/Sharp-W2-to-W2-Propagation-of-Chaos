module

public import SharpWasserstein.Compat
public import SharpWasserstein.PropagatedSourceEquationDistribution
public import SharpWasserstein.InitialSourceMarginalConfiguration

@[expose] public section

/-! Zero-time identification of the actual propagated initial current.
The field is the genuine reference-minus-particle drift defect, so no
replacement of its propagation by a canonical gradient field is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff InnerProductSpace
namespace SharpWasserstein.PropagatedSourceEquation.Brownian
open WeightedTangent NoiseAverage FlowSemigroupDerivative
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Configuration d N → Configuration d N} {M' K' : ℝ≥0}
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) b)))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) b y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) b))
  {T : ℝ} (hT : 0 ≤ T) (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]

theorem sourceAt_zero_pairing {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 μ)
    (φ : Test (N*d)) :
    sourceAt hv' hb' hl' hT hbs hB μ u hu 0 φ =
      ∫ x,⟪gradient φ.val x,u x⟫_ℝ ∂μ := by
  rw [sourceAt_apply,clampedExpectation_of_mem hv' hb' hl' hT _ _ (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),
    expectation_zero hv' hb' hl' hT _ (euclideanBrownianPathLaw_zero_ae hT)]
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => inner_gradient_left.symm

theorem sourceAt_zero_of_divergence {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 μ)
    (σ : Test (N*d) →ₗ[ℝ] ℝ)
    (hσ : ∀ φ : Test (N*d),σ φ = ∫ x,⟪gradient φ.val x,u x⟫_ℝ ∂μ) :
    sourceAt hv' hb' hl' hT hbs hB μ u hu 0 = σ := by
  ext φ
  rw [sourceAt_zero_pairing,hσ]

omit [IsFiniteMeasure μ] in
/-- The actual carrying law also starts at the original law. -/
theorem lawAt_zero : lawAt hv' hb' hl' hT μ 0 = μ := by
  unfold lawAt
  rw [projIcc_of_mem _ (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩)]
  have he : PropagatedFlux.Flow.endpoint hv' hb' hl' hT (t := 0) =ᵐ[μ.prod (euclideanBrownianPathLaw d N T)] Prod.fst := by
    have hz := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := euclideanBrownianPathLaw d N T)).ae
      (euclideanBrownianPathLaw_zero_ae hT)
    filter_upwards [hz] with q hq
    change BoundedFlow.flow hv' hb' hl' hT q.1 q.2 0 = q.1
    have hx := (BoundedFlow.flow_trajectory hv' hb' hl' hT q.1 q.2).equation 0 ⟨le_rfl,hT⟩
    simpa only [intervalIntegral.integral_same,add_zero,BoundedFlow.noiseExtension,
      projIcc_of_mem _ (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),hq,add_zero] using hx
  rw [Measure.map_congr he]
  simp

end SharpWasserstein.PropagatedSourceEquation.Brownian
