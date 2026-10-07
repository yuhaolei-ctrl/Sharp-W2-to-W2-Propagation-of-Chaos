module

public import SharpWasserstein.Compat
public import SharpWasserstein.PropagatedSourceEquationBrownian
public import SharpWasserstein.PropagatedSourceEquationIntegration
public import SharpWasserstein.PropagatedFluxFlow
public import SharpWasserstein.BoundedDerivativeLinear

@[expose] public section

/-! The actual Brownian-propagated Jacobian flux solves the integrated
homogeneous source equation. Its state norm is the genuine Euclidean norm;
its drift Lipschitz constant is the supplied Euclidean constant. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff Interval
namespace SharpWasserstein.PropagatedSourceEquation
open WeightedTangent NoiseAverage FlowSemigroupDerivative

/-- Exact linear changes of coordinates preserve the stated drift smoothness. -/
theorem equivDrift_smooth {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F) {b : E → E}
    (hbs : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (equivDrift L b) :=
  L.contDiff.comp (hbs.comp L.symm.contDiff)

theorem equivDrift_allDerivativesBounded {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F) {b : E → E}
    (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b) :
    AllDerivativesBounded (equivDrift L b) :=
  (hB.comp_linear hbs L.symm.toContinuousLinearMap).linear_comp
    (hbs.comp L.symm.contDiff) L.toContinuousLinearMap

/-- Every compact smooth test has the bounds used by actual differentiated expectations. -/
theorem compactTest_bounds {n : ℕ} (φ : Test n) :
    ∃ (C : ℝ) (L : ℝ≥0), (∀ x : Point n, ‖(φ : Point n → ℝ) x‖ ≤ C) ∧
      (∀ x, ‖fderiv ℝ (φ : Point n → ℝ) x‖ ≤ L) := by
  obtain ⟨C,hC⟩ := φ.property.2.exists_bound_of_continuous φ.property.1.continuous
  obtain ⟨L,hL⟩ := (φ.property.2.fderiv ℝ).exists_bound_of_continuous
    (φ.property.1.continuous_fderiv (by simp))
  exact ⟨C,NNReal.mk L ((norm_nonneg (fderiv ℝ (φ : Point n → ℝ) 0)).trans (hL 0)),hC,hL⟩

namespace Brownian
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Configuration d N → Configuration d N} {M' K' : ℝ≥0}
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) b)))
  (hb' : ∀ _ : ℝ, ∀ y, ‖equivDrift (configurationEuclidean d N) b y‖ ≤ M')
  (hl' : ∀ _ : ℝ, LipschitzWith K' (equivDrift (configurationEuclidean d N) b))
  {T : ℝ} (hT : 0 ≤ T) (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]

/-- The source is literally the previously constructed actual JV random-map
flux, driven by the pushed law of the constructed Brownian paths. -/
def sourceAt (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ) (r : ℝ) : Test (N*d) →ₗ[ℝ] ℝ :=
  PropagatedFlux.Flow.source hv' hb' hl' hT (euclideanBrownianPathLaw d N T)
    (projIcc 0 T hT r).property (equivDrift_smooth _ hbs) (equivDrift_allDerivativesBounded _ hbs hB)
    μ u hu

/-- The actual random flux is the initial source paired with the proved
semigroup derivative. -/
theorem sourceAt_apply (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ)
    (r : ℝ) (φ : Test (N*d)) :
    sourceAt hv' hb' hl' hT hbs hB μ u hu r φ =
      ∫ x, fderiv ℝ (clampedExpectation hv' hb' hl' hT (euclideanBrownianPathLaw d N T) φ r) x (u x) ∂μ :=
  PropagatedFlux.Flow.source_eq_semigroup_pairing hv' hb' hl' hT _ (projIcc 0 T hT r).property
    (equivDrift_smooth _ hbs) (equivDrift_allDerivativesBounded _ hbs hB) μ u hu φ

/-- The propagated source action is genuinely time integrable. -/
theorem sourceAt_intervalIntegrable (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ)
    (φ : Test (N*d)) (s t : ℝ) :
    IntervalIntegrable (fun r => sourceAt hv' hb' hl' hT hbs hB μ u hu r φ) volume s t := by
  obtain ⟨C,L,hC,hL⟩ := compactTest_bounds φ
  simpa only [sourceAt_apply] using intervalIntegrable_initial_pairing hv' hb' hl' hT _
    (equivDrift_smooth _ hbs) (equivDrift_allDerivativesBounded _ hbs hB) μ
    (φ.property.1.of_le (by simp)) hC hL hu s t

variable {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)

include hv hb hl in
/-- The actual JV source satisfies the homogeneous integrated weak PDE. The
proof differentiates the already proved Brownian weak equation and invokes
proved time/initial integrability; the source equation is not a hypothesis. -/
theorem sourceAt_equation (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ)
    (φ : Test (N*d)) {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    sourceAt hv' hb' hl' hT hbs hB μ u hu t φ - sourceAt hv' hb' hl' hT hbs hB μ u hu s φ =
      ∫ r in s..t,sourceAt hv' hb' hl' hT hbs hB μ u hu r (euclideanGeneratorTest hbs φ) := by
  obtain ⟨C,L,hC,hL⟩ := compactTest_bounds φ
  obtain ⟨D,L',hD,hL'⟩ := compactTest_bounds (euclideanGeneratorTest hbs φ)
  simp_rw [sourceAt_apply]
  rw [clampedExpectation_of_mem hv' hb' hl' hT _ _ ht,
    clampedExpectation_of_mem hv' hb' hl' hT _ _ hs]
  exact integrated_source_identity hv' hb' hl' hT (euclideanBrownianPathLaw d N T)
    (equivDrift_smooth _ hbs) (equivDrift_allDerivativesBounded _ hbs hB) μ
    (φ.property.1.of_le (by simp)) hC hL
    ((euclideanGenerator_test hbs φ).1.of_le (by simp)) hD hL' hs ht
    (euclidean_brownian_primal_identity hv hb hl hT hv' hb' hl' φ hs ht) hu

end Brownian
end SharpWasserstein.PropagatedSourceEquation
