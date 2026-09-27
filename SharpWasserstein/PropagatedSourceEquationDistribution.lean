import SharpWasserstein.PropagatedSourceEquation

/-! The actual Brownian-propagated finite-energy distribution: initial value,
weak homogeneous evolution, and the full Euclidean energy estimate. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff Interval
namespace SharpWasserstein.PropagatedSourceEquation
open WeightedTangent NoiseAverage FlowSemigroupDerivative

/-- The actual Euclidean Brownian inputs start at zero almost surely. -/
theorem euclideanBrownianPathLaw_zero_ae {d N : ℕ}
    [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ w ∂euclideanBrownianPathLaw d N T, w ⟨0,le_rfl,hT⟩ = 0 := by
  apply (ae_map_iff (equivPath_continuous (configurationEuclidean d N)).measurable.aemeasurable
    ((by fun_prop : Continuous (fun w : C(Icc 0 T,Point (N*d)) => w ⟨0,le_rfl,hT⟩)).measurable
      (measurableSet_singleton 0))).mpr
  filter_upwards [BrownianNoise.configurationLaw_zero_ae (d := d) (N := N) hT] with w hw
  change configurationEuclidean d N (w ⟨0,le_rfl,hT⟩) = 0
  rw [hw,map_zero]

namespace Brownian
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Configuration d N → Configuration d N} {M' K' : ℝ≥0}
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) b)))
  (hb' : ∀ _ : ℝ, ∀ y, ‖equivDrift (configurationEuclidean d N) b y‖ ≤ M')
  (hl' : ∀ _ : ℝ, LipschitzWith K' (equivDrift (configurationEuclidean d N) b))
  {T : ℝ} (hT : 0 ≤ T) (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]

/-- The actual output probability/finite measure of the Brownian flow. -/
def lawAt (r : ℝ) : Measure (Point (N*d)) :=
  (μ.prod (euclideanBrownianPathLaw d N T)).map
    (PropagatedFlux.Flow.endpoint hv' hb' hl' hT (t := projIcc 0 T hT r))

/-- Propagation of the canonical Riesz representative of an initial source. -/
def distributionAt (σ : Test (N*d) →ₗ[ℝ] ℝ) (r : ℝ) : Test (N*d) →ₗ[ℝ] ℝ :=
  sourceAt hv' hb' hl' hT hbs hB μ
    (representative μ σ : Lp (Point (N*d)) 2 μ) (Lp.memLp _) r

/-- The actual source energy has no conversion from a supremum state norm. -/
theorem sourceAt_finiteEnergy_and_energy_le
    (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    FiniteEnergy (lawAt hv' hb' hl' hT μ t) (sourceAt hv' hb' hl' hT hbs hB μ u hu t) ∧
      energy (lawAt hv' hb' hl' hT μ t) (sourceAt hv' hb' hl' hT hbs hB μ u hu t) ≤
        Real.exp ((K':ℝ)*t)^2 * ∫ x, ‖u x‖^2 ∂μ := by
  change FiniteEnergy _ (PropagatedFlux.Flow.source _ _ _ _ _ _ _ _ _ _ _) ∧ _
  simpa only [lawAt,sourceAt,projIcc_of_mem _ ht] using
    And.intro (PropagatedFlux.Flow.source_finiteEnergy hv' hb' hl' hT _ ht
      (equivDrift_smooth _ hbs) (equivDrift_allDerivativesBounded _ hbs hB) μ u hu)
      (PropagatedFlux.Flow.source_energy_le hv' hb' hl' hT _ ht
      (equivDrift_smooth _ hbs) (equivDrift_allDerivativesBounded _ hbs hB) μ u hu)

/-- A genuine initial finite-energy distribution retains finite energy. -/
theorem distributionAt_finiteEnergy_and_energy_le
    (σ : Test (N*d) →ₗ[ℝ] ℝ) (hσ : FiniteEnergy μ σ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    FiniteEnergy (lawAt hv' hb' hl' hT μ t) (distributionAt hv' hb' hl' hT hbs hB μ σ t) ∧
      energy (lawAt hv' hb' hl' hT μ t) (distributionAt hv' hb' hl' hT hbs hB μ σ t) ≤
        Real.exp ((K':ℝ)*t)^2 * energy μ σ := by
  have hh := sourceAt_finiteEnergy_and_energy_le hv' hb' hl' hT hbs hB μ
    (representative μ σ : Lp (Point (N*d)) 2 μ) (Lp.memLp _) ht
  rwa [← energy_eq_integral μ σ hσ] at hh

/-- The propagated finite-energy distribution starts at exactly its initial source. -/
theorem distributionAt_zero (σ : Test (N*d) →ₗ[ℝ] ℝ) (hσ : FiniteEnergy μ σ) :
    distributionAt hv' hb' hl' hT hbs hB μ σ 0 = σ := by
  simpa only [distributionAt,sourceAt,projIcc_of_mem _ (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),
    PropagatedFlux.Flow.distribution] using
      PropagatedFlux.Flow.distribution_zero hv' hb' hl' hT (euclideanBrownianPathLaw d N T)
        (equivDrift_smooth _ hbs) (equivDrift_allDerivativesBounded _ hbs hB) μ
        (euclideanBrownianPathLaw_zero_ae hT) σ hσ

/-- Actual time integrability of every compact test pairing. -/
theorem distributionAt_intervalIntegrable (σ : Test (N*d) →ₗ[ℝ] ℝ) (φ : Test (N*d)) (s t : ℝ) :
    IntervalIntegrable (fun r => distributionAt hv' hb' hl' hT hbs hB μ σ r φ) volume s t :=
  sourceAt_intervalIntegrable hv' hb' hl' hT hbs hB μ _ (Lp.memLp _) φ s t

variable {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)

include hv hb hl in
/-- The constructed propagated finite-energy distribution solves the actual
homogeneous source equation for every compact smooth test. -/
theorem distributionAt_equation (σ : Test (N*d) →ₗ[ℝ] ℝ)
    (φ : Test (N*d)) {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    distributionAt hv' hb' hl' hT hbs hB μ σ t φ - distributionAt hv' hb' hl' hT hbs hB μ σ s φ =
      ∫ r in s..t,distributionAt hv' hb' hl' hT hbs hB μ σ r (euclideanGeneratorTest hbs φ) :=
  sourceAt_equation hv' hb' hl' hT hbs hB μ hv hb hl _ (Lp.memLp _) φ hs ht

end Brownian
end SharpWasserstein.PropagatedSourceEquation
