import SharpWasserstein.PeriodicConvolutionPDECalculus
import SharpWasserstein.PeriodicConvolutionPDEIntegral

/-! The strong smoothed Fokker–Planck equation is derived from the original
weak evolution. The density and flux are the actual convolution integrals;
the Laplacian coefficient, flattening, and divergence sign are exact. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ContDiff BigOperators BoundedContinuousFunction
namespace SharpWasserstein.PeriodicConvolution
open WeightedTangent PeriodicIntegrationByParts PeriodicPositiveKernel

variable {d N : ℕ}

theorem flattenedDrift_integrable (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {v : Configuration d N → Configuration d N} (hv : Continuous v) {M : ℝ}
    (hM : ∀ y,‖v y‖ ≤ M) :
    Integrable (flattenedDrift v) (μ.map (configurationFlatten d N)) := by
  letI : IsProbabilityMeasure (μ.map (configurationFlatten d N)) :=
    Measure.isProbabilityMeasure_map (configurationFlatten d N).measurable.aemeasurable
  apply Integrable.of_bound (flattenedDrift_continuous hv).aestronglyMeasurable
    (‖(flattenEquiv d N).toContinuousLinearMap‖*M)
  exact Eventually.of_forall fun x => ((flattenEquiv d N).toContinuousLinearMap.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))

/-- Exact identification of the integrated original generator with the
Laplacian of the smoothed density minus divergence of the smoothed drift flux. -/
theorem integral_generator_kernelTest_eq (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {v : Configuration d N → Configuration d N} (hv : Continuous v) {M : ℝ}
    (hM : ∀ y,‖v y‖ ≤ M) (κ : ℝ) (x : Coordinates (N*d)) :
    (∫ y,generator v (kernelTest κ x) y ∂μ) =
      PeriodicIntegrationByParts.laplacian (density κ (μ.map (configurationFlatten d N))) x-
        PeriodicDriftEnergy.divergence (flux κ (μ.map (configurationFlatten d N)) (flattenedDrift v)) x := by
  letI : IsProbabilityMeasure (μ.map (configurationFlatten d N)) :=
    Measure.isProbabilityMeasure_map (configurationFlatten d N).measurable.aemeasurable
  have hvI := flattenedDrift_integrable μ hv hM
  have hL := kernel_laplacian_integrable (μ.map (configurationFlatten d N)) κ x
  have hD := kernel_drift_integrable (μ.map (configurationFlatten d N)) κ hvI x
  have hm := integral_map (configurationFlatten d N).measurable.aemeasurable (hL.sub hD).aestronglyMeasurable
  simp only [Pi.sub_apply] at hm
  rw [laplacian_density,divergence_flux _ κ hvI,← integral_sub hL hD,hm]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    simp only [generator_kernelTest,flattenedDrift_at_flatten]

/-- The exact commutator form of the smoothed spatial operator. This
algebraic identity also holds for nonperiodic C¹ drifts. -/
theorem integral_generator_kernelTest_eq_commutator
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {v : Configuration d N → Configuration d N} (hv : ContDiff ℝ 1 v) {M : ℝ}
    (hM : ∀ y,‖v y‖ ≤ M) (κ : ℝ) (x : Coordinates (N*d)) :
    (∫ y,generator v (kernelTest κ x) y ∂μ) =
      PeriodicIntegrationByParts.laplacian (density κ (μ.map (configurationFlatten d N))) x-
        PeriodicDriftEnergy.divergence
          (fun z => density κ (μ.map (configurationFlatten d N)) z • flattenedDrift v z) x-
        PeriodicDriftEnergy.divergence
          (commutator κ (μ.map (configurationFlatten d N)) (flattenedDrift v)) x := by
  letI : IsProbabilityMeasure (μ.map (configurationFlatten d N)) :=
    Measure.isProbabilityMeasure_map (configurationFlatten d N).measurable.aemeasurable
  rw [integral_generator_kernelTest_eq μ hv.continuous hM]
  rw [divergence_commutator κ _ (flattenedDrift_contDiff hv)
    (flattenedDrift_integrable μ hv.continuous hM)]
  ring

variable [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {v : ℝ → Configuration d N → Configuration d N} {P : ℝ → Measure (Configuration d N)}

/-- The derivative already proved in the bounded continuous function norm is
exactly the genuine smoothed Fokker–Planck spatial operator. -/
theorem evolutionGeneratorBCF_eq_laplacian_sub_divergence (h : WeakEvolution v P)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t y,‖v t y‖ ≤ M)
    (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) (x : Point (N*d)) :
    evolutionGeneratorBCF h hvC hv hM κ t x =
      PeriodicIntegrationByParts.laplacian (evolutionDensity κ P t) (WithLp.ofLp x)-
        PeriodicDriftEnergy.divergence
          (flux κ ((P t).map (configurationFlatten d N)) (flattenedDrift (v t))) (WithLp.ofLp x) := by
  letI := h.probability t ht
  rw [evolutionGeneratorBCF_apply,max_eq_right ht]
  exact integral_generator_kernelTest_eq (P t) (hv t).continuous (hM t) κ (WithLp.ofLp x)

/-- Pointwise strong PDE, including its one-sided initial-time interpretation,
is a theorem about the original weak law, not an imposed regularity premise. -/
theorem evolutionDensity_hasDerivWithinAt_pde (h : WeakEvolution v P)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t y,‖v t y‖ ≤ M)
    (κ : ℝ) (x : Coordinates (N*d)) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => evolutionDensity κ P s x)
      (PeriodicIntegrationByParts.laplacian (evolutionDensity κ P t) x-
        PeriodicDriftEnergy.divergence
          (flux κ ((P t).map (configurationFlatten d N)) (flattenedDrift (v t))) x) (Ici 0) t := by
  letI := h.probability t ht
  change HasDerivWithinAt (fun s => evolutionDensity κ P s x)
    (PeriodicIntegrationByParts.laplacian (density κ ((P t).map (configurationFlatten d N))) x-
      PeriodicDriftEnergy.divergence (flux κ ((P t).map (configurationFlatten d N)) (flattenedDrift (v t))) x) (Ici 0) t
  rw [← integral_generator_kernelTest_eq (P t) (hv t).continuous (hM t) κ x]
  exact evolutionDensity_hasDerivWithinAt h hvC hv hM κ x ht

theorem evolutionDensity_hasDerivAt_pde (h : WeakEvolution v P)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t y,‖v t y‖ ≤ M)
    (κ : ℝ) (x : Coordinates (N*d)) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => evolutionDensity κ P s x)
      (PeriodicIntegrationByParts.laplacian (evolutionDensity κ P t) x-
        PeriodicDriftEnergy.divergence
          (flux κ ((P t).map (configurationFlatten d N)) (flattenedDrift (v t))) x) t :=
  (evolutionDensity_hasDerivWithinAt_pde h hvC hv hM κ x ht.le).hasDerivAt (Ici_mem_nhds ht)

/-- Identification of the actual Banach-space derivative with diffusion,
transport by the original flattened drift, and the exact commutator error. -/
theorem evolutionGeneratorBCF_eq_commutator (h : WeakEvolution v P)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t y,‖v t y‖ ≤ M)
    (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) (hvt : ContDiff ℝ 1 (v t)) (x : Point (N*d)) :
    evolutionGeneratorBCF h hvC hv hM κ t x =
      PeriodicIntegrationByParts.laplacian (evolutionDensity κ P t) (WithLp.ofLp x)-
        PeriodicDriftEnergy.divergence
          (fun z => evolutionDensity κ P t z • flattenedDrift (v t) z) (WithLp.ofLp x)-
        PeriodicDriftEnergy.divergence
          (commutator κ ((P t).map (configurationFlatten d N)) (flattenedDrift (v t))) (WithLp.ofLp x) := by
  letI := h.probability t ht
  rw [evolutionGeneratorBCF_apply,max_eq_right ht]
  exact integral_generator_kernelTest_eq_commutator (P t) hvt (hM t) κ (WithLp.ofLp x)

end SharpWasserstein.PeriodicConvolution
