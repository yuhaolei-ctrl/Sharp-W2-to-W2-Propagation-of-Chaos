module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicConvolutionDensity
public import SharpWasserstein.WeakTimeEulerConsistency
public import SharpWasserstein.BrownianForwardDerivative
public import SharpWasserstein.FlattenedEuclidean

@[expose] public section

/-! Genuine time derivatives of product-periodic convolution densities of
actual weak evolutions. The time continuity of generator expectations follows
from the proved narrow-law/drift continuity theorem, rather than from an
assumed temporal modulus or a presumed differentiated equation. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal ContDiff Interval
namespace SharpWasserstein
open WeightedTangent NoiseAverage

namespace WeakEvolution
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {v : ℝ → Configuration d N → Configuration d N} {P : ℝ → Measure (Configuration d N)}

theorem bounded_generatorExpectation_uniformContinuousOn (h : WeakEvolution v P)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t x,‖v t x‖ ≤ M)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hB : AllDerivativesBounded φ) (T : ℝ) :
    UniformContinuousOn (fun t => ∫ x,generator (v t) φ x ∂P t) (Icc 0 T) := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ φ) := (contDiff_infty_iff_fderiv.mp hφ).2
  have hddf : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ φ)) := (contDiff_infty_iff_fderiv.mp hdf).2
  obtain ⟨L,hL⟩ := hB.lipschitz (hφ.differentiable (by simp))
  obtain ⟨L₁,hL₁⟩ := hB.fderiv.lipschitz (hdf.differentiable (by simp))
  obtain ⟨L₂,hL₂⟩ := hB.fderiv.fderiv.lipschitz (hddf.differentiable (by simp))
  apply Metric.uniformContinuousOn_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := uniform_time_generator_expectation h hvC hv hM T L L₁ L₂ hε
  refine ⟨δ,hδ,fun s hs t ht hst => ?_⟩
  rw [dist_eq_norm]
  exact hd s hs t ht hst φ
    (hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hL hL₁ hL₂

theorem bounded_generatorExpectation_continuousOn (h : WeakEvolution v P)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t x,‖v t x‖ ≤ M)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hB : AllDerivativesBounded φ) :
    ContinuousOn (fun t => ∫ x,generator (v t) φ x ∂P t) (Ici 0) := by
  intro t ht
  have hc := (bounded_generatorExpectation_uniformContinuousOn h hvC hv hM hφ hB (t+1)).continuousOn
    t (show t ∈ Icc 0 (t+1) from ⟨ht,by linarith⟩)
  apply hc.mono_of_mem_nhdsWithin
  rw [← Ici_inter_Iic]
  exact inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iic_mem_nhds (by linarith : t < t+1)))

/-- The bounded-configuration weak equation has a genuine right derivative
at zero and an ordinary derivative at every positive time. -/
theorem hasDerivWithinAt_bounded_configuration (h : WeakEvolution v P)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t x,‖v t x‖ ≤ M)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hB : AllDerivativesBounded φ)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => ∫ x,φ x ∂P s)
      (∫ x,generator (v t) φ x ∂P t) (Ici 0) t := by
  apply hasDerivWithinAt_nonneg_of_integral_eq
    (bounded_generatorExpectation_continuousOn h hvC hv hM hφ hB) ?_ ht
  intro s hs
  exact (equation_time_bounded_configuration_interval h hv hM hφ hB (le_refl 0) hs).2

end WeakEvolution
namespace PeriodicConvolution
open PeriodicIntegrationByParts PeriodicPositiveKernel

/-- Actual flattening as a continuous linear map, with no coordinate scaling. -/
def flattenCLM (d N : ℕ) : Configuration d N →L[ℝ] Coordinates (N*d) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (N*d) => ℝ)).toContinuousLinearMap.comp
    (configurationEuclidean d N).toContinuousLinearMap

theorem flattenCLM_apply {d N : ℕ} (y : Configuration d N) :
    flattenCLM d N y = configurationFlatten d N y :=
  (configurationFlatten_eq_euclidean y).symm

/-- The genuine translated kernel used as a bounded test of the weak law. -/
def kernelTest {d N : ℕ} (κ : ℝ) (x : Coordinates (N*d)) (y : Configuration d N) : ℝ :=
  kernel κ (x-configurationFlatten d N y)

theorem kernelTest_smooth {d N : ℕ} (κ : ℝ) (x : Coordinates (N*d)) :
    ContDiff ℝ ∞ (kernelTest κ x) := by
  have he : kernelTest κ x = kernel κ ∘ (fun y => x-flattenCLM d N y) := by
    funext y
    rw [Function.comp_apply,flattenCLM_apply]
    rfl
  rw [he]
  exact (kernel_smooth (N*d) κ).comp (contDiff_const.sub (flattenCLM d N).contDiff)

theorem kernelTest_derivatives_bounded {d N : ℕ} (κ : ℝ) (x : Coordinates (N*d)) :
    AllDerivativesBounded (kernelTest κ x) := by
  let a : Configuration d N → Coordinates (N*d) := fun y => x-flattenCLM d N y
  have ha : ContDiff ℝ ∞ a := contDiff_const.sub (flattenCLM d N).contDiff
  have hda : fderiv ℝ a = fun _ => -(flattenCLM d N) := by
    funext y
    convert ((hasFDerivAt_const x y).sub (flattenCLM d N).hasFDerivAt).fderiv using 1 <;>
      first | rfl | simp only [zero_sub]
  have he : kernelTest κ x = kernel κ ∘ a := by
    funext y
    simp only [kernelTest,Function.comp_def,a,flattenCLM_apply]
  rw [he]
  apply AllDerivativesBounded.comp_of_fderiv (kernel_smooth (N*d) κ) ha
    (kernel_derivatives_bounded (N*d) κ)
  rw [hda]
  exact allDerivativesBounded_const _

theorem density_flatten_eq_integral {d N : ℕ} (κ : ℝ) (μ : Measure (Configuration d N))
    (x : Coordinates (N*d)) :
    density κ (μ.map (configurationFlatten d N)) x = ∫ y,kernelTest κ x y ∂μ := by
  unfold density
  exact integral_map (configurationFlatten d N).measurable.aemeasurable
    ((kernel_smooth (N*d) κ).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable

/-- Actual time-dependent smoothed density, obtained from the given weak law
by the existing periodic product convolution construction. -/
def evolutionDensity {d N : ℕ} (κ : ℝ) (P : ℝ → Measure (Configuration d N))
    (t : ℝ) (x : Coordinates (N*d)) : ℝ :=
  density κ ((P t).map (configurationFlatten d N)) x

variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {v : ℝ → Configuration d N → Configuration d N} {P : ℝ → Measure (Configuration d N)}

/-- The genuine integrated generator equation for a periodic convolution
density holds for arbitrary weak laws, including singular laws. -/
theorem evolutionDensity_equation (h : WeakEvolution v P)
    {K M : ℝ≥0} (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t y,‖v t y‖ ≤ M)
    (κ : ℝ) (x : Coordinates (N*d)) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IntervalIntegrable (fun r => ∫ y,generator (v r) (kernelTest κ x) y ∂P r) volume s t ∧
      evolutionDensity κ P t x-evolutionDensity κ P s x =
        ∫ r in s..t,∫ y,generator (v r) (kernelTest κ x) y ∂P r := by
  simpa only [evolutionDensity,density_flatten_eq_integral] using
    WeakEvolution.equation_time_bounded_configuration_interval h hv hM
      (kernelTest_smooth κ x) (kernelTest_derivatives_bounded κ x) hs ht

/-- The pointwise generator expectation is continuous in time as a consequence
of the actual narrow weak law and the jointly continuous bounded drift. -/
theorem evolutionDensity_generator_continuousOn (h : WeakEvolution v P)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t y,‖v t y‖ ≤ M)
    (κ : ℝ) (x : Coordinates (N*d)) :
    ContinuousOn (fun t => ∫ y,generator (v t) (kernelTest κ x) y ∂P t) (Ici 0) :=
  WeakEvolution.bounded_generatorExpectation_continuousOn h hvC hv hM
    (kernelTest_smooth κ x) (kernelTest_derivatives_bounded κ x)

/-- The actual periodic convolution density has its claimed right time
derivative at every nonnegative time, including the initial time. -/
theorem evolutionDensity_hasDerivWithinAt (h : WeakEvolution v P)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t y,‖v t y‖ ≤ M)
    (κ : ℝ) (x : Coordinates (N*d)) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => evolutionDensity κ P s x)
      (∫ y,generator (v t) (kernelTest κ x) y ∂P t) (Ici 0) t := by
  simpa only [evolutionDensity,density_flatten_eq_integral] using
    WeakEvolution.hasDerivWithinAt_bounded_configuration h hvC hv hM
      (kernelTest_smooth κ x) (kernelTest_derivatives_bounded κ x) ht

/-- At positive times the density has an ordinary, two-sided time derivative. -/
theorem evolutionDensity_hasDerivAt (h : WeakEvolution v P)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t y,‖v t y‖ ≤ M)
    (κ : ℝ) (x : Coordinates (N*d)) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => evolutionDensity κ P s x)
      (∫ y,generator (v t) (kernelTest κ x) y ∂P t) t :=
  (evolutionDensity_hasDerivWithinAt h hvC hv hM κ x ht.le).hasDerivAt (Ici_mem_nhds ht)


/-- The true convolution density is jointly continuous in position and time
on the nonnegative evolution, extended constantly in time before zero. -/
theorem evolutionDensity_joint_continuous_nonnegExtension (h : WeakEvolution v P) (κ : ℝ) :
    Continuous (fun p : ℝ × Coordinates (N*d) => evolutionDensity κ P (max 0 p.1) p.2) := by
  have hc := continuous_integral_parameter_probability
    (fun p : ℝ × Coordinates (N*d) => WeakEvolution.probabilityCurve h p.1)
    ((WeakEvolution.continuous_probabilityCurve h).comp continuous_fst)
    (fun p : (ℝ × Coordinates (N*d)) × Configuration d N =>
      kernel κ (p.1.2-flattenCLM d N p.2))
    ((kernel_smooth (N*d) κ).continuous.comp
      ((continuous_snd.comp continuous_fst).sub ((flattenCLM d N).continuous.comp continuous_snd)))
    (C := (Real.exp |κ|/normalizer κ)^(N*d)) (fun p => by
      rw [Real.norm_eq_abs,abs_of_pos (kernel_pos κ _)]
      exact (kernel_bounds κ _).2)
  convert hc using 1 <;> try rfl
  funext p
  rw [evolutionDensity,density_flatten_eq_integral]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by dsimp only; rw [flattenCLM_apply]; rfl)

end PeriodicConvolution
end SharpWasserstein
