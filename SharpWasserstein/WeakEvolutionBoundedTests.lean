import SharpWasserstein.WeakEvolutionContinuity
import SharpWasserstein.ConfigurationGeneratorEuclidean

/-! Extension of the actual `WeakEvolution.equation` to bounded smooth tests
with bounded gradient and Laplacian. Both spatial and temporal cutoff limits
are proved directly. No occupation measure or extended weak equation is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff InnerProductSpace Interval
namespace SharpWasserstein
open WeightedTangent SmoothCutoff
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]

omit [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))] in
theorem generator_pullback_norm_le (f : Point (N*d) → ℝ)
    (v : Configuration d N → Configuration d N) {M B D : ℝ}
    (hv : ∀ x, ‖configurationEuclidean d N (v x)‖ ≤ M)
    (hB : ∀ x, ‖gradient f x‖ ≤ B) (hD : ∀ x, |PDEPairings.laplacian f x| ≤ D)
    (x : Configuration d N) :
    ‖generator v (f ∘ configurationEuclidean d N) x‖ ≤ D + M * B := by
  rw [generator_pullback]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact hD _
  · exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
      (mul_le_mul (hv x) (hB _) (norm_nonneg _) ((norm_nonneg _).trans (hv x)))

omit [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))] in
theorem integral_generator_pullback_norm_le (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (f : Point (N*d) → ℝ) (v : Configuration d N → Configuration d N) {M B D : ℝ}
    (hv : ∀ x, ‖configurationEuclidean d N (v x)‖ ≤ M)
    (hB : ∀ x, ‖gradient f x‖ ≤ B) (hD : ∀ x, |PDEPairings.laplacian f x| ≤ D) :
    ‖∫ x, generator v (f ∘ configurationEuclidean d N) x ∂μ‖ ≤ D + M * B := by
  simpa using norm_integral_le_of_norm_le_const (μ := μ)
    (f := generator v (f ∘ configurationEuclidean d N))
    (Filter.Eventually.of_forall (generator_pullback_norm_le f v hv hB hD))

theorem integrable_generator_pullback (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (f : Point (N*d) → ℝ) (hf : ContDiff ℝ ∞ f)
    (v : Configuration d N → Configuration d N) (hv : Measurable v) {M B D : ℝ}
    (hM : ∀ x, ‖configurationEuclidean d N (v x)‖ ≤ M)
    (hB : ∀ x, ‖gradient f x‖ ≤ B) (hD : ∀ x, |PDEPairings.laplacian f x| ≤ D) :
    Integrable (generator v (f ∘ configurationEuclidean d N)) μ := by
  have hvint : Integrable (fun x ↦ configurationEuclidean d N (v x)) μ :=
    Integrable.of_bound ((configurationEuclidean d N).continuous.measurable.comp hv).aestronglyMeasurable M
      (Filter.Eventually.of_forall hM)
  have hh := BoundedWeakTests.integrable_generator μ (configurationEuclidean d N)
    (fun x ↦ configurationEuclidean d N (v x)) (by fun_prop) hvint f hf hB hD
  change Integrable (fun x ↦ generator v (f ∘ configurationEuclidean d N) x) μ
  simpa only [generator_pullback] using hh

namespace WeakEvolution
variable {v : ℝ → Configuration d N → Configuration d N}
  {P : ℝ → Measure (Configuration d N)} (h : WeakEvolution v P)

include h in
/-- Temporal integrability and the genuine weak equation extend to bounded
smooth tests. The only drift inputs are actual spatial measurability and a
uniform bound on its Euclidean norm on nonnegative times. -/
theorem equation_bounded_smooth
    (hv : ∀ s, 0 ≤ s → Measurable (v s)) {M : ℝ}
    (hM : ∀ s, 0 ≤ s → ∀ x, ‖configurationEuclidean d N (v s x)‖ ≤ M)
    (f : Point (N*d) → ℝ) (hf : ContDiff ℝ ∞ f) {A B D : ℝ}
    (hfa : ∀ x, |f x| ≤ A) (hfb : ∀ x, ‖gradient f x‖ ≤ B)
    (hfd : ∀ x, |PDEPairings.laplacian f x| ≤ D) (t : ℝ) (ht : 0 ≤ t) :
    IntervalIntegrable (fun s ↦ ∫ x, generator (v s) (f ∘ configurationEuclidean d N) x ∂P s) volume 0 t ∧
    (∫ x, f (configurationEuclidean d N x) ∂P t) -
        (∫ x, f (configurationEuclidean d N x) ∂P 0) =
      ∫ s in 0..t, ∫ x, generator (v s) (f ∘ configurationEuclidean d N) x ∂P s := by
  let F (j : ℕ) (s : ℝ) :=
    ∫ x, generator (v s) ((approximate f hf j : Point (N*d) → ℝ) ∘ configurationEuclidean d N) x ∂P s
  let G (s : ℝ) := ∫ x, generator (v s) (f ∘ configurationEuclidean d N) x ∂P s
  have hA : 0 ≤ A := (abs_nonneg (f 0)).trans (hfa 0)
  let Cg := B + A * (baseLipschitzConstant (N*d) : ℝ)
  let Cd := D + A * ((N*d : ℕ) * (baseHessianConstant (N*d) : ℝ)) +
    2 * (baseLipschitzConstant (N*d) : ℝ) * B
  have hFi (j : ℕ) : IntervalIntegrable (F j) volume 0 t :=
    h.timeIntegrable _ (smoothCompactTest_pullback (approximate f hf j)) t ht
  have hFm (j : ℕ) : AEStronglyMeasurable (F j) (volume.restrict (Ioc 0 t)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp (hFi j)).aestronglyMeasurable
  have hlim (s : ℝ) (hs : 0 ≤ s) : Tendsto (fun j ↦ F j s) atTop (𝓝 (G s)) := by
    letI := h.probability s hs
    have hvint : Integrable (fun x ↦ configurationEuclidean d N (v s x)) (P s) :=
      Integrable.of_bound ((configurationEuclidean d N).continuous.measurable.comp (hv s hs)).aestronglyMeasurable M
        (Filter.Eventually.of_forall (hM s hs))
    have hh := BoundedWeakTests.tendsto_integral_generator_approximate (P s)
      (configurationEuclidean d N) (fun x ↦ configurationEuclidean d N (v s x))
      (by fun_prop) hvint f hf hfa hfb hfd
    simpa only [F, G, generator_pullback] using hh
  have hbound (j : ℕ) (s : ℝ) (hs : 0 ≤ s) : ‖F j s‖ ≤ Cd + M * Cg := by
    letI := h.probability s hs
    exact integral_generator_pullback_norm_le (P s) (approximate f hf j) (v s)
      (hM s hs) (approximate_gradient_bound f hf hA hfa hfb j)
      (approximate_laplacian_bound f hf hA hfa hfb hfd j)
  have hae : ∀ᵐ s ∂volume.restrict (Ioc 0 t), Tendsto (fun j ↦ F j s) atTop (𝓝 (G s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hlim s hs.1.le
  have hGm := aestronglyMeasurable_of_tendsto_ae atTop hFm hae
  have hGi : Integrable G (volume.restrict (Ioc 0 t)) :=
    Integrable.of_bound hGm (Cd + M * Cg) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact le_of_tendsto (hlim s hs.1.le).norm (Filter.Eventually.of_forall fun j ↦ hbound j s hs.1.le))
  have htime : Tendsto (fun j ↦ ∫ s in 0..t, F j s) atTop (𝓝 (∫ s in 0..t, G s)) := by
    simp only [intervalIntegral.integral_of_le ht]
    exact tendsto_integral_of_dominated_convergence (fun _ ↦ Cd + M * Cg) hFm (integrable_const _)
      (fun j ↦ by filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs; exact hbound j s hs.1.le) hae
  have hval (s : ℝ) (hs : 0 ≤ s) :
      Tendsto (fun j ↦ ∫ x, (approximate f hf j : Point (N*d) → ℝ) (configurationEuclidean d N x) ∂P s)
        atTop (𝓝 (∫ x, f (configurationEuclidean d N x) ∂P s)) := by
    letI := h.probability s hs
    simpa only [integral_euclideanLaw] using
      BoundedWeakTests.tendsto_integral_approximate (euclideanLaw (P s)) f hf hfa
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr hGi, ?_⟩
  apply tendsto_nhds_unique ((hval t ht).sub (hval 0 le_rfl))
  apply htime.congr'
  filter_upwards [] with j
  exact (h.equation _ (smoothCompactTest_pullback (approximate f hf j)) t ht).symm

end WeakEvolution
end SharpWasserstein
