import SharpWasserstein.BoundedWeakTests
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! Actual narrow continuity from compact-smooth tests and a uniform second moment.
The cutoff estimates are quantitative, so no weak topology assumption is hidden
in the construction of the probability-valued curve. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SharpWasserstein.WeakTestContinuity
open WeightedTangent SmoothCutoff
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

omit [MeasurableSpace (Point d)] [BorelSpace (Point d)] in
theorem cutoff_eq_one_of_norm_le (j : ℕ) (x : Point d) (hx : ‖x‖ ≤ (j : ℝ) + 1) :
    cutoff d j x = 1 := by
  apply (baseBump d).one_of_mem_closedBall
  change ‖((j : ℝ) + 1)⁻¹ • x - 0‖ ≤ 1
  rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity : 0 < (j : ℝ) + 1)]
  exact (inv_mul_le_one₀ (by positivity : 0 < (j : ℝ) + 1)).mpr hx

omit [MeasurableSpace (Point d)] [BorelSpace (Point d)] in
theorem cutoff_error_le_moment (f : Point d → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ x, |f x| ≤ A) (j : ℕ) (x : Point d) :
    |f x - cutoff d j x * f x| ≤ A / ((j : ℝ) + 1)^2 * ‖x‖^2 := by
  by_cases hx : ‖x‖ ≤ (j : ℝ) + 1
  · rw [cutoff_eq_one_of_norm_le j x hx, one_mul, sub_self, abs_zero]
    positivity
  · have hR : 0 < (j : ℝ) + 1 := by positivity
    have hxR : ((j : ℝ) + 1)^2 ≤ ‖x‖^2 :=
      (sq_le_sq₀ hR.le (norm_nonneg _)).mpr (le_of_not_ge hx)
    have hc0 := cutoff_nonneg d j x
    have hc1 : cutoff d j x ≤ 1 := (le_abs_self _).trans (cutoff_abs_le_one d j x)
    calc
      _ = |1 - cutoff d j x| * |f x| := by rw [← abs_mul]; congr 1; ring
      _ ≤ 1 * A := mul_le_mul (by rw [abs_of_nonneg (by linarith)]; linarith) (hf x)
        (abs_nonneg _) (by norm_num)
      _ ≤ _ := by
        rw [one_mul, div_mul_eq_mul_div]
        exact (le_div_iff₀ (sq_pos_of_pos hR)).mpr (mul_le_mul_of_nonneg_left hxR hA)

theorem integral_cutoff_error_le (μ : Measure (Point d)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Point d ↦ ‖x‖^2) μ)
    (f : Point d → ℝ) (hf : ContDiff ℝ ∞ f) {A : ℝ} (hA : 0 ≤ A)
    (hfa : ∀ x, |f x| ≤ A) (j : ℕ) :
    |(∫ x, f x ∂μ) - ∫ x, (approximate f hf j : Point d → ℝ) x ∂μ| ≤
      A / ((j : ℝ) + 1)^2 * ∫ x, ‖x‖^2 ∂μ := by
  have hfi : Integrable f μ := Integrable.of_bound hf.continuous.aestronglyMeasurable A
    (Filter.Eventually.of_forall fun x ↦ hfa x)
  have hgi : Integrable (approximate f hf j : Point d → ℝ) μ :=
    Integrable.of_bound (approximate f hf j).property.1.continuous.aestronglyMeasurable A
      (Filter.Eventually.of_forall fun x ↦ approximate_abs_bound f hf hfa j x)
  rw [← integral_sub hfi hgi]
  have h := norm_integral_le_of_norm_le
    (f := fun x ↦ f x - (approximate f hf j : Point d → ℝ) x) (hμ.const_mul (A / ((j : ℝ) + 1)^2))
    (Filter.Eventually.of_forall fun x ↦ cutoff_error_le_moment f hA hfa j x)
  simpa only [Real.norm_eq_abs, integral_const_mul] using h

variable {ι : Type*} [TopologicalSpace ι]

/-- A uniform second moment turns the compact cutoff approximation into a
uniform approximation of actual integrals over the entire family of laws. -/
theorem continuous_integral_smooth_of_uniformMoment
    (μ : ι → Measure (Point d)) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable (fun x : Point d ↦ ‖x‖^2) (μ i)) {C : ℝ}
    (hC : ∀ i, (∫ x, ‖x‖^2 ∂μ i) ≤ C)
    (hc : ∀ φ : Test d, Continuous (fun i ↦ ∫ x, (φ : Point d → ℝ) x ∂μ i))
    (f : Point d → ℝ) (hf : ContDiff ℝ ∞ f) {A : ℝ} (hA : 0 ≤ A)
    (hfa : ∀ x, |f x| ≤ A) : Continuous (fun i ↦ ∫ x, f x ∂μ i) := by
  have ht : Tendsto (fun j : ℕ ↦ A * C * (1 / ((j : ℝ) + 1))^2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.pow 2).const_mul (A * C)
  have hu : TendstoUniformly (fun j i ↦ ∫ x, (approximate f hf j : Point d → ℝ) x ∂μ i)
      (fun i ↦ ∫ x, f x ∂μ i) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [ht.eventually_lt_const hε] with j hj
    intro i
    rw [Real.dist_eq]
    apply lt_of_le_of_lt (integral_cutoff_error_le (μ i) (hμ i) f hf hA hfa j) ?_
    have h := mul_le_mul_of_nonneg_left (hC i) (by positivity : 0 ≤ A / ((j : ℝ) + 1)^2)
    apply lt_of_le_of_lt h
    simpa only [div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow, mul_assoc, mul_comm, mul_left_comm] using hj
  exact hu.continuous (Filter.Eventually.of_forall fun j ↦ hc (approximate f hf j)).frequently

/-- The extension reaches every bounded Lipschitz observable, by genuine smooth
convolution approximation followed by the already justified compact cutoffs. -/
theorem continuous_integral_lipschitz_of_uniformMoment
    (μ : ι → Measure (Point d)) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable (fun x : Point d ↦ ‖x‖^2) (μ i)) {C : ℝ}
    (hC : ∀ i, (∫ x, ‖x‖^2 ∂μ i) ≤ C)
    (hc : ∀ φ : Test d, Continuous (fun i ↦ ∫ x, (φ : Point d → ℝ) x ∂μ i))
    (f : Point d → ℝ) {A : ℝ} (hA : 0 ≤ A) (hfa : ∀ x, |f x| ≤ A)
    {L : ℝ≥0} (hf : LipschitzWith L f) : Continuous (fun i ↦ ∫ x, f x ∂μ i) := by
  apply continuous_of_uniform_approx_of_continuous
  intro u hu
  obtain ⟨ε, hε, he⟩ := Metric.mem_uniformity_dist.mp hu
  obtain ⟨g, hg, hgf⟩ := hf.uniformContinuous.exists_contDiff_dist_le (half_pos hε)
  have hga (x : Point d) : |g x| ≤ A + ε / 2 := by
    have h := norm_add_le (g x - f x) (f x)
    have hd := hgf x
    rw [Real.dist_eq] at hd
    simp only [sub_add_cancel, Real.norm_eq_abs] at h
    linarith [hfa x]
  refine ⟨fun i ↦ ∫ x, g x ∂μ i,
    continuous_integral_smooth_of_uniformMoment μ hμ hC hc g hg (by positivity) hga, ?_⟩
  intro i
  apply he
  rw [Real.dist_eq, ← integral_sub
    (Integrable.of_bound hf.continuous.aestronglyMeasurable A (Filter.Eventually.of_forall hfa))
    (Integrable.of_bound hg.continuous.aestronglyMeasurable (A + ε/2) (Filter.Eventually.of_forall hga))]
  have hh : ‖∫ x, f x - g x ∂μ i‖ ≤ ε/2 := by
    simpa using norm_integral_le_of_norm_le_const (μ := μ i)
      (f := fun x ↦ f x - g x) (C := ε/2)
      (Filter.Eventually.of_forall fun x ↦ by
        simpa only [Real.norm_eq_abs, Real.dist_eq, abs_sub_comm] using (hgf x).le)
  exact hh.trans_lt (half_lt_self hε)

/-- Narrow continuity is a conclusion of the compact-test and moment hypotheses. -/
theorem continuous_probabilityMeasure_of_uniformMoment
    [FirstCountableTopology ι] (μ : ι → ProbabilityMeasure (Point d))
    (hμ : ∀ i, Integrable (fun x : Point d ↦ ‖x‖^2) (μ i : Measure (Point d))) {C : ℝ}
    (hC : ∀ i, (∫ x, ‖x‖^2 ∂(μ i : Measure (Point d))) ≤ C)
    (hc : ∀ φ : Test d, Continuous (fun i ↦ ∫ x, (φ : Point d → ℝ) x ∂(μ i : Measure (Point d)))) :
    Continuous μ := by
  apply continuous_iff_continuousAt.mpr
  intro i
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro f ⟨A, hA⟩ ⟨L, hf⟩
  have hbound (x : Point d) : |f x| ≤ A + |f 0| := by
    have h := norm_add_le (f x - f 0) (f 0)
    simp only [sub_add_cancel, Real.norm_eq_abs] at h
    have hd := hA x 0
    rw [Real.dist_eq] at hd
    linarith
  exact (continuous_integral_lipschitz_of_uniformMoment (fun i ↦ (μ i : Measure (Point d)))
    hμ hC hc f ((abs_nonneg _).trans (hbound 0)) hbound hf).continuousAt

end SharpWasserstein.WeakTestContinuity
