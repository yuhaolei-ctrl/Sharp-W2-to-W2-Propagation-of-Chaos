import SharpWasserstein.WeightedTangent
import SharpWasserstein.SmoothCutoff
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Actual dominated `L²` convergence for Euclidean vector fields, and its
application to membership in the closed space of compact smooth gradients.
The approximation hypothesis below is pointwise convergence of concrete
gradients with one uniform bound; it is verified by smooth cutoffs separately. -/

noncomputable section
namespace SharpWasserstein.WeightedTangent

open MeasureTheory Set Filter
open scoped InnerProductSpace Topology ContDiff

variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]
variable (μ : Measure (Point d)) [IsFiniteMeasure μ]

omit [BorelSpace (Point d)] in
/-- Uniformly bounded pointwise convergence of actual vector fields gives strong weighted `L²` convergence. -/
theorem tendsto_toLp_of_bounded_pointwise
    (fs : ℕ → Point d → Point d) (f : Point d → Point d)
    (hfs : ∀ n, MemLp (fs n) 2 μ) (hf : MemLp f 2 μ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ n x, ‖fs n x‖ ≤ C)
    (hfb : ∀ x, ‖f x‖ ≤ C) (hlim : ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hf.toLp f)) := by
  have hsq : Tendsto (fun n => ∫ x, ‖fs n x - f x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : Point d => (2 * C) ^ 2)
      (F := fun n x => ‖fs n x - f x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun n => ((hfs n).1.sub hf.1).norm.pow 2) (integrable_const _) ?_ ?_
    · simpa using h
    · intro n
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      exact (norm_sub_le _ _).trans (by linarith [hbound n x, hfb x])
    · filter_upwards [] with x
      simpa using ((hlim x).sub (tendsto_const_nhds (x := f x))).norm.pow 2
  have hnormsq (n : ℕ) : ‖(hfs n).toLp (fs n) - hf.toLp f‖ ^ 2 =
      ∫ x, ‖fs n x - f x‖ ^ 2 ∂μ := by
    rw [lp_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hfs n).toLp (fs n)) (hf.toLp f),
      (hfs n).coeFn_toLp, hf.coeFn_toLp] with x ha hb hc
    rw [ha]
    simp only [Pi.sub_apply, hb, hc]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, ← hnormsq, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

/-- Concrete uniformly bounded approximations by compact smooth gradients give actual tangent-space membership. -/
theorem mem_gradientClosure_of_bounded_gradient_approximation
    (g : Point d → Point d) (hg : MemLp g 2 μ) (φs : ℕ → Test d)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n x, ‖gradient ((φs n : Test d) : Point d → ℝ) x‖ ≤ C)
    (hgb : ∀ x, ‖g x‖ ≤ C)
    (hlim : ∀ x, Tendsto (fun n => gradient ((φs n : Test d) : Point d → ℝ) x)
      atTop (𝓝 (g x))) :
    hg.toLp g ∈ gradientClosure μ := by
  have ht := tendsto_toLp_of_bounded_pointwise μ
    (fun n => gradient ((φs n : Test d) : Point d → ℝ)) g
    (fun n => test_gradient_memLp μ (φs n)) hg hC hbound hgb hlim
  apply (testGradientLinear μ).range.isClosed_topologicalClosure.mem_of_tendsto ht
  filter_upwards [] with n
  exact (testGradientLinear μ).range.le_topologicalClosure (LinearMap.mem_range_self _ (φs n))

/-- A smooth bounded gradient is genuinely in weighted `L²` for every finite Borel weight. -/
theorem bounded_smooth_gradient_memLp (f : Point d → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfb : ∃ B : ℝ, ∀ x, ‖gradient f x‖ ≤ B) : MemLp (gradient f) 2 μ := by
  obtain ⟨B, hB⟩ := hfb
  have hc : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp (hf.continuous_fderiv (by simp))
  exact MemLp.of_bound hc.aestronglyMeasurable B (Eventually.of_forall hB)

/-- Explicit smooth cutoffs approximate the actual gradient of a bounded smooth function strongly in `L²`. -/
theorem exists_test_gradient_tendsto (f : Point d → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfa : ∃ A : ℝ, ∀ x, |f x| ≤ A) (hfb : ∃ B : ℝ, ∀ x, ‖gradient f x‖ ≤ B)
    (hg : MemLp (gradient f) 2 μ) :
    ∃ φs : ℕ → Test d, Tendsto (fun j => testGradient μ (φs j)) atTop
      (𝓝 (hg.toLp (gradient f))) := by
  obtain ⟨φs, C, hC, hbound, heq⟩ := SmoothCutoff.exists_test_approximation f hf hfa hfb
  have hgb (x : Point d) : ‖gradient f x‖ ≤ C := by
    obtain ⟨j, hj⟩ := (heq x).exists
    rw [← hj]
    exact hbound j x
  have hlim (x : Point d) : Tendsto (fun j => gradient ((φs j : Test d) : Point d → ℝ) x)
      atTop (𝓝 (gradient f x)) := tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (heq x))
  exact ⟨φs, tendsto_toLp_of_bounded_pointwise μ
    (fun j => gradient ((φs j : Test d) : Point d → ℝ)) (gradient f)
    (fun j => test_gradient_memLp μ (φs j)) hg hC hbound hgb hlim⟩

/-- Bounded smooth cylinder functions are admissible in the gradient closure, although not compactly supported. -/
theorem bounded_smooth_gradient_memClosure (f : Point d → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfa : ∃ A : ℝ, ∀ x, |f x| ≤ A) (hfb : ∃ B : ℝ, ∀ x, ‖gradient f x‖ ≤ B)
    (hg : MemLp (gradient f) 2 μ) : hg.toLp (gradient f) ∈ gradientClosure μ := by
  obtain ⟨φs, ht⟩ := exists_test_gradient_tendsto μ f hf hfa hfb hg
  apply (testGradientLinear μ).range.isClosed_topologicalClosure.mem_of_tendsto ht
  filter_upwards [] with j
  exact (testGradientLinear μ).range.le_topologicalClosure (LinearMap.mem_range_self _ (φs j))

end SharpWasserstein.WeightedTangent
