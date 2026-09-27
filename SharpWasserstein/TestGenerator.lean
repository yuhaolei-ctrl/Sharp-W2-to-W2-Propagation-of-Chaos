import SharpWasserstein.BrownianParticle
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue

/-! Compact-test generator bounds and continuity for actual finite-horizon
particle laws. These analytic facts do not assert the still separate weak
evolution equation. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace SharpWasserstein
namespace CompactGenerator

theorem coordinate_test {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) (i : Fin N) (a : Fin d) :
    SmoothCompactTest (coordinateDerivative φ i a) := by
  refine ⟨?_, hφ.2.fderiv_apply ℝ (coordinateVector i a)⟩
  exact (hφ.1.fderiv_right (by simp)).clm_apply contDiff_const

theorem laplacian_test {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) : SmoothCompactTest (laplacian φ) := by
  constructor
  · apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro a _
    exact (coordinate_test (coordinate_test hφ i a) i a).1
  · have hc : HasCompactSupport (∑ i : Fin N, ∑ a : Fin d,
        coordinateDerivative (coordinateDerivative φ i a) i a) := by
      apply HasCompactSupport.finset_sum
      intro i _
      apply HasCompactSupport.finset_sum
      intro a _
      exact (coordinate_test (coordinate_test hφ i a) i a).2
    convert hc using 1
    ext x
    simp [laplacian, Finset.sum_apply]

theorem generator_continuous {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) {v : Configuration d N → Configuration d N} (hv : Continuous v) :
    Continuous (generator v φ) := by
  apply (laplacian_test hφ).1.continuous.add
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro a _
  exact ((continuous_apply a).comp ((continuous_apply i).comp hv)).mul (coordinate_test hφ i a).1.continuous

theorem generator_compact {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) (v : Configuration d N → Configuration d N) :
    HasCompactSupport (generator v φ) := by
  have hc : HasCompactSupport (∑ i : Fin N, ∑ a : Fin d,
      (fun x => v x i a) * coordinateDerivative φ i a) := by
    apply HasCompactSupport.finset_sum
    intro i _
    apply HasCompactSupport.finset_sum
    intro a _
    exact (coordinate_test hφ i a).2.mul_left
  have he : generator v φ = laplacian φ + ∑ i : Fin N, ∑ a : Fin d,
      (fun x => v x i a) * coordinateDerivative φ i a := by
    funext x
    simp [generator, Finset.sum_apply]
  rw [he]
  exact (laplacian_test hφ).2.add hc

/-- A genuinely compact continuous function is integrable under every finite law. -/
theorem integrable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {f : E → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (μ : Measure E) [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨C,hC⟩ := (hc.isCompact_range hf).isBounded.exists_norm_le
  exact Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hC _ (mem_range_self x))

/-- Narrowly continuous probability curves give continuous compact-test expectations. -/
theorem expectation_continuous {E I : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [TopologicalSpace I]
    {f : E → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    {P : I → ProbabilityMeasure E} (hP : Continuous P) :
    Continuous (fun t => ∫ x, f x ∂P t) := by
  let F : BoundedContinuousFunction E ℝ := ⟨⟨f,hf⟩, Metric.isBounded_range_iff.mp (hc.isCompact_range hf).isBounded⟩
  exact ProbabilityMeasure.continuous_iff_forall_continuous_integral.mp hP F

theorem generator_smooth {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) {v : Configuration d N → Configuration d N}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) : SmoothCompactTest (generator v φ) := by
  refine ⟨?_, generator_compact hφ v⟩
  apply (laplacian_test hφ).1.add
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro a _
  exact ((contDiff_apply ℝ ℝ a).comp ((contDiff_apply ℝ (Position d) i).comp hv)).mul
    (coordinate_test hφ i a).1

/-- Compact smooth tests have a proved global Lipschitz constant. -/
theorem test_lipschitz {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) : ∃ C : ℝ≥0, LipschitzWith C φ := by
  have hcont : Continuous (fderiv ℝ φ) := hφ.1.continuous_fderiv (by simp)
  obtain ⟨C,hC⟩ := ((hφ.2.fderiv ℝ).isCompact_range hcont).isBounded.exists_norm_le
  let D : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  refine ⟨D, lipschitzWith_of_nnnorm_fderiv_le (hφ.1.differentiable (by simp)) ?_⟩
  intro x
  change ‖fderiv ℝ φ x‖ ≤ max C 0
  exact (hC _ (mem_range_self x)).trans (le_max_left _ _)

theorem generator_lipschitz {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) {v : Configuration d N → Configuration d N}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) : ∃ C : ℝ≥0, LipschitzWith C (generator v φ) :=
  test_lipschitz (generator_smooth hφ hv)

end CompactGenerator
end SharpWasserstein
