import SharpWasserstein.QuantitativeGenerator
import SharpWasserstein.BoundedConfigurationTests
import SharpWasserstein.FrozenGaussianError

/-! Quantitative frozen Gaussian consistency for actual bounded smooth tests,
with an explicit coefficient determined by their first three derivatives. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators Interval ContDiff
namespace SharpWasserstein.FrozenGaussian
open GaussianSharpness NoiseAverage WeightedTangent
variable {d N : ℕ}

theorem timeExpectation_continuous_bounded {f : Configuration d N → ℝ}
    (hf : Continuous f) {A : ℝ} (hA : ∀ x, ‖f x‖ ≤ A) (x u : Configuration d N) :
    Continuous (timeExpectation f x u) := by
  letI := standardLabels_probability (N*d+1)
  have hc : Continuous (expectation f x u) := by
    apply continuous_of_dominated (bound := fun _ => A)
    · intro α
      exact (hf.comp (label_continuous x u α)).aestronglyMeasurable
    · intro α
      exact Eventually.of_forall fun z => hA _
    · exact integrable_const A
    · exact Eventually.of_forall fun z => hf.comp
        ((label_joint_continuous x u).comp (continuous_id.prodMk continuous_const))
  exact hc.comp (by fun_prop)

theorem timeExpectation_deviation_bounded {f : Configuration d N → ℝ}
    {A : ℝ} (hA : ∀ x, ‖f x‖ ≤ A) {C : ℝ≥0} (hL : LipschitzWith C f)
    (x u : Configuration d N) {t : ℝ} (ht : 0 ≤ t) :
    ‖timeExpectation f x u t-f x‖ ≤ (C:ℝ)*(t*‖u‖+Real.sqrt (2*t)*noiseFirstMoment d N) := by
  letI := standardLabels_probability (N*d+1)
  have hi : Integrable (fun z => f (label x u (Real.sqrt (2*t)) z)) (standardLabels (N*d+1)) :=
    Integrable.of_bound (hL.continuous.comp (label_continuous x u _)).aestronglyMeasurable A
      (Eventually.of_forall fun z => hA _)
  have hn := (label_displacement_integrable x u (Real.sqrt (2*t))).norm
  have he : timeExpectation f x u t-f x =
      ∫ z, f (label x u (Real.sqrt (2*t)) z)-f x ∂standardLabels (N*d+1) := by
    rw [integral_sub hi (integrable_const _), integral_const]
    simp [timeExpectation, expectation]
  rw [he]
  calc
    _ ≤ ∫ z, ‖f (label x u (Real.sqrt (2*t)) z)-f x‖ ∂standardLabels (N*d+1) := norm_integral_le_integral_norm _
    _ ≤ ∫ z, (C:ℝ)*‖label x u (Real.sqrt (2*t)) z-x‖ ∂standardLabels (N*d+1) :=
      integral_mono (hi.sub (integrable_const _)).norm (hn.const_mul _)
        (fun z => hL.norm_sub_le _ _)
    _ = (C:ℝ)*∫ z, ‖label x u (Real.sqrt (2*t)) z-x‖ ∂standardLabels (N*d+1) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (label_displacement_integral_le x u ht) C.coe_nonneg

variable [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]

/-- Explicit local Gaussian weak consistency, uniform over tests with the
stated derivative bounds and over all frozen drifts of norm at most M. -/
theorem step_error_bound_bounded {φ : Configuration d N → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hB : AllDerivativesBounded φ) {L L₁ L₂ M : ℝ≥0}
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    (hL₂ : LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ)))
    (x u : Configuration d N) (hu : ‖u‖ ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    ‖timeExpectation φ x u t-φ x-t*generator (fun _ => u) φ x‖ ≤
      t*((N*d:ℕ)*(L₂:ℝ)+L₁*M)*((M:ℝ)*t+Real.sqrt (2*t)*noiseFirstMoment d N) := by
  let G := generator (fun _ => u) φ
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hGL : LipschitzWith ((N*d:ℕ)*L₂+L₁*M) G := by
    simpa only [mul_zero, add_zero] using generator_lipschitz_of_derivatives hφ2 hL hL₁ hL₂
      (LipschitzWith.const u) (fun _ => hu)
  have hGn : ∀ z, ‖G z‖ ≤ (N*d:ℕ)*L₁+L*M :=
    generator_norm_le_of_derivatives hφ2 hL hL₁ (fun _ => hu)
  have hGc := timeExpectation_continuous_bounded hGL.continuous hGn x u
  have he : timeExpectation φ x u t-φ x-t*G x =
      ∫ s in 0..t, timeExpectation G x u s-G x := by
    rw [intervalIntegral.integral_sub (hGc.intervalIntegrable 0 t) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    rw [timeExpectation_sub_eq_integral_bounded_configuration hφ hB x u ht]
  rw [he]
  have hb : ∀ s ∈ Ι (0:ℝ) t, ‖timeExpectation G x u s-G x‖ ≤
      ((N*d:ℕ)*(L₂:ℝ)+L₁*M)*((M:ℝ)*t+Real.sqrt (2*t)*noiseFirstMoment d N) := by
    intro s hs
    rw [uIoc_of_le ht] at hs
    have hdev := timeExpectation_deviation_bounded hGn hGL x u hs.1.le
    apply hdev.trans
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add
    · calc s*‖u‖ ≤ s*(M:ℝ) := mul_le_mul_of_nonneg_left hu hs.1.le
           _ ≤ (M:ℝ)*t := by rw [mul_comm s]; exact mul_le_mul_of_nonneg_left hs.2 M.coe_nonneg
    · exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith [hs.2])) (noiseFirstMoment_nonneg d N)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa only [sub_zero, abs_of_nonneg ht, mul_assoc, mul_comm, mul_left_comm] using h

end SharpWasserstein.FrozenGaussian
