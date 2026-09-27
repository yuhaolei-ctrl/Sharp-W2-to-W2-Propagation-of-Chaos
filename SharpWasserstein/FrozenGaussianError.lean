import SharpWasserstein.FrozenGeneratorBounds

/-! Quantitative frozen-step error from the actual finite Gaussian moment. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators Interval
namespace SharpWasserstein.FrozenGaussian
open GaussianSharpness

theorem noiseMap_memLp (d N : ℕ) : MemLp (noiseMap d N) 2 (standardLabels (N*d+1)) := by
  apply memLp_pi_iff.mpr
  intro i
  apply memLp_pi_iff.mpr
  intro a
  exact coordinate_memLp (N*d+1) (finProdFinEquiv (i,a)).succ

def noiseFirstMoment (d N : ℕ) : ℝ := ∫ ω, ‖noiseMap d N ω‖ ∂standardLabels (N*d+1)

theorem noiseFirstMoment_nonneg (d N : ℕ) : 0 ≤ noiseFirstMoment d N :=
  integral_nonneg fun _ => norm_nonneg _

theorem label_displacement_integrable {d N : ℕ} (x u : Configuration d N) (α : ℝ) :
    Integrable (fun ω => label x u α ω-x) (standardLabels (N*d+1)) := by
  letI := standardLabels_probability (N*d+1)
  have h := (integrable_const (x+(α^2/2)•u)).add
    ((noiseMap_memLp d N).integrable (by norm_num) |>.smul α)
  exact h.sub (integrable_const x)

theorem label_displacement_bound {d N : ℕ} (x u : Configuration d N) {t : ℝ} (ht : 0 ≤ t)
    (ω : Fin (N*d+1) → ℝ) :
    ‖label x u (Real.sqrt (2*t)) ω-x‖ ≤ t*‖u‖ + Real.sqrt (2*t)*‖noiseMap d N ω‖ := by
  have he : label x u (Real.sqrt (2*t)) ω-x = t•u + Real.sqrt (2*t)•noiseMap d N ω := by
    unfold label
    rw [Real.sq_sqrt (by positivity), mul_div_cancel_left₀ t (by norm_num : (2 : ℝ) ≠ 0)]
    abel
  rw [he]
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht,
    abs_of_nonneg (Real.sqrt_nonneg _)] using norm_add_le (t•u) (Real.sqrt (2*t)•noiseMap d N ω)

theorem label_displacement_integral_le {d N : ℕ} (x u : Configuration d N) {t : ℝ} (ht : 0 ≤ t) :
    (∫ ω, ‖label x u (Real.sqrt (2*t)) ω-x‖ ∂standardLabels (N*d+1)) ≤
      t*‖u‖ + Real.sqrt (2*t)*noiseFirstMoment d N := by
  letI := standardLabels_probability (N*d+1)
  have hn := ((noiseMap_memLp d N).integrable (by norm_num)).norm
  calc
    _ ≤ ∫ ω, t*‖u‖ + Real.sqrt (2*t)*‖noiseMap d N ω‖ ∂standardLabels (N*d+1) :=
      integral_mono (label_displacement_integrable x u _).norm
        ((integrable_const _).add (hn.const_mul _)) (label_displacement_bound x u ht)
    _ = _ := by rw [integral_add (integrable_const _) (hn.const_mul _), integral_const, integral_const_mul]; simp [noiseFirstMoment]

theorem timeExpectation_deviation {d N : ℕ} {f : Configuration d N → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) {C : ℝ≥0} (hL : LipschitzWith C f)
    (x u : Configuration d N) {t : ℝ} (ht : 0 ≤ t) :
    ‖timeExpectation f x u t-f x‖ ≤ (C : ℝ)*(t*‖u‖+Real.sqrt (2*t)*noiseFirstMoment d N) := by
  letI := standardLabels_probability (N*d+1)
  have hi := integrable_comp_label hf hc x u (Real.sqrt (2*t))
  have hn := (label_displacement_integrable x u (Real.sqrt (2*t))).norm
  have he : timeExpectation f x u t-f x =
      ∫ ω, f (label x u (Real.sqrt (2*t)) ω)-f x ∂standardLabels (N*d+1) := by
    rw [integral_sub hi (integrable_const _), integral_const]
    simp [timeExpectation, expectation]
  rw [he]
  calc
    _ ≤ ∫ ω, ‖f (label x u (Real.sqrt (2*t)) ω)-f x‖ ∂standardLabels (N*d+1) := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (C : ℝ)*‖label x u (Real.sqrt (2*t)) ω-x‖ ∂standardLabels (N*d+1) :=
      integral_mono (hi.sub (integrable_const _)).norm (hn.const_mul _)
        (fun ω => hL.norm_sub_le _ _)
    _ = (C : ℝ)*∫ ω, ‖label x u (Real.sqrt (2*t)) ω-x‖ ∂standardLabels (N*d+1) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (label_displacement_integral_le x u ht) C.coe_nonneg

/-- A quantitative local weak error uniform over all frozen drifts of size M. -/
theorem step_error_bound {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) (M : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (x u : Configuration d N), ‖u‖ ≤ M → ∀ t : ℝ, 0 ≤ t →
      ‖timeExpectation φ x u t - φ x - t*generator (fun _ => u) φ x‖ ≤
        t * C * ((M : ℝ)*t + Real.sqrt (2*t)*noiseFirstMoment d N) := by
  obtain ⟨C,hC⟩ := generator_uniform_lipschitz hφ M
  refine ⟨C, ?_⟩
  intro x u hu t ht
  let G := generator (fun _ => u) φ
  have hG := constant_generator_test hφ u
  have he : timeExpectation φ x u t - φ x - t*G x =
      ∫ s in 0..t, timeExpectation G x u s-G x := by
    rw [intervalIntegral.integral_sub ((timeExpectation_continuous hG x u).intervalIntegrable 0 t) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    rw [timeExpectation_sub_eq_integral hφ x u ht]
  rw [he]
  have hb : ∀ s ∈ Ι (0 : ℝ) t, ‖timeExpectation G x u s-G x‖ ≤
      (C : ℝ)*((M : ℝ)*t + Real.sqrt (2*t)*noiseFirstMoment d N) := by
    intro s hs
    rw [uIoc_of_le ht] at hs
    have hdev := timeExpectation_deviation hG.1.continuous hG.2 (hC u hu) x u hs.1.le
    apply hdev.trans
    apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
    apply add_le_add
    · calc s*‖u‖ ≤ s*(M : ℝ) := mul_le_mul_of_nonneg_left hu hs.1.le
           _ ≤ (M : ℝ)*t := by rw [mul_comm s]; exact mul_le_mul_of_nonneg_left hs.2 M.coe_nonneg
    · exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith [hs.2])) (noiseFirstMoment_nonneg d N)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa only [sub_zero, abs_of_nonneg ht, mul_assoc, mul_comm, mul_left_comm] using h

end SharpWasserstein.FrozenGaussian
