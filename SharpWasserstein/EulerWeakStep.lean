module

public import SharpWasserstein.Compat
public import SharpWasserstein.FrozenGaussianMeasurable
public import SharpWasserstein.EulerBrownianGridLaw
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-! Actual one-step weak expectation estimates along Gaussian Euler histories. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators
namespace SharpWasserstein

theorem gaussianHistory_integral_last {A : Type*} [MeasurableSpace A] {d : ℕ}
    (μ₀ : Measure (GaussianHistory A d 0)) [IsProbabilityMeasure μ₀]
    (a : (n : ℕ) → GaussianHistory A d n → Position d) (ha : ∀ n, Measurable (a n))
    (v : ℕ → ℝ≥0) (n : ℕ) (f : Position d → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ z, ‖f z‖ ≤ B) :
    (∫ h, f (h.2 (Fin.last n)) ∂gaussianHistoryLaw μ₀ a ha v (n+1)) =
      ∫ h, ∫ z, f z ∂gaussianVectorLaw (a n h) (v n) ∂gaussianHistoryLaw μ₀ a ha v n := by
  have hf' : Measurable (fun h : GaussianHistory A d (n+1) => f (h.2 (Fin.last n))) :=
    hf.comp ((measurable_pi_apply (Fin.last n)).comp measurable_snd)
  rw [gaussianHistoryLaw, integral_map (gaussianHistoryStepEquiv A d n).symm.measurable.aemeasurable hf'.aestronglyMeasurable]
  have he : (fun p : GaussianHistory A d n × Position d =>
      f (((gaussianHistoryStepEquiv A d n).symm p).2 (Fin.last n))) = fun p => f p.2 := by
    funext p
    exact congrArg f (congrArg Prod.snd ((gaussianHistoryStepEquiv A d n).apply_symm_apply p))
  rw [he]
  have hi : Integrable (fun p : GaussianHistory A d n × Position d => f p.2)
      ((gaussianHistoryLaw μ₀ a ha v n) ⊗ₘ gaussianVectorKernel (a n) (ha n) (v n)) :=
    Integrable.of_bound (hf.comp measurable_snd).aestronglyMeasurable B (Eventually.of_forall fun p => hB p.2)
  exact Measure.integral_compProd hi

namespace EulerWeak

def mean {d N : ℕ} (b : Configuration d N → Configuration d N) (δ : ℝ≥0) :
    (j : ℕ) → GaussianHistory (Configuration d N) (N*d) j → Position (N*d) :=
  configurationEulerMean id (fun _ _ => b) δ

theorem mean_measurable {d N : ℕ} (b : Configuration d N → Configuration d N) (hb : Measurable b)
    (δ : ℝ≥0) (j : ℕ) : Measurable (mean b δ j) :=
  configurationEulerMean_measurable id measurable_id (fun _ _ => b) (fun _ => hb.comp measurable_snd) δ j

def law {d N : ℕ} (μ : Measure (Configuration d N))
    (b : Configuration d N → Configuration d N) (hb : Measurable b) (δ : ℝ≥0) (j : ℕ) :=
  gaussianHistoryLaw (gaussianInitialHistory (N*d) μ) (mean b δ) (mean_measurable b hb δ) (fun _ => 2*δ) j

instance law_probability {d N : ℕ} (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (b : Configuration d N → Configuration d N) (hb : Measurable b) (δ : ℝ≥0) (j : ℕ) :
    IsProbabilityMeasure (law μ b hb δ j) := by unfold law; infer_instance

def state {d N : ℕ} (j : ℕ) : GaussianHistory (Configuration d N) (N*d) j → Configuration d N :=
  configurationEulerObservation id j

theorem state_measurable {d N : ℕ} (j : ℕ) : Measurable (state (d := d) (N := N) j) :=
  configurationEulerObservation_measurable id measurable_id j

theorem mean_eq {d N : ℕ} (b : Configuration d N → Configuration d N) (δ : ℝ≥0) (j : ℕ)
    (h : GaussianHistory (Configuration d N) (N*d) j) :
    mean b δ j h = configurationFlatten d N (state j h+(δ : ℝ)•b (state j h)) := by
  simp only [mean, configurationEulerMean, eulerLabelHistoryMean, state,
    configurationEulerObservation, flattenedDrift, configurationFlatten_add, configurationFlatten_smul,
    MeasurableEquiv.apply_symm_apply]

theorem state_integrable {d N : ℕ} (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (b : Configuration d N → Configuration d N) (hb : Measurable b) (δ : ℝ≥0) (j : ℕ)
    {f : Configuration d N → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun h => f (state j h)) (law μ b hb δ j) := by
  obtain ⟨B,hB⟩ := (hc.isCompact_range hf).isBounded.exists_norm_le
  exact Integrable.of_bound (hf.measurable.comp (state_measurable j)).aestronglyMeasurable
    B (Eventually.of_forall fun h => hB _ (mem_range_self _))

def expectation {d N : ℕ} (μ : Measure (Configuration d N))
    (b : Configuration d N → Configuration d N) (hb : Measurable b) (δ : ℝ≥0) (j : ℕ)
    (f : Configuration d N → ℝ) : ℝ := ∫ h, f (state j h) ∂law μ b hb δ j

theorem expectation_succ {d N : ℕ} (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (b : Configuration d N → Configuration d N) (hb : Measurable b) (δ : ℝ≥0) (j : ℕ)
    {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) :
    expectation μ b hb δ (j+1) φ =
      ∫ h, FrozenGaussian.timeExpectation φ (state j h) (b (state j h)) δ ∂law μ b hb δ j := by
  obtain ⟨B,_,hB⟩ := FrozenGaussian.compact_bound hφ
  have h := gaussianHistory_integral_last (gaussianInitialHistory (N*d) μ)
    (mean b δ) (mean_measurable b hb δ) (fun _ => 2*δ) j
    (fun z => φ ((configurationFlatten d N).symm z))
    (hφ.1.continuous.measurable.comp (configurationFlatten d N).symm.measurable) B (fun z => hB _)
  change expectation μ b hb δ (j+1) φ = _ at h
  rw [h]
  apply integral_congr_ae
  exact Eventually.of_forall fun h => by
    change (∫ z, φ ((configurationFlatten d N).symm z) ∂gaussianVectorLaw (mean b δ j h) (2*δ)) =
      FrozenGaussian.timeExpectation φ (state j h) (b (state j h)) δ
    rw [mean_eq]
    rw [← FrozenGaussian.integral_transitionLaw hφ.1.continuous (state j h) (b (state j h)) δ]
    exact (integral_map (configurationFlatten d N).symm.measurable.aemeasurable hφ.1.continuous.aestronglyMeasurable).symm

theorem expectation_step_error {d N : ℕ} (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (b : Configuration d N → Configuration d N) (hb : Continuous b) (M : ℝ≥0)
    (hbound : ∀ x, ‖b x‖ ≤ M) {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) :
    ∃ C : ℝ≥0, ∀ (δ : ℝ≥0) (j : ℕ),
      ‖expectation μ b hb.measurable δ (j+1) φ - expectation μ b hb.measurable δ j φ -
        (δ : ℝ)*expectation μ b hb.measurable δ j (generator b φ)‖ ≤
      (δ : ℝ)*C*((M : ℝ)*δ+Real.sqrt (2*δ)*FrozenGaussian.noiseFirstMoment d N) := by
  obtain ⟨C,hC⟩ := FrozenGaussian.step_error_bound hφ M
  refine ⟨C, ?_⟩
  intro δ j
  obtain ⟨B,_,hB⟩ := FrozenGaussian.compact_bound hφ
  have ht : Integrable (fun h => FrozenGaussian.timeExpectation φ (state j h) (b (state j h)) δ)
      (law μ b hb.measurable δ j) :=
    Integrable.of_bound
      (FrozenGaussian.timeExpectation_comp_measurable hφ.1.continuous.measurable
        (state_measurable j) (hb.measurable.comp (state_measurable j)) δ).aestronglyMeasurable
      B (Eventually.of_forall fun h => FrozenGaussian.timeExpectation_norm_le hφ.1.continuous hφ.2 B hB _ _ _)
  have hi := state_integrable μ b hb.measurable δ j hφ.1.continuous hφ.2
  have hg := state_integrable μ b hb.measurable δ j (CompactGenerator.generator_continuous hφ hb)
    (CompactGenerator.generator_compact hφ b)
  have he : expectation μ b hb.measurable δ (j+1) φ - expectation μ b hb.measurable δ j φ -
        (δ : ℝ)*expectation μ b hb.measurable δ j (generator b φ) =
      ∫ h, FrozenGaussian.timeExpectation φ (state j h) (b (state j h)) δ - φ (state j h) -
        (δ : ℝ)*generator b φ (state j h) ∂law μ b hb.measurable δ j := by
    have he' := integral_sub (ht.sub hi) (hg.const_mul (δ : ℝ))
    simp only [Pi.sub_apply] at he'
    rw [he', integral_sub ht hi, integral_const_mul, expectation_succ μ b hb.measurable δ j hφ]
    rfl
  rw [he]
  calc
    _ ≤ ∫ h, ‖FrozenGaussian.timeExpectation φ (state j h) (b (state j h)) δ - φ (state j h) -
        (δ : ℝ)*generator b φ (state j h)‖ ∂law μ b hb.measurable δ j := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : GaussianHistory (Configuration d N) (N*d) j,
        (δ : ℝ)*C*((M : ℝ)*δ+Real.sqrt (2*δ)*FrozenGaussian.noiseFirstMoment d N) ∂law μ b hb.measurable δ j :=
      integral_mono ((ht.sub hi).sub (hg.const_mul _)).norm (integrable_const _)
        (fun h => hC (state j h) (b (state j h)) (hbound _) δ δ.coe_nonneg)
    _ = _ := by simp

end EulerWeak
end SharpWasserstein
