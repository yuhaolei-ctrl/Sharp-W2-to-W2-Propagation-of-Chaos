import SharpWasserstein.EulerWeakStep
import SharpWasserstein.EulerBrownianGridLaw
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Actual one-step weak expectation estimates along Gaussian Euler histories. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators
namespace SharpWasserstein

namespace EulerTimeWeak

def mean {d N : ℕ} (b : ℝ → Configuration d N → Configuration d N) (δ : ℝ≥0) :
    (j : ℕ) → GaussianHistory (Configuration d N) (N*d) j → Position (N*d) :=
  configurationEulerMean id (fun _ => b) δ

theorem mean_measurable {d N : ℕ} (b : ℝ → Configuration d N → Configuration d N) (hb : ∀ t, Measurable (b t))
    (δ : ℝ≥0) (j : ℕ) : Measurable (mean b δ j) :=
  configurationEulerMean_measurable id measurable_id (fun _ => b) (fun t => (hb t).comp measurable_snd) δ j

def law {d N : ℕ} (μ : Measure (Configuration d N))
    (b : ℝ → Configuration d N → Configuration d N) (hb : ∀ t, Measurable (b t)) (δ : ℝ≥0) (j : ℕ) :=
  gaussianHistoryLaw (gaussianInitialHistory (N*d) μ) (mean b δ) (mean_measurable b hb δ) (fun _ => 2*δ) j

instance law_probability {d N : ℕ} (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (b : ℝ → Configuration d N → Configuration d N) (hb : ∀ t, Measurable (b t)) (δ : ℝ≥0) (j : ℕ) :
    IsProbabilityMeasure (law μ b hb δ j) := by unfold law; infer_instance

def state {d N : ℕ} (j : ℕ) : GaussianHistory (Configuration d N) (N*d) j → Configuration d N :=
  configurationEulerObservation id j

theorem state_measurable {d N : ℕ} (j : ℕ) : Measurable (state (d := d) (N := N) j) :=
  configurationEulerObservation_measurable id measurable_id j

theorem mean_eq {d N : ℕ} (b : ℝ → Configuration d N → Configuration d N) (δ : ℝ≥0) (j : ℕ)
    (h : GaussianHistory (Configuration d N) (N*d) j) :
    mean b δ j h = configurationFlatten d N (state j h+(δ : ℝ)•b ((j : ℝ)*δ) (state j h)) := by
  simp only [mean, configurationEulerMean, eulerLabelHistoryMean, state,
    configurationEulerObservation, flattenedDrift, configurationFlatten_add, configurationFlatten_smul,
    MeasurableEquiv.apply_symm_apply]

theorem state_integrable {d N : ℕ} (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (b : ℝ → Configuration d N → Configuration d N) (hb : ∀ t, Measurable (b t)) (δ : ℝ≥0) (j : ℕ)
    {f : Configuration d N → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun h => f (state j h)) (law μ b hb δ j) := by
  obtain ⟨B,hB⟩ := (hc.isCompact_range hf).isBounded.exists_norm_le
  exact Integrable.of_bound (hf.measurable.comp (state_measurable j)).aestronglyMeasurable
    B (Eventually.of_forall fun h => hB _ (mem_range_self _))

def expectation {d N : ℕ} (μ : Measure (Configuration d N))
    (b : ℝ → Configuration d N → Configuration d N) (hb : ∀ t, Measurable (b t)) (δ : ℝ≥0) (j : ℕ)
    (f : Configuration d N → ℝ) : ℝ := ∫ h, f (state j h) ∂law μ b hb δ j

theorem expectation_succ {d N : ℕ} (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (b : ℝ → Configuration d N → Configuration d N) (hb : ∀ t, Measurable (b t)) (δ : ℝ≥0) (j : ℕ)
    {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) :
    expectation μ b hb δ (j+1) φ =
      ∫ h, FrozenGaussian.timeExpectation φ (state j h) (b ((j : ℝ)*δ) (state j h)) δ ∂law μ b hb δ j := by
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
      FrozenGaussian.timeExpectation φ (state j h) (b ((j : ℝ)*δ) (state j h)) δ
    rw [mean_eq]
    rw [← FrozenGaussian.integral_transitionLaw hφ.1.continuous (state j h) (b ((j : ℝ)*δ) (state j h)) δ]
    exact (integral_map (configurationFlatten d N).symm.measurable.aemeasurable hφ.1.continuous.aestronglyMeasurable).symm

theorem expectation_step_error {d N : ℕ} (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (b : ℝ → Configuration d N → Configuration d N) (hb : ∀ t, Continuous (b t)) (M : ℝ≥0)
    (hbound : ∀ t x, ‖b t x‖ ≤ M) {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) :
    ∃ C : ℝ≥0, ∀ (δ : ℝ≥0) (j : ℕ),
      ‖expectation μ b (fun t => (hb t).measurable) δ (j+1) φ - expectation μ b (fun t => (hb t).measurable) δ j φ -
        (δ : ℝ)*expectation μ b (fun t => (hb t).measurable) δ j (generator (b ((j : ℝ)*δ)) φ)‖ ≤
      (δ : ℝ)*C*((M : ℝ)*δ+Real.sqrt (2*δ)*FrozenGaussian.noiseFirstMoment d N) := by
  obtain ⟨C,hC⟩ := FrozenGaussian.step_error_bound hφ M
  refine ⟨C, ?_⟩
  intro δ j
  obtain ⟨B,_,hB⟩ := FrozenGaussian.compact_bound hφ
  have ht : Integrable (fun h => FrozenGaussian.timeExpectation φ (state j h) (b ((j : ℝ)*δ) (state j h)) δ)
      (law μ b (fun t => (hb t).measurable) δ j) :=
    Integrable.of_bound
      (FrozenGaussian.timeExpectation_comp_measurable hφ.1.continuous.measurable
        (state_measurable j) ((hb ((j : ℝ)*δ)).measurable.comp (state_measurable j)) δ).aestronglyMeasurable
      B (Eventually.of_forall fun h => FrozenGaussian.timeExpectation_norm_le hφ.1.continuous hφ.2 B hB _ _ _)
  have hi := state_integrable μ b (fun t => (hb t).measurable) δ j hφ.1.continuous hφ.2
  have hg := state_integrable μ b (fun t => (hb t).measurable) δ j (CompactGenerator.generator_continuous hφ (hb ((j : ℝ)*δ)))
    (CompactGenerator.generator_compact hφ (b ((j : ℝ)*δ)))
  have he : expectation μ b (fun t => (hb t).measurable) δ (j+1) φ - expectation μ b (fun t => (hb t).measurable) δ j φ -
        (δ : ℝ)*expectation μ b (fun t => (hb t).measurable) δ j (generator (b ((j : ℝ)*δ)) φ) =
      ∫ h, FrozenGaussian.timeExpectation φ (state j h) (b ((j : ℝ)*δ) (state j h)) δ - φ (state j h) -
        (δ : ℝ)*generator (b ((j : ℝ)*δ)) φ (state j h) ∂law μ b (fun t => (hb t).measurable) δ j := by
    have he' := integral_sub (ht.sub hi) (hg.const_mul (δ : ℝ))
    simp only [Pi.sub_apply] at he'
    rw [he', integral_sub ht hi, integral_const_mul, expectation_succ μ b (fun t => (hb t).measurable) δ j hφ]
    rfl
  rw [he]
  calc
    _ ≤ ∫ h, ‖FrozenGaussian.timeExpectation φ (state j h) (b ((j : ℝ)*δ) (state j h)) δ - φ (state j h) -
        (δ : ℝ)*generator (b ((j : ℝ)*δ)) φ (state j h)‖ ∂law μ b (fun t => (hb t).measurable) δ j := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : GaussianHistory (Configuration d N) (N*d) j,
        (δ : ℝ)*C*((M : ℝ)*δ+Real.sqrt (2*δ)*FrozenGaussian.noiseFirstMoment d N) ∂law μ b (fun t => (hb t).measurable) δ j :=
      integral_mono ((ht.sub hi).sub (hg.const_mul _)).norm (integrable_const _)
        (fun h => hC (state j h) (b ((j : ℝ)*δ) (state j h)) (hbound _ _) δ δ.coe_nonneg)
    _ = _ := by simp

end EulerTimeWeak
end SharpWasserstein
