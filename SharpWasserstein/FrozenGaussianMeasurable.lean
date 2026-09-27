import SharpWasserstein.FrozenGaussianError

/-! Measurability and bounds for parameterized genuine frozen expectations. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal
namespace SharpWasserstein.FrozenGaussian
open GaussianSharpness

theorem timeExpectation_comp_measurable {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    {φ : Configuration d N → ℝ} (hφ : Measurable φ)
    {x u : Ω → Configuration d N} (hx : Measurable x) (hu : Measurable u) (t : ℝ) :
    Measurable (fun ω => timeExpectation φ (x ω) (u ω) t) := by
  letI := standardLabels_probability (N*d+1)
  have hm : Measurable (fun p : Ω × (Fin (N*d+1) → ℝ) =>
      φ (label (x p.1) (u p.1) (Real.sqrt (2*t)) p.2)) := by
    unfold label
    exact hφ.comp (((hx.comp measurable_fst).add ((hu.comp measurable_fst).const_smul ((Real.sqrt (2*t))^2/2))).add
      (((noiseMap d N).continuous.measurable.comp measurable_snd).const_smul (Real.sqrt (2*t))))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem timeExpectation_norm_le {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (B : ℝ) (hB : ∀ x, ‖φ x‖ ≤ B)
    (x u : Configuration d N) (t : ℝ) : ‖timeExpectation φ x u t‖ ≤ B := by
  letI := standardLabels_probability (N*d+1)
  calc
    _ ≤ ∫ ω, ‖φ (label x u (Real.sqrt (2*t)) ω)‖ ∂standardLabels (N*d+1) := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : Fin (N*d+1) → ℝ, B ∂standardLabels (N*d+1) :=
      integral_mono (integrable_comp_label hφ hc x u _).norm (integrable_const _) (fun ω => hB _)
    _ = B := by simp

end SharpWasserstein.FrozenGaussian
