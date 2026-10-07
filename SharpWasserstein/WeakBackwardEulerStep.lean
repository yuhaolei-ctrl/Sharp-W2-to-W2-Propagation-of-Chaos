module

public import SharpWasserstein.Compat
public import SharpWasserstein.WeakEulerConsistency
public import SharpWasserstein.BackwardEulerIntegratedError

@[expose] public section

/-! Direct comparison of an arbitrary weak solution with the actual
Gaussian Euler step, uniformly over a bounded smooth test family. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ContDiff
namespace SharpWasserstein.WeakEvolution
open WeightedTangent NoiseAverage BackwardEuler
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Configuration d N → Configuration d N} {P : ℝ → Measure (Configuration d N)}
  (h : WeakEvolution (fun _ => b) P)
include h

theorem uniform_backward_step_error {K M : ℝ≥0} (hb : LipschitzWith K b)
    (hM : ∀ x, ‖b x‖ ≤ M) (T : ℝ) (L L₁ L₂ : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ≥0, (δ:ℝ) < η → ∀ s ∈ Icc 0 T, s+(δ:ℝ) ∈ Icc 0 T →
      ∀ φ : Configuration d N → ℝ, ContDiff ℝ ∞ φ → AllDerivativesBounded φ →
        LipschitzWith L φ → LipschitzWith L₁ (fderiv ℝ φ) →
        LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ)) →
        ‖(∫ x, φ x ∂P (s+δ))-(∫ x, step b δ φ x ∂P s)‖ ≤
          (δ:ℝ)*(ε+((N*d:ℕ)*(L₂:ℝ)+L₁*M)*
            ((M:ℝ)*δ+Real.sqrt (2*δ)*FrozenGaussian.noiseFirstMoment d N)) := by
  obtain ⟨η,hη,he⟩ := uniform_weak_step_error h hb hM T L L₁ L₂ hε
  refine ⟨η,hη,fun δ hδ s hs hst φ hφ hB hL hL₁ hL₂ => ?_⟩
  letI := h.probability s hs.1
  have hw := he s hs (s+δ) hst (by exact le_add_of_nonneg_right δ.coe_nonneg)
    (by simpa only [add_sub_cancel_left] using hδ) φ hφ hB hL hL₁ hL₂
  simp only [add_sub_cancel_left] at hw
  have hg := integral_step_error_bound hb hM hφ hB hL hL₁ hL₂ (P s) δ
  have halg : (∫ x, φ x ∂P (s+δ))-(∫ x, step b δ φ x ∂P s) =
      ((∫ x, φ x ∂P (s+δ))-(∫ x, φ x ∂P s)-(δ:ℝ)*(∫ x, generator b φ x ∂P s))-
      ((∫ x, step b δ φ x ∂P s)-(∫ x, φ x ∂P s)-(δ:ℝ)*(∫ x, generator b φ x ∂P s)) := by ring
  rw [halg]
  exact (norm_sub_le _ _).trans ((add_le_add hw hg).trans_eq (by ring))

end SharpWasserstein.WeakEvolution
