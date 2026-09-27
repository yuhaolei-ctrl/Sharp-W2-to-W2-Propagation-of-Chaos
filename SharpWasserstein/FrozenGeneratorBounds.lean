import SharpWasserstein.FrozenGaussianLaw

/-! Uniform Lipschitz control of the frozen generators, obtained from genuine
bounded derivatives of compact smooth tests. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal BigOperators
namespace SharpWasserstein.FrozenGaussian

theorem generator_uniform_lipschitz {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) (M : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ u : Configuration d N, ‖u‖ ≤ M →
      LipschitzWith C (generator (fun _ => u) φ) := by
  obtain ⟨C₀,h₀⟩ := CompactGenerator.test_lipschitz (CompactGenerator.laplacian_test hφ)
  choose C hC using fun i : Fin N => fun a : Fin d =>
    CompactGenerator.test_lipschitz (CompactGenerator.coordinate_test hφ i a)
  refine ⟨C₀ + M * (∑ i, ∑ a, C i a), ?_⟩
  intro u hu
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [dist_eq_norm, dist_eq_norm]
  have hi (i : Fin N) (a : Fin d) :
      ‖u i a * (coordinateDerivative φ i a y-coordinateDerivative φ i a z)‖ ≤
        (M : ℝ) * (C i a : ℝ) * ‖y-z‖ := by
    have hua : ‖u i a‖ ≤ (M : ℝ) := ((norm_le_pi_norm (u i) a).trans (norm_le_pi_norm u i)).trans hu
    rw [norm_mul]
    calc
      _ ≤ (M : ℝ) * ((C i a : ℝ) * ‖y-z‖) :=
        mul_le_mul hua ((hC i a).norm_sub_le y z) (norm_nonneg _) M.coe_nonneg
      _ = _ := by ring
  have he : generator (fun _ => u) φ y - generator (fun _ => u) φ z =
      (laplacian φ y-laplacian φ z) + ∑ i, ∑ a,
        u i a * (coordinateDerivative φ i a y-coordinateDerivative φ i a z) := by
    simp only [generator, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [he]
  calc
    _ ≤ ‖laplacian φ y-laplacian φ z‖ + ∑ i, ∑ a,
        ‖u i a * (coordinateDerivative φ i a y-coordinateDerivative φ i a z)‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)))
    _ ≤ (C₀ : ℝ)*‖y-z‖ + ∑ i, ∑ a, (M : ℝ)*(C i a : ℝ)*‖y-z‖ :=
      add_le_add (h₀.norm_sub_le y z) (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ => hi i a)
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_sum,
      add_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]

end SharpWasserstein.FrozenGaussian
