module

public import SharpWasserstein.Compat
public import SharpWasserstein.FrozenGeneratorBounds

@[expose] public section

/-! Joint continuity and uniform spatial bounds for the actual time-dependent
compact-test generator. No time derivative of the drift is required. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal BigOperators
namespace SharpWasserstein.CompactGenerator

theorem generator_joint_continuous {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) {v : ℝ → Configuration d N → Configuration d N}
    (hv : Continuous (Function.uncurry v)) :
    Continuous (fun p : ℝ × Configuration d N => generator (v p.1) φ p.2) := by
  apply ((laplacian_test hφ).1.continuous.comp continuous_snd).add
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro a _
  exact ((continuous_apply a).comp ((continuous_apply i).comp hv)).mul
    ((coordinate_test hφ i a).1.continuous.comp continuous_snd)

theorem generator_uniform_bound {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) (M : ℝ≥0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (v : Configuration d N → Configuration d N),
      (∀ x, ‖v x‖ ≤ M) → ∀ x, ‖generator v φ x‖ ≤ B := by
  obtain ⟨A,hA0,hA⟩ := FrozenGaussian.compact_bound (laplacian_test hφ)
  choose B hB0 hB using fun i : Fin N => fun a : Fin d =>
    FrozenGaussian.compact_bound (coordinate_test hφ i a)
  refine ⟨A + (M : ℝ) * ∑ i, ∑ a, B i a, add_nonneg hA0 (mul_nonneg M.coe_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => hB0 i a)), ?_⟩
  intro v hv x
  have hi (i : Fin N) (a : Fin d) :
      ‖v x i a * coordinateDerivative φ i a x‖ ≤ (M : ℝ)*B i a := by
    rw [norm_mul]
    exact mul_le_mul (((norm_le_pi_norm (v x i) a).trans (norm_le_pi_norm (v x) i)).trans (hv x))
      (hB i a x) (norm_nonneg _) M.coe_nonneg
  calc
    _ ≤ ‖laplacian φ x‖ + ∑ i, ∑ a, ‖v x i a * coordinateDerivative φ i a x‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)))
    _ ≤ A + ∑ i, ∑ a, (M : ℝ)*B i a :=
      add_le_add (hA x) (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ => hi i a)
    _ = _ := by simp only [Finset.mul_sum]

theorem generator_uniform_spatial_lipschitz {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) (M K : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (v : Configuration d N → Configuration d N),
      (∀ x, ‖v x‖ ≤ M) → LipschitzWith K v → LipschitzWith C (generator v φ) := by
  obtain ⟨C,hC⟩ := FrozenGaussian.generator_uniform_lipschitz hφ M
  choose B hB0 hB using fun i : Fin N => fun a : Fin d =>
    FrozenGaussian.compact_bound (coordinate_test hφ i a)
  let D : ℝ≥0 := NNReal.mk (∑ i, ∑ a, B i a) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => hB0 i a)
  refine ⟨C+K*D, ?_⟩
  intro v hv hLip
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm]
  have hi (i : Fin N) (a : Fin d) :
      ‖(v x i a-v y i a)*coordinateDerivative φ i a y‖ ≤ (K : ℝ)*‖x-y‖*B i a := by
    rw [norm_mul]
    apply mul_le_mul _ (hB i a y) (norm_nonneg _) (by positivity)
    exact ((norm_le_pi_norm ((v x-v y) i) a).trans (norm_le_pi_norm (v x-v y) i)).trans
      (hLip.norm_sub_le x y)
  have he : generator v φ x-generator v φ y =
      (generator (fun _ => v x) φ x-generator (fun _ => v x) φ y) +
        ∑ i, ∑ a, (v x i a-v y i a)*coordinateDerivative φ i a y := by
    simp only [generator,sub_mul,Finset.sum_sub_distrib]
    ring
  rw [he]
  calc
    _ ≤ ‖generator (fun _ => v x) φ x-generator (fun _ => v x) φ y‖ +
        ∑ i, ∑ a, ‖(v x i a-v y i a)*coordinateDerivative φ i a y‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)))
    _ ≤ (C : ℝ)*‖x-y‖ + ∑ i, ∑ a, (K : ℝ)*‖x-y‖*B i a :=
      add_le_add ((hC (v x) (hv x)).norm_sub_le x y)
        (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ => hi i a)
    _ = _ := by
      change (C : ℝ)*‖x-y‖ + ∑ i, ∑ a, (K : ℝ)*‖x-y‖*B i a =
        ((C : ℝ)+(K : ℝ)*(∑ i, ∑ a, B i a))*‖x-y‖
      simp only [add_mul, Finset.sum_mul, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      ring

end SharpWasserstein.CompactGenerator
