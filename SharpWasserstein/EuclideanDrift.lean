module

public import SharpWasserstein.Compat
public import SharpWasserstein.DriftBounds
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

/-! Conversion between the coordinate sup norm and the actual Euclidean cost,
and quadratic bounds on the mean-field drift with no particle-number loss. -/

noncomputable section
open scoped BigOperators

namespace SharpWasserstein

def positionSq {d : ℕ} (x : Position d) : ℝ := ∑ a, (x a) ^ 2

theorem positionSq_nonneg {d : ℕ} (x : Position d) : 0 ≤ positionSq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem norm_sq_le_positionSq {d : ℕ} (x : Position d) : ‖x‖ ^ 2 ≤ positionSq x := by
  classical
  rcases isEmpty_or_nonempty (Fin d) with h | h
  · letI := h
    simp [Subsingleton.elim x 0, positionSq]
  · letI := h
    obtain ⟨⟨a, ha⟩, _⟩ := IsGreatest.pi_norm x
    calc
      ‖x‖ ^ 2 = (x a) ^ 2 := by
        calc
          ‖x‖ ^ 2 = ‖x a‖ ^ 2 := congrArg (fun r : ℝ => r ^ 2) ha.symm
          _ = (x a) ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
      _ ≤ positionSq x := Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ a)

theorem positionSq_le_norm_sq {d : ℕ} (x : Position d) :
    positionSq x ≤ d * ‖x‖ ^ 2 := by
  calc
    positionSq x ≤ ∑ _a : Fin d, ‖x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro a _
      have h := (sq_le_sq₀ (norm_nonneg (x a)) (norm_nonneg x)).2 (norm_le_pi_norm x a)
      simpa only [Real.norm_eq_abs, sq_abs] using h
    _ = _ := by simp

theorem productCost_eq_sum_positionSq {d N : ℕ} (x y : Configuration d N) :
    productCost x y = ∑ i, positionSq (x i - y i) := rfl

/-- Finite-dimensional Jensen for an actual arithmetic mean, with coefficient `1/N`. -/
theorem positionSq_average_le {d N : ℕ} (hN : 0 < N) (z : Fin N → Position d) :
    positionSq ((N : ℝ)⁻¹ • ∑ j, z j) ≤ (N : ℝ)⁻¹ * ∑ j, positionSq (z j) := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold positionSq
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hc : (∑ j, z j a) ^ 2 ≤ (N : ℝ) * ∑ j, (z j a) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _j : Fin N => (1 : ℝ))
      (fun j => z j a)
  calc
    ((N : ℝ)⁻¹ * ∑ j, z j a) ^ 2 = ((N : ℝ)⁻¹) ^ 2 * (∑ j, z j a) ^ 2 := by ring
    _ ≤ ((N : ℝ)⁻¹) ^ 2 * ((N : ℝ) * ∑ j, (z j a) ^ 2) :=
      mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    _ = (N : ℝ)⁻¹ * ∑ j, (z j a) ^ 2 := by
      field_simp

theorem kernel_joint_quadratic_difference {d : ℕ}
    {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (x x' y y' : Position d) :
    positionSq (b x y - b x' y') ≤
      2 * d * (L₁ ^ 2 * positionSq (x - x') + L₂ ^ 2 * positionSq (y - y')) := by
  have hnorm := kernel_joint_difference hb hbound x x' y y'
  have hsq : ‖b x y - b x' y'‖ ^ 2 ≤
      (L₁ * ‖x - x'‖ + L₂ * ‖y - y'‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
  calc
    positionSq (b x y - b x' y') ≤ d * ‖b x y - b x' y'‖ ^ 2 := positionSq_le_norm_sq _
    _ ≤ d * (L₁ * ‖x - x'‖ + L₂ * ‖y - y'‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg d)
    _ ≤ 2 * d * (L₁ ^ 2 * ‖x - x'‖ ^ 2 + L₂ ^ 2 * ‖y - y'‖ ^ 2) := by
      have h := mul_nonneg (show (0 : ℝ) ≤ d by positivity)
        (sq_nonneg (L₁ * ‖x - x'‖ - L₂ * ‖y - y'‖))
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left (norm_sq_le_positionSq _) (sq_nonneg L₁))
        (mul_le_mul_of_nonneg_left (norm_sq_le_positionSq _) (sq_nonneg L₂))) (by positivity)

/-- The true unnormalized Euclidean Lipschitz bound is uniform in `N`. -/
theorem particleDrift_quadratic_difference {d N : ℕ}
    {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (x y : Configuration d N) :
    productCost (particleDrift b x) (particleDrift b y) ≤
      (2 * d * (L₁ ^ 2 + L₂ ^ 2)) * productCost x y := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [productCost_eq_sum_positionSq, productCost_eq_sum_positionSq]
  calc
    (∑ i, positionSq (particleDrift b x i - particleDrift b y i)) ≤
        ∑ i, (N : ℝ)⁻¹ * ∑ j, positionSq (b (x i) (x j) - b (y i) (y j)) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [particleDrift, ← smul_sub, ← Finset.sum_sub_distrib] using
        positionSq_average_le hN (fun j => b (x i) (x j) - b (y i) (y j))
    _ ≤ ∑ i, (N : ℝ)⁻¹ * ∑ j,
        2 * d * (L₁ ^ 2 * positionSq (x i - y i) + L₂ ^ 2 * positionSq (x j - y j)) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j _
      exact kernel_joint_quadratic_difference hb hbound hL₁ hL₂ _ _ _ _
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
      field_simp

end SharpWasserstein
