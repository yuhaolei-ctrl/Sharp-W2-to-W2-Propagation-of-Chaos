import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Pointwise finite-dimensional algebra of the tangent hierarchy

This module proves the symmetric-Hessian cancellation and the Frobenius control
of its action on a vector. It also gives the `sqrt m` bound for the pairing of
`m` uniformly bounded vector blocks with a tangent vector. All norms on the
assembled vectors are Euclidean (`PiLp 2`), not coordinate supremum norms.

The PDE differentiation, integration by parts, and identification of these
matrices and vectors with derivatives of weighted Riesz potentials are separate
analytic obligations; they are not conclusions of this module.
-/

noncomputable section

namespace SharpWasserstein.HierarchyAlgebra

open scoped BigOperators InnerProductSpace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A matrix acts on Euclidean vectors, with the Euclidean norm on the output. -/
def matrixAction (H : Matrix ι κ ℝ) (v : EuclideanSpace ℝ κ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (H.mulVec v)

/-- Squared Hilbert--Schmidt/Frobenius norm, explicitly as a sum of squares. -/
def frobeniusSq (H : Matrix ι κ ℝ) : ℝ := ∑ i, ∑ j, H i j ^ 2

omit [Fintype ι] in
@[simp]
theorem matrixAction_apply (H : Matrix ι κ ℝ) (v : EuclideanSpace ℝ κ) (i : ι) :
    matrixAction H v i = ∑ j, H i j * v j := rfl

/-- Symmetry of the Hessian exchanges the two vectors in its bilinear form. -/
theorem symmetric_hessian_pairing (H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (w v : EuclideanSpace ℝ ι) :
    ⟪w, matrixAction H v⟫_ℝ = ⟪v, matrixAction H w⟫_ℝ := by
  have h := Matrix.dotProduct_transpose_mulVec H (fun i => w i) (fun i => v i)
  rw [hH.eq] at h
  simpa [dotProduct, matrixAction, PiLp.inner_apply, RCLike.inner_apply, mul_comm] using h

/-- The lifted external Hessian terms cancel exactly, with their actual coefficients. -/
theorem external_hessian_cancellation (H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (w v : EuclideanSpace ℝ ι) (α : ℝ) :
    2 * α * ⟪w, matrixAction H v⟫_ℝ -
      α * (2 * ⟪v, matrixAction H w⟫_ℝ) = 0 := by
  rw [symmetric_hessian_pairing H hH w v]
  ring

/-- After cancellation, only the non-Hessian derivative term remains. -/
theorem external_lifted_remainder (H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (w v : EuclideanSpace ℝ ι) (α q : ℝ) :
    2 * α * (⟪w, matrixAction H v⟫_ℝ + q) -
      α * (2 * ⟪v, matrixAction H w⟫_ℝ) = 2 * α * q := by
  rw [symmetric_hessian_pairing H hH w v]
  ring

/-- Rowwise Cauchy--Schwarz gives the precise quadratic Hessian-action bound. -/
theorem matrixAction_norm_sq_le (H : Matrix ι κ ℝ) (v : EuclideanSpace ℝ κ) :
    ‖matrixAction H v‖ ^ 2 ≤ frobeniusSq H * ‖v‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  unfold frobeniusSq
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [matrixAction_apply] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => H i j) (fun j => v j)

theorem frobeniusSq_nonneg (H : Matrix ι κ ℝ) : 0 ≤ frobeniusSq H := by
  apply Finset.sum_nonneg
  intro i hi
  exact Finset.sum_nonneg (fun j hj => sq_nonneg (H i j))

/-- Substitute any proved squared norm bound on the empirical-force vector. -/
theorem matrixAction_norm_sq_le_of_norm_sq_le (H : Matrix ι κ ℝ)
    (v : EuclideanSpace ℝ κ) (A : ℝ) (hv : ‖v‖ ^ 2 ≤ A) :
    ‖matrixAction H v‖ ^ 2 ≤ frobeniusSq H * A :=
  (matrixAction_norm_sq_le H v).trans
    (mul_le_mul_of_nonneg_left hv (frobeniusSq_nonneg H))


/-- Quadratic residual-gradient bound for a Hessian action plus a derivative term. -/
theorem hessian_plus_remainder_norm_sq_le (H : Matrix ι κ ℝ)
    (v : EuclideanSpace ℝ κ) (z : EuclideanSpace ℝ ι) :
    ‖matrixAction H v + z‖ ^ 2 ≤
      2 * frobeniusSq H * ‖v‖ ^ 2 + 2 * ‖z‖ ^ 2 := by
  have hplus := norm_add_sq_real (matrixAction H v) z
  have hminus := norm_sub_sq_real (matrixAction H v) z
  have haction := matrixAction_norm_sq_le H v
  nlinarith [sq_nonneg ‖matrixAction H v - z‖]

section Blocks

variable {F : Type*} [NormedAddCommGroup F]

/-- Squared Euclidean norm of uniformly bounded particle blocks. -/
theorem block_norm_sq_le (b : PiLp 2 (fun _ : ι => F)) (M : ℝ)
    (hM : 0 ≤ M) (hb : ∀ i, ‖b i‖ ≤ M) :
    ‖b‖ ^ 2 ≤ (Fintype.card ι : ℝ) * M ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    ∑ i, ‖b i‖ ^ 2 ≤ ∑ _i : ι, M ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hi := hb i
      have hn := norm_nonneg (b i)
      nlinarith
    _ = (Fintype.card ι : ℝ) * M ^ 2 := by simp

/-- `m` bounded interaction blocks have Euclidean norm at most `M sqrt(m)`. -/
theorem block_norm_le (b : PiLp 2 (fun _ : ι => F)) (M : ℝ)
    (hM : 0 ≤ M) (hb : ∀ i, ‖b i‖ ≤ M) :
    ‖b‖ ≤ M * Real.sqrt (Fintype.card ι) := by
  have hs := block_norm_sq_le b M hM hb
  have hc : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hr := Real.sq_sqrt hc
  have hp := mul_nonneg hM (Real.sqrt_nonneg (Fintype.card ι))
  have hn := norm_nonneg b
  nlinarith

variable [InnerProductSpace ℝ F]

/-- The actual vector-block Cauchy--Schwarz bound with the sharp `sqrt(m)` factor. -/
theorem block_pairing_bound (b w : PiLp 2 (fun _ : ι => F)) (M : ℝ)
    (hM : 0 ≤ M) (hb : ∀ i, ‖b i‖ ≤ M) :
    |∑ i, ⟪b i, w i⟫_ℝ| ≤ M * Real.sqrt (Fintype.card ι) * ‖w‖ := by
  calc
    |∑ i, ⟪b i, w i⟫_ℝ| = |⟪b, w⟫_ℝ| := by rw [PiLp.inner_apply]
    _ ≤ ‖b‖ * ‖w‖ := abs_real_inner_le_norm b w
    _ ≤ M * Real.sqrt (Fintype.card ι) * ‖w‖ :=
      mul_le_mul_of_nonneg_right (block_norm_le b M hM hb) (norm_nonneg w)

/-- The squared form used in residual-gradient bounds, without square roots. -/
theorem block_pairing_sq_bound (b w : PiLp 2 (fun _ : ι => F)) (M : ℝ)
    (hM : 0 ≤ M) (hb : ∀ i, ‖b i‖ ≤ M) :
    (∑ i, ⟪b i, w i⟫_ℝ) ^ 2 ≤ (Fintype.card ι : ℝ) * M ^ 2 * ‖w‖ ^ 2 := by
  have hc := real_inner_mul_inner_self_le b w
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hc
  have hs := mul_le_mul_of_nonneg_right (block_norm_sq_le b M hM hb) (sq_nonneg ‖w‖)
  rw [PiLp.inner_apply] at hc
  nlinarith

end Blocks

end SharpWasserstein.HierarchyAlgebra
