/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Statement
public import SharpWasserstein.Dynamics
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Smooth coefficients for the smooth case of Theorem 2.1

The development describes positions by their coordinates, `Position d = Fin d → ℝ`, a type whose
norm is the sup norm. The smooth case of Theorem 2.1 is stated for a bounded smooth one-body
drift `a` and a smooth interaction `K` on coordinates, all of whose derivatives are bounded, which
satisfy Assumption A **for the Euclidean norm**. The predicate `IsSmoothCoefficients` records this
through the Euclidean conjugates `euclidMap a` and `euclidMap₂ K`, so that the constants
`L_a, L₁, L₂, M` are exactly those of the paper.

The particle and reference dynamics of the development are driven by the single kernel
`kernelOf a K x y = a x + K x y`, whose particle drift `N⁻¹ ∑ⱼ (a xᵢ + K xᵢ xⱼ)` is the drift
`a xᵢ + N⁻¹ ∑ⱼ K xᵢ xⱼ` of the paper. The development's qualitative hypotheses on that kernel
(`BoundedSmoothKernel` and `KernelBounds` with some sup-norm constants) follow from
`IsSmoothCoefficients`; those constants never enter the final estimate.
-/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace SharpWasserstein.Sharp

variable {d : ℕ}

/-- The Euclidean conjugate `toLp ∘ f ∘ ofLp` of a map on coordinates. -/
def euclidMap (f : Position d → Position d) :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
  fun x => WithLp.toLp 2 (f (WithLp.ofLp x))

/-- The Euclidean conjugate of an interaction on coordinates. -/
def euclidMap₂ (K : Position d → Position d → Position d) :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
  fun x y => WithLp.toLp 2 (K (WithLp.ofLp x) (WithLp.ofLp y))

/-- The coordinate form `ofLp ∘ f ∘ toLp` of a map on `ℝᵈ`. -/
def coordMap (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    Position d → Position d :=
  fun x => WithLp.ofLp (f (WithLp.toLp 2 x))

/-- The coordinate form of an interaction on `ℝᵈ`. -/
def coordMap₂
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    Position d → Position d → Position d :=
  fun x y => WithLp.ofLp (K (WithLp.toLp 2 x) (WithLp.toLp 2 y))

@[simp] theorem euclidMap_coordMap (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    euclidMap (coordMap f) = f :=
  rfl

@[simp] theorem euclidMap₂_coordMap₂
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    euclidMap₂ (coordMap₂ K) = K :=
  rfl

/-- The kernel `b(x, y) = a(x) + K(x, y)` driving the development's dynamics. -/
def kernelOf (a : Position d → Position d) (K : Position d → Position d → Position d) :
    Position d → Position d → Position d :=
  fun x y => a x + K x y

/-- Smooth coefficients for the smooth case of Theorem 2.1: Assumption A for the Euclidean
norm with constants `La, L₁, L₂, M`, smoothness, boundedness of `a`, and bounded derivatives of
every order. -/
structure IsSmoothCoefficients (a : Position d → Position d)
    (K : Position d → Position d → Position d) (La L₁ L₂ M : ℝ) : Prop where
  assumptionA : SharpChaos.AssumptionA (euclidMap a) (euclidMap₂ K) La L₁ L₂ M
  contDiff_a : ContDiff ℝ ∞ a
  contDiff_K : ContDiff ℝ ∞ (Function.uncurry K)
  bounded_a : ∃ C, ∀ x, ‖a x‖ ≤ C
  iteratedFDeriv_a_le : ∀ n : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n a x‖ ≤ C
  iteratedFDeriv_K_le : ∀ n : ℕ, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (Function.uncurry K) z‖ ≤ C

/-- The sup norm of a coordinate vector is at most its Euclidean norm. -/
theorem norm_le_norm_toLp (x : Position d) : ‖x‖ ≤ ‖WithLp.toLp 2 x‖ := by
  refine pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun i => ?_
  simpa using PiLp.norm_apply_le (WithLp.toLp 2 x) i

namespace IsSmoothCoefficients

variable {a : Position d → Position d} {K : Position d → Position d → Position d}
  {La L₁ L₂ M : ℝ}

theorem uncurry_kernelOf :
    Function.uncurry (kernelOf a K) = fun z => a z.1 + Function.uncurry K z :=
  rfl

theorem contDiff_kernelOf (h : IsSmoothCoefficients a K La L₁ L₂ M) :
    ContDiff ℝ ∞ (Function.uncurry (kernelOf a K)) := by
  rw [uncurry_kernelOf]
  exact (h.contDiff_a.comp contDiff_fst).add h.contDiff_K

/-- Every derivative of the kernel `kernelOf a K` is bounded. -/
theorem iteratedFDeriv_kernelOf_le (h : IsSmoothCoefficients a K La L₁ L₂ M) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖iteratedFDeriv ℝ n (Function.uncurry (kernelOf a K)) z‖ ≤ C := by
  obtain ⟨Ca, hCa⟩ := h.iteratedFDeriv_a_le n
  obtain ⟨CK, hCK⟩ := h.iteratedFDeriv_K_le n
  refine ⟨max 0 (Ca * ‖ContinuousLinearMap.fst ℝ (Position d) (Position d)‖ ^ n + CK),
    le_max_left _ _, fun z => ?_⟩
  rw [uncurry_kernelOf]
  have ha : ContDiff ℝ ∞ (fun z : Position d × Position d => a z.1) :=
    h.contDiff_a.comp contDiff_fst
  have hn : ((n : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  change ‖iteratedFDeriv ℝ n ((fun z : Position d × Position d => a z.1) + Function.uncurry K) z‖
    ≤ _
  rw [iteratedFDeriv_add_apply (ha.contDiffAt.of_le hn) (h.contDiff_K.contDiffAt.of_le hn)]
  refine (norm_add_le _ _).trans (le_max_of_le_right (add_le_add ?_ (hCK z)))
  have hcomp : (fun z : Position d × Position d => a z.1) =
      a ∘ (ContinuousLinearMap.fst ℝ (Position d) (Position d)) := rfl
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ h.contDiff_a z hn]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  gcongr
  exact hCa _

/-- The development's qualitative smoothness hypothesis on the kernel. -/
theorem boundedSmoothKernel (h : IsSmoothCoefficients a K La L₁ L₂ M) :
    BoundedSmoothKernel (kernelOf a K) where
  smooth := h.contDiff_kernelOf
  boundedDerivatives := h.iteratedFDeriv_kernelOf_le

/-- The interaction is bounded by `M` also for the sup norm. -/
theorem norm_K_le (h : IsSmoothCoefficients a K La L₁ L₂ M) (x y : Position d) :
    ‖K x y‖ ≤ M :=
  (norm_le_norm_toLp _).trans (h.assumptionA.norm_K_le (WithLp.toLp 2 x) (WithLp.toLp 2 y))

/-- The development's qualitative bounds on the value and first derivatives of the kernel, with
some sup-norm constants (these never enter the final estimate). -/
theorem exists_kernelBounds (h : IsSmoothCoefficients a K La L₁ L₂ M) :
    ∃ Mb Lb₁ Lb₂ : ℝ, 0 ≤ Mb ∧ 0 ≤ Lb₁ ∧ 0 ≤ Lb₂ ∧ KernelBounds (kernelOf a K) Mb Lb₁ Lb₂ := by
  obtain ⟨Ca, hCa⟩ := h.bounded_a
  obtain ⟨C₁, hC₁0, hC₁⟩ := h.iteratedFDeriv_kernelOf_le 1
  have hdiff : Differentiable ℝ (Function.uncurry (kernelOf a K)) :=
    h.contDiff_kernelOf.differentiable (by simp)
  have hfd : ∀ z, ‖fderiv ℝ (Function.uncurry (kernelOf a K)) z‖ ≤ C₁ := fun z => by
    rw [← norm_iteratedFDeriv_one]; exact hC₁ z
  refine ⟨max 0 (Ca + M), C₁, C₁, le_max_left _ _, hC₁0, hC₁0, ?_, ?_, ?_⟩
  · intro x y
    refine (norm_add_le _ _).trans (le_max_of_le_right (add_le_add (hCa x) (h.norm_K_le x y)))
  · intro x y
    have hx : (fun z => kernelOf a K z y) =
        Function.uncurry (kernelOf a K) ∘ fun z => (z, y) := rfl
    rw [hx, fderiv_comp x (hdiff _) ((hasFDerivAt_prodMk_left x y).differentiableAt)]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [(hasFDerivAt_prodMk_left x y).fderiv]
    calc _ ≤ C₁ * 1 := mul_le_mul (hfd _) (ContinuousLinearMap.norm_inl_le_one ℝ _ _) (norm_nonneg _)
          hC₁0
      _ = C₁ := mul_one _
  · intro x y
    have hy : kernelOf a K x = Function.uncurry (kernelOf a K) ∘ fun z => (x, z) := rfl
    rw [hy, fderiv_comp y (hdiff _) ((hasFDerivAt_prodMk_right x y).differentiableAt)]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [(hasFDerivAt_prodMk_right x y).fderiv]
    calc _ ≤ C₁ * 1 := mul_le_mul (hfd _) (ContinuousLinearMap.norm_inr_le_one ℝ _ _) (norm_nonneg _)
          hC₁0
      _ = C₁ := mul_one _

end IsSmoothCoefficients

end SharpWasserstein.Sharp
