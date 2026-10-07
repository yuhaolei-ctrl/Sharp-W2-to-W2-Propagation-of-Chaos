/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.SmoothCoefficients
public import SharpWasserstein.PeriodicParticleApproximation

/-!
# Split drift/interaction pairs with Euclidean constants

Section 5 of the paper treats the one-body drift `a` and the interaction `K` separately: the
drift of level `m` of the hierarchy is `b^{[m]}_i(x) = a(xᵢ) + N⁻¹ ∑_{j ≤ m} K(xᵢ, xⱼ)` and the
external operator is `Φψ(x, y) = ∑ᵢ K(xᵢ, y) · ∇ᵢψ(x)` (`eq:Bm-Phi`). The constants of
Lemma 5.2 (`lem:pointwise`) are the Euclidean constants `L_a, L₁, L₂, M` of Assumption A.

This file packages the hypotheses used by the sharp hierarchy in the predicate `SplitKernel`:
Assumption A for the Euclidean conjugates, and qualitative smoothness with bounded derivatives
of `a` and `K` separately. It derives the Euclidean first-derivative bounds used in Lemma 5.2,
shows that `IsSmoothCoefficients` implies `SplitKernel`, and that the predicate (with the same
constants) is preserved by the coordinatewise sine periodization used to reduce to periodic
coefficients.

## Main definitions

* `oneBodyKernel a`: the drift `a` as a kernel `(x, y) ↦ a x`.
* `SplitKernel a K La L₁ L₂ M`.

## Main statements

* `SplitKernel.norm_toLp_fderiv_first_le`, `SplitKernel.norm_toLp_fderiv_second_le`,
  `SplitKernel.norm_toLp_K_le`: `‖D_x K‖ ≤ L₁`, `‖D_y K‖ ≤ L₂`, `|K| ≤ M` in Euclidean norms.
* `SplitKernel.of_smooth`: smooth coefficients (`IsSmoothCoefficients`) form a split pair.
* `SplitKernel.sine`, `sine_oneBody_periodic`: the sine-periodized pair.
-/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace SharpWasserstein.Sharp.Hierarchy

variable {d : ℕ}

/-- The one-body drift `a`, regarded as a kernel that ignores its second argument. -/
def oneBodyKernel (a : Position d → Position d) : Position d → Position d → Position d :=
  fun x _ => a x

/-- A split pair `(a, K)` for the sharp hierarchy: Assumption A for the Euclidean conjugates with
constants `La, L₁, L₂, M`, and smoothness with bounded derivatives of all orders of `a` and of
`K` separately. -/
structure SplitKernel (a : Position d → Position d) (K : Position d → Position d → Position d)
    (La L₁ L₂ M : ℝ) : Prop where
  assumptionA : SharpChaos.AssumptionA (euclidMap a) (euclidMap₂ K) La L₁ L₂ M
  smooth_a : BoundedSmoothKernel (oneBodyKernel a)
  smooth_K : BoundedSmoothKernel K

/-! ### Euclidean first-derivative bounds -/

/-- A differentiable map on coordinates whose Euclidean conjugate is `L`-Lipschitz has a
derivative of Euclidean operator norm at most `L`. -/
theorem norm_toLp_fderiv_le {f : Position d → Position d} {L : ℝ} (hL : 0 ≤ L)
    (hf : Differentiable ℝ f)
    (hlip : ∀ x x', ‖euclidMap f x - euclidMap f x'‖ ≤ L * ‖x - x'‖) (x u : Position d) :
    ‖WithLp.toLp 2 (fderiv ℝ f x u)‖ ≤ L * ‖WithLp.toLp 2 u‖ := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  have hl : LipschitzWith ⟨L, hL⟩ (euclidMap f) :=
    LipschitzWith.of_dist_le_mul fun x x' => by
      rw [dist_eq_norm, dist_eq_norm]
      exact hlip x x'
  have hd : HasFDerivAt (euclidMap f)
      (e.symm.toContinuousLinearMap.comp ((fderiv ℝ f x).comp e.toContinuousLinearMap))
      (WithLp.toLp 2 x) := by
    have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) => f (e y))
        ((fderiv ℝ f x).comp e.toContinuousLinearMap) (WithLp.toLp 2 x) :=
      (hf x).hasFDerivAt.comp _ e.hasFDerivAt
    exact e.symm.hasFDerivAt.comp _ h1
  have hn := norm_fderiv_le_of_lipschitz ℝ hl (x₀ := WithLp.toLp 2 x)
  rw [hd.fderiv] at hn
  exact (ContinuousLinearMap.le_opNorm _ (WithLp.toLp 2 u)).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

namespace SplitKernel

variable {a : Position d → Position d} {K : Position d → Position d → Position d}
  {La L₁ L₂ M : ℝ}

theorem La_nonneg (h : SplitKernel a K La L₁ L₂ M) : 0 ≤ La := h.assumptionA.La_nonneg

theorem L₁_nonneg (h : SplitKernel a K La L₁ L₂ M) : 0 ≤ L₁ := h.assumptionA.L₁_nonneg

theorem L₂_nonneg (h : SplitKernel a K La L₁ L₂ M) : 0 ≤ L₂ := h.assumptionA.L₂_nonneg

theorem M_nonneg (h : SplitKernel a K La L₁ L₂ M) : 0 ≤ M := h.assumptionA.M_nonneg

/-- `a` is smooth. -/
theorem contDiff_a (h : SplitKernel a K La L₁ L₂ M) : ContDiff ℝ ∞ a := by
  have he : a = Function.uncurry (oneBodyKernel a) ∘ fun x => (x, (0 : Position d)) := rfl
  rw [he]
  exact h.smooth_a.smooth.comp (contDiff_id.prodMk contDiff_const)

/-- `K` is differentiable in its first argument. -/
theorem differentiable_first (h : SplitKernel a K La L₁ L₂ M) (y : Position d) :
    Differentiable ℝ (fun q => K q y) := by
  have he : (fun q => K q y) = Function.uncurry K ∘ fun q => (q, y) := rfl
  rw [he]
  exact (h.smooth_K.smooth.differentiable (by simp)).comp
    (differentiable_id.prodMk (differentiable_const _))

/-- `K` is differentiable in its second argument. -/
theorem differentiable_second (h : SplitKernel a K La L₁ L₂ M) (x : Position d) :
    Differentiable ℝ (K x) := by
  have he : K x = Function.uncurry K ∘ fun q => (x, q) := rfl
  rw [he]
  exact (h.smooth_K.smooth.differentiable (by simp)).comp
    ((differentiable_const _).prodMk differentiable_id)

/-- Euclidean Lipschitz bound for `a`. -/
theorem norm_sub_a_le (h : SplitKernel a K La L₁ L₂ M) (x x' : Position d) :
    ‖WithLp.toLp 2 (a x) - WithLp.toLp 2 (a x')‖ ≤
      La * ‖WithLp.toLp 2 x - WithLp.toLp 2 x'‖ :=
  h.assumptionA.lipschitz_a (WithLp.toLp 2 x) (WithLp.toLp 2 x')

/-- Euclidean Lipschitz bound for `K`. -/
theorem norm_sub_K_le (h : SplitKernel a K La L₁ L₂ M) (x x' y y' : Position d) :
    ‖WithLp.toLp 2 (K x y) - WithLp.toLp 2 (K x' y')‖ ≤
      L₁ * ‖WithLp.toLp 2 x - WithLp.toLp 2 x'‖ + L₂ * ‖WithLp.toLp 2 y - WithLp.toLp 2 y'‖ :=
  h.assumptionA.lipschitz_K _ _ _ _

/-- Euclidean bound `|K| ≤ M`. -/
theorem norm_toLp_K_le (h : SplitKernel a K La L₁ L₂ M) (x y : Position d) :
    ‖WithLp.toLp 2 (K x y)‖ ≤ M :=
  h.assumptionA.norm_K_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)

/-- `‖D_x K‖ ≤ L₁` in the Euclidean operator norm. -/
theorem norm_toLp_fderiv_first_le (h : SplitKernel a K La L₁ L₂ M) (x y u : Position d) :
    ‖WithLp.toLp 2 (fderiv ℝ (fun q => K q y) x u)‖ ≤ L₁ * ‖WithLp.toLp 2 u‖ := by
  refine norm_toLp_fderiv_le h.L₁_nonneg (h.differentiable_first y) (fun z z' => ?_) x u
  have hh := h.assumptionA.lipschitz_K z z' (WithLp.toLp 2 y) (WithLp.toLp 2 y)
  simpa [euclidMap, euclidMap₂] using hh

/-- `‖D_y K‖ ≤ L₂` in the Euclidean operator norm. -/
theorem norm_toLp_fderiv_second_le (h : SplitKernel a K La L₁ L₂ M) (x y u : Position d) :
    ‖WithLp.toLp 2 (fderiv ℝ (K x) y u)‖ ≤ L₂ * ‖WithLp.toLp 2 u‖ := by
  refine norm_toLp_fderiv_le h.L₂_nonneg (h.differentiable_second x) (fun z z' => ?_) y u
  have hh := h.assumptionA.lipschitz_K (WithLp.toLp 2 x) (WithLp.toLp 2 x) z z'
  simpa [euclidMap, euclidMap₂] using hh

end SplitKernel

/-! ### Smooth coefficients are split pairs -/

section SmoothCoefficients

variable {a : Position d → Position d} {K : Position d → Position d → Position d}
  {La L₁ L₂ M : ℝ}

/-- The one-body drift of smooth coefficients is a bounded smooth kernel. -/
theorem boundedSmooth_oneBody_of_smooth (h : IsSmoothCoefficients a K La L₁ L₂ M) :
    BoundedSmoothKernel (oneBodyKernel a) := by
  have ha : ContDiff ℝ ∞ (fun z : Position d × Position d => a z.1) :=
    h.contDiff_a.comp contDiff_fst
  refine ⟨ha, fun n => ?_⟩
  obtain ⟨Ca, hCa⟩ := h.iteratedFDeriv_a_le n
  have hn : ((n : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  refine ⟨max 0 (Ca * ‖ContinuousLinearMap.fst ℝ (Position d) (Position d)‖ ^ n),
    le_max_left _ _, fun z => ?_⟩
  have hcomp : Function.uncurry (oneBodyKernel a) =
      a ∘ (ContinuousLinearMap.fst ℝ (Position d) (Position d)) := rfl
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ h.contDiff_a z hn]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    (le_max_of_le_right ?_)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  gcongr
  exact hCa _

/-- The interaction of smooth coefficients is a bounded smooth kernel. -/
theorem boundedSmooth_K_of_smooth (h : IsSmoothCoefficients a K La L₁ L₂ M) :
    BoundedSmoothKernel K := by
  refine ⟨h.contDiff_K, fun n => ?_⟩
  obtain ⟨C, hC⟩ := h.iteratedFDeriv_K_le n
  exact ⟨max 0 C, le_max_left _ _, fun z => (hC z).trans (le_max_right _ _)⟩

/-- Smooth coefficients form a split pair with the same constants. -/
theorem SplitKernel.of_smooth (h : IsSmoothCoefficients a K La L₁ L₂ M) :
    SplitKernel a K La L₁ L₂ M :=
  ⟨h.assumptionA, boundedSmooth_oneBody_of_smooth h, boundedSmooth_K_of_smooth h⟩

end SmoothCoefficients

/-! ### Sine periodization -/

open SinePeriodization in
/-- The coordinate sine map is `1`-Lipschitz for the Euclidean norm. -/
theorem norm_toLp_coordinates_sub_le {R : ℝ} (hR : R ≠ 0) (x x' : Position d) :
    ‖WithLp.toLp 2 (coordinates R x) - WithLp.toLp 2 (coordinates R x')‖ ≤
      ‖WithLp.toLp 2 x - WithLp.toLp 2 x'‖ := by
  rw [← WithLp.toLp_sub, ← WithLp.toLp_sub, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  have hh : |scalar R (x i) - scalar R (x' i)| ≤ |x i - x' i| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      (scalar_lipschitz hR).dist_le_mul (x i) (x' i)
  simp only [Pi.sub_apply, Real.norm_eq_abs, sq_abs]
  exact sq_le_sq.mpr hh

open SinePeriodization in
/-- The sine-periodized kernel `kernelOf a K` is the kernel of the sine-periodized pair. -/
theorem kernel_kernelOf (R : ℝ) (a : Position d → Position d)
    (K : Position d → Position d → Position d) :
    SinePeriodization.kernel R (kernelOf a K) = kernelOf (a ∘ coordinates R) (kernel R K) :=
  rfl

namespace SplitKernel

variable {a : Position d → Position d} {K : Position d → Position d → Position d}
  {La L₁ L₂ M : ℝ}

open SinePeriodization in
/-- Sine periodization preserves split pairs together with their Euclidean constants. -/
theorem sine (h : SplitKernel a K La L₁ L₂ M) {R : ℝ} (hR : 0 < R) :
    SplitKernel (a ∘ coordinates R) (kernel R K) La L₁ L₂ M where
  assumptionA :=
    { La_nonneg := h.La_nonneg
      L₁_nonneg := h.L₁_nonneg
      L₂_nonneg := h.L₂_nonneg
      M_nonneg := h.M_nonneg
      lipschitz_a := fun x x' => by
        refine (h.norm_sub_a_le _ _).trans (mul_le_mul_of_nonneg_left ?_ h.La_nonneg)
        simpa using norm_toLp_coordinates_sub_le hR.ne' (WithLp.ofLp x) (WithLp.ofLp x')
      norm_K_le := fun x y => h.norm_toLp_K_le _ _
      lipschitz_K := fun x x' y y' => by
        refine (h.norm_sub_K_le _ _ _ _).trans (add_le_add
          (mul_le_mul_of_nonneg_left ?_ h.L₁_nonneg) (mul_le_mul_of_nonneg_left ?_ h.L₂_nonneg))
        · simpa using norm_toLp_coordinates_sub_le hR.ne' (WithLp.ofLp x) (WithLp.ofLp x')
        · simpa using norm_toLp_coordinates_sub_le hR.ne' (WithLp.ofLp y) (WithLp.ofLp y') }
  smooth_a := kernel_boundedSmooth hR h.smooth_a.smooth
  smooth_K := kernel_boundedSmooth hR h.smooth_K.smooth

end SplitKernel

open SinePeriodization in
/-- The sine-periodized one-body drift has period `2πR` in every coordinate. -/
theorem sine_oneBody_periodic {R : ℝ} (hR : R ≠ 0) (a : Position d → Position d) (i : Fin d)
    (x : Position d) :
    (a ∘ coordinates R) (x + Pi.single i (2 * Real.pi * R)) = (a ∘ coordinates R) x := by
  simp only [Function.comp_apply, coordinates_periodic hR]

end SharpWasserstein.Sharp.Hierarchy
