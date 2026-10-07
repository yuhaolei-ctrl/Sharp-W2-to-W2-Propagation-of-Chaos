/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.SmoothCoefficients
public import SharpWasserstein.Sharp.Constants
public import SharpWasserstein.PrescribedReference
public import SharpWasserstein.GaussianControlledBridge

/-!
# The reference drift of the smooth case

For smooth coefficients `a`, `K` (`IsSmoothCoefficients a K La L₁ L₂ M`) the development drives
its dynamics by the single kernel `kernelOf a K x y = a x + K x y`. For a probability law `q`
the nonlinear drift of this kernel is the reference drift of the paper,
`B(x) = a(x) + ∫ K(x, y) q(dy)` (Section 3.1, `eq:generators`), and Lemma 3.1
(`lem:wellposed`, `eq:lip`) states that it is Lipschitz for the Euclidean norm with constant
`L = L_a + L₁` (`eq:const1`).

This file proves these two facts, together with the corresponding statement for the drift
`PrescribedReference.singleDrift` of the reference evolution `R^N_s` of Section 3.3, in the
form `LipschitzWith L (GaussianBridge.euclideanDrift _ t)` required by the entropy–cost
inequality of Lemma 4.1 (`lem:entropy-cost`). No dimension-dependent conversion between the
sup norm and the Euclidean norm is used.

## Main statements

* `nonlinearDrift_kernelOf`: `nonlinearDrift (kernelOf a K) q x = a x + ∫ K x y dq`.
* `lipschitzWith_euclidMap_nonlinearDrift`: the Euclidean conjugate of the reference drift is
  `L`-Lipschitz, `L = L_a + L₁`.
* `lipschitzWith_euclideanDrift_singleDrift`: the same for the drift of the reference
  evolution.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped NNReal

namespace SharpWasserstein.Sharp.Source

variable {d : ℕ}

/-- The coordinate vector of a point of `ℝᵈ` regarded as a Euclidean vector, as a continuous
linear equivalence (it is `WithLp.toLp 2`). -/
abbrev toEuclid (d : ℕ) : Position d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm

@[simp] theorem toEuclid_apply (x : Position d) : toEuclid d x = WithLp.toLp 2 x :=
  rfl

@[simp] theorem toEuclid_symm_apply (x : EuclideanSpace ℝ (Fin d)) :
    (toEuclid d).symm x = WithLp.ofLp x :=
  rfl

/-- The square of the Euclidean norm of a coordinate vector is the sum of the squares of its
coordinates. -/
theorem norm_toLp_sq (x : Position d) : ‖WithLp.toLp 2 x‖ ^ 2 = ∑ a, x a ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]

/-- `L = L_a + L₁` as a nonnegative real number. -/
def lipLNN (La L₁ : ℝ) : ℝ≥0 := Real.toNNReal (lipL La L₁)

theorem coe_lipLNN {La L₁ : ℝ} (hLa : 0 ≤ La) (hL₁ : 0 ≤ L₁) :
    (lipLNN La L₁ : ℝ) = lipL La L₁ :=
  Real.coe_toNNReal _ (lipL_nonneg hLa hL₁)

namespace IsSmoothCoefficients

variable {a : Position d → Position d} {K : Position d → Position d → Position d}
  {La L₁ L₂ M : ℝ}

/-- The interaction is jointly continuous. -/
theorem continuous_K (h : IsSmoothCoefficients a K La L₁ L₂ M) :
    Continuous (Function.uncurry K) :=
  h.contDiff_K.continuous

/-- The interaction is jointly measurable. -/
theorem measurable_K (h : IsSmoothCoefficients a K La L₁ L₂ M) :
    Measurable (Function.uncurry K) :=
  (IsSmoothCoefficients.continuous_K h).measurable

/-- The Euclidean form `(x, y) ↦ toLp (K x y)` of the interaction is jointly measurable. -/
theorem measurable_toLp_K (h : IsSmoothCoefficients a K La L₁ L₂ M) :
    Measurable (Function.uncurry fun x y => WithLp.toLp 2 (K x y)) :=
  (toEuclid d).continuous.measurable.comp (IsSmoothCoefficients.measurable_K h)

/-- The bound `|K| ≤ M` of Assumption A (`eq:A2`) for the Euclidean norm, on coordinates. -/
theorem norm_toLp_K_le (h : IsSmoothCoefficients a K La L₁ L₂ M) (x y : Position d) :
    ‖WithLp.toLp 2 (K x y)‖ ≤ M :=
  h.assumptionA.norm_K_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)

/-- The Lipschitz bound of Assumption A (`eq:A3`) for the Euclidean norm, on coordinates. -/
theorem norm_toLp_K_sub_le (h : IsSmoothCoefficients a K La L₁ L₂ M) (x x' y y' : Position d) :
    ‖WithLp.toLp 2 (K x y) - WithLp.toLp 2 (K x' y')‖ ≤
      L₁ * ‖WithLp.toLp 2 x - WithLp.toLp 2 x'‖ + L₂ * ‖WithLp.toLp 2 y - WithLp.toLp 2 y'‖ :=
  h.assumptionA.lipschitz_K (WithLp.toLp 2 x) (WithLp.toLp 2 x') (WithLp.toLp 2 y)
    (WithLp.toLp 2 y')

/-- The Lipschitz bound of Assumption A (`eq:A1`) for the Euclidean norm, on coordinates. -/
theorem norm_toLp_a_sub_le (h : IsSmoothCoefficients a K La L₁ L₂ M) (x x' : Position d) :
    ‖WithLp.toLp 2 (a x) - WithLp.toLp 2 (a x')‖ ≤ La * ‖WithLp.toLp 2 x - WithLp.toLp 2 x'‖ :=
  h.assumptionA.lipschitz_a (WithLp.toLp 2 x) (WithLp.toLp 2 x')

/-- The sections `K x` are integrable for every finite measure. -/
theorem integrable_K (h : IsSmoothCoefficients a K La L₁ L₂ M) (q : Measure (Position d))
    [IsFiniteMeasure q] (x : Position d) : Integrable (K x) q :=
  Integrable.of_bound
    ((IsSmoothCoefficients.measurable_K h).comp measurable_prodMk_left).aestronglyMeasurable M
    (ae_of_all _ (h.norm_K_le x))

/-- The Euclidean sections `y ↦ toLp (K x y)` are integrable for every finite measure. -/
theorem integrable_toLp_K (h : IsSmoothCoefficients a K La L₁ L₂ M) (q : Measure (Position d))
    [IsFiniteMeasure q] (x : Position d) : Integrable (fun y => WithLp.toLp 2 (K x y)) q :=
  (toEuclid d).integrable_comp_iff.2 (IsSmoothCoefficients.integrable_K h q x)

/-- The nonlinear drift of the kernel `kernelOf a K` is the reference drift
`B(x) = a(x) + ∫ K(x, y) q(dy)` of the paper. -/
theorem nonlinearDrift_kernelOf (h : IsSmoothCoefficients a K La L₁ L₂ M)
    (q : Measure (Position d)) [IsProbabilityMeasure q] (x : Position d) :
    nonlinearDrift (kernelOf a K) q x = a x + ∫ y, K x y ∂q := by
  unfold nonlinearDrift kernelOf
  rw [integral_add (integrable_const _) (IsSmoothCoefficients.integrable_K h q x),
    integral_const, probReal_univ, one_smul]

/-- The integral of the Euclidean sections commutes with `toLp`. -/
theorem integral_toLp_K (q : Measure (Position d)) (x : Position d) :
    ∫ y, WithLp.toLp 2 (K x y) ∂q = WithLp.toLp 2 (∫ y, K x y ∂q) :=
  (toEuclid d).integral_comp_comm (K x)

/-- **Lemma 3.1 (`eq:lip`), reference drift.** For every probability law `q`, the Euclidean
conjugate of the reference drift `x ↦ a(x) + ∫ K(x, y) q(dy)` is Lipschitz with constant
`L = L_a + L₁`. -/
theorem lipschitzWith_euclidMap_nonlinearDrift (h : IsSmoothCoefficients a K La L₁ L₂ M)
    (q : Measure (Position d)) [IsProbabilityMeasure q] :
    LipschitzWith (lipLNN La L₁) (euclidMap (nonlinearDrift (kernelOf a K) q)) := by
  have hA := h.assumptionA
  apply LipschitzWith.of_dist_le_mul
  intro x x'
  rw [dist_eq_norm, dist_eq_norm, coe_lipLNN hA.La_nonneg hA.L₁_nonneg]
  set u := WithLp.ofLp x
  set u' := WithLp.ofLp x'
  have hx : x = WithLp.toLp 2 u := rfl
  have hx' : x' = WithLp.toLp 2 u' := rfl
  have hK : ‖∫ y, WithLp.toLp 2 (K u y) ∂q - ∫ y, WithLp.toLp 2 (K u' y) ∂q‖ ≤
      L₁ * ‖x - x'‖ := by
    rw [← integral_sub (IsSmoothCoefficients.integrable_toLp_K h q u)
      (IsSmoothCoefficients.integrable_toLp_K h q u')]
    simpa using norm_integral_le_of_norm_le_const (μ := q) (C := L₁ * ‖x - x'‖)
      (ae_of_all _ fun y => by
        simpa [hx, hx'] using IsSmoothCoefficients.norm_toLp_K_sub_le h u u' y y)
  have heq : euclidMap (nonlinearDrift (kernelOf a K) q) x -
      euclidMap (nonlinearDrift (kernelOf a K) q) x' =
      (WithLp.toLp 2 (a u) - WithLp.toLp 2 (a u')) +
        (∫ y, WithLp.toLp 2 (K u y) ∂q - ∫ y, WithLp.toLp 2 (K u' y) ∂q) := by
    simp only [euclidMap, IsSmoothCoefficients.nonlinearDrift_kernelOf h q, integral_toLp_K,
      WithLp.toLp_add]
    abel
  rw [heq, lipL, add_mul]
  exact (norm_add_le _ _).trans (add_le_add
    (by simpa [hx, hx'] using IsSmoothCoefficients.norm_toLp_a_sub_le h u u') hK)

/-- **Lemma 3.1 (`eq:lip`) for the reference evolution.** The drift of the reference evolution
`R^N_s` of Section 3.3, `B_t(x) = a(x) + ∫ K(x, y) μ_t(dy)`, is Lipschitz for the Euclidean norm
with constant `L = L_a + L₁`, uniformly in time. -/
theorem lipschitzWith_euclideanDrift_singleDrift (h : IsSmoothCoefficients a K La L₁ L₂ M)
    {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution (kernelOf a K) μ) (t : ℝ) :
    LipschitzWith (lipLNN La L₁) (GaussianBridge.euclideanDrift
      (PrescribedReference.singleDrift (b := kernelOf a K) (μ := μ)) t) := by
  have := hμ.1 (max 0 t) (le_max_left _ _)
  exact IsSmoothCoefficients.lipschitzWith_euclidMap_nonlinearDrift h (μ (max 0 t))

end IsSmoothCoefficients

end SharpWasserstein.Sharp.Source
