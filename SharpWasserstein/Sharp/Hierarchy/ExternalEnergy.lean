/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.Hierarchy.ExternalBounds
public import SharpWasserstein.ExternalInteractionEnergyCancellation

/-!
# The integrated external term of the hierarchy

This file integrates the pointwise estimates of Lemma 5.2 (`lem:pointwise`) for the external
operator `Φ` against an arbitrary law `ρ'` of `m + 1` particles and an arbitrary square
integrable field `U`. Writing `U = (∇f, 0) + z`, the external contribution
`III = 2 ∫ ⟨U, ∇Φf⟩ dρ' - ∫ Φ(|∇f|²) dρ'` of the proof of Lemma 5.3 (`lem:gal-ode`) satisfies
`III ≤ (2L₁ + ε) ρ(|∇f|²) + ε ρ(|D²f|²) + (mG/ε) ‖z‖²`.
With `ε = 1/2` this is the bound `III ≤ (2L₁ + 1/2) P + H/2 + 2mG (E_{m+1} - ε)` of the paper.

The proof is the one of the development (`ExternalInteraction.integral_external_le`), with the
dimension-dependent pointwise constants replaced by the sharp ones of
`SharpWasserstein.Sharp.Hierarchy.ExternalBounds`. Integrability is inherited from the
development, which needs only some (sup-norm) bounds on `K`; these do not enter the estimate.

## Main statements

* `BoundedSmoothKernel.exists_kernelBounds`: qualitative sup-norm bounds of a bounded smooth
  kernel.
* `integral_external_le_sharp`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ContDiff InnerProductSpace BigOperators

namespace SharpWasserstein.Sharp.Hierarchy

open WeightedTangent WeightedMarginal BochnerIdentity ExternalInteraction

variable {d m : ℕ}

/-- A bounded smooth kernel has some sup-norm value and first-derivative bounds. -/
theorem exists_kernelBounds_of_boundedSmooth {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) :
    ∃ Mb Lb₁ Lb₂ : ℝ, 0 ≤ Mb ∧ 0 ≤ Lb₁ ∧ 0 ≤ Lb₂ ∧ KernelBounds b Mb Lb₁ Lb₂ := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := hb.boundedDerivatives 0
  obtain ⟨C₁, hC₁0, hC₁⟩ := hb.boundedDerivatives 1
  have hdiff : Differentiable ℝ (Function.uncurry b) := hb.smooth.differentiable (by simp)
  have hfd : ∀ z, ‖fderiv ℝ (Function.uncurry b) z‖ ≤ C₁ := fun z => by
    rw [← norm_iteratedFDeriv_one]; exact hC₁ z
  refine ⟨C₀, C₁, C₁, hC₀0, hC₁0, hC₁0, ?_, ?_, ?_⟩
  · intro x y
    have := hC₀ (x, y)
    rwa [norm_iteratedFDeriv_zero] at this
  · intro x y
    have hx : (fun z => b z y) = Function.uncurry b ∘ fun z => (z, y) := rfl
    rw [hx, fderiv_comp x (hdiff _) ((hasFDerivAt_prodMk_left x y).differentiableAt)]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [(hasFDerivAt_prodMk_left x y).fderiv]
    calc _ ≤ C₁ * 1 := mul_le_mul (hfd _) (ContinuousLinearMap.norm_inl_le_one ℝ _ _)
          (norm_nonneg _) hC₁0
      _ = C₁ := mul_one _
  · intro x y
    have hy : b x = Function.uncurry b ∘ fun z => (x, z) := rfl
    rw [hy, fderiv_comp y (hdiff _) ((hasFDerivAt_prodMk_right x y).differentiableAt)]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [(hasFDerivAt_prodMk_right x y).fderiv]
    calc _ ≤ C₁ * 1 := mul_le_mul (hfd _) (ContinuousLinearMap.norm_inr_le_one ℝ _ _)
          (norm_nonneg _) hC₁0
      _ = C₁ := mul_one _

variable [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]
  (μ : Measure (Point (m*d+d)))
  {a : Position d → Position d} {K : Position d → Position d → Position d} {La L₁ L₂ M : ℝ}
  (h : SplitKernel a K La L₁ L₂ M) (hm : 1 ≤ m)
  {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
  (hG : MemLp (fun z => gradient f (prefixProjection (m*d) d z)) 2 μ)
  (hH : Integrable (fun z => HierarchyAlgebra.frobeniusSq
    (hessian f (prefixProjection (m*d) d z))) μ)
include h hm hf hG hH

/-- `∇Φf` is square integrable. -/
theorem interaction_gradient_memLp_sharp : MemLp (gradient (interaction K f)) 2 μ := by
  obtain ⟨Mb, Lb₁, Lb₂, hMb, hLb₁, hLb₂, hbound⟩ := exists_kernelBounds_of_boundedSmooth h.smooth_K
  exact interaction_gradient_memLp μ h.smooth_K hbound hm hMb hLb₁ hLb₂ hf hG hH

/-- `∫ |∇Φf|² ≤ mG (∫ |∇f|² + ∫ |D²f|²)`. -/
theorem integral_interaction_gradient_sq_le_sharp :
    (∫ z, ‖gradient (interaction K f) z‖ ^ 2 ∂μ) ≤
      gConst L₁ L₂ M * (m : ℝ) *
        ((∫ z, ‖gradient f (prefixProjection (m*d) d z)‖ ^ 2 ∂μ) +
          ∫ z, HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z)) ∂μ) := by
  have hg := (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  have hΦ := interaction_gradient_memLp_sharp μ h hm hf hG hH
  have hi := (memLp_two_iff_integrable_sq_norm hΦ.aestronglyMeasurable).mp hΦ
  have hh := integral_mono hi ((hg.add hH).const_mul (gConst L₁ L₂ M * (m : ℝ)))
    (interaction_gradient_norm_sq_le_sharp h hm hf)
  simpa only [Pi.add_apply, integral_const_mul, integral_add hg hH] using hh

/-- Cauchy–Schwarz with the sharp constant, in squared form. -/
theorem integral_pairing_sq_le_sharp {V : Point (m*d+d) → Point (m*d+d)} (hV : MemLp V 2 μ) :
    (∫ z, ⟪V z, gradient (interaction K f) z⟫_ℝ ∂μ) ^ 2 ≤
      gConst L₁ L₂ M * (m : ℝ) * (∫ z, ‖V z‖ ^ 2 ∂μ) *
        ((∫ z, ‖gradient f (prefixProjection (m*d) d z)‖ ^ 2 ∂μ) +
          ∫ z, HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z)) ∂μ) := by
  have hΦ := interaction_gradient_memLp_sharp μ h hm hf hG hH
  have hc := (norm_integral_le_integral_norm
    (fun z => ⟪V z, gradient (interaction K f) z⟫_ℝ)).trans
    (PointwiseTrajectory.integral_norm_inner_le hV hΦ)
  rw [Real.norm_eq_abs, PointwiseTrajectory.norm_toLp_two_eq_sqrt hV,
    PointwiseTrajectory.norm_toLp_two_eq_sqrt hΦ] at hc
  have hV₀ : 0 ≤ ∫ z, ‖V z‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hΦ₀ : 0 ≤ ∫ z, ‖gradient (interaction K f) z‖ ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hc
  rw [sq_abs, mul_pow, Real.sq_sqrt hV₀, Real.sq_sqrt hΦ₀] at hs
  have hI := integral_interaction_gradient_sq_le_sharp μ h hm hf hG hH
  calc _ ≤ (∫ z, ‖V z‖ ^ 2 ∂μ) * ∫ z, ‖gradient (interaction K f) z‖ ^ 2 ∂μ := hs
    _ ≤ (∫ z, ‖V z‖ ^ 2 ∂μ) * (gConst L₁ L₂ M * (m : ℝ) *
        ((∫ z, ‖gradient f (prefixProjection (m*d) d z)‖ ^ 2 ∂μ) +
          ∫ z, HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z)) ∂μ)) :=
        mul_le_mul_of_nonneg_left hI hV₀
    _ = _ := by ring

/-- Young absorption of the fluctuation pairing with the sharp constant `mG/ε`. -/
theorem fluctuation_pairing_young_sharp {U : Point (m*d+d) → Point (m*d+d)} (hU : MemLp U 2 μ)
    {ε : ℝ} (hε : 0 < ε) :
    2 * |∫ z, ⟪U z - prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z)),
      gradient (interaction K f) z⟫_ℝ ∂μ| ≤
      ε * ((∫ z, ‖gradient f (prefixProjection (m*d) d z)‖ ^ 2 ∂μ) +
          ∫ z, HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z)) ∂μ) +
        (gConst L₁ L₂ M * (m : ℝ) / ε) *
          (∫ z, ‖U z - prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z))‖ ^ 2
            ∂μ) := by
  have hC := gConst_nonneg L₁ L₂ M
  have hV₀ : 0 ≤ ∫ z, ‖U z - prefixEmbedding (m*d) d
      (gradient f (prefixProjection (m*d) d z))‖ ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  have hG₀ : 0 ≤ ∫ z, ‖gradient f (prefixProjection (m*d) d z)‖ ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  have hH₀ : 0 ≤ ∫ z, HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z)) ∂μ :=
    integral_nonneg fun _ => HierarchyAlgebra.frobeniusSq_nonneg _
  have hh := young_of_sq_le (by positivity) (add_nonneg hG₀ hH₀) hε
    (integral_pairing_sq_le_sharp μ h hm hf hG hH (fluctuation_memLp μ hG hU))
  simp only [fluctuation, liftedGradient] at hh
  convert hh using 1
  ring

omit hH in
/-- `∫ diag ≤ L₁ ∫ |∇f|²` (integrated `eq:cancel`). -/
theorem integral_diagonalEnergy_le_sharp :
    (∫ z, diagonalEnergy K z (gradient f (prefixProjection (m*d) d z)) ∂μ) ≤
      L₁ * (∫ z, ‖gradient f (prefixProjection (m*d) d z)‖ ^ 2 ∂μ) := by
  obtain ⟨Mb, Lb₁, Lb₂, hMb, hLb₁, hLb₂, hbound⟩ := exists_kernelBounds_of_boundedSmooth h.smooth_K
  have hg := (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  have hh := integral_mono (diagonalEnergy_integrable μ h.smooth_K hbound hm hLb₁ hLb₂ hf hG)
    (hg.const_mul L₁) (fun z => diagonalEnergy_le_sharp h z _)
  simpa only [integral_const_mul] using hh

/-- The external contribution `III` with the sharp constants (proof of Lemma 5.3):
`III ≤ (2L₁ + ε) ∫|∇f|² + ε ∫|D²f|² + (mG/ε) ∫ |U - (∇f, 0)|²`. -/
theorem integral_external_le_sharp {U : Point (m*d+d) → Point (m*d+d)} (hU : MemLp U 2 μ)
    {ε : ℝ} (hε : 0 < ε) :
    2 * (∫ z, ⟪U z, gradient (interaction K f) z⟫_ℝ ∂μ) -
      (∫ z, ⟪liftedForce K z,
        gradient (fun q => ‖gradient f (prefixProjection (m*d) d q)‖ ^ 2) z⟫_ℝ ∂μ) ≤
      (2 * L₁ + ε) * (∫ z, ‖gradient f (prefixProjection (m*d) d z)‖ ^ 2 ∂μ) +
      ε * (∫ z, HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z)) ∂μ) +
      (gConst L₁ L₂ M * (m : ℝ) / ε) *
        (∫ z, ‖U z - prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z))‖ ^ 2
          ∂μ) := by
  obtain ⟨Mb, Lb₁, Lb₂, hMb, hLb₁, hLb₂, hbound⟩ := exists_kernelBounds_of_boundedSmooth h.smooth_K
  rw [integral_external_decomposition μ h.smooth_K hbound hm hMb hLb₁ hLb₂ hf hG hH hU]
  have hD := integral_diagonalEnergy_le_sharp μ h hm hf hG
  have hY := fluctuation_pairing_young_sharp μ h hm hf hG hH hU hε
  have habs := le_abs_self (∫ z, ⟪U z - prefixEmbedding (m*d) d
    (gradient f (prefixProjection (m*d) d z)), gradient (interaction K f) z⟫_ℝ ∂μ)
  nlinarith

end SharpWasserstein.Sharp.Hierarchy
