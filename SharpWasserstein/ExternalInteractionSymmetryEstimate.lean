import SharpWasserstein.ExternalInteractionSymmetryMarginal

/-! Applying genuine source averaging to the actual interaction test. Bounds
needed for the noncompact source action are derived from the kernel bounds
and first/second derivatives of the potential; compact tests supply these
bounds automatically. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.ExternalInteractionSymmetry
open WeightedTangent WeightedMarginal ExternalInteraction PropagatedSourcePermutation
open BochnerIdentity PDEPairings

/-- The actual external interaction is bounded and has bounded gradient when
the smooth potential has bounded gradient and Hessian. The interaction bounds
are derived, rather than imposed as source-action assumptions. -/
theorem interaction_bounded_gradient {d m : ℕ} {b : Position d → Position d → Position d}
    {M L₁ L₂ : ℝ} (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hm : 1 ≤ m) (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ∃ G : ℝ, ∀ x, ‖gradient f x‖ ≤ G)
    (hh : ∃ H : ℝ, ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ H) :
    (∃ A : ℝ, ∀ z, |interaction b f z| ≤ A) ∧
      (∃ B : ℝ, ∀ z, ‖gradient (interaction b f) z‖ ≤ B) := by
  obtain ⟨G,hG⟩ := hg
  obtain ⟨H,hH⟩ := hh
  let A := Real.sqrt ((d:ℝ)*(m:ℝ)*M^2)
  let D := Real.sqrt (2*(d:ℝ)*(m:ℝ)*(L₁^2+L₂^2))
  have hA (z : Point (m*d+d)) : ‖force b z‖ ≤ A := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity)]
    exact force_norm_sq_le hbound hM z
  have hD (z : Point (m*d+d)) : ‖fderiv ℝ (force b) z‖ ≤ D := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity)]
    exact force_fderiv_norm_sq_le hb hbound hm hL₁ hL₂ z
  constructor
  · refine ⟨A*G,fun z => ?_⟩
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hA z) (hG _) (norm_nonneg _) (Real.sqrt_nonneg _))
  · refine ⟨D*G+A*H,fun z => ?_⟩
    exact (interaction_gradient_norm_le hb hf z).trans (add_le_add
      (mul_le_mul (hD z) (hG _) (norm_nonneg _) (Real.sqrt_nonneg _))
      (mul_le_mul (hA z) (hH _) (norm_nonneg _) (Real.sqrt_nonneg _)))

/-- Genuine compact smooth marginal potentials supply the bounded-gradient
and bounded-Hessian hypotheses automatically. -/
theorem compact_interaction_bounded_gradient {d m : ℕ}
    {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hm : 1 ≤ m) (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (φ : Test (m*d)) :
    (∃ A : ℝ, ∀ z, |interaction b (φ : Point (m*d) → ℝ) z| ≤ A) ∧
      (∃ B : ℝ, ∀ z, ‖gradient (interaction b (φ : Point (m*d) → ℝ)) z‖ ≤ B) := by
  apply interaction_bounded_gradient hb hbound hm hM hL₁ hL₂ φ.property.1
  · exact (compactSupport_test_gradient φ).exists_bound_of_continuous (continuous_test_gradient φ)
  · exact ((compactSupport_test_gradient φ).fderiv ℝ).exists_bound_of_continuous
      ((smooth_gradient φ.property.1).continuous_fderiv (by simp))

/-- The manuscript's actual external interaction contribution is the canonical
next-coordinate source pairing with coefficient (N−m)/N. Smooth compact
potential hypotheses discharge every noncompact source-action bound. -/
theorem external_interaction_meanField_marginal {d m N : ℕ}
    [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
    [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]
    (hm : m < N) (hm0 : 1 ≤ m) (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    (hμ : ∀ e : Equiv.Perm (Fin N), μ.map (euclideanPermutation e) = μ)
    (U : Lp (Point (N*d)) 2 μ)
    (hU : ∀ e : Equiv.Perm (Fin N), ∀ᵐ x ∂μ,
      U (euclideanPermutation e x) = euclideanPermutation e (U x))
    {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (φ : Test (m*d)) :
    (N:ℝ)⁻¹*(∑ j : Fin N with m ≤ j.val, pairing μ U
      (particleInteraction hm.le j b (φ : Point (m*d) → ℝ))) =
      (((N:ℝ)-m)/N) * ∫ y, ⟪gradient (interaction b (φ : Point (m*d) → ℝ)) y,
        (representative (μ.map (observation hm.le ⟨m,hm⟩))
          (observedSource hm.le ⟨m,hm⟩ μ U) :
          Lp (Point (m*d+d)) 2 (μ.map (observation hm.le ⟨m,hm⟩))) y⟫_ℝ
        ∂μ.map (observation hm.le ⟨m,hm⟩) := by
  obtain ⟨hA,hB⟩ := compact_interaction_bounded_gradient hb hbound hm0 hM hL₁ hL₂ φ
  exact external_pairing_meanField_marginal hm μ hμ U hU _
    (interaction_smooth hb φ.property.1) hA hB

end SharpWasserstein.ExternalInteractionSymmetry
