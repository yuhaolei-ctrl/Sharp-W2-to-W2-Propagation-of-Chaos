module

public import SharpWasserstein.Compat
public import SharpWasserstein.ExternalInteractionEnergy

@[expose] public section

/-! Separation of the actual external flux into a lifted marginal cancellation
and an L² fluctuation. Integrability follows from the literal field energies. -/
noncomputable section
namespace SharpWasserstein.ExternalInteraction
open MeasureTheory WeightedTangent WeightedMarginal BochnerIdentity PDEPairings Filter
open scoped BigOperators InnerProductSpace ContDiff
variable {d m : ℕ} [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]

omit [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))] in
/-- A finite bound for the absolute diagonal pairing, used only to justify
integration. The sharper signed bound remains `diagonalEnergy_le`. -/
theorem diagonalEnergy_abs_le {b : Position d → Position d → Position d}
    {M L₁ L₂ : ℝ} (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hm : 1 ≤ m) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (z : Point (m*d+d)) (w : Point (m*d)) :
    |diagonalEnergy b z w| ≤ Real.sqrt (2*(d:ℝ)*(m:ℝ)*(L₁^2+L₂^2))*‖w‖^2 := by
  have hK : 0 ≤ 2*(d:ℝ)*(m:ℝ)*(L₁^2+L₂^2) := by positivity
  have hD : ‖fderiv ℝ (force b) z‖ ≤ Real.sqrt (2*(d:ℝ)*(m:ℝ)*(L₁^2+L₂^2)) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hK]
    exact force_fderiv_norm_sq_le hb hbound hm hL₁ hL₂ z
  rw [← force_prefix_pairing hb]
  calc
    _ ≤ ‖fderiv ℝ (force b) z (prefixEmbedding (m*d) d w)‖*‖w‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖fderiv ℝ (force b) z‖*‖w‖)*‖w‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa only [LinearIsometry.norm_map] using ContinuousLinearMap.le_opNorm (fderiv ℝ (force b) z) (prefixEmbedding (m*d) d w)
    _ ≤ (Real.sqrt (2*(d:ℝ)*(m:ℝ)*(L₁^2+L₂^2))*‖w‖)*‖w‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

section Energy
variable (μ : Measure (Point (m*d+d)))
  {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hm : 1 ≤ m) (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
  (hG : MemLp (fun z => gradient f (prefixProjection (m*d) d z)) 2 μ)
  (hH : Integrable (fun z => HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z))) μ)
include hb hbound hm hL₁ hL₂ hf hG

/-- The genuine `D₁b` energy is integrable from the actual marginal tangent action. -/
theorem diagonalEnergy_integrable :
    Integrable (fun z => diagonalEnergy b z (gradient f (prefixProjection (m*d) d z))) μ := by
  have hg := (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  have hgC : Continuous (fun z : Point (m*d+d) => gradient f (prefixProjection (m*d) d z)) :=
    (smooth_gradient hf).continuous.comp (prefixProjection (m*d) d).continuous
  have hc : Continuous (fun z : Point (m*d+d) =>
      ⟪fderiv ℝ (force b) z (prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z))),
        gradient f (prefixProjection (m*d) d z)⟫_ℝ) :=
    (((force_smooth hb).continuous_fderiv (by simp)).clm_apply
      ((prefixEmbedding (m*d) d).continuous.comp hgC)).inner hgC
  have he : (fun z => diagonalEnergy b z (gradient f (prefixProjection (m*d) d z))) =
      (fun z => ⟪fderiv ℝ (force b) z (prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z))),
        gradient f (prefixProjection (m*d) d z)⟫_ℝ) := by
    funext z
    exact (force_prefix_pairing hb z _).symm
  apply (hg.const_mul (Real.sqrt (2*(d:ℝ)*(m:ℝ)*(L₁^2+L₂^2)))).mono'
    (by rw [he]; exact hc.aestronglyMeasurable)
  exact Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs]
    exact diagonalEnergy_abs_le hb hbound hm hL₁ hL₂ z _)

/-- Integrating the signed diagonal term costs no particle factor. -/
theorem integral_diagonalEnergy_le :
    (∫ z, diagonalEnergy b z (gradient f (prefixProjection (m*d) d z)) ∂μ) ≤
      (d:ℝ)*L₁*(∫ z, ‖gradient f (prefixProjection (m*d) d z)‖^2 ∂μ) := by
  have hg := (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  have hh := integral_mono (diagonalEnergy_integrable μ hb hbound hm hL₁ hL₂ hf hG)
    (hg.const_mul ((d:ℝ)*L₁)) (fun z => diagonalEnergy_le hbound hL₁ z _)
  simpa only [integral_const_mul] using hh

include hM hH

/-- The other lifted cancellation term is integrable; no undefined integral
is used in the subsequent exact decomposition. -/
theorem lifted_energy_transport_integrable :
    Integrable (fun z => ⟪liftedForce b z,
      gradient (fun q => ‖gradient f (prefixProjection (m*d) d q)‖^2) z⟫_ℝ) μ := by
  have hΦ := interaction_gradient_memLp μ hb hbound hm hM hL₁ hL₂ hf hG hH
  have hL : MemLp (liftedGradient f) 2 μ :=
    (prefixEmbedding (m*d) d).toContinuousLinearMap.comp_memLp' hG
  have hI := PointwiseTrajectory.integrable_inner_of_memLp hL hΦ
  have hD := diagonalEnergy_integrable μ hb hbound hm hL₁ hL₂ hf hG
  apply ((hI.const_mul 2).sub (hD.const_mul 2)).congr
  filter_upwards [] with z
  have hh := lifted_hessian_cancellation hb hf z
  change 2*⟪liftedGradient f z,gradient (interaction b f) z⟫_ℝ-
    2*diagonalEnergy b z (gradient f (prefixProjection (m*d) d z)) = _
  dsimp only [liftedGradient]
  linarith

/-- The actual full external contribution splits into the literal fluctuation
pairing and the genuine diagonal derivative energy. -/
theorem integral_external_decomposition {U : Point (m*d+d) → Point (m*d+d)} (hU : MemLp U 2 μ) :
    2*(∫ z, ⟪U z,gradient (interaction b f) z⟫_ℝ ∂μ)-
      (∫ z, ⟪liftedForce b z,
        gradient (fun q => ‖gradient f (prefixProjection (m*d) d q)‖^2) z⟫_ℝ ∂μ) =
    2*(∫ z, ⟪U z-prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z)),
      gradient (interaction b f) z⟫_ℝ ∂μ)+
    2*(∫ z, diagonalEnergy b z (gradient f (prefixProjection (m*d) d z)) ∂μ) := by
  have hΦ := interaction_gradient_memLp μ hb hbound hm hM hL₁ hL₂ hf hG hH
  have hI := PointwiseTrajectory.integrable_inner_of_memLp hU hΦ
  have hV := PointwiseTrajectory.integrable_inner_of_memLp (fluctuation_memLp μ hG hU) hΦ
  have hD := diagonalEnergy_integrable μ hb hbound hm hL₁ hL₂ hf hG
  have hT := lifted_energy_transport_integrable μ hb hbound hm hM hL₁ hL₂ hf hG hH
  calc
    _ = ∫ z, (2*⟪U z,gradient (interaction b f) z⟫_ℝ-
        ⟪liftedForce b z,gradient (fun q => ‖gradient f (prefixProjection (m*d) d q)‖^2) z⟫_ℝ) ∂μ := by
      rw [integral_sub (hI.const_mul 2) hT,integral_const_mul]
    _ = ∫ z, (2*⟪fluctuation f U z,gradient (interaction b f) z⟫_ℝ+
        2*diagonalEnergy b z (gradient f (prefixProjection (m*d) d z))) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      have hh := lifted_hessian_cancellation hb hf z
      simp only [fluctuation,liftedGradient,inner_sub_left]
      linarith
    _ = _ := by rw [integral_add (hV.const_mul 2) (hD.const_mul 2),integral_const_mul,integral_const_mul]; rfl

/-- The actual external contribution obeys a sharp linear-in-`m` fluctuation
bound and an arbitrarily small Hessian absorption. This is derived from the
literal fields, not an assumed differential hierarchy. -/
theorem integral_external_le {U : Point (m*d+d) → Point (m*d+d)} (hU : MemLp U 2 μ)
    {ε : ℝ} (hε : 0 < ε) :
    2*(∫ z, ⟪U z,gradient (interaction b f) z⟫_ℝ ∂μ)-
      (∫ z, ⟪liftedForce b z,
        gradient (fun q => ‖gradient f (prefixProjection (m*d) d q)‖^2) z⟫_ℝ ∂μ) ≤
      (2*(d:ℝ)*L₁+ε)*(∫ z, ‖gradient f (prefixProjection (m*d) d z)‖^2 ∂μ)+
      ε*(∫ z, HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z)) ∂μ)+
      (gradientConstant d M L₁ L₂*(m:ℝ)/ε)*
        (∫ z, ‖U z-prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z))‖^2 ∂μ) := by
  rw [integral_external_decomposition μ hb hbound hm hM hL₁ hL₂ hf hG hH hU]
  have hD := integral_diagonalEnergy_le μ hb hbound hm hL₁ hL₂ hf hG
  have hY := fluctuation_pairing_young μ hb hbound hm hM hL₁ hL₂ hf hG hH hU hε
  have habs := le_abs_self (∫ z, ⟪U z-prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z)),
    gradient (interaction b f) z⟫_ℝ ∂μ)
  nlinarith

end Energy
end SharpWasserstein.ExternalInteraction
