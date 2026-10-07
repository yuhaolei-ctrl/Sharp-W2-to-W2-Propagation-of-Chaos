module

public import SharpWasserstein.Compat
public import SharpWasserstein.ExternalInteractionGradientBase

@[expose] public section

/-! The actual external interaction test and its sharp-in-particle-count
Euclidean gradient bound. All matrices below are genuine Fréchet derivatives. -/
noncomputable section
namespace SharpWasserstein.ExternalInteraction
open WeightedTangent WeightedMarginal BochnerIdentity PDEPairings
open scoped BigOperators InnerProductSpace ContDiff
variable {n k d m : ℕ}

/-- Coordinate expansion of an actual Euclidean vector. -/
theorem sum_coordinate_vectors (v : Point n) :
    (∑ i : Fin n, v i • EuclideanSpace.single i 1) = v := by
  ext j
  simp [Pi.single_apply]

/-- Coordinate expansion of a genuine first differential. -/
theorem directionDeriv_coordinate_sum (f : Point n → ℝ) (v x : Point n) :
    directionDeriv v f x = ∑ i : Fin n, v i*directionDeriv (EuclideanSpace.single i 1) f x := by
  unfold directionDeriv
  conv_lhs => rw [← sum_coordinate_vectors v]
  simp only [map_sum,map_smul,smul_eq_mul]

/-- The differential of the gradient is the actual Hessian matrix action. -/
theorem fderiv_gradient_matrixAction {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f) (x v : Point n) :
    fderiv ℝ (gradient f) x v = HierarchyAlgebra.matrixAction (hessian f x) v := by
  ext i
  have hh := DriftEnergyIdentity.fderiv_gradient_inner hf v (EuclideanSpace.single i 1) x
  simp only [EuclideanSpace.inner_single_right,RCLike.conj_to_real,one_mul] at hh
  rw [hh,directionDeriv_coordinate_sum]
  apply Finset.sum_congr rfl
  intro j _
  change v j*hessian f x j i = hessian f x i j*v j
  rw [show hessian f x j i = hessian f x i j from
    directionDeriv_commute (contDiff_two_of_smooth hf) _ _ _]
  ring

/-- Hilbert--Schmidt control of the genuine derivative of the gradient. -/
theorem fderiv_gradient_norm_sq_le {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f) (x : Point n) :
    ‖fderiv ℝ (gradient f) x‖^2 ≤ HierarchyAlgebra.frobeniusSq (hessian f x) := by
  let H := HierarchyAlgebra.frobeniusSq (hessian f x)
  have hH : 0 ≤ H := HierarchyAlgebra.frobeniusSq_nonneg _
  have hh : ‖fderiv ℝ (gradient f) x‖ ≤ Real.sqrt H := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    rw [fderiv_gradient_matrixAction hf]
    have hb := HierarchyAlgebra.matrixAction_norm_sq_le (hessian f x) v
    apply (sq_le_sq₀ (norm_nonneg _) (show 0 ≤ Real.sqrt H*‖v‖ by positivity)).mp
    have hs := Real.sq_sqrt hH
    nlinarith
  have hs := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg H)).mpr hh
  rwa [Real.sq_sqrt hH] at hs

/-- The genuine scalar external interaction, with Euclidean gradient blocks. -/
def interaction (b : Position d → Position d → Position d) (f : Point (m*d) → ℝ)
    (z : Point (m*d+d)) : ℝ :=
  ⟪force b z,gradient f (prefixProjection (m*d) d z)⟫_ℝ

/-- The external test is genuinely smooth when the kernel and potential are smooth. -/
theorem interaction_smooth {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (interaction b f) :=
  (force_smooth hb).inner ℝ ((smooth_gradient hf).comp (prefixProjection (m*d) d).contDiff)

/-- Unfolding the Euclidean inner product gives the manuscript's actual block sum. -/
theorem interaction_eq_sum (b : Position d → Position d → Position d) (f : Point (m*d) → ℝ)
    (z : Point (m*d+d)) :
    interaction b f z = ∑ i : Fin m, ∑ a : Fin d,
      b (positions z i) (externalPosition z) a*
        gradient f (prefixProjection (m*d) d z) (finProdFinEquiv (i,a)) := by
  unfold interaction
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply,conj_trivial]
  calc
    _ = ∑ p : Fin m × Fin d, b (positions z p.1) (externalPosition z) p.2*
        gradient f (prefixProjection (m*d) d z) (finProdFinEquiv p) := by
      symm
      apply Fintype.sum_equiv finProdFinEquiv
      rintro ⟨i,a⟩
      simp only [force,configurationEuclidean_apply_coordinate]
      ring
    _ = _ := Fintype.sum_prod_type _

/-- The exact chain and product rule for the external interaction. -/
theorem fderiv_interaction {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (z v : Point (m*d+d)) :
    fderiv ℝ (interaction b f) z v =
      ⟪fderiv ℝ (force b) z v,gradient f (prefixProjection (m*d) d z)⟫_ℝ+
      ⟪force b z,fderiv ℝ (gradient f) (prefixProjection (m*d) d z)
        (prefixProjection (m*d) d v)⟫_ℝ := by
  have ha := (force_smooth (m := m) hb).differentiable (by simp)
  have hg := (smooth_gradient hf).differentiable (by simp)
  unfold interaction
  have he := fderiv_inner_apply ℝ (ha z) (hg.comp (prefixProjection (m*d) d).differentiable z) v
  dsimp only [Function.comp_apply] at he
  rw [he]
  rw [fderiv_comp z (hg _) (prefixProjection (m*d) d).differentiableAt,
    ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  ring

/-- No particle factor is introduced by the chain/product-rule estimate itself. -/
theorem interaction_gradient_norm_le {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (z : Point (m*d+d)) :
    ‖gradient (interaction b f) z‖ ≤
      ‖fderiv ℝ (force b) z‖*‖gradient f (prefixProjection (m*d) d z)‖+
      ‖force b z‖*‖fderiv ℝ (gradient f) (prefixProjection (m*d) d z)‖ := by
  rw [SmoothCutoff.norm_gradient_eq_fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [fderiv_interaction hb hf]
  calc
    ‖⟪fderiv ℝ (force b) z v,gradient f (prefixProjection (m*d) d z)⟫_ℝ+
        ⟪force b z,fderiv ℝ (gradient f) (prefixProjection (m*d) d z)
          (prefixProjection (m*d) d v)⟫_ℝ‖ ≤
      ‖fderiv ℝ (force b) z v‖*‖gradient f (prefixProjection (m*d) d z)‖+
        ‖force b z‖*‖fderiv ℝ (gradient f) (prefixProjection (m*d) d z)
          (prefixProjection (m*d) d v)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
    _ ≤ (‖fderiv ℝ (force b) z‖*‖v‖)*‖gradient f (prefixProjection (m*d) d z)‖+
        ‖force b z‖*(‖fderiv ℝ (gradient f) (prefixProjection (m*d) d z)‖*‖v‖) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_left (prefix_norm_le _ _ _) (norm_nonneg _))
    _ = _ := by ring

/-- The actual external-test gradient has linear, not quadratic, dependence on
particle count. The only coordinate norm-equivalence loss depends on `d`. -/
theorem interaction_gradient_norm_sq_le {b : Position d → Position d → Position d}
    {M L₁ L₂ : ℝ} (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hm : 1 ≤ m) (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f) (z : Point (m*d+d)) :
    ‖gradient (interaction b f) z‖^2 ≤
      4*(d:ℝ)*(m:ℝ)*(L₁^2+L₂^2)*‖gradient f (prefixProjection (m*d) d z)‖^2+
      2*(d:ℝ)*(m:ℝ)*M^2*HierarchyAlgebra.frobeniusSq
        (hessian f (prefixProjection (m*d) d z)) := by
  have hn := interaction_gradient_norm_le hb hf z
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  have ha := force_norm_sq_le hbound hM z
  have hd := force_fderiv_norm_sq_le hb hbound hm hL₁ hL₂ z
  have hh := fderiv_gradient_norm_sq_le hf (prefixProjection (m*d) d z)
  have hterm₁ := mul_le_mul_of_nonneg_right hd (sq_nonneg ‖gradient f (prefixProjection (m*d) d z)‖)
  have hterm₂ := mul_le_mul ha hh (sq_nonneg _) (by positivity : 0 ≤ (d:ℝ)*(m:ℝ)*M^2)
  nlinarith [sq_nonneg (‖fderiv ℝ (force b) z‖*‖gradient f (prefixProjection (m*d) d z)‖-
    ‖force b z‖*‖fderiv ℝ (gradient f) (prefixProjection (m*d) d z)‖)]

/-- A single coefficient depending only on the original kernel bounds and `d`. -/
theorem interaction_gradient_norm_sq_le_combined {b : Position d → Position d → Position d}
    {M L₁ L₂ : ℝ} (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hm : 1 ≤ m) (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f) (z : Point (m*d+d)) :
    ‖gradient (interaction b f) z‖^2 ≤
      (4*(d:ℝ)*(L₁^2+L₂^2)+2*(d:ℝ)*M^2)*(m:ℝ)*
        (‖gradient f (prefixProjection (m*d) d z)‖^2+
          HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z))) := by
  apply (interaction_gradient_norm_sq_le hb hbound hm hM hL₁ hL₂ hf z).trans
  have hH := HierarchyAlgebra.frobeniusSq_nonneg (hessian f (prefixProjection (m*d) d z))
  have hcross₁ : 0 ≤ 4*(d:ℝ)*(m:ℝ)*(L₁^2+L₂^2)*
      HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z)) := by positivity
  have hcross₂ : 0 ≤ 2*(d:ℝ)*(m:ℝ)*M^2*‖gradient f (prefixProjection (m*d) d z)‖^2 := by positivity
  nlinarith

end SharpWasserstein.ExternalInteraction
