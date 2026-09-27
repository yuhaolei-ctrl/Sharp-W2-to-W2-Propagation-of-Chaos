import SharpWasserstein.ExternalInteractionGradient

/-! Exact lifted external-Hessian cancellation. The remaining diagonal term is
the actual first-argument derivative of the original interaction kernel. -/
noncomputable section
namespace SharpWasserstein.ExternalInteraction
open WeightedTangent WeightedMarginal BochnerIdentity PDEPairings
open scoped BigOperators InnerProductSpace ContDiff
variable {d m : ℕ}

/-- Extract the actual `i`th visible position as a linear map. -/
def positionMap (i : Fin m) : Point (m*d+d) →L[ℝ] Position d :=
  (ContinuousLinearMap.proj i).comp
    ((configurationEuclidean d m).symm.toContinuousLinearMap.comp (prefixProjection (m*d) d))

/-- Extract the extra particle in the kernel's original coordinate norm. -/
def externalMap : Point (m*d+d) →L[ℝ] Position d where
  toFun := externalPosition
  map_add' x y := rfl
  map_smul' c x := rfl
  cont := by unfold externalPosition; fun_prop

/-- The genuine full Jacobian of the assembled external-force field. -/
def forceDerivative (b : Position d → Position d → Position d) (z : Point (m*d+d)) :
    Point (m*d+d) →L[ℝ] Point (m*d) :=
  (configurationEuclidean d m).toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      (fderiv ℝ (Function.uncurry b) (positions z i,externalPosition z)).comp
        ((positionMap i).prod externalMap)))

theorem force_hasFDerivAt {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) (z : Point (m*d+d)) :
    HasFDerivAt (force b) (forceDerivative b z) z := by
  apply (configurationEuclidean d m).hasFDerivAt.comp z
  apply hasFDerivAt_pi.mpr
  intro i
  exact (hb.smooth.differentiable (by simp) (positions z i,externalPosition z)).hasFDerivAt.comp z
    ((positionMap i).hasFDerivAt.prodMk externalMap.hasFDerivAt)

/-- Holding the second argument fixed identifies the true first partial derivative. -/
theorem uncurry_fderiv_first {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) (x y u : Position d) :
    fderiv ℝ (Function.uncurry b) (x,y) (u,0) = fderiv ℝ (fun q => b q y) x u := by
  have hq : HasFDerivAt (fun q : Position d => (q,y))
      ((ContinuousLinearMap.id ℝ (Position d)).prod (0 : Position d →L[ℝ] Position d)) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const y x)
  have hh := ((hb.smooth.differentiable (by simp) (x,y)).hasFDerivAt.comp x hq).fderiv
  have hv := congrArg (fun A : Position d →L[ℝ] Position d => A u) hh
  simpa only [Function.comp_def,Function.uncurry,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,zero_apply] using hv.symm

/-- Visible tangent directions do not move the extra particle. -/
theorem externalMap_prefixEmbedding (w : Point (m*d)) :
    externalMap (prefixEmbedding (m*d) d w) = (0 : Position d) := by
  ext a
  simp [externalMap,externalPosition,suffixProjection,prefixEmbedding]

/-- The derivative in a lifted marginal direction is the actual block-diagonal
first-argument kernel derivative. -/
theorem force_fderiv_prefixEmbedding {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) (z : Point (m*d+d)) (w : Point (m*d)) :
    fderiv ℝ (force b) z (prefixEmbedding (m*d) d w) =
      configurationEuclidean d m (fun i =>
        fderiv ℝ (fun q => b q (externalPosition z)) (positions z i)
          ((configurationEuclidean d m).symm w i)) := by
  rw [(force_hasFDerivAt hb z).fderiv]
  simp only [forceDerivative,ContinuousLinearMap.comp_apply]
  apply congrArg (configurationEuclidean d m)
  funext i
  change fderiv ℝ (Function.uncurry b) (positions z i,externalPosition z)
    (positionMap i (prefixEmbedding (m*d) d w),externalMap (prefixEmbedding (m*d) d w)) = _
  rw [externalMap_prefixEmbedding]
  have hp : positionMap i (prefixEmbedding (m*d) d w) = (configurationEuclidean d m).symm w i := by
    simp [positionMap]
  rw [hp,uncurry_fderiv_first hb]

/-- The diagonal term is a genuine coordinate sum of `D₁b`, with no Hessian. -/
def diagonalEnergy (b : Position d → Position d → Position d)
    (z : Point (m*d+d)) (w : Point (m*d)) : ℝ :=
  ∑ i : Fin m, ∑ a : Fin d,
    (fderiv ℝ (fun q => b q (externalPosition z)) (positions z i)
      ((configurationEuclidean d m).symm w i)) a *
        ((configurationEuclidean d m).symm w i) a

/-- The exact Euclidean pairing of the actual diagonal derivative. -/
theorem force_prefix_pairing {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) (z : Point (m*d+d)) (w : Point (m*d)) :
    ⟪fderiv ℝ (force b) z (prefixEmbedding (m*d) d w),w⟫_ℝ = diagonalEnergy b z w := by
  rw [force_fderiv_prefixEmbedding hb,PiLp.inner_apply]
  simp only [RCLike.inner_apply,conj_trivial]
  calc
    _ = ∑ p : Fin m × Fin d,
        (fderiv ℝ (fun q => b q (externalPosition z)) (positions z p.1)
          ((configurationEuclidean d m).symm w p.1)) p.2*
            ((configurationEuclidean d m).symm w p.1) p.2 := by
      symm
      apply Fintype.sum_equiv finProdFinEquiv
      rintro ⟨i,a⟩
      simp only [configurationEuclidean_apply_coordinate,configurationEuclidean_symm_apply]
      ring
    _ = _ := Fintype.sum_prod_type _

/-- Lift the external force by zero in its extra-particle coordinate. -/
def liftedForce (b : Position d → Position d → Position d) : Point (m*d+d) → Point (m*d+d) :=
  (prefixEmbedding (m*d) d) ∘ force b

/-- The lifted drift test is exactly the actual external interaction. -/
theorem lifted_interaction_eq {b : Position d → Position d → Position d}
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f) :
    (fun z => ⟪liftedForce b z,gradient (f ∘ prefixProjection (m*d) d) z⟫_ℝ) = interaction b f := by
  funext z
  rw [gradient_comp_prefixProjection (hf.differentiable (by simp))]
  exact (inner_prefixEmbedding (m*d) d _ _).trans (by rw [prefixProjection_embedding]; rfl)

/-- Actual lifted Hessian terms cancel, leaving precisely the diagonal `D₁b`
energy. This is a differential identity for the original kernel and potential. -/
theorem lifted_hessian_cancellation {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (z : Point (m*d+d)) :
    2*⟪prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z)),
      gradient (interaction b f) z⟫_ℝ-
      ⟪liftedForce b z,gradient (fun q => ‖gradient f (prefixProjection (m*d) d q)‖^2) z⟫_ℝ =
      2*diagonalEnergy b z (gradient f (prefixProjection (m*d) d z)) := by
  have hF := hf.comp (prefixProjection (m*d) d).contDiff
  have hA : Differentiable ℝ (liftedForce (m := m) b) :=
    (prefixEmbedding (m*d) d).toContinuousLinearMap.differentiable.comp
      ((force_smooth hb).differentiable (by simp))
  have hh := DriftEnergyIdentity.drift_energy_integrand hF hA z
  rw [lifted_interaction_eq hf] at hh
  simp only [gradient_comp_prefixProjection (hf.differentiable (by simp)),LinearIsometry.norm_map] at hh
  rw [hh]
  congr 1
  rw [show fderiv ℝ (liftedForce b) z =
      (prefixEmbedding (m*d) d).toContinuousLinearMap.comp (fderiv ℝ (force b) z) from
    by
      change fderiv ℝ ((prefixEmbedding (m*d) d).toContinuousLinearMap ∘ force b) z = _
      rw [fderiv_comp z (prefixEmbedding (m*d) d).toContinuousLinearMap.differentiableAt
        ((force_smooth hb).differentiable (by simp) z),ContinuousLinearMap.fderiv]]
  rw [ContinuousLinearMap.comp_apply]
  change ⟪prefixEmbedding (m*d) d
    (fderiv ℝ (force b) z (prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z)))),
    prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z))⟫_ℝ = _
  rw [inner_prefixEmbedding,prefixProjection_embedding]
  exact force_prefix_pairing hb z _

/-- The surviving diagonal energy has no particle-count loss. -/
theorem diagonalEnergy_le {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hbound : KernelBounds b M L₁ L₂) (hL₁ : 0 ≤ L₁)
    (z : Point (m*d+d)) (w : Point (m*d)) :
    diagonalEnergy b z w ≤ (d:ℝ)*L₁*‖w‖^2 := by
  let u : Configuration d m := (configurationEuclidean d m).symm w
  have hcoord (i : Fin m) (a : Fin d) :
      (fderiv ℝ (fun q => b q (externalPosition z)) (positions z i) (u i)) a*u i a ≤
        L₁*‖u i‖^2 := by
    calc
      _ ≤ |(fderiv ℝ (fun q => b q (externalPosition z)) (positions z i) (u i)) a*u i a| := le_abs_self _
      _ = ‖(fderiv ℝ (fun q => b q (externalPosition z)) (positions z i) (u i)) a‖*‖u i a‖ := by
        rw [abs_mul,Real.norm_eq_abs,Real.norm_eq_abs]
      _ ≤ (L₁*‖u i‖)*‖u i‖ := by
        apply mul_le_mul _ (norm_le_pi_norm (u i) a) (norm_nonneg _) (by positivity)
        exact (norm_le_pi_norm _ a).trans
          ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (hbound.first _ _) (norm_nonneg _)))
      _ = _ := by ring
  calc
    diagonalEnergy b z w ≤ ∑ i : Fin m, (d:ℝ)*L₁*positionSq (u i) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        (∑ a : Fin d, (fderiv ℝ (fun q => b q (externalPosition z)) (positions z i) (u i)) a*u i a) ≤
            ∑ _a : Fin d, L₁*‖u i‖^2 := Finset.sum_le_sum (fun a _ => hcoord i a)
        _ = (d:ℝ)*L₁*‖u i‖^2 := by simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (norm_sq_le_positionSq _) (by positivity)
    _ = _ := by
      rw [← Finset.mul_sum]
      have he : (∑ i : Fin m, positionSq (u i)) = ‖w‖^2 := by
        change (∑ i : Fin m, ∑ a : Fin d, (u i a)^2) = _
        rw [← configurationEuclidean_norm_sq]
        simp only [u,ContinuousLinearEquiv.apply_symm_apply]
      rw [he]

/-- The cancelled lifted contribution is controlled by `2 d L₁` times the
marginal energy, independently of the number of visible particles. -/
theorem lifted_hessian_cancellation_le {b : Position d → Position d → Position d}
    {M L₁ L₂ : ℝ} (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hL₁ : 0 ≤ L₁) {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (z : Point (m*d+d)) :
    2*⟪prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z)),
      gradient (interaction b f) z⟫_ℝ-
      ⟪liftedForce b z,gradient (fun q => ‖gradient f (prefixProjection (m*d) d q)‖^2) z⟫_ℝ ≤
      2*(d:ℝ)*L₁*‖gradient f (prefixProjection (m*d) d z)‖^2 := by
  rw [lifted_hessian_cancellation hb hf]
  nlinarith [diagonalEnergy_le hbound hL₁ z (gradient f (prefixProjection (m*d) d z))]

end SharpWasserstein.ExternalInteraction
