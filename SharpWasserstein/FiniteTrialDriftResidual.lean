import SharpWasserstein.ExternalInteractionGradient
import SharpWasserstein.ExternalInteractionEnergy

/-! The actual drift-test gradient and its residual estimate. The drift
supremum enters only the coefficient multiplying the residual error; the
Hessian term is reserved for absorption before any limiting passage. -/
noncomputable section
open scoped InnerProductSpace ContDiff
namespace SharpWasserstein.FiniteTrialDriftResidual
open WeightedTangent BochnerIdentity DriftEnergyIdentity
variable {n : ℕ}

theorem gradient_drift {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f)
    {b : Point n → Point n} (hb : Differentiable ℝ b) (x : Point n) :
    gradient (fun y => ⟪b y,gradient f y⟫_ℝ) x =
      (fderiv ℝ b x).adjoint (gradient f x)+fderiv ℝ (gradient f) x (b x) := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left,fderiv_inner_apply ℝ (hb x)
    ((smooth_gradient hf).differentiable (by simp) x),inner_add_left,
    ContinuousLinearMap.adjoint_inner_left]
  have hs : ⟪b x,fderiv ℝ (gradient f) x z⟫_ℝ =
      ⟪fderiv ℝ (gradient f) x (b x),z⟫_ℝ := by
    calc
      _ = ⟪fderiv ℝ (gradient f) x z,b x⟫_ℝ := real_inner_comm _ _
      _ = _ := fderiv_gradient_symmetric hf z (b x) x
  rw [hs]
  simp only [real_inner_comm]
  ring

theorem gradient_drift_norm_sq_le {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f)
    {b : Point n → Point n} (hb : Differentiable ℝ b) {L M : ℝ}
    (_hL : 0 ≤ L) (_hM : 0 ≤ M) (hbL : ∀ x,‖fderiv ℝ b x‖ ≤ L)
    (hbM : ∀ x,‖b x‖ ≤ M) (x : Point n) :
    ‖gradient (fun y => ⟪b y,gradient f y⟫_ℝ) x‖^2 ≤
      2*L^2*‖gradient f x‖^2+2*M^2*HierarchyAlgebra.frobeniusSq (hessian f x) := by
  have h₁ : ‖(fderiv ℝ b x).adjoint (gradient f x)‖ ≤ L*‖gradient f x‖ := by
    apply ((fderiv ℝ b x).adjoint.le_opNorm _).trans
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact mul_le_mul_of_nonneg_right (hbL x) (norm_nonneg _)
  have h₂ := HierarchyAlgebra.matrixAction_norm_sq_le_of_norm_sq_le
    (hessian f x) (b x) (M^2) (pow_le_pow_left₀ (norm_nonneg _) (hbM x) 2)
  rw [← ExternalInteraction.fderiv_gradient_matrixAction hf] at h₂
  have hs := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
  rw [gradient_drift hf hb]
  have hn := norm_add_sq_real ((fderiv ℝ b x).adjoint (gradient f x))
    (fderiv ℝ (gradient f) x (b x))
  have hm := norm_sub_sq_real ((fderiv ℝ b x).adjoint (gradient f x))
    (fderiv ℝ (gradient f) x (b x))
  nlinarith [sq_nonneg ‖(fderiv ℝ b x).adjoint (gradient f x)-
    fderiv ℝ (gradient f) x (b x)‖]

/-- The positive Hessian error is absorbed while still finite-dimensional.
The possibly dimension-dependent drift bound multiplies only the vanishing
trial residual. -/
theorem drift_residual_young {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f)
    {b : Point n → Point n} (hb : Differentiable ℝ b) {L M ε : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hbL : ∀ x,‖fderiv ℝ b x‖ ≤ L)
    (hbM : ∀ x,‖b x‖ ≤ M) (hε : 0 < ε) (x r : Point n) :
    2*⟪r,gradient (fun y => ⟪b y,gradient f y⟫_ℝ) x⟫_ℝ ≤
      ε*(‖gradient f x‖^2+HierarchyAlgebra.frobeniusSq (hessian f x))+
        (2*(L^2+M^2)/ε)*‖r‖^2 := by
  have hG := gradient_drift_norm_sq_le hf hb hL hM hbL hbM x
  have hH := HierarchyAlgebra.frobeniusSq_nonneg (hessian f x)
  have hq := real_inner_mul_inner_self_le r (gradient (fun y => ⟪b y,gradient f y⟫_ℝ) x)
  simp only [real_inner_self_eq_norm_sq] at hq
  have hbnd : ‖gradient (fun y => ⟪b y,gradient f y⟫_ℝ) x‖^2 ≤
      2*(L^2+M^2)*(‖gradient f x‖^2+HierarchyAlgebra.frobeniusSq (hessian f x)) := by
    nlinarith [mul_nonneg (sq_nonneg L) hH,mul_nonneg (sq_nonneg M) (sq_nonneg ‖gradient f x‖)]
  have hq' := hq.trans (mul_le_mul_of_nonneg_left hbnd (sq_nonneg ‖r‖))
  have h := ExternalInteraction.young_of_sq_le
    (show 0 ≤ 2*(L^2+M^2)*‖r‖^2 by positivity)
    (show 0 ≤ ‖gradient f x‖^2+HierarchyAlgebra.frobeniusSq (hessian f x) by positivity)
    hε (show ⟪r,gradient (fun y => ⟪b y,gradient f y⟫_ℝ) x⟫_ℝ^2 ≤
      (2*(L^2+M^2)*‖r‖^2)*(‖gradient f x‖^2+HierarchyAlgebra.frobeniusSq (hessian f x)) by
      nlinarith [hq'])
  have hle := (mul_le_mul_of_nonneg_left (le_abs_self
    ⟪r,gradient (fun y => ⟪b y,gradient f y⟫_ℝ) x⟫_ℝ) (by norm_num : (0 : ℝ) ≤ 2)).trans h
  calc
    _ ≤ ε*(‖gradient f x‖^2+HierarchyAlgebra.frobeniusSq (hessian f x))+
      2*(L^2+M^2)*‖r‖^2/ε := hle
    _ = _ := by ring

end SharpWasserstein.FiniteTrialDriftResidual
