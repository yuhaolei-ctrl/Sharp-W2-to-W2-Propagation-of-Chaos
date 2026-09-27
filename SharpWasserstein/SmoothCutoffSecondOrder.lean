import SharpWasserstein.SmoothCutoff
import SharpWasserstein.BochnerIdentity
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-! Second-order bounds for the actual smooth cutoff sequence. The true second
Fréchet derivative decays as the inverse radius squared; consequently the actual
Euclidean Laplacian admits the same decay. -/

noncomputable section
namespace SharpWasserstein.SmoothCutoff
open WeightedTangent PDEPairings BochnerIdentity
open scoped InnerProductSpace Topology ContDiff NNReal

/-- The derivative of the fixed smooth compact bump is globally Lipschitz in operator norm. -/
theorem base_derivative_lipschitz_exists (d : ℕ) :
    ∃ C : ℝ≥0, LipschitzWith C (fderiv ℝ (baseBump d)) := by
  have hb : ContDiff ℝ ∞ (baseBump d) := (baseBump d).contDiff
  have hbd : ContDiff ℝ ∞ (fderiv ℝ (baseBump d)) := hb.fderiv_right (by simp)
  exact ContDiff.lipschitzWith_of_hasCompactSupport
    ((baseBump d).hasCompactSupport.fderiv ℝ) hbd (by simp)

/-- A fixed finite second-derivative bound, depending only on the bump dimension. -/
def baseHessianConstant (d : ℕ) : ℝ≥0 := Classical.choose (base_derivative_lipschitz_exists d)

theorem base_derivative_lipschitz (d : ℕ) :
    LipschitzWith (baseHessianConstant d) (fderiv ℝ (baseBump d)) :=
  Classical.choose_spec (base_derivative_lipschitz_exists d)

theorem base_second_derivative_bound (d : ℕ) (x : Point d) :
    ‖fderiv ℝ (fderiv ℝ (baseBump d)) x‖ ≤ (baseHessianConstant d : ℝ) :=
  norm_fderiv_le_of_lipschitz ℝ (base_derivative_lipschitz d)

/-- The true second Fréchet derivative of a dilation has exactly two scaling factors. -/
theorem second_derivative_comp_smul {d : ℕ} (f : Point d → ℝ) (c : ℝ) (x : Point d) :
    fderiv ℝ (fderiv ℝ (fun y => f (c • y))) x =
      (c * c) • fderiv ℝ (fderiv ℝ f) (c • x) := by
  have heq : fderiv ℝ (fun y => f (c • y)) =
      c • (fun y => fderiv ℝ f (c • y)) := by
    funext y
    exact fderiv_comp_smul c
  rw [heq, fderiv_const_smul_field (𝕜 := ℝ) (E := Point d)
    (F := Point d →L[ℝ] ℝ)]
  simp only [Pi.smul_apply, fderiv_comp_smul, smul_smul]

/-- The genuine Hessian operator norm has the required inverse-square-radius decay. -/
theorem cutoff_second_derivative_bound_scaled (d j : ℕ) (x : Point d) :
    ‖fderiv ℝ (fderiv ℝ (cutoff d j)) x‖ ≤
      (baseHessianConstant d : ℝ) / ((j : ℝ) + 1) ^ 2 := by
  change ‖fderiv ℝ (fderiv ℝ (fun y : Point d => baseBump d (((j : ℝ) + 1)⁻¹ • y))) x‖ ≤ _
  rw [second_derivative_comp_smul]
  have hp : 0 < (j : ℝ) + 1 := by positivity
  calc
    _ ≤ ‖((j : ℝ) + 1)⁻¹ * ((j : ℝ) + 1)⁻¹‖ *
        ‖fderiv ℝ (fderiv ℝ (baseBump d)) (((j : ℝ) + 1)⁻¹ • x)‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖((j : ℝ) + 1)⁻¹ * ((j : ℝ) + 1)⁻¹‖ * (baseHessianConstant d : ℝ) :=
      mul_le_mul_of_nonneg_left (base_second_derivative_bound d _) (norm_nonneg _)
    _ = _ := by
      rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hp]
      field_simp

/-- Each actual Hessian coefficient is bounded by the genuine second Fréchet operator norm. -/
theorem hessian_entry_le_second_derivative {d : ℕ} (f : Point d → ℝ) (hf : ContDiff ℝ 2 f)
    (x : Point d) (i k : Fin d) :
    |hessian f x i k| ≤ ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  rw [hessian, directionDeriv_twice_eq_fderiv hf, ← Real.norm_eq_abs]
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)‖ * ‖EuclideanSpace.single k 1‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖fderiv ℝ (fderiv ℝ f) x‖ * ‖EuclideanSpace.single i 1‖) *
        ‖EuclideanSpace.single k 1‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = _ := by simp

/-- Every actual Hessian coefficient has inverse-square-radius decay. -/
theorem cutoff_hessian_entry_bound_scaled (d j : ℕ) (x : Point d) (i k : Fin d) :
    |hessian (cutoff d j) x i k| ≤ (baseHessianConstant d : ℝ) / ((j : ℝ) + 1) ^ 2 :=
  (hessian_entry_le_second_derivative _ (contDiff_two_of_smooth (cutoff_contDiff d j)) x i k).trans
    (cutoff_second_derivative_bound_scaled d j x)

/-- The actual Euclidean Laplacian has inverse-square-radius decay. -/
theorem cutoff_laplacian_bound_scaled (d j : ℕ) (x : Point d) :
    |laplacian (cutoff d j) x| ≤
      (d : ℝ) * (baseHessianConstant d : ℝ) / ((j : ℝ) + 1) ^ 2 := by
  change |∑ i : Fin d, hessian (cutoff d j) x i i| ≤ _
  calc
    _ ≤ ∑ i : Fin d, |hessian (cutoff d j) x i i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, (baseHessianConstant d : ℝ) / ((j : ℝ) + 1) ^ 2 :=
      Finset.sum_le_sum (fun i _ => cutoff_hessian_entry_bound_scaled d j x i i)
    _ = _ := by simp [mul_div_assoc]

/-- A uniform Laplacian bound follows from the sharper inverse-square-radius estimate. -/
theorem cutoff_laplacian_bound (d j : ℕ) (x : Point d) :
    |laplacian (cutoff d j) x| ≤ (d : ℝ) * (baseHessianConstant d : ℝ) := by
  apply (cutoff_laplacian_bound_scaled d j x).trans
  apply div_le_self (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) j]

/-- Linearity of the actual directional derivative for differentiable scalar fields. -/
theorem directionDeriv_add {d : ℕ} {f g : Point d → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (v x : Point d) :
    directionDeriv v (fun y => f y + g y) x = directionDeriv v f x + directionDeriv v g x := by
  simp only [directionDeriv, fderiv_fun_add (hf x) (hg x), add_apply]

/-- The actual second directional derivative of a product obeys the full product rule. -/
theorem directionDeriv_mul_twice {d : ℕ} {f g : Point d → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (v x : Point d) :
    directionDeriv v (directionDeriv v (fun y => f y * g y)) x =
      f x * directionDeriv v (directionDeriv v g) x +
      g x * directionDeriv v (directionDeriv v f) x +
      2 * (directionDeriv v f x * directionDeriv v g x) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hfv : Differentiable ℝ (directionDeriv v f) :=
    (contDiff_directionDeriv (m := 1) hf (by norm_num) v).differentiable (by simp)
  have hgv : Differentiable ℝ (directionDeriv v g) :=
    (contDiff_directionDeriv (m := 1) hg (by norm_num) v).differentiable (by simp)
  have heq : directionDeriv v (fun y => f y * g y) =
      fun y => f y * directionDeriv v g y + g y * directionDeriv v f y := by
    funext y
    exact directionDeriv_mul hfd hgd v y
  rw [heq, directionDeriv_add (f := fun y => f y * directionDeriv v g y)
    (g := fun y => g y * directionDeriv v f y) (hfd.mul hgv) (hgd.mul hfv),
    directionDeriv_mul hfd hgv, directionDeriv_mul hgd hfv]
  ring

/-- The true Euclidean Laplacian product rule. -/
theorem laplacian_mul {d : ℕ} {f g : Point d → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Point d) :
    laplacian (fun y => f y * g y) x =
      f x * laplacian g x + g x * laplacian f x + 2 * ⟪gradient f x, gradient g x⟫_ℝ := by
  unfold laplacian
  simp_rw [directionDeriv_mul_twice hf hg]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  congr 1
  simp only [directionDeriv_eq_gradient_component, PiLp.inner_apply,
    RCLike.inner_apply, RCLike.conj_to_real, mul_comm]

/-- Compact cutoffs preserve a uniform bound on the function itself. -/
theorem approximate_abs_bound {d : ℕ} (f : Point d → ℝ) (hf : ContDiff ℝ ∞ f)
    {A : ℝ} (hfa : ∀ x, |f x| ≤ A) (j : ℕ) (x : Point d) :
    |(approximate f hf j : Point d → ℝ) x| ≤ A := by
  change |cutoff d j x * f x| ≤ A
  rw [abs_mul]
  calc
    _ ≤ 1 * |f x| := mul_le_mul_of_nonneg_right (cutoff_abs_le_one d j x) (abs_nonneg _)
    _ ≤ A := by simpa only [one_mul] using hfa x

/-- Bounded value, gradient, and Laplacian give a uniform actual Laplacian bound for compact approximants. -/
theorem approximate_laplacian_bound {d : ℕ} (f : Point d → ℝ) (hf : ContDiff ℝ ∞ f)
    {A B D : ℝ} (hA : 0 ≤ A)
    (hfa : ∀ x, |f x| ≤ A) (hfb : ∀ x, ‖gradient f x‖ ≤ B)
    (hfd : ∀ x, |laplacian f x| ≤ D) (j : ℕ) (x : Point d) :
    |laplacian (approximate f hf j : Point d → ℝ) x| ≤
      D + A * ((d : ℝ) * (baseHessianConstant d : ℝ)) +
        2 * (baseLipschitzConstant d : ℝ) * B := by
  change |laplacian (fun y => cutoff d j y * f y) x| ≤ _
  rw [laplacian_mul (contDiff_two_of_smooth (cutoff_contDiff d j)) (contDiff_two_of_smooth hf)]
  calc
    _ ≤ |cutoff d j x * laplacian f x| + |f x * laplacian (cutoff d j) x| +
        |2 * ⟪gradient (cutoff d j) x, gradient f x⟫_ℝ| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 1 * D + A * ((d : ℝ) * (baseHessianConstant d : ℝ)) +
        2 * ((baseLipschitzConstant d : ℝ) * B) := by
      apply add_le_add
      · apply add_le_add
        · rw [abs_mul]
          exact mul_le_mul (cutoff_abs_le_one d j x) (hfd x) (abs_nonneg _) (by norm_num)
        · rw [abs_mul]
          exact mul_le_mul (hfa x) (cutoff_laplacian_bound d j x) (abs_nonneg _) hA
      · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
        calc
          _ ≤ ‖gradient (cutoff d j) x‖ * ‖gradient f x‖ := by
            simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (gradient (cutoff d j) x) (gradient f x)
          _ ≤ (baseLipschitzConstant d : ℝ) * B :=
            mul_le_mul (cutoff_gradient_bound d j x) (hfb x) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Germ equality of functions entails equality of their actual Euclidean Laplacians. -/
theorem laplacian_eq_of_eventuallyEq {d : ℕ} {f g : Point d → ℝ} {x : Point d}
    (hfg : f =ᶠ[𝓝 x] g) : laplacian f x = laplacian g x := by
  unfold laplacian
  apply Finset.sum_congr rfl
  intro i _
  have heq : directionDeriv (EuclideanSpace.single i 1) f =ᶠ[𝓝 x]
      directionDeriv (EuclideanSpace.single i 1) g := by
    filter_upwards [hfg.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun L : Point d →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hy
  exact congrArg (fun L : Point d →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) (heq.fderiv_eq (𝕜 := ℝ))

/-- At each point the actual compact approximants eventually have the exact original Laplacian. -/
theorem approximate_laplacian_eventuallyEq {d : ℕ} (f : Point d → ℝ)
    (hf : ContDiff ℝ ∞ f) (x : Point d) :
    ∀ᶠ j in Filter.atTop, laplacian (approximate f hf j : Point d → ℝ) x = laplacian f x := by
  filter_upwards [cutoff_eventuallyEq_one x] with j hj
  apply laplacian_eq_of_eventuallyEq
  filter_upwards [hj] with y hy
  change cutoff d j y * f y = f y
  rw [hy, one_mul]

end SharpWasserstein.SmoothCutoff
