import SharpWasserstein.PeriodicSourceConvolutionPotential

/-! A fixed continuous linear map from actual bounded scalar sources to the
dual of the cube gradient closure. Its restriction to periodic gradients is
exact scalar-source integration after mean subtraction. -/
set_option synthInstance.maxHeartbeats 100000
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff InnerProductSpace BoundedContinuousFunction
namespace SharpWasserstein.PeriodicSourceConvolution
open PeriodicIntegrationByParts PeriodicBochner PeriodicGalerkin PeriodicGradientClosure
open PeriodicSmoothGradient PeriodicTestL2 WeightedTangent

variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

/-- Actual scalar pairing, with the periodic potential reconstructed by Poincaré. -/
def sourceFunctional : (Point n →ᵇ ℝ) →L[ℝ]
    (gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ) := by
  let H := gradientClosure (cubePoint (n := n))
  let L := Lp ℝ 2 (cubePoint (n := n))
  letI : NormedAddCommGroup (L →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (L →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup (H →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (H →L[ℝ] ℝ) := inferInstance
  let P : (L →L[ℝ] ℝ) →L[ℝ] H →L[ℝ] ℝ :=
    (ContinuousLinearMap.flipₗᵢ ℝ (L →L[ℝ] ℝ) (H →L[ℝ] L) (H →L[ℝ] ℝ)
      (ContinuousLinearMap.compL ℝ H L ℝ)) projectedPotential
  let D : L →L[ℝ] L →L[ℝ] ℝ := innerSL ℝ
  exact P.comp (D.comp (BoundedContinuousFunction.toLp 2 cubePoint ℝ))

theorem sourceFunctional_apply (σ : Point n →ᵇ ℝ)
    (v : gradientClosure (cubePoint (n := n))) :
    sourceFunctional σ v =
      ∫ y, σ y * projectedPotential v y ∂cubePoint := by
  change ⟪BoundedContinuousFunction.toLp 2 cubePoint ℝ σ,projectedPotential v⟫_ℝ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 (cubePoint (n := n)) ℝ σ] with y hy
  rw [hy]
  simp only [RCLike.inner_apply,conj_trivial,mul_comm]

/-- The actual dual pairing on every smooth periodic potential. -/
theorem sourceFunctional_periodicGradient (σ : Point n →ᵇ ℝ) (f : SmoothPeriodicTest n) :
    sourceFunctional σ (periodicGradientMap f) =
      ∫ x, σ ((coordinateEquiv n).symm x) *
        (f.val x-∫ z, f.val z ∂cube n) ∂cube n := by
  rw [sourceFunctional_apply,projectedPotential_gradient]
  calc
    _ = ∫ y, σ y * (compactTest (centerTest f).val (centerTest f).property.1 : Point n → ℝ) y
        ∂cubePoint := by
      apply integral_congr_ae
      filter_upwards [scalarTestLp_ae (compactTest (centerTest f).val (centerTest f).property.1)] with y hy
      exact congrArg (σ y*·) hy
    _ = _ := by
      rw [integral_cubePoint]
      apply integral_congr_ae
      filter_upwards [cube_ae_mem n] with x hx
      rw [compactTest_value_on_cube (centerTest f).val (centerTest f).property.1 hx]
      rfl

/-- Zero-mean scalar sources have precisely the required, uncentered test pairing. -/
theorem sourceFunctional_periodicGradient_of_mean_zero (σ : Point n →ᵇ ℝ)
    (hσ : ∫ y, σ y ∂cubePoint = 0) (f : SmoothPeriodicTest n) :
    sourceFunctional σ (periodicGradientMap f) =
      ∫ x, σ ((coordinateEquiv n).symm x)*f.val x ∂cube n := by
  rw [sourceFunctional_periodicGradient]
  simp_rw [mul_sub]
  rw [integral_sub (f := fun x => σ ((coordinateEquiv n).symm x)*f.val x)
    (g := fun x => σ ((coordinateEquiv n).symm x)*(∫ z,f.val z ∂cube n))
    (continuous_integrable_cube ((σ.continuous.comp (coordinateEquiv n).symm.continuous).mul
      f.property.1.continuous))
    (continuous_integrable_cube ((σ.continuous.comp (coordinateEquiv n).symm.continuous).mul
      continuous_const)),integral_mul_const,← integral_cubePoint,hσ,zero_mul,sub_zero]

/-- Projection preserves the sharp periodic potential norm estimate. -/
theorem projectedPotential_norm_le (v : gradientClosure (cubePoint (n := n))) :
    ‖projectedPotential v‖ ≤ (2*Real.pi)⁻¹*‖v‖ :=
  (periodicPotential_norm_le ((periodicSpace (n := n)).orthogonalProjectionOnto v)).trans
    (mul_le_mul_of_nonneg_left ((periodicSpace (n := n)).norm_orthogonalProjectionOnto_apply_le v)
      (inv_nonneg.mpr (mul_nonneg (by norm_num) Real.pi_pos.le)))

/-- The actual source-to-dual map has a genuine global operator bound. -/
theorem sourceFunctional_norm_le (σ : Point n →ᵇ ℝ) :
    ‖sourceFunctional σ‖ ≤ (2*Real.pi)⁻¹*‖σ‖ := by
  have hp : 0 ≤ (2*Real.pi)⁻¹ := inv_nonneg.mpr (mul_nonneg (by norm_num) Real.pi_pos.le)
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hp (norm_nonneg σ))
  intro v
  change ‖⟪BoundedContinuousFunction.toLp 2 cubePoint ℝ σ,projectedPotential v⟫_ℝ‖ ≤ _
  have hLp : ‖BoundedContinuousFunction.toLp 2 cubePoint ℝ σ‖ ≤ ‖σ‖ := by
    have hb : ‖BoundedContinuousFunction.toLp (E := ℝ) 2 (cubePoint (n := n)) ℝ‖ ≤ 1 := by
      simpa [measureUnivNNReal] using BoundedContinuousFunction.toLp_norm_le (p := 2) (𝕜 := ℝ) (E := ℝ) (cubePoint (n := n))
    exact ((BoundedContinuousFunction.toLp 2 cubePoint ℝ).le_opNorm σ).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (norm_nonneg σ))
  calc
    _ ≤ ‖BoundedContinuousFunction.toLp 2 cubePoint ℝ σ‖*‖projectedPotential v‖ := norm_inner_le_norm _ _
    _ ≤ ‖σ‖*((2*Real.pi)⁻¹*‖v‖) := mul_le_mul hLp (projectedPotential_norm_le v)
      (norm_nonneg _) (norm_nonneg _)
    _ = _ := by ring

/-- The fixed actual source map transfers Banach derivatives to the dual norm. -/
theorem sourceFunctional_hasDerivAt {σ : ℝ → (Point n →ᵇ ℝ)} {σ' : Point n →ᵇ ℝ}
    {t : ℝ} (hσ : HasDerivAt σ σ' t) :
    HasDerivAt (fun s => sourceFunctional (σ s)) (sourceFunctional σ') t := by
  letI : NormedAddCommGroup (gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ) := inferInstance
  exact (sourceFunctional (n := n)).hasFDerivAt.comp_hasDerivAt t hσ

theorem sourceFunctional_hasDerivWithinAt {σ : ℝ → (Point n →ᵇ ℝ)} {σ' : Point n →ᵇ ℝ}
    {t : ℝ} {s : Set ℝ} (hσ : HasDerivWithinAt σ σ' s t) :
    HasDerivWithinAt (fun r => sourceFunctional (σ r)) (sourceFunctional σ') s t := by
  letI : NormedAddCommGroup (gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ) := inferInstance
  exact (sourceFunctional (n := n)).hasFDerivAt.comp_hasDerivWithinAt t hσ

end SharpWasserstein.PeriodicSourceConvolution
