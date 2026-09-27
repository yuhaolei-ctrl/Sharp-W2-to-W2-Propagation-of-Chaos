import SharpWasserstein.PeriodicSourceConvolutionPoincare
import SharpWasserstein.PeriodicTestL2

/-! A bounded linear reconstruction of the mean-zero periodic potential from
its actual L² gradient. This supplies a canonical extension through the true
periodic closed subspace, without identifying nonperiodic cube gradients. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators ContDiff InnerProductSpace BoundedContinuousFunction
namespace SharpWasserstein.PeriodicSourceConvolution
open PeriodicIntegrationByParts PeriodicBochner PeriodicGalerkin PeriodicGradientClosure
open PeriodicSmoothGradient PeriodicTestL2 WeightedTangent

variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

/-- Actual mean subtraction on the vector space of smooth periodic tests. -/
def centerTest : SmoothPeriodicTest n →ₗ[ℝ] SmoothPeriodicTest n where
  toFun f := ⟨fun x => f.val x-∫ y, f.val y ∂cube n,
    f.property.1.sub contDiff_const,fun i x => congrArg (·-∫ y,f.val y ∂cube n) (f.property.2 i x)⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    change f.val x+g.val x-(∫ y,f.val y+g.val y ∂cube n) =
      (f.val x-∫ y,f.val y ∂cube n)+(g.val x-∫ y,g.val y ∂cube n)
    rw [integral_add (continuous_integrable_cube f.property.1.continuous)
      (continuous_integrable_cube g.property.1.continuous)]
    ring
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change c*f.val x-(∫ y,c*f.val y ∂cube n) = c*(f.val x-∫ y,f.val y ∂cube n)
    rw [integral_const_mul]
    ring

/-- Mean-zero scalar values in the literal cube L² space. -/
def centeredValue : SmoothPeriodicTest n →ₗ[ℝ] Lp ℝ 2 (cubePoint (n := n)) :=
  value.comp centerTest

/-- Every smooth gradient lands in the actual periodic closed space. -/
def gradientToPeriodic : SmoothPeriodicTest n →ₗ[ℝ] periodicSpace (n := n) :=
  periodicGradientMap.codRestrict periodicSpace
    (fun f => gradientVector_mem_periodicSpace f.val f.property.1 f.property.2)

/-- This map has dense range by the already proved Fourier gradient closure. -/
theorem gradientToPeriodic_dense : DenseRange (gradientToPeriodic (n := n)) := by
  rw [DenseRange,Subtype.dense_iff]
  intro v hv
  rw [periodicSpace_eq_smoothGradientClosure] at hv
  change v ∈ closure (Set.range (periodicGradientMap (n := n))) at hv
  convert hv using 1
  congr 1
  ext w
  simp only [Set.mem_image,Set.mem_range]
  constructor
  · rintro ⟨z,⟨f,rfl⟩,rfl⟩
    exact ⟨f,rfl⟩
  · rintro ⟨f,rfl⟩
    exact ⟨gradientToPeriodic f,⟨f,rfl⟩,rfl⟩

/-- The scalar Hilbert norm is the actual square-integral of the periodic test. -/
theorem value_norm_sq (f : SmoothPeriodicTest n) :
    ‖value f‖^2 = ∫ x, (f.val x)^2 ∂cube n := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]
  calc
    _ = ∫ y, ((compactTest f.val f.property.1 : Point n → ℝ) y)^2 ∂cubePoint := by
      apply integral_congr_ae
      filter_upwards [scalarTestLp_ae (compactTest f.val f.property.1)] with y hy
      change ‖scalarTestLp (compactTest f.val f.property.1) y‖^2 = _
      rw [hy,Real.norm_eq_abs,sq_abs]
    _ = _ := by
      rw [integral_cubePoint]
      apply integral_congr_ae
      filter_upwards [cube_ae_mem n] with x hx
      rw [compactTest_value_on_cube f.val f.property.1 hx]

/-- The actual gradient Hilbert norm is the Euclidean Dirichlet integral. -/
theorem gradientToPeriodic_norm_sq (f : SmoothPeriodicTest n) :
    ‖gradientToPeriodic f‖^2 = ∑ i : Fin n, ∫ x,(coordinatePartial f.val i x)^2 ∂cube n := by
  change ‖testGradient cubePoint (compactTest f.val f.property.1)‖^2 = _
  rw [testGradient_norm_sq,integral_cubePoint]
  calc
    _ = ∫ x, ∑ i : Fin n,(coordinatePartial f.val i x)^2 ∂cube n := by
      apply integral_congr_ae
      filter_upwards [cube_ae_mem n] with x hx
      rw [compactTest_gradient_on_cube f.val f.property.1 hx,gradientSquare_pullback,
        ContinuousLinearEquiv.apply_symm_apply]
      rfl
    _ = _ := integral_finsetSum Finset.univ (fun i _ => continuous_integrable_cube
      ((PeriodicFourierTests.smooth_coordinatePartial f.property.1 i).continuous.pow 2))

/-- Genuine Poincaré controls potential reconstruction by the gradient norm. -/
theorem centeredValue_norm_le (f : SmoothPeriodicTest n) :
    ‖centeredValue f‖ ≤ (2*Real.pi)⁻¹ * ‖gradientToPeriodic f‖ := by
  have h := periodic_poincare_centered_sq
    (f.property.1.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) f.property.2
  have he : ‖centeredValue f‖^2 =
      ∫ x,(f.val x-∫ y,f.val y ∂cube n)^2 ∂cube n := value_norm_sq (centerTest f)
  rw [← he,← gradientToPeriodic_norm_sq f] at h
  have hp : 0 < 2*Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hb : (2*Real.pi)*‖centeredValue f‖ ≤ ‖gradientToPeriodic f‖ := by
    nlinarith [norm_nonneg (centeredValue f),norm_nonneg (gradientToPeriodic f)]
  calc
    _ = (2*Real.pi)⁻¹*((2*Real.pi)*‖centeredValue f‖) := by rw [← mul_assoc,inv_mul_cancel₀ hp.ne',one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hp.le)

/-- A constructed bounded linear inverse of the periodic gradient, with mean zero. -/
def periodicPotential : periodicSpace (n := n) →L[ℝ] Lp ℝ 2 (cubePoint (n := n)) :=
  centeredValue.extendOfNorm gradientToPeriodic

@[simp] theorem periodicPotential_gradient (f : SmoothPeriodicTest n) :
    periodicPotential (gradientToPeriodic f) = centeredValue f :=
  LinearMap.extendOfNorm_eq gradientToPeriodic_dense ⟨(2*Real.pi)⁻¹,centeredValue_norm_le⟩ f

theorem periodicPotential_norm_le (v : periodicSpace (n := n)) :
    ‖periodicPotential v‖ ≤ (2*Real.pi)⁻¹*‖v‖ :=
  LinearMap.norm_extendOfNorm_apply_le gradientToPeriodic_dense (2*Real.pi)⁻¹ centeredValue_norm_le v

/-- The full cube extension first projects onto genuine periodic gradients. -/
def projectedPotential : gradientClosure (cubePoint (n := n)) →L[ℝ] Lp ℝ 2 (cubePoint (n := n)) :=
  periodicPotential.comp (periodicSpace (n := n)).orthogonalProjectionOnto

@[simp] theorem projectedPotential_gradient (f : SmoothPeriodicTest n) :
    projectedPotential (periodicGradientMap f) = centeredValue f := by
  change periodicPotential ((periodicSpace (n := n)).orthogonalProjectionOnto
    (gradientToPeriodic f : gradientClosure cubePoint)) = _
  simp only [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,periodicPotential_gradient]

end SharpWasserstein.PeriodicSourceConvolution
