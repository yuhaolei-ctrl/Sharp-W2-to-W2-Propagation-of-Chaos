module

public import SharpWasserstein.Compat
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import SharpWasserstein.RoughEulerianCompressionGeometry
public import SharpWasserstein.ExternalInteractionPeriodicSource

@[expose] public section

/-! Actual physical-period smooth tests approximating every compact Euclidean
test in value and gradient, at arbitrarily large integer multiples of any
fixed positive period. This closes the distinction between periodic and full
weighted tangent energies without identifying their finite-period spaces. -/
noncomputable section
open Filter Set
open scoped ContDiff Topology InnerProductSpace
namespace SharpWasserstein.CompressionPeriodicTests
open WeightedTangent RoughEulerianCompression PeriodicBochner
open WeightedPeriodicFourierScale
variable {n : ℕ}

theorem compression_scaled {A : ℝ} (hA : A ≠ 0) (R : ℝ) (x : Point n) :
    compression (A*R) x = A • compression R (A⁻¹ • x) := by
  ext i
  simp only [compression_apply,PiLp.smul_apply,smul_eq_mul,SinePeriodization.scalar]
  rw [mul_assoc]
  congr 1
  congr 1
  congr 1
  field_simp

theorem compression_scaled_tendsto {A : ℝ} (hA : A ≠ 0) (x : Point n) :
    Tendsto (fun k : ℕ => compression (A*((k:ℝ)+1)) x) atTop (𝓝 x) := by
  simp_rw [compression_scaled hA]
  have h := (compression_tendsto (A⁻¹ • x)).const_smul A
  simpa only [smul_smul,mul_inv_cancel₀ hA,one_smul] using h

theorem compression_fderiv {R : ℝ} (hR : R ≠ 0) (x : Point n) :
    fderiv ℝ (compression R) x = euclideanCoordinates.symm.toContinuousLinearMap.comp
      ((SinePeriodization.coordinateDerivative R (euclideanCoordinates x)).comp
        euclideanCoordinates.toContinuousLinearMap) := by
  exact (euclideanCoordinates.symm.hasFDerivAt.comp x
    ((SinePeriodization.coordinates_hasFDerivAt hR (euclideanCoordinates x)).comp x
      euclideanCoordinates.hasFDerivAt)).fderiv

theorem compression_scaled_fderiv_tendsto {A : ℝ} (hA : A ≠ 0) (x : Point n) :
    Tendsto (fun k : ℕ => fderiv ℝ (compression (A*((k:ℝ)+1))) x) atTop
      (𝓝 (ContinuousLinearMap.id ℝ (Point n))) := by
  have hcos (i : Fin n) : Tendsto (fun k : ℕ => Real.cos (x i/(A*((k:ℝ)+1)))) atTop (𝓝 1) := by
    have hz := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (x i/A)
    have he : (fun k : ℕ => x i/(A*((k:ℝ)+1))) = fun k : ℕ => (x i/A)*(1/((k:ℝ)+1)) := by
      funext k
      simp only [div_eq_mul_inv,mul_inv_rev,one_mul]
      ring
    change Tendsto (Real.cos ∘ (fun k : ℕ => x i/(A*((k:ℝ)+1)))) atTop (𝓝 1)
    rw [he]
    simpa only [mul_zero,Real.cos_zero] using Real.continuous_cos.continuousAt.tendsto.comp hz
  have hd := tendsto_finsetSum Finset.univ
    (fun i _ => (hcos i).smul (tendsto_const_nhds (x := SinePeriodization.coordinateProjection i)))
  simp only [one_smul,SinePeriodization.coordinateProjection_sum] at hd
  have hc : Continuous (fun L : Position n →L[ℝ] Position n =>
      euclideanCoordinates.symm.toContinuousLinearMap.comp (L.comp euclideanCoordinates.toContinuousLinearMap)) :=
    continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
  have ht := hc.continuousAt.tendsto.comp hd
  have he : euclideanCoordinates.symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.id ℝ (Position n)).comp euclideanCoordinates.toContinuousLinearMap) =
      ContinuousLinearMap.id ℝ (Point n) := by
    ext v
    simp
  simp only [he] at ht
  have heq (k : ℕ) := compression_fderiv (mul_ne_zero hA (by positivity : (k:ℝ)+1 ≠ 0)) x
  simp_rw [heq]
  exact ht

theorem compressed_gradient {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f)
    (R : ℝ) (x : Point n) :
    gradient (f ∘ compression R) x = (fderiv ℝ (compression R) x).adjoint (gradient f (compression R x)) := by
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left,inner_gradient_left,inner_gradient_left]
  exact congrArg (fun L : Point n →L[ℝ] ℝ => L v)
    (fderiv_comp x (hf.differentiable (by simp) _) ((compression_contDiff R).differentiable (by simp) x))

theorem compressed_gradient_bound {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f)
    {B : ℝ} (hB : ∀ x,‖gradient f x‖ ≤ B) {R : ℝ} (hR : R ≠ 0) (x : Point n) :
    ‖gradient (f ∘ compression R) x‖ ≤ B := by
  rw [compressed_gradient hf]
  calc
    _ ≤ ‖(fderiv ℝ (compression R) x).adjoint‖*‖gradient f (compression R x)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (compression R) x‖*‖gradient f (compression R x)‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1*‖gradient f (compression R x)‖ :=
      mul_le_mul_of_nonneg_right (compression_fderiv_norm_le hR x) (norm_nonneg _)
    _ ≤ B := by simpa only [one_mul] using hB _

theorem compressed_gradient_tendsto {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f)
    {A : ℝ} (hA : A ≠ 0) (x : Point n) :
    Tendsto (fun k : ℕ => gradient (f ∘ compression (A*((k:ℝ)+1))) x) atTop (𝓝 (gradient f x)) := by
  have hg := (BochnerIdentity.smooth_gradient hf).continuous.continuousAt.tendsto.comp (compression_scaled_tendsto hA x)
  have hd := ContinuousLinearMap.adjoint.continuous.continuousAt.tendsto.comp
    (compression_scaled_fderiv_tendsto hA x)
  have hc : Continuous (fun q : (Point n →L[ℝ] Point n) × Point n => q.1 q.2) :=
    continuous_fst.clm_apply continuous_snd
  have hh := hc.continuousAt.tendsto.comp (hd.prodMk_nhds hg)
  simp_rw [compressed_gradient hf]
  simpa only [Function.comp_def,ContinuousLinearMap.adjoint_id,ContinuousLinearMap.id_apply] using hh

theorem compression_coordinates (R : ℝ) (x : PeriodicIntegrationByParts.Coordinates n) :
    compression R ((coordinateEquiv n).symm x) =
      (coordinateEquiv n).symm (SinePeriodization.coordinates R x) := rfl

theorem compressed_periodic {R : ℝ} (hR : R ≠ 0) (f : Point n → ℝ) :
    PeriodicOf (n := n) (2*Real.pi*R)
      (fun x => f (compression (d := n) R ((coordinateEquiv n).symm x))) := by
  intro i x
  simp only [compression_coordinates]
  exact congrArg (fun y : Position n => f ((coordinateEquiv n).symm y))
    (SinePeriodization.coordinates_periodic hR i x)

end SharpWasserstein.CompressionPeriodicTests
