import SharpWasserstein.PeriodicFluxSmooth

/-! Differentiation of the actual periodic density and flux integrals.
These identities identify the diffusion and divergence in the convolved PDE. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators
namespace SharpWasserstein.PeriodicConvolution
open PeriodicIntegrationByParts PeriodicPositiveKernel PeriodicFourierTests NoiseAverage
variable {n : ℕ} (μ : Measure (Coordinates n)) [IsProbabilityMeasure μ]

theorem coordinatePartial_average {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) (i : Fin n) (x : Coordinates n) :
    coordinatePartial (average μ (fun y => -y) f) i x =
      average μ (fun y => -y) (coordinatePartial f i) x := by
  have hB : AllDerivativesBounded f := PeriodicSmoothBounds.iteratedFDeriv_bound hp hf
  obtain ⟨L,hL⟩ := hB.lipschitz (hf.differentiable (by simp))
  obtain ⟨C,_,hC⟩ := hB.bounded
  obtain ⟨D,_,hD⟩ := hB.fderiv.bounded
  unfold coordinatePartial
  rw [fderiv_average μ (fun y => -y) continuous_neg.stronglyMeasurable
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hL hC]
  change (∫ y,fderiv ℝ f (x+-y) ∂μ) (Pi.single i 1) = _
  rw [ContinuousLinearMap.integral_apply
    (integrable_translate μ (fun y => -y) continuous_neg.stronglyMeasurable
      (hf.continuous_fderiv (by simp)) hD x)]
  rfl

theorem laplacian_average {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) (x : Coordinates n) :
    PeriodicIntegrationByParts.laplacian (average μ (fun y => -y) f) x =
      ∫ y,PeriodicIntegrationByParts.laplacian f (x-y) ∂μ := by
  have he (i : Fin n) : coordinatePartial (average μ (fun y => -y) f) i =
      average μ (fun y => -y) (coordinatePartial f i) :=
    funext (coordinatePartial_average μ hf hp i)
  unfold PeriodicIntegrationByParts.laplacian
  simp_rw [he,coordinatePartial_average μ (smooth_coordinatePartial hf _) (periodic_coordinatePartial hp _)]
  have hi (i : Fin n) : Integrable (fun y => coordinatePartial (coordinatePartial f i) i (x-y)) μ := by
    obtain ⟨C,_,hC⟩ := PeriodicSmoothBounds.norm_bound
      (periodic_coordinatePartial (periodic_coordinatePartial hp i) i)
      (smooth_coordinatePartial (smooth_coordinatePartial hf i) i).continuous
    simpa only [sub_eq_add_neg] using integrable_translate μ (fun y => -y)
      continuous_neg.stronglyMeasurable (smooth_coordinatePartial (smooth_coordinatePartial hf i) i).continuous hC x
  symm
  rw [integral_finsetSum _ (fun i _ => hi i)]
  rfl

theorem laplacian_density (κ : ℝ) (x : Coordinates n) :
    PeriodicIntegrationByParts.laplacian (density κ μ) x =
      ∫ y,PeriodicIntegrationByParts.laplacian (kernel κ) (x-y) ∂μ := by
  exact laplacian_average μ (kernel_smooth n κ) (kernel_periodic n κ) x

omit [IsProbabilityMeasure μ] in
theorem kernelFDeriv_smulRight_integrable (κ : ℝ)
    {v : Coordinates n → Coordinates n} (hv : Integrable v μ) (x : Coordinates n) :
    Integrable (fun y => (fderiv ℝ (kernel (n := n) κ) (x-y)).smulRight (v y)) μ := by
  have hB : AllDerivativesBounded (kernel (n := n) κ) := kernel_derivatives_bounded n κ
  obtain ⟨D,_,hD⟩ := hB.fderiv.bounded
  apply Integrable.mono' (hv.norm.const_mul D)
  · exact (((ContinuousLinearMap.smulRightL ℝ (Coordinates n) (Coordinates n)).continuous.comp
      continuous_fst).clm_apply continuous_snd).comp_aestronglyMeasurable
      ((((kernel_smooth n κ).continuous_fderiv (by simp)).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable.prodMk hv.aestronglyMeasurable)
  · exact Eventually.of_forall fun y => by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul_of_nonneg_right (hD (x-y)) (norm_nonneg _)

omit [IsProbabilityMeasure μ] in
theorem coordinatePartial_flux (κ : ℝ) {v : Coordinates n → Coordinates n}
    (hv : Integrable v μ) (i j : Fin n) (x : Coordinates n) :
    coordinatePartial (fun z => flux κ μ v z i) j x =
      ∫ y,coordinatePartial (kernel κ) j (x-y)*v y i ∂μ := by
  have hi := kernelFDeriv_smulRight_integrable μ κ hv x
  unfold coordinatePartial
  rw [fderiv_apply ((flux_smooth_of_integrable κ μ hv).differentiable (by simp) x) i,
    fderiv_flux_of_integrable κ μ hv x]
  change ((∫ y,(fderiv ℝ (kernel κ) (x-y)).smulRight (v y) ∂μ) (Pi.single j 1)) i = _
  rw [ContinuousLinearMap.integral_apply hi]
  exact ((ContinuousLinearMap.proj i : Coordinates n →L[ℝ] ℝ).integral_comp_comm
    (hi.apply_continuousLinearMap (Pi.single j 1))).symm

theorem fderiv_eq_sum_coordinatePartial {f : Coordinates n → ℝ} (x w : Coordinates n) :
    fderiv ℝ f x w = ∑ i : Fin n,coordinatePartial f i x*w i := by
  have hh := congrArg (fderiv ℝ f x) (pi_eq_sum_univ' w)
  simpa only [map_sum,map_smul,smul_eq_mul,coordinatePartial,mul_comm] using hh

omit [IsProbabilityMeasure μ] in
theorem divergence_flux (κ : ℝ) {v : Coordinates n → Coordinates n}
    (hv : Integrable v μ) (x : Coordinates n) :
    PeriodicDriftEnergy.divergence (flux κ μ v) x =
      ∫ y,fderiv ℝ (kernel κ) (x-y) (v y) ∂μ := by
  have hi := kernelFDeriv_smulRight_integrable μ κ hv x
  have hi' (i : Fin n) : Integrable (fun y => coordinatePartial (kernel κ) i (x-y)*v y i) μ :=
    (ContinuousLinearMap.proj i : Coordinates n →L[ℝ] ℝ).integrable_comp
      (hi.apply_continuousLinearMap (Pi.single i 1))
  simp only [PeriodicDriftEnergy.divergence,coordinatePartial_flux μ κ hv]
  rw [← integral_finsetSum _ (fun i _ => hi' i)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => (fderiv_eq_sum_coordinatePartial (x-y) (v y)).symm

omit [IsProbabilityMeasure μ] in
theorem kernel_drift_integrable (κ : ℝ) {v : Coordinates n → Coordinates n}
    (hv : Integrable v μ) (x : Coordinates n) :
    Integrable (fun y => fderiv ℝ (kernel κ) (x-y) (v y)) μ := by
  have hB : AllDerivativesBounded (kernel (n := n) κ) := kernel_derivatives_bounded n κ
  obtain ⟨D,_,hD⟩ := hB.fderiv.bounded
  apply Integrable.mono' (hv.norm.const_mul D)
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      ((((kernel_smooth n κ).continuous_fderiv (by simp)).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable.prodMk hv.aestronglyMeasurable)
  · exact Eventually.of_forall fun y => (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hD (x-y)) (norm_nonneg _))

theorem kernel_laplacian_integrable (κ : ℝ) (x : Coordinates n) :
    Integrable (fun y => PeriodicIntegrationByParts.laplacian (kernel κ) (x-y)) μ := by
  have hp : Periodic (PeriodicIntegrationByParts.laplacian (kernel (n := n) κ)) := by
    intro j z
    unfold PeriodicIntegrationByParts.laplacian
    apply Finset.sum_congr rfl
    intro i _
    exact periodic_coordinatePartial (periodic_coordinatePartial (kernel_periodic n κ) i) i j z
  obtain ⟨C,_,hC⟩ := PeriodicSmoothBounds.norm_bound hp
    (PeriodicBochner.smooth_laplacian (kernel_smooth n κ)).continuous
  simpa only [sub_eq_add_neg] using integrable_translate μ (fun y => -y)
    continuous_neg.stronglyMeasurable (PeriodicBochner.smooth_laplacian (kernel_smooth n κ)).continuous hC x

end SharpWasserstein.PeriodicConvolution
