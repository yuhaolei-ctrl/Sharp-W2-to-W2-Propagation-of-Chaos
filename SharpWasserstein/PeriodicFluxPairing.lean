import SharpWasserstein.PeriodicFluxContraction
import SharpWasserstein.PeriodicConvolutionApproximation

/-! The convolved finite-energy flux acts on actual periodic test fields by
convolving the tests. This exact Fubini identity gives convergence of source
pairings without a density or boundedness assumption on the original flux. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace SharpWasserstein.PeriodicConvolution
open PeriodicIntegrationByParts PeriodicPositiveKernel
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (κ : ℝ) (μ : Measure (Coordinates n)) [IsProbabilityMeasure μ]

omit [CompleteSpace E] in
theorem flux_pairing_joint_integrable {v F : Coordinates n → E}
    (hv : Integrable v μ) (hF : Continuous F) {M : ℝ} (hM : ∀ x, ‖F x‖ ≤ M) :
    Integrable (fun p : Coordinates n × Coordinates n =>
      kernel κ (p.1-p.2)*⟪F p.1,v p.2⟫_ℝ) ((cube n).prod μ) := by
  let C := (Real.exp |κ|/normalizer κ)^n
  have hC : 0 ≤ C := pow_nonneg (div_pos (Real.exp_pos _) (normalizer_pos κ)).le n
  apply ((hv.norm.comp_snd (cube n)).const_mul (C*M)).mono'
    ((((kernel_smooth n κ).continuous.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mul
      ((hF.comp continuous_fst).aestronglyMeasurable.inner hv.aestronglyMeasurable.comp_snd))
  exact Eventually.of_forall fun p => by
    change ‖kernel κ (p.1-p.2)*⟪F p.1,v p.2⟫_ℝ‖ ≤ C*M*‖v p.2‖
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (kernel_pos κ (p.1-p.2))]
    calc
      _ ≤ C*(‖F p.1‖*‖v p.2‖) := mul_le_mul (kernel_bounds κ (p.1-p.2)).2
        (norm_inner_le_norm _ _) (norm_nonneg _) hC
      _ ≤ C*(M*‖v p.2‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hM p.1) (norm_nonneg _)) hC
      _ = _ := by ring

variable [SecondCountableTopology E]

/-- Literal duality between flux convolution and test convolution. -/
theorem integral_inner_flux {v F : Coordinates n → E}
    (hv : Integrable v μ) (hF : Continuous F) {M : ℝ} (hM : ∀ x, ‖F x‖ ≤ M) :
    (∫ x, ⟪F x,flux κ μ v x⟫_ℝ ∂cube n) =
      ∫ y, ⟪∫ x, kernel κ (x-y) • F x ∂cube n,v y⟫_ℝ ∂μ := by
  have hi := flux_pairing_joint_integrable κ μ hv hF hM
  calc
    _ = ∫ x, ∫ y, kernel κ (x-y)*⟪F x,v y⟫_ℝ ∂μ ∂cube n := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only
      rw [flux,← integral_inner (kernel_smul_integrable_of_integrable κ μ hv x)]
      simp only [real_inner_smul_right]
    _ = ∫ y, ∫ x, kernel κ (x-y)*⟪F x,v y⟫_ℝ ∂cube n ∂μ := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      dsimp only
      rw [real_inner_comm (v y) (∫ x, kernel κ (x-y) • F x ∂cube n),
        ← integral_inner (weighted_test_integrable hF hM κ y)]
      simp only [real_inner_smul_right,real_inner_comm (v y)]

omit [CompleteSpace E] [SecondCountableTopology E] in
/-- Pairing against the smoothed law and its actual velocity is exactly the flux pairing. -/
theorem integral_inner_fluxVelocity {v F : Coordinates n → E} :
    (∫ x, ⟪F x,fluxVelocity κ μ v x⟫_ℝ ∂smoothLaw κ μ) =
      ∫ x, ⟪F x,flux κ μ v x⟫_ℝ ∂cube n := by
  change (∫ x, ⟪F x,fluxVelocity κ μ v x⟫_ℝ ∂(cube n).withDensity
    (fun x => ENNReal.ofReal (density κ μ x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (density_smooth κ μ).continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (density_pos κ μ x).le,smul_eq_mul,← real_inner_smul_right,
      density_smul_fluxVelocity]

/-- Convolving a finite vector measure preserves every periodic continuous test
pairing in the approximate-identity limit. -/
theorem integral_inner_flux_tendsto {v F : Coordinates n → E}
    (hv : Integrable v μ) (hF : Continuous F)
    (hpF : ∀ i, Function.Periodic F (Pi.single i 1)) :
    Tendsto (fun m : ℕ => ∫ x, ⟪F x,flux (m : ℝ) μ v x⟫_ℝ ∂cube n) atTop
      (𝓝 (∫ y, ⟪F y,v y⟫_ℝ ∂μ)) := by
  obtain ⟨M,hM,hbound⟩ := PeriodicSmoothBounds.norm_bound hpF hF
  simp_rw [integral_inner_flux _ μ hv hF hbound]
  apply tendsto_integral_of_dominated_convergence (fun y => M*‖v y‖)
  · intro m
    have he (y : Coordinates n) :
        ⟪∫ x, kernel (m : ℝ) (x-y) • F x ∂cube n,v y⟫_ℝ =
          ∫ x, kernel (m : ℝ) (x-y)*⟪F x,v y⟫_ℝ ∂cube n := by
      rw [real_inner_comm,← integral_inner (weighted_test_integrable hF hbound (m : ℝ) y)]
      simp only [real_inner_smul_right,real_inner_comm (v y)]
    simp_rw [he]
    exact (flux_pairing_joint_integrable (m : ℝ) μ hv hF hbound).integral_prod_right.aestronglyMeasurable
  · exact hv.norm.const_mul M
  · intro m
    exact Eventually.of_forall fun y =>
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
        (norm_weighted_test_integral_le hF hbound (m : ℝ) y) (norm_nonneg _))
  · exact Eventually.of_forall fun y =>
      (integral_kernel_translate_tendsto hpF hF y).inner (𝕜 := ℝ) tendsto_const_nhds

end SharpWasserstein.PeriodicConvolution
