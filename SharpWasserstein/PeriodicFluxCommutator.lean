import SharpWasserstein.PeriodicFluxContraction

/-! Actual coefficient/flux convolution commutators for finite-energy vector
measures. The weighted estimate avoids a smoothing-uniform density lower
bound and permits merely integrable original fluxes. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SharpWasserstein.PeriodicConvolution
open PeriodicIntegrationByParts PeriodicPositiveKernel
variable {n : ℕ} {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (κ : ℝ) (μ : Measure (Coordinates n)) [IsProbabilityMeasure μ]

def fluxCommutator (A : Coordinates n → E →L[ℝ] F) (v : Coordinates n → E)
    (x : Coordinates n) : F := flux κ μ (fun y => A y (v y)) x-A x (flux κ μ v x)

omit [CompleteSpace E] [CompleteSpace F] [IsProbabilityMeasure μ] in
theorem coefficient_apply_integrable {A : Coordinates n → E →L[ℝ] F}
    (hA : Continuous A) {M : ℝ} (hM : ∀ x, ‖A x‖ ≤ M)
    {v : Coordinates n → E} (hv : Integrable v μ) : Integrable (fun y => A y (v y)) μ := by
  apply (hv.norm.const_mul M).mono'
    ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hA.aestronglyMeasurable.prodMk hv.aestronglyMeasurable))
  exact Eventually.of_forall fun y => (A y).le_of_opNorm_le (hM y) (v y)

omit [CompleteSpace E] [CompleteSpace F] [IsProbabilityMeasure μ] in
theorem coefficient_apply_normsq_integrable {A : Coordinates n → E →L[ℝ] F}
    (hA : Continuous A) {M : ℝ} (hM : ∀ x, ‖A x‖ ≤ M)
    {v : Coordinates n → E} (hv : AEStronglyMeasurable v μ)
    (hv₂ : Integrable (fun y => ‖v y‖^2) μ) :
    Integrable (fun y => ‖A y (v y)‖^2) μ := by
  apply (hv₂.const_mul (M^2)).mono'
    (((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hA.aestronglyMeasurable.prodMk hv)).norm.pow 2)
  exact Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (M*‖v y‖)^2 := pow_le_pow_left₀ (norm_nonneg _) ((A y).le_of_opNorm_le (hM y) _) 2
      _ = _ := mul_pow _ _ _

omit [IsProbabilityMeasure μ] in
theorem fluxCommutator_eq_integral {A : Coordinates n → E →L[ℝ] F}
    (hA : Continuous A) {M : ℝ} (hM : ∀ x, ‖A x‖ ≤ M)
    {v : Coordinates n → E} (hv : Integrable v μ) (x : Coordinates n) :
    fluxCommutator κ μ A v x = ∫ y, kernel κ (x-y) • ((A y-A x) (v y)) ∂μ := by
  have hav := coefficient_apply_integrable μ hA hM hv
  have hvx := (A x).integrable_comp hv
  have he : A x (flux κ μ v x) = flux κ μ (fun y => A x (v y)) x := by
    rw [flux,flux,← (A x).integral_comp_comm (kernel_smul_integrable_of_integrable κ μ hv x)]
    simp only [map_smul]
  rw [fluxCommutator,he,flux,flux,← integral_sub
    (kernel_smul_integrable_of_integrable κ μ hav x)
    (kernel_smul_integrable_of_integrable κ μ hvx x)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by simp [smul_sub]

omit [CompleteSpace E] [CompleteSpace F] [IsProbabilityMeasure μ] in
theorem fluxCommutator_continuous {A : Coordinates n → E →L[ℝ] F}
    (hA : Continuous A) {M : ℝ} (hM : ∀ x, ‖A x‖ ≤ M)
    {v : Coordinates n → E} (hv : Integrable v μ) : Continuous (fluxCommutator κ μ A v) :=
  (flux_continuous_of_integrable κ μ (coefficient_apply_integrable μ hA hM hv)).sub
    (hA.clm_apply (flux_continuous_of_integrable κ μ hv))

omit [CompleteSpace E] [CompleteSpace F] in
theorem fluxCommutator_action_integrable {A : Coordinates n → E →L[ℝ] F}
    (hA : Continuous A) {M : ℝ} (hM : ∀ x, ‖A x‖ ≤ M)
    {v : Coordinates n → E} (hv : Integrable v μ) :
    Integrable (fun x => ‖fluxCommutator κ μ A v x‖^2/density κ μ x) (cube n) :=
  continuous_integrable_cube (((fluxCommutator_continuous κ μ hA hM hv).norm.pow 2).div
    (density_smooth κ μ).continuous (fun x => (density_pos κ μ x).ne'))

/-- Genuine weighted Jensen bound for the actual operator/flux commutator. -/
theorem fluxCommutator_action_le {A : Coordinates n → E →L[ℝ] F}
    (hA : Continuous A) {M : ℝ} (hM : ∀ x, ‖A x‖ ≤ M)
    {v : Coordinates n → E} (hv : Integrable v μ)
    (hv₂ : Integrable (fun y => ‖v y‖^2) μ) (x : Coordinates n) :
    ‖fluxCommutator κ μ A v x‖^2/density κ μ x ≤
      ∫ y, kernel κ (x-y)*‖A y-A x‖^2*‖v y‖^2 ∂μ := by
  have hAx : Continuous (fun y => A y-A x) := hA.sub continuous_const
  have hMx (y : Coordinates n) : ‖A y-A x‖ ≤ 2*M :=
    (norm_sub_le _ _).trans (by linarith [hM y,hM x])
  have h₁ := coefficient_apply_integrable μ hAx hMx hv
  have h₂ := coefficient_apply_normsq_integrable μ hAx hMx hv.aestronglyMeasurable hv₂
  rw [fluxCommutator_eq_integral κ μ hA hM hv]
  apply (flux_action_le_of_integrable κ μ h₁ h₂ x).trans
  have hr : Integrable (fun y => ‖A y-A x‖^2*‖v y‖^2) μ := by
    apply hv₂.bdd_mul (hAx.norm.pow 2).aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hMx y) 2
  have hrk := kernel_mul_integrable_of_integrable κ μ hr x
  simp only [← mul_assoc] at hrk
  apply integral_mono (kernel_mul_integrable_of_integrable κ μ h₂ x) hrk
  intro y
  calc
    _ ≤ kernel κ (x-y)*(‖A y-A x‖*‖v y‖)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ((A y-A x).le_opNorm (v y)) 2)
        (kernel_pos κ (x-y)).le
    _ = _ := by ring

end SharpWasserstein.PeriodicConvolution
