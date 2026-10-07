module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicKernelConcentration

@[expose] public section

/-! Approximation of every probability law by its actual positive periodic
convolution densities, tested against continuous periodic functions. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace SharpWasserstein.PeriodicConvolution
open PeriodicIntegrationByParts PeriodicPositiveKernel

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] in
theorem integral_kernel_translate {f : Coordinates n → E}
    (hp : ∀ i, Function.Periodic f (Pi.single i 1)) (hf : Continuous f)
    (κ : ℝ) (y : Coordinates n) :
    (∫ x, kernel κ (x-y) • f x ∂cube n) = ∫ z, kernel κ z • f (z+y) ∂cube n := by
  let g : Coordinates n → E := fun z => kernel κ z • f (z+y)
  have hg : Continuous g := (kernel_smooth n κ).continuous.smul (hf.comp (continuous_id.add continuous_const))
  have hgp : ∀ i, Function.Periodic g (Pi.single i 1) := by
    intro i x
    dsimp only [g]
    rw [kernel_periodic n κ i]
    congr 1
    have he : x+Pi.single i 1+y = (x+y)+Pi.single i 1 := by abel
    rw [he,hp i]
  have he := integral_cube_sub hgp hg y
  simpa only [g,sub_add_cancel] using he

theorem integral_kernel_translate_tendsto {f : Coordinates n → E}
    (hp : ∀ i, Function.Periodic f (Pi.single i 1)) (hf : Continuous f) (y : Coordinates n) :
    Tendsto (fun m : ℕ => ∫ x, kernel (m : ℝ) (x-y) • f x ∂cube n) atTop (𝓝 (f y)) := by
  have hp' : ∀ i, Function.Periodic (fun z => f (z+y)) (Pi.single i 1) := by
    intro i x
    have he : x+Pi.single i 1+y = (x+y)+Pi.single i 1 := by abel
    change f (x+Pi.single i 1+y) = f (x+y)
    rw [he,hp i]
  have h := integral_kernel_tendsto hp' (hf.comp (continuous_id.add continuous_const))
  simpa only [integral_kernel_translate hp hf,zero_add] using h

omit [CompleteSpace E] in
theorem weighted_test_integrable {f : Coordinates n → E} (hf : Continuous f)
    {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (κ : ℝ) (y : Coordinates n) :
    Integrable (fun x => kernel κ (x-y) • f x) (cube n) :=
  (continuous_integrable_cube ((kernel_smooth n κ).continuous.comp
    (continuous_id.sub continuous_const))).smul_bdd M hf.aestronglyMeasurable
      (Eventually.of_forall hM)

omit [CompleteSpace E] in
theorem norm_weighted_test_integral_le {f : Coordinates n → E} (hf : Continuous f)
    {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (κ : ℝ) (y : Coordinates n) :
    ‖∫ x, kernel κ (x-y) • f x ∂cube n‖ ≤ M := by
  have hi := weighted_test_integrable hf hM κ y
  calc
    _ ≤ ∫ x, ‖kernel κ (x-y) • f x‖ ∂cube n := norm_integral_le_integral_norm _
    _ ≤ ∫ x, kernel κ (x-y)*M ∂cube n := by
      apply integral_mono hi.norm
        ((continuous_integrable_cube ((kernel_smooth n κ).continuous.comp
          (continuous_id.sub continuous_const))).mul_const M)
      intro x
      change ‖kernel κ (x-y) • f x‖ ≤ kernel κ (x-y)*M
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (kernel_pos κ (x-y))]
      exact mul_le_mul_of_nonneg_left (hM x) (kernel_pos κ (x-y)).le
    _ = M := by rw [integral_mul_const,integral_cube_sub (kernel_periodic n κ)
        (kernel_smooth n κ).continuous,kernel_integral,one_mul]

omit [CompleteSpace E] in
theorem convolution_test_joint_integrable {f : Coordinates n → E} (hf : Continuous f)
    {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (κ : ℝ) (μ : Measure (Coordinates n))
    [IsProbabilityMeasure μ] :
    Integrable (fun p : Coordinates n × Coordinates n => kernel κ (p.1-p.2) • f p.1)
      ((cube n).prod μ) := by
  apply Integrable.of_bound (((kernel_smooth n κ).continuous.comp
      (continuous_fst.sub continuous_snd)).smul (hf.comp continuous_fst)).aestronglyMeasurable
    ((Real.exp |κ|/normalizer κ)^n*M)
  exact Eventually.of_forall (fun p => by
    change ‖kernel κ (p.1-p.2) • f p.1‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (kernel_pos κ (p.1-p.2))]
    exact mul_le_mul (kernel_bounds κ (p.1-p.2)).2 (hM p.1) (norm_nonneg _)
      (pow_nonneg (div_pos (Real.exp_pos _) (normalizer_pos κ)).le n))

theorem integral_smoothLaw {f : Coordinates n → E} (hf : Continuous f)
    {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (κ : ℝ) (μ : Measure (Coordinates n))
    [IsProbabilityMeasure μ] :
    (∫ x, f x ∂smoothLaw κ μ) = ∫ y, ∫ x, kernel κ (x-y) • f x ∂cube n ∂μ := by
  change (∫ x, f x ∂(cube n).withDensity (fun x => ENNReal.ofReal (density κ μ x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (density_smooth κ μ).continuous.measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (density_pos κ μ _).le]
  have he : (fun x => density κ μ x • f x) =
      (fun x => ∫ y, kernel κ (x-y) • f x ∂μ) := by
    funext x
    rw [integral_smul_const]
    rfl
  rw [he,integral_integral_swap (convolution_test_joint_integrable hf hM κ μ)]

theorem integral_smoothLaw_tendsto {f : Coordinates n → E}
    (hp : ∀ i, Function.Periodic f (Pi.single i 1)) (hf : Continuous f)
    (μ : Measure (Coordinates n)) [IsProbabilityMeasure μ] :
    Tendsto (fun m : ℕ => ∫ x, f x ∂smoothLaw (m : ℝ) μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  obtain ⟨M,_,hM⟩ := PeriodicSmoothBounds.norm_bound hp hf
  simp_rw [integral_smoothLaw hf hM]
  apply tendsto_integral_of_dominated_convergence (fun _ => M)
  · intro m
    exact (convolution_test_joint_integrable hf hM (m : ℝ) μ).integral_prod_right.aestronglyMeasurable
  · exact integrable_const M
  · intro m
    exact Eventually.of_forall (norm_weighted_test_integral_le hf hM (m : ℝ))
  · exact Eventually.of_forall (integral_kernel_translate_tendsto hp hf)

end SharpWasserstein.PeriodicConvolution
