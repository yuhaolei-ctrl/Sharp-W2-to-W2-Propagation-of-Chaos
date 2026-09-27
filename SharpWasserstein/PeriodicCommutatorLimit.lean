import SharpWasserstein.PeriodicConvolutionApproximation
import SharpWasserstein.PeriodicDriftCommutator

/-! The actual drift-convolution commutator tends to zero in integrated
weighted quadratic action for every continuous periodic drift and arbitrary
probability law. No density lower bound uniform in the smoothing parameter
is used; integrability of the actual action is proved separately. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace SharpWasserstein.PeriodicConvolution
open PeriodicIntegrationByParts PeriodicPositiveKernel

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem flux_continuous {b : Coordinates n → E} (hb : Continuous b)
    {M : ℝ} (hM : ∀ y, ‖b y‖ ≤ M) (κ : ℝ) (μ : Measure (Coordinates n))
    [IsProbabilityMeasure μ] : Continuous (flux κ μ b) := by
  apply continuous_of_dominated (bound := fun _ => (Real.exp |κ|/normalizer κ)^n*M)
  · intro x
    exact (kernel_smul_integrable κ μ hb hM x).aestronglyMeasurable
  · intro x
    apply Eventually.of_forall
    intro y
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (kernel_pos κ (x-y))]
    exact mul_le_mul (kernel_bounds κ (x-y)).2 (hM y) (norm_nonneg _)
      (pow_nonneg (div_pos (Real.exp_pos _) (normalizer_pos κ)).le n)
  · exact integrable_const _
  · exact Eventually.of_forall (fun y => ((kernel_smooth n κ).continuous.comp
      (continuous_id.sub continuous_const)).smul continuous_const)

omit [CompleteSpace E] in
theorem commutator_continuous {b : Coordinates n → E} (hb : Continuous b)
    {M : ℝ} (hM : ∀ y, ‖b y‖ ≤ M) (κ : ℝ) (μ : Measure (Coordinates n))
    [IsProbabilityMeasure μ] : Continuous (commutator κ μ b) :=
  (flux_continuous hb hM κ μ).sub ((density_smooth κ μ).continuous.smul hb)

omit [CompleteSpace E] in
theorem commutator_action_integrable {b : Coordinates n → E} (hb : Continuous b)
    {M : ℝ} (hM : ∀ y, ‖b y‖ ≤ M) (κ : ℝ) (μ : Measure (Coordinates n))
    [IsProbabilityMeasure μ] :
    Integrable (fun x => ‖commutator κ μ b x‖^2 / density κ μ x) (cube n) :=
  continuous_integrable_cube (((commutator_continuous hb hM κ μ).norm.pow 2).div
    (density_smooth κ μ).continuous (fun x => (density_pos κ μ x).ne'))

omit [CompleteSpace E] [NormedSpace ℝ E] in
theorem differenceSquare_bound {b : Coordinates n → E} {M : ℝ} (hM : ∀ y, ‖b y‖ ≤ M)
    (x y : Coordinates n) : ‖b y-b x‖^2 ≤ (2*M)^2 := by
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact (norm_sub_le _ _).trans (by linarith [hM y,hM x])

omit [CompleteSpace E] [NormedSpace ℝ E] in
theorem differenceSquare_joint_integrable {b : Coordinates n → E} (hb : Continuous b)
    {M : ℝ} (hM : ∀ y, ‖b y‖ ≤ M) (κ : ℝ) (μ : Measure (Coordinates n))
    [IsProbabilityMeasure μ] :
    Integrable (fun p : Coordinates n × Coordinates n => kernel κ (p.1-p.2)*‖b p.2-b p.1‖^2)
      ((cube n).prod μ) := by
  apply Integrable.of_bound (((kernel_smooth n κ).continuous.comp
      (continuous_fst.sub continuous_snd)).mul
      (((hb.comp continuous_snd).sub (hb.comp continuous_fst)).norm.pow 2)).aestronglyMeasurable
    ((Real.exp |κ|/normalizer κ)^n*(2*M)^2)
  exact Eventually.of_forall (fun p => by
    change ‖kernel κ (p.1-p.2)*‖b p.2-b p.1‖^2‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (kernel_pos κ (p.1-p.2)).le (sq_nonneg _))]
    exact mul_le_mul (kernel_bounds κ (p.1-p.2)).2 (differenceSquare_bound hM p.1 p.2)
      (sq_nonneg _) (pow_nonneg (div_pos (Real.exp_pos _) (normalizer_pos κ)).le n))

omit [CompleteSpace E] [NormedSpace ℝ E] in
theorem integrated_differenceSquare_tendsto {b : Coordinates n → E}
    (hp : ∀ i, Function.Periodic b (Pi.single i 1)) (hb : Continuous b)
    (μ : Measure (Coordinates n)) [IsProbabilityMeasure μ] :
    Tendsto (fun m : ℕ => ∫ x, ∫ y, kernel (m : ℝ) (x-y)*‖b y-b x‖^2 ∂μ ∂cube n)
      atTop (𝓝 0) := by
  obtain ⟨M,_,hM⟩ := PeriodicSmoothBounds.norm_bound hp hb
  have he (m : ℕ) : (∫ x, ∫ y, kernel (m : ℝ) (x-y)*‖b y-b x‖^2 ∂μ ∂cube n) =
      ∫ y, ∫ x, kernel (m : ℝ) (x-y)*‖b y-b x‖^2 ∂cube n ∂μ :=
    integral_integral_swap (differenceSquare_joint_integrable hb hM (m : ℝ) μ)
  simp_rw [he]
  have hlim (y : Coordinates n) : Tendsto
      (fun m : ℕ => ∫ x, kernel (m : ℝ) (x-y)*‖b y-b x‖^2 ∂cube n) atTop (𝓝 0) := by
    have hpf : ∀ i, Function.Periodic (fun x => ‖b y-b x‖^2) (Pi.single i 1) := by
      intro i x
      change ‖b y-b (x+Pi.single i 1)‖^2 = ‖b y-b x‖^2
      rw [hp i]
    have h := integral_kernel_translate_tendsto hpf ((continuous_const.sub hb).norm.pow 2) y
    simpa only [smul_eq_mul,sub_self,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun m y => ∫ x, kernel (m : ℝ) (x-y)*‖b y-b x‖^2 ∂cube n)
    (f := fun _ => (0 : ℝ)) (fun _ => (2*M)^2)
    (fun m => (differenceSquare_joint_integrable hb hM (m : ℝ) μ).integral_prod_right.aestronglyMeasurable)
    (integrable_const _) ?_ (Eventually.of_forall hlim)
  · simpa only [integral_zero] using h
  · intro m
    apply Eventually.of_forall
    intro y
    exact norm_weighted_test_integral_le ((continuous_const.sub hb).norm.pow 2)
      (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]; exact differenceSquare_bound hM x y)
      (m : ℝ) y

theorem commutator_action_tendsto {b : Coordinates n → E}
    (hp : ∀ i, Function.Periodic b (Pi.single i 1)) (hb : Continuous b)
    (μ : Measure (Coordinates n)) [IsProbabilityMeasure μ] :
    Tendsto (fun m : ℕ => ∫ x, ‖commutator (m : ℝ) μ b x‖^2 / density (m : ℝ) μ x ∂cube n)
      atTop (𝓝 0) := by
  obtain ⟨M,_,hM⟩ := PeriodicSmoothBounds.norm_bound hp hb
  refine squeeze_zero (fun m : ℕ => ?_) (fun m : ℕ => ?_) (integrated_differenceSquare_tendsto hp hb μ)
  · exact integral_nonneg (fun x => div_nonneg (sq_nonneg _) (density_pos (m : ℝ) μ x).le)
  · exact integral_mono (commutator_action_integrable hb hM (m : ℝ) μ)
      (differenceSquare_joint_integrable hb hM (m : ℝ) μ).integral_prod_left
      (commutator_action_le (m : ℝ) μ hb hM)

end SharpWasserstein.PeriodicConvolution
