module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicDriftCommutator

@[expose] public section

/-! Genuine convolution of an arbitrary finite-energy flux. The velocity is
constructed from the convolved flux and positive density, and its actual
weighted quadratic action contracts. No boundedness or continuity of the
original velocity, nor absolute continuity of the original law, is assumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace SharpWasserstein.PeriodicConvolution
open PeriodicIntegrationByParts PeriodicPositiveKernel
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (κ : ℝ) (μ : Measure (Coordinates n)) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem kernel_smul_integrable_of_integrable {v : Coordinates n → E}
    (hv : Integrable v μ) (x : Coordinates n) :
    Integrable (fun y => kernel κ (x-y) • v y) μ := by
  apply hv.bdd_smul ((Real.exp |κ|/normalizer κ)^n) ((kernel_smooth n κ).continuous.comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact Eventually.of_forall (fun y => by
    change ‖kernel κ (x-y)‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_pos (kernel_pos κ (x-y))]
    exact (kernel_bounds κ (x-y)).2)

omit [IsProbabilityMeasure μ] in
theorem flux_continuous_of_integrable {v : Coordinates n → E} (hv : Integrable v μ) :
    Continuous (flux κ μ v) := by
  apply continuous_of_dominated (bound := fun y => (Real.exp |κ|/normalizer κ)^n*‖v y‖)
  · intro x
    exact (((kernel_smooth n κ).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).smul hv.aestronglyMeasurable
  · intro x
    exact Eventually.of_forall (fun y => by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (kernel_pos κ (x-y))]
      exact mul_le_mul_of_nonneg_right (kernel_bounds κ (x-y)).2 (norm_nonneg _))
  · exact hv.norm.const_mul _
  · exact Eventually.of_forall fun y => ((kernel_smooth n κ).continuous.comp
      (continuous_id.sub continuous_const)).smul continuous_const

omit [IsProbabilityMeasure μ] in
theorem flux_periodic (v : Coordinates n → E) :
    ∀ i, Function.Periodic (flux κ μ v) (Pi.single i 1) := by
  intro i x
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  have he : (x+Pi.single i 1)-y = (x-y)+Pi.single i 1 := by abel
  change kernel κ ((x+Pi.single i 1)-y) • v y = kernel κ (x-y) • v y
  rw [he,kernel_periodic n κ i]

omit [IsProbabilityMeasure μ] in
theorem kernel_mul_integrable_of_integrable {f : Coordinates n → ℝ}
    (hf : Integrable f μ) (x : Coordinates n) :
    Integrable (fun y => kernel κ (x-y)*f y) μ := by
  simpa only [smul_eq_mul] using kernel_smul_integrable_of_integrable κ μ hf x

theorem flux_action_le_of_integrable {v : Coordinates n → E}
    (hv : Integrable v μ) (hv₂ : Integrable (fun y => ‖v y‖^2) μ) (x : Coordinates n) :
    ‖flux κ μ v x‖^2 / density κ μ x ≤ ∫ y, kernel κ (x-y)*‖v y‖^2 ∂μ :=
  WeightedIntegralSquare.weighted_norm_integral_sq_le (kernel_translate_integrable κ μ x)
    (kernel_mul_integrable_of_integrable κ μ hv.norm x)
    (kernel_mul_integrable_of_integrable κ μ hv₂ x)
    (Eventually.of_forall fun y => (kernel_pos κ (x-y)).le) (density_pos κ μ x)

omit [NormedSpace ℝ E] in
theorem kernel_normsq_joint_integrable {v : Coordinates n → E}
    (hv₂ : Integrable (fun y => ‖v y‖^2) μ) :
    Integrable (fun p : Coordinates n × Coordinates n => kernel κ (p.1-p.2)*‖v p.2‖^2)
      ((cube n).prod μ) := by
  apply (hv₂.comp_snd (cube n)).bdd_mul
    ((kernel_smooth n κ).continuous.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    change ‖kernel κ (p.1-p.2)‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_pos (kernel_pos κ (p.1-p.2))]
    exact (kernel_bounds κ (p.1-p.2)).2

/-- Jensen contraction for the actual smoothed flux, uniform in the smoothing parameter. -/
theorem integral_flux_action_le {v : Coordinates n → E}
    (hv : Integrable v μ) (hv₂ : Integrable (fun y => ‖v y‖^2) μ) :
    (∫ x, ‖flux κ μ v x‖^2 / density κ μ x ∂cube n) ≤ ∫ y, ‖v y‖^2 ∂μ := by
  have hi := kernel_normsq_joint_integrable κ μ hv₂
  have hc := ((flux_continuous_of_integrable κ μ hv).norm.pow 2).div
    (density_smooth κ μ).continuous (fun x => (density_pos κ μ x).ne')
  calc
    _ ≤ ∫ x, ∫ y, kernel κ (x-y)*‖v y‖^2 ∂μ ∂cube n :=
      integral_mono (continuous_integrable_cube hc) hi.integral_prod_left
        (flux_action_le_of_integrable κ μ hv hv₂)
    _ = ∫ y, ∫ x, kernel κ (x-y)*‖v y‖^2 ∂cube n ∂μ := integral_integral_swap hi
    _ = _ := by
      simp_rw [integral_mul_const,integral_cube_sub (kernel_periodic n κ)
        (kernel_smooth n κ).continuous,kernel_integral,one_mul]

/-- The actual representing velocity of the smoothed flux. -/
def fluxVelocity (v : Coordinates n → E) (x : Coordinates n) : E :=
  (density κ μ x)⁻¹ • flux κ μ v x

theorem fluxVelocity_continuous {v : Coordinates n → E} (hv : Integrable v μ) :
    Continuous (fluxVelocity κ μ v) :=
  ((density_smooth κ μ).continuous.inv₀ (fun x => (density_pos κ μ x).ne')).smul
    (flux_continuous_of_integrable κ μ hv)

omit [IsProbabilityMeasure μ] in
theorem fluxVelocity_periodic (v : Coordinates n → E) :
    ∀ i, Function.Periodic (fluxVelocity κ μ v) (Pi.single i 1) := by
  intro i x
  simp only [fluxVelocity,density_periodic κ μ i x,flux_periodic κ μ v i x]

theorem fluxVelocity_sq_integrable {v : Coordinates n → E} (hv : Integrable v μ) :
    Integrable (fun x => ‖fluxVelocity κ μ v x‖^2) (smoothLaw κ μ) := by
  letI := smoothLaw_probability κ μ
  obtain ⟨C,hC,hbound⟩ := PeriodicSmoothBounds.norm_bound
    (fluxVelocity_periodic κ μ v) (fluxVelocity_continuous κ μ hv)
  apply Integrable.of_bound ((fluxVelocity_continuous κ μ hv).norm.pow 2).aestronglyMeasurable (C^2)
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound x) 2

theorem fluxVelocity_memLp {v : Coordinates n → E} (hv : Integrable v μ) :
    MemLp (fluxVelocity κ μ v) 2 (smoothLaw κ μ) := by
  letI := smoothLaw_probability κ μ
  obtain ⟨C,_,hbound⟩ := PeriodicSmoothBounds.norm_bound
    (fluxVelocity_periodic κ μ v) (fluxVelocity_continuous κ μ hv)
  exact MemLp.of_bound (fluxVelocity_continuous κ μ hv).aestronglyMeasurable C
    (Eventually.of_forall hbound)

theorem density_smul_fluxVelocity (v : Coordinates n → E) (x : Coordinates n) :
    density κ μ x • fluxVelocity κ μ v x = flux κ μ v x := by
  rw [fluxVelocity,smul_smul,mul_inv_cancel₀ (density_pos κ μ x).ne',one_smul]

/-- The law-weighted action of the genuinely constructed velocity contracts,
including when the original law is singular. -/
theorem integral_fluxVelocity_sq_le {v : Coordinates n → E}
    (hv : Integrable v μ) (hv₂ : Integrable (fun y => ‖v y‖^2) μ) :
    (∫ x, ‖fluxVelocity κ μ v x‖^2 ∂smoothLaw κ μ) ≤ ∫ y, ‖v y‖^2 ∂μ := by
  change (∫ x, ‖fluxVelocity κ μ v x‖^2 ∂(cube n).withDensity
    (fun x => ENNReal.ofReal (density κ μ x))) ≤ _
  rw [integral_withDensity_eq_integral_toReal_smul
    (density_smooth κ μ).continuous.measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have he (x : Coordinates n) :
      (ENNReal.ofReal (density κ μ x)).toReal • ‖fluxVelocity κ μ v x‖^2 =
        ‖flux κ μ v x‖^2/density κ μ x := by
    rw [ENNReal.toReal_ofReal (density_pos κ μ x).le,smul_eq_mul,fluxVelocity,norm_smul,
      norm_inv,Real.norm_eq_abs,abs_of_pos (density_pos κ μ x)]
    field_simp [(density_pos κ μ x).ne']
  simp_rw [he]
  exact integral_flux_action_le κ μ hv hv₂

end SharpWasserstein.PeriodicConvolution
