import SharpWasserstein.RoughEulerianSmoothingGaussian

/-! Actual probability-law regularization by compact convolution and a
stationary Gaussian floor. The constructed smooth velocity carries exactly
the scaled convolved flux and its genuine law-weighted energy contracts. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff NNReal
namespace SharpWasserstein.RoughEulerianSmoothing
open WeightedTangent NoiseAverage
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

def regularizedDensity (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (μ : Measure (Point d)) : Point d → ℝ :=
  floorDensity (1-δ) (density ε hε μ) (fun x => δ*gaussianFloor x)

def regularizedVelocity (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (μ : Measure (Point d))
    (v : Point d → Point d) : Point d → Point d :=
  floorVelocity (1-δ) (density ε hε μ) (fun x => δ*gaussianFloor x) (flux ε hε μ v)

def regularizedLaw (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (μ : Measure (Point d)) : Measure (Point d) :=
  volume.withDensity (fun x => ENNReal.ofReal (regularizedDensity ε hε δ μ x))

theorem regularizedDensity_pos {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (μ : Measure (Point d)) (x : Point d) : 0 < regularizedDensity ε hε δ μ x :=
  floorDensity_pos (sub_nonneg.mpr hδ₁) (density_nonneg hε μ)
    (fun y => mul_pos hδ (gaussianFloor_pos y)) x

theorem regularizedDensity_smooth {ε : ℝ} (hε : 0 < ε) (δ : ℝ)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ] :
    ContDiff ℝ ∞ (regularizedDensity ε hε δ μ) :=
  (contDiff_const.mul (density_smooth hε μ)).add (contDiff_const.mul gaussianFloor_smooth)

theorem regularizedDensity_integrable {ε : ℝ} (hε : 0 < ε) (δ : ℝ)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ] :
    Integrable (regularizedDensity ε hε δ μ) := by
  exact ((density_integrable hε μ).const_mul (1-δ)).add (gaussianFloor_integrable.const_mul δ)

theorem regularizedDensity_integral {ε : ℝ} (hε : 0 < ε) (δ : ℝ)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ] :
    (∫ x, regularizedDensity ε hε δ μ x) = 1 := by
  change (∫ x, (1-δ)*density ε hε μ x + δ*gaussianFloor x) = 1
  rw [integral_add ((density_integrable hε μ).const_mul (1-δ))
    (gaussianFloor_integrable.const_mul δ), integral_const_mul, integral_const_mul,
    density_integral hε μ, gaussianFloor_integral]
  ring

theorem regularizedLaw_probability {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (regularizedLaw ε hε δ μ) := by
  apply isProbabilityMeasure_iff.mpr
  rw [regularizedLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (regularizedDensity_integrable hε δ μ)
      (Eventually.of_forall fun x => (regularizedDensity_pos hε hδ hδ₁ μ x).le),
    regularizedDensity_integral hε δ μ, ENNReal.ofReal_one]

theorem regularizedVelocity_flux {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (μ : Measure (Point d)) (v : Point d → Point d) (x : Point d) :
    regularizedDensity ε hε δ μ x • regularizedVelocity ε hε δ μ v x =
      (1-δ) • flux ε hε μ v x :=
  floorVelocity_flux (sub_nonneg.mpr hδ₁) (density_nonneg hε μ)
    (fun y => mul_pos hδ (gaussianFloor_pos y)) (flux ε hε μ v) x

/-- This bound is for the actual representing velocity under the actual
regularized probability law, rather than an unweighted density proxy. -/
theorem regularizedLaw_velocity_energy_le {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (μ : Measure (Point d)) [IsProbabilityMeasure μ]
    {v : Point d → Point d} (hv : Integrable v μ)
    (hv₂ : Integrable (fun y => ‖v y‖^2) μ) :
    (∫ x, ‖regularizedVelocity ε hε δ μ v x‖^2 ∂regularizedLaw ε hε δ μ) ≤
      (1-δ) * ∫ y, ‖v y‖^2 ∂μ := by
  rw [regularizedLaw, integral_withDensity_eq_integral_toReal_smul
    (regularizedDensity_smooth hε δ μ).continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (regularizedDensity_pos hε hδ hδ₁ μ _).le, smul_eq_mul]
  exact integral_convolved_floor_action_le hε (sub_nonneg.mpr hδ₁) μ hv hv₂
    (fun y => mul_pos hδ (gaussianFloor_pos y)) (gaussianFloor_smooth.continuous.const_mul δ)

theorem regularizedVelocity_smooth {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (μ : Measure (Point d)) [IsProbabilityMeasure μ]
    {v : Point d → Point d} (hv : Integrable v μ) :
    ContDiff ℝ ∞ (regularizedVelocity ε hε δ μ v) :=
  floorVelocity_smooth (sub_nonneg.mpr hδ₁) (density_nonneg hε μ)
    (fun y => mul_pos hδ (gaussianFloor_pos y)) (density_smooth hε μ)
    (contDiff_const.mul gaussianFloor_smooth) (flux_smooth hε μ hv)

theorem regularizedLaw_velocity_memLp {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (μ : Measure (Point d)) [IsProbabilityMeasure μ]
    {v : Point d → Point d} (hv : Integrable v μ)
    (hv₂ : Integrable (fun y => ‖v y‖^2) μ) :
    MemLp (regularizedVelocity ε hε δ μ v) 2 (regularizedLaw ε hε δ μ) := by
  apply (memLp_two_iff_integrable_sq_norm
    (regularizedVelocity_smooth hε hδ hδ₁ μ hv).continuous.aestronglyMeasurable).mpr
  apply (integrable_withDensity_iff_integrable_smul'
    (regularizedDensity_smooth hε δ μ).continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  simp only [ENNReal.toReal_ofReal (regularizedDensity_pos hε hδ hδ₁ μ _).le, smul_eq_mul]
  exact convolved_floor_action_integrable hε (sub_nonneg.mpr hδ₁) μ hv hv₂
    (fun y => mul_pos hδ (gaussianFloor_pos y)) (gaussianFloor_smooth.continuous.const_mul δ)

theorem regularizedVelocity_regular {ε δ R : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (μ : Measure (Point d)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ R) {v : Point d → Point d} (hv : Integrable v μ) :
    AllDerivativesBounded (regularizedVelocity ε hε δ μ v) ∧
      (∃ K : ℝ≥0, LipschitzWith K (regularizedVelocity ε hε δ μ v)) ∧
      (∃ K₁ : ℝ≥0, LipschitzWith K₁ (fderiv ℝ (regularizedVelocity ε hε δ μ v))) :=
  convolved_floor_regular hε (sub_nonneg.mpr hδ₁) μ hμ hv
    (fun y => mul_pos hδ (gaussianFloor_pos y)) (contDiff_const.mul gaussianFloor_smooth)

theorem density_compact {ε R : ℝ} (hε : 0 < ε) (μ : Measure (Point d))
    (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ R) : HasCompactSupport (density ε hε μ) := by
  apply HasCompactSupport.intro' (isCompact_closedBall (0 : Point d) (R+ε))
    Metric.isClosed_closedBall
  intro x hx
  have hx' : R+ε < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  apply integral_eq_zero_of_ae
  filter_upwards [hμ] with y hy
  have hdist : ε ≤ ‖x-y‖ := by
    have hh := norm_le_norm_sub_add x y
    linarith
  exact mollifier_eq_zero hε hdist

/-- The positive floor does not lose the second-moment condition after
compression: the convolution part is compactly supported and the Gaussian
part has an explicitly proved integrable quadratic moment. -/
theorem regularizedLaw_quadratic_integrable {ε δ R : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (μ : Measure (Point d)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ R) :
    Integrable (fun x : Point d => ‖x‖^2) (regularizedLaw ε hε δ μ) := by
  have hρ : Integrable (fun x : Point d => density ε hε μ x * ‖x‖^2) :=
    ((density_smooth hε μ).continuous.mul (continuous_norm.pow 2)).integrable_of_hasCompactSupport
      (density_compact hε μ hμ).mul_right
  apply (integrable_withDensity_iff_integrable_smul'
    (regularizedDensity_smooth hε δ μ).continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  simp only [ENNReal.toReal_ofReal (regularizedDensity_pos hε hδ hδ₁ μ _).le, smul_eq_mul]
  simp only [regularizedDensity, floorDensity, add_mul, mul_assoc]
  exact (hρ.const_mul (1-δ)).add (gaussianFloor_quadratic_integrable.const_mul δ)

end SharpWasserstein.RoughEulerianSmoothing
