module

public import SharpWasserstein.Compat
public import SharpWasserstein.RoughEulerianSmoothingCoupling

@[expose] public section

/-! An actual coupling for the Gaussian-floor regularization. The compact
convolution contributes at most ε², and the stationary floor contributes a
vanishing multiple of finite original/Gaussian quadratic moments. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff NNReal
namespace SharpWasserstein.RoughEulerianSmoothing
open WeightedTangent
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

def gaussianFloorLaw : Measure (Point d) := volume.withDensity (fun x => ENNReal.ofReal (gaussianFloor x))

instance gaussianFloorLaw_probability : IsProbabilityMeasure (gaussianFloorLaw (d := d)) := by
  apply isProbabilityMeasure_iff.mpr
  rw [gaussianFloorLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal gaussianFloor_integrable
      (Eventually.of_forall fun x => (gaussianFloor_pos x).le), gaussianFloor_integral, ENNReal.ofReal_one]

theorem gaussianFloorLaw_quadratic_integrable :
    Integrable (fun x : Point d => ‖x‖^2) gaussianFloorLaw := by
  apply (integrable_withDensity_iff_integrable_smul'
    gaussianFloor_smooth.continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  simp only [ENNReal.toReal_ofReal (gaussianFloor_pos _).le, smul_eq_mul]
  exact gaussianFloor_quadratic_integrable

theorem regularizedLaw_eq_mixture {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ] :
    regularizedLaw ε hε δ μ = ENNReal.ofReal (1-δ) • convolvedLaw ε hε μ +
      ENNReal.ofReal δ • gaussianFloorLaw := by
  have hd : (fun x => ENNReal.ofReal (regularizedDensity ε hε δ μ x)) =
      ENNReal.ofReal (1-δ) • (fun x => ENNReal.ofReal (density ε hε μ x)) +
      ENNReal.ofReal δ • (fun x => ENNReal.ofReal (gaussianFloor x)) := by
    funext x
    simp only [regularizedDensity, floorDensity, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.ofReal_add (mul_nonneg (sub_nonneg.mpr hδ₁) (density_nonneg hε μ x))
      (mul_nonneg hδ (gaussianFloor_pos x).le), ENNReal.ofReal_mul (sub_nonneg.mpr hδ₁),
      ENNReal.ofReal_mul hδ]
  rw [regularizedLaw, hd, withDensity_add_left
    ((density_smooth hε μ).continuous.measurable.ennreal_ofReal.const_smul _),
    withDensity_smul _ (density_smooth hε μ).continuous.measurable.ennreal_ofReal,
    withDensity_smul _ gaussianFloor_smooth.continuous.measurable.ennreal_ofReal]
  rfl

omit [MeasurableSpace (Point d)] [BorelSpace (Point d)] in
theorem euclidean_displacement_sq_le (x y : Point d) : ‖x-y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2 := by
  have hh := pow_le_pow_left₀ (norm_nonneg (x-y)) (norm_sub_le x y) 2
  nlinarith [sq_nonneg (‖x‖-‖y‖)]

theorem product_displacement_integrable (μ ν : Measure (Point d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x => ‖x‖^2) μ) (hν : Integrable (fun x => ‖x‖^2) ν) :
    Integrable (fun z : Point d × Point d => ‖z.1-z.2‖^2) (μ.prod ν) := by
  apply Integrable.mono' (((hμ.comp_fst ν).const_mul 2).add ((hν.comp_snd μ).const_mul 2))
    ((continuous_fst.sub continuous_snd).norm.pow 2).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact euclidean_displacement_sq_le z.1 z.2

theorem product_displacement_integral_le (μ ν : Measure (Point d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x => ‖x‖^2) μ) (hν : Integrable (fun x => ‖x‖^2) ν) :
    (∫ z : Point d × Point d, ‖z.1-z.2‖^2 ∂μ.prod ν) ≤
      2*(∫ x, ‖x‖^2 ∂μ)+2*(∫ y, ‖y‖^2 ∂ν) := by
  calc
    _ ≤ ∫ z : Point d × Point d, 2*‖z.1‖^2+2*‖z.2‖^2 ∂μ.prod ν :=
      integral_mono (product_displacement_integrable μ ν hμ hν)
        (((hμ.comp_fst ν).const_mul 2).add ((hν.comp_snd μ).const_mul 2))
        (fun z => euclidean_displacement_sq_le z.1 z.2)
    _ = _ := by
      rw [integral_add ((hμ.comp_fst ν).const_mul 2) ((hν.comp_snd μ).const_mul 2),
        integral_const_mul, integral_const_mul,
        integral_fun_fst (μ := μ) (ν := ν) (fun x : Point d => ‖x‖^2),
        integral_fun_snd (μ := μ) (ν := ν) (fun x : Point d => ‖x‖^2)]
      simp only [probReal_univ, one_smul]

def regularizationCoupling (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (μ : Measure (Point d)) :
    Measure (Point d × Point d) := ENNReal.ofReal (1-δ) • convolutionCoupling ε hε μ +
      ENNReal.ofReal δ • (gaussianFloorLaw.prod μ)

theorem regularizationCoupling_isCoupling {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ] :
    IsCoupling (regularizedLaw ε hε δ μ) μ (regularizationCoupling ε hε δ μ) := by
  have hc := convolutionCoupling_isCoupling hε μ
  letI : IsProbabilityMeasure (convolutionCoupling ε hε μ) := hc.1
  have hsum : ENNReal.ofReal (1-δ)+ENNReal.ofReal δ = 1 := by
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hδ₁) hδ]
    simp
  refine ⟨isProbabilityMeasure_iff.mpr ?_, ?_, ?_⟩
  · simp only [regularizationCoupling, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one, hsum]
  · rw [regularizationCoupling, Measure.map_add _ _ measurable_fst,
      Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_smul _ measurable_fst.aemeasurable,
      hc.2.1, Measure.map_fst_prod, measure_univ, one_smul, regularizedLaw_eq_mixture hε hδ hδ₁ μ]
  · rw [regularizationCoupling, Measure.map_add _ _ measurable_snd,
      Measure.map_smul _ measurable_snd.aemeasurable, Measure.map_smul _ measurable_snd.aemeasurable,
      hc.2.2, Measure.map_snd_prod, measure_univ, one_smul, ← add_smul, hsum, one_smul]

theorem regularizationCoupling_cost_integrable {ε : ℝ} (hε : 0 < ε) (δ : ℝ)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ] (hμ : Integrable (fun x => ‖x‖^2) μ) :
    Integrable (fun z : Point d × Point d => ‖z.1-z.2‖^2) (regularizationCoupling ε hε δ μ) :=
  ((convolutionCoupling_cost_integrable hε μ).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((product_displacement_integrable gaussianFloorLaw μ gaussianFloorLaw_quadratic_integrable hμ).smul_measure
      ENNReal.ofReal_ne_top)

theorem regularizationCoupling_cost_le {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ] (hμ : Integrable (fun x => ‖x‖^2) μ) :
    (∫ z : Point d × Point d, ‖z.1-z.2‖^2 ∂regularizationCoupling ε hε δ μ) ≤
      ε^2 + δ*(2*(∫ x : Point d, ‖x‖^2 ∂gaussianFloorLaw)+2*(∫ y, ‖y‖^2 ∂μ)) := by
  have hi₁ := (convolutionCoupling_cost_integrable hε μ).smul_measure (c := ENNReal.ofReal (1-δ)) ENNReal.ofReal_ne_top
  have hi₂ := (product_displacement_integrable gaussianFloorLaw μ gaussianFloorLaw_quadratic_integrable hμ).smul_measure
    (c := ENNReal.ofReal δ) ENNReal.ofReal_ne_top
  rw [regularizationCoupling, integral_add_measure hi₁ hi₂, integral_smul_measure, integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (sub_nonneg.mpr hδ₁), ENNReal.toReal_ofReal hδ, smul_eq_mul]
  have h₁ := mul_le_mul_of_nonneg_left (convolutionCoupling_cost_le hε μ) (sub_nonneg.mpr hδ₁)
  have h₂ := mul_le_mul_of_nonneg_left
    (product_displacement_integral_le gaussianFloorLaw μ gaussianFloorLaw_quadratic_integrable hμ) hδ
  have hε₂ : 0 ≤ δ*ε^2 := mul_nonneg hδ (sq_nonneg ε)
  linarith

end SharpWasserstein.RoughEulerianSmoothing
