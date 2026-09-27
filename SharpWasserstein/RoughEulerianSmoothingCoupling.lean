import SharpWasserstein.RoughEulerianSmoothingLaw
import SharpWasserstein.Transport

/-! The compact convolution law is identified with an actual independent
additive-noise law. Its explicit coupling with the original measure has
quadratic Euclidean displacement at most the squared mollifier radius. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff NNReal
namespace SharpWasserstein.RoughEulerianSmoothing
open WeightedTangent
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

def mollifierLaw (ε : ℝ) (hε : 0 < ε) : Measure (Point d) :=
  volume.withDensity (fun x => ENNReal.ofReal (mollifier ε hε x))

instance mollifierLaw_probability {ε : ℝ} (hε : 0 < ε) :
    IsProbabilityMeasure (mollifierLaw (d := d) ε hε) := by
  apply isProbabilityMeasure_iff.mpr
  rw [mollifierLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (mollifier_integrable hε)
      (Eventually.of_forall (mollifier_nonneg hε)), mollifier_integral hε, ENNReal.ofReal_one]

def convolvedLaw (ε : ℝ) (hε : 0 < ε) (μ : Measure (Point d)) : Measure (Point d) :=
  volume.withDensity (fun x => ENNReal.ofReal (density ε hε μ x))

instance convolvedLaw_probability {ε : ℝ} (hε : 0 < ε) (μ : Measure (Point d)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (convolvedLaw ε hε μ) := by
  apply isProbabilityMeasure_iff.mpr
  rw [convolvedLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (density_integrable hε μ)
      (Eventually.of_forall (density_nonneg hε μ)), density_integral hε μ, ENNReal.ofReal_one]

theorem mollifierLaw_quadratic_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : Point d => ‖x‖^2) (mollifierLaw ε hε) := by
  apply (integrable_withDensity_iff_integrable_smul'
    (mollifier_smooth hε).continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  simp only [ENNReal.toReal_ofReal (mollifier_nonneg hε _), smul_eq_mul]
  exact ((mollifier_smooth hε).continuous.mul (continuous_norm.pow 2)).integrable_of_hasCompactSupport
    (mollifier_compact hε).mul_right

theorem mollifierLaw_quadratic_le {ε : ℝ} (hε : 0 < ε) :
    (∫ x : Point d, ‖x‖^2 ∂mollifierLaw ε hε) ≤ ε^2 := by
  rw [mollifierLaw, integral_withDensity_eq_integral_toReal_smul
    (mollifier_smooth hε).continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (mollifier_nonneg hε _), smul_eq_mul]
  have hi : Integrable (fun x : Point d => mollifier ε hε x * ‖x‖^2) :=
    ((mollifier_smooth hε).continuous.mul (continuous_norm.pow 2)).integrable_of_hasCompactSupport
      (mollifier_compact hε).mul_right
  calc
    _ ≤ ∫ x : Point d, mollifier ε hε x * ε^2 := by
      apply integral_mono hi ((mollifier_integrable hε).mul_const (ε^2))
      intro x
      change mollifier ε hε x * ‖x‖^2 ≤ mollifier ε hε x * ε^2
      by_cases hx : ‖x‖ ≤ ε
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx 2) (mollifier_nonneg hε x)
      · rw [mollifier_eq_zero hε (le_of_lt (not_le.mp hx)), zero_mul, zero_mul]
    _ = ε^2 := by rw [integral_mul_const, mollifier_integral hε, one_mul]

theorem convolvedLaw_eq_map_add {ε : ℝ} (hε : 0 < ε) (μ : Measure (Point d)) [IsProbabilityMeasure μ] :
    convolvedLaw ε hε μ = (μ.prod (mollifierLaw ε hε)).map (fun z => z.1+z.2) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  have hadd : Measurable (fun z : Point d × Point d => z.1+z.2) := measurable_fst.add measurable_snd
  rw [convolvedLaw, lintegral_withDensity_eq_lintegral_mul volume
    (density_smooth hε μ).continuous.measurable.ennreal_ofReal hφ,
    lintegral_map hφ hadd, lintegral_prod _ (by fun_prop)]
  have hd (x : Point d) : ENNReal.ofReal (density ε hε μ x) =
      ∫⁻ y, ENNReal.ofReal (mollifier ε hε (x-y)) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal (mollifier_translate_integrable hε μ x)
      (Eventually.of_forall fun y => mollifier_nonneg hε (x-y))
  simp only [Pi.mul_apply]
  simp_rw [hd]
  have hp (x : Point d) : (∫⁻ y, ENNReal.ofReal (mollifier ε hε (x-y)) ∂μ) * φ x =
      ∫⁻ y, ENNReal.ofReal (mollifier ε hε (x-y)) * φ x ∂μ :=
    (lintegral_mul_const'' (φ x) (((mollifier_smooth hε).continuous.measurable.comp
      (measurable_const.sub measurable_id)).ennreal_ofReal.aemeasurable)).symm
  simp_rw [hp]
  rw [lintegral_lintegral_swap ((((mollifier_smooth hε).continuous.measurable.comp
    (measurable_fst.sub measurable_snd)).ennreal_ofReal.mul (hφ.comp measurable_fst)).aemeasurable)]
  apply lintegral_congr
  intro y
  rw [mollifierLaw, lintegral_withDensity_eq_lintegral_mul volume
    (g := fun z => φ (y+z)) (mollifier_smooth hε).continuous.measurable.ennreal_ofReal
    (hφ.comp (measurable_const.add measurable_id))]
  have hh := lintegral_add_left_eq_self (μ := volume)
    (fun x : Point d => ENNReal.ofReal (mollifier ε hε (x-y))*φ x) y
  simp only [add_sub_cancel_left] at hh
  simp only [Pi.mul_apply]
  exact hh.symm

def convolutionCoupling (ε : ℝ) (hε : 0 < ε) (μ : Measure (Point d)) : Measure (Point d × Point d) :=
  (μ.prod (mollifierLaw ε hε)).map (fun z => (z.1+z.2,z.1))

theorem convolutionCoupling_isCoupling {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ] :
    IsCoupling (convolvedLaw ε hε μ) μ (convolutionCoupling ε hε μ) := by
  have hm : Measurable (fun z : Point d × Point d => (z.1+z.2,z.1)) :=
    (measurable_fst.add measurable_snd).prodMk measurable_fst
  refine ⟨Measure.isProbabilityMeasure_map hm.aemeasurable, ?_, ?_⟩
  · rw [convolutionCoupling, Measure.map_map measurable_fst hm, convolvedLaw_eq_map_add hε μ]
    rfl
  · rw [convolutionCoupling, Measure.map_map measurable_snd hm]
    change (μ.prod (mollifierLaw ε hε)).map Prod.fst = μ
    simp only [Measure.map_fst_prod, measure_univ, one_smul]

theorem convolutionCoupling_cost_integrable {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ] :
    Integrable (fun z : Point d × Point d => ‖z.1-z.2‖^2) (convolutionCoupling ε hε μ) := by
  have hm : Measurable (fun z : Point d × Point d => (z.1+z.2,z.1)) :=
    (measurable_fst.add measurable_snd).prodMk measurable_fst
  have hc : Continuous (fun z : Point d × Point d => ‖z.1-z.2‖^2) :=
    (continuous_fst.sub continuous_snd).norm.pow 2
  apply (integrable_map_measure hc.aestronglyMeasurable
    hm.aemeasurable).mpr
  simp only [Function.comp_def, add_sub_cancel_left]
  exact (mollifierLaw_quadratic_integrable (d := d) hε).comp_snd μ

/-- The coupling has actual finite Euclidean cost at most ε², with no
regularity or moment assumption on the original probability law. -/
theorem convolutionCoupling_cost_le {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ] :
    (∫ z : Point d × Point d, ‖z.1-z.2‖^2 ∂convolutionCoupling ε hε μ) ≤ ε^2 := by
  have hm : Measurable (fun z : Point d × Point d => (z.1+z.2,z.1)) :=
    (measurable_fst.add measurable_snd).prodMk measurable_fst
  have hc : Continuous (fun z : Point d × Point d => ‖z.1-z.2‖^2) :=
    (continuous_fst.sub continuous_snd).norm.pow 2
  rw [convolutionCoupling, integral_map hm.aemeasurable hc.aestronglyMeasurable]
  simp only [add_sub_cancel_left]
  rw [integral_prod _ ((mollifierLaw_quadratic_integrable (d := d) hε).comp_snd μ)]
  simpa only [integral_const, probReal_univ, one_smul] using mollifierLaw_quadratic_le (d := d) hε

end SharpWasserstein.RoughEulerianSmoothing
