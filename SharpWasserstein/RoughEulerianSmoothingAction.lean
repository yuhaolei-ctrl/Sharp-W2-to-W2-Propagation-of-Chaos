import SharpWasserstein.RoughEulerianSmoothingKernel
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Normalization and exact action contraction for the actual compact
convolution with a stationary positive floor. All integrals are Euclidean
Lebesgue integrals; the original law and field may be singular or rough. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff NNReal
namespace SharpWasserstein.RoughEulerianSmoothing
open WeightedTangent
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

theorem mollifier_mul_integrable {ε : ℝ} (hε : 0 < ε) (μ : Measure (Point d))
    {f : Point d → ℝ} (hf : Integrable f μ) (x : Point d) :
    Integrable (fun y => mollifier ε hε (x-y) * f y) μ := by
  obtain ⟨C,_,hC⟩ := (mollifier_allDerivativesBounded (d := d) hε).bounded
  exact hf.bdd_mul ((mollifier_smooth hε).continuous.comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable (Eventually.of_forall fun y => hC _)

/-- The product-space integrability needed for Fubini is proved from the
normalized kernel and the original integrable scalar field. -/
theorem mollifier_mul_joint_integrable {ε : ℝ} (hε : 0 < ε) (μ : Measure (Point d))
    [SFinite μ] {f : Point d → ℝ} (hf : Integrable f μ) :
    Integrable (fun p : Point d × Point d => mollifier ε hε (p.1-p.2) * f p.2)
      (volume.prod μ) := by
  have hm : AEStronglyMeasurable
      (fun p : Point d × Point d => mollifier ε hε (p.1-p.2) * f p.2) (volume.prod μ) :=
    (((mollifier_smooth hε).continuous.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mul
      hf.aestronglyMeasurable.comp_snd
  apply (integrable_prod_iff' hm).mpr
  constructor
  · exact Eventually.of_forall fun y => ((mollifier_integrable hε).comp_sub_right y).mul_const (f y)
  · have he (y : Point d) : (∫ x : Point d, ‖mollifier ε hε (x-y)*f y‖) = ‖f y‖ := by
      simp_rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (mollifier_nonneg hε _)]
      rw [integral_mul_const, integral_sub_right_eq_self, mollifier_integral hε, one_mul]
    simpa only [he] using hf.norm

theorem integral_mollifier_mul {ε : ℝ} (hε : 0 < ε) (μ : Measure (Point d))
    [SFinite μ] {f : Point d → ℝ} (hf : Integrable f μ) :
    (∫ x : Point d, ∫ y, mollifier ε hε (x-y)*f y ∂μ) = ∫ y, f y ∂μ := by
  rw [integral_integral_swap (mollifier_mul_joint_integrable hε μ hf)]
  simp_rw [integral_mul_const, integral_sub_right_eq_self, mollifier_integral hε, one_mul]

theorem density_integrable {ε : ℝ} (hε : 0 < ε) (μ : Measure (Point d)) [IsFiniteMeasure μ] :
    Integrable (density ε hε μ) := by
  have hh := (mollifier_mul_joint_integrable hε μ (integrable_const (1 : ℝ))).integral_prod_left
  simp only [mul_one] at hh
  exact hh

theorem density_integral {ε : ℝ} (hε : 0 < ε) (μ : Measure (Point d)) [IsProbabilityMeasure μ] :
    (∫ x, density ε hε μ x) = 1 := by
  simpa only [mul_one, density, integral_const, probReal_univ, smul_eq_mul, one_mul] using
    integral_mollifier_mul hε μ (integrable_const (1 : ℝ))

/-- Pointwise action contracts even where the original mollified density is
zero. The positive floor contributes mass and zero velocity. -/
theorem convolved_floor_action_le {ε a : ℝ} (hε : 0 < ε) (ha : 0 ≤ a)
    (μ : Measure (Point d)) [IsFiniteMeasure μ]
    {v : Point d → Point d} (hv : Integrable v μ)
    (hv₂ : Integrable (fun y => ‖v y‖^2) μ)
    {g : Point d → ℝ} (hg : ∀ x, 0 < g x) (x : Point d) :
    floorDensity a (density ε hε μ) g x *
        ‖floorVelocity a (density ε hε μ) g (flux ε hε μ v) x‖^2 ≤
      a * ∫ y, mollifier ε hε (x-y)*‖v y‖^2 ∂μ := by
  rw [floorVelocity_action ha (density_nonneg hε μ) hg]
  have hh := weighted_norm_integral_sq_le_add (v := v)
    ((mollifier_translate_integrable hε μ x).const_mul a)
    (by simpa only [mul_assoc] using (mollifier_mul_integrable hε μ hv.norm x).const_mul a)
    (by simpa only [mul_assoc] using (mollifier_mul_integrable hε μ hv₂ x).const_mul a)
    (Eventually.of_forall fun y => mul_nonneg ha (mollifier_nonneg hε (x-y))) (hg x)
  simpa only [mul_assoc, mul_smul, integral_smul, integral_const_mul, density, flux, floorDensity]
    using hh

theorem convolved_floor_action_integrable {ε a : ℝ} (hε : 0 < ε) (ha : 0 ≤ a)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ]
    {v : Point d → Point d} (hv : Integrable v μ)
    (hv₂ : Integrable (fun y => ‖v y‖^2) μ)
    {g : Point d → ℝ} (hg : ∀ x, 0 < g x) (hgc : Continuous g) :
    Integrable (fun x => floorDensity a (density ε hε μ) g x *
        ‖floorVelocity a (density ε hε μ) g (flux ε hε μ v) x‖^2) := by
  have hd : Continuous (floorDensity a (density ε hε μ) g) :=
    (continuous_const.mul (density_smooth hε μ).continuous).add hgc
  have hvel : Continuous (floorVelocity a (density ε hε μ) g (flux ε hε μ v)) :=
    (hd.inv₀ (fun x => (floorDensity_pos ha (density_nonneg hε μ) hg x).ne')).smul
      ((flux_smooth hε μ hv).continuous.const_smul a)
  have hmajor := ((mollifier_mul_joint_integrable hε μ hv₂).integral_prod_left).const_mul a
  apply Integrable.mono' hmajor (hd.mul (hvel.norm.pow 2)).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (floorDensity_pos ha (density_nonneg hε μ) hg x).le (sq_nonneg _))]
    exact convolved_floor_action_le hε ha μ hv hv₂ hg x

/-- The spatially integrated action contracts with the exact factor `a`;
there is no dimension-dependent norm comparison. -/
theorem integral_convolved_floor_action_le {ε a : ℝ} (hε : 0 < ε) (ha : 0 ≤ a)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ]
    {v : Point d → Point d} (hv : Integrable v μ)
    (hv₂ : Integrable (fun y => ‖v y‖^2) μ)
    {g : Point d → ℝ} (hg : ∀ x, 0 < g x) (hgc : Continuous g) :
    (∫ x, floorDensity a (density ε hε μ) g x *
        ‖floorVelocity a (density ε hε μ) g (flux ε hε μ v) x‖^2) ≤
      a * ∫ y, ‖v y‖^2 ∂μ := by
  have hi := convolved_floor_action_integrable hε ha μ hv hv₂ hg hgc
  have hmajor := ((mollifier_mul_joint_integrable hε μ hv₂).integral_prod_left).const_mul a
  calc
    _ ≤ ∫ x, a * ∫ y, mollifier ε hε (x-y)*‖v y‖^2 ∂μ :=
      integral_mono hi hmajor (convolved_floor_action_le hε ha μ hv hv₂ hg)
    _ = _ := by rw [integral_const_mul, integral_mollifier_mul hε μ hv₂]

end SharpWasserstein.RoughEulerianSmoothing
