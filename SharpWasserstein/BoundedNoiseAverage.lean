import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Actual probability averages of translated bounded tests preserve their
bounds, Lipschitz constants and C¹ regularity, with a proved Fréchet derivative
under the integral. This applies in particular to genuine Gaussian Euler noise. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace SharpWasserstein.NoiseAverage
variable {Ω E F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Ω → E)

def average (f : E → F) (x : E) : F := ∫ ω, f (x + ξ ω) ∂μ

omit [NormedSpace ℝ F] in
theorem integrable_translate (hξ : StronglyMeasurable ξ) {f : E → F} (hf : Continuous f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (x : E) : Integrable (fun ω ↦ f (x + ξ ω)) μ :=
  Integrable.of_bound (hf.comp_stronglyMeasurable (stronglyMeasurable_const.add hξ)).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun _ ↦ hC _)

theorem norm_average_le {f : E → F} {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (x : E) :
    ‖average μ ξ f x‖ ≤ C := by
  simpa only [average, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω ↦ f (x + ξ ω))
      (Filter.Eventually.of_forall fun _ ↦ hC _)

theorem continuous_average (hξ : StronglyMeasurable ξ) {f : E → F} (hf : Continuous f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) : Continuous (average μ ξ f) := by
  apply continuous_of_dominated (bound := fun _ ↦ C)
  · intro x
    exact (hf.comp_stronglyMeasurable (stronglyMeasurable_const.add hξ)).aestronglyMeasurable
  · exact fun x ↦ Filter.Eventually.of_forall fun _ ↦ hC _
  · exact integrable_const C
  · exact Filter.Eventually.of_forall fun ω ↦ hf.comp (continuous_id.add continuous_const)

theorem lipschitz_average (hξ : StronglyMeasurable ξ) {f : E → F} {L : ℝ≥0}
    (hf : LipschitzWith L f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    LipschitzWith L (average μ ξ f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, average, average, ← integral_sub
    (integrable_translate μ ξ hξ hf.continuous hC x) (integrable_translate μ ξ hξ hf.continuous hC y)]
  have hpoint (ω : Ω) : ‖f (x + ξ ω) - f (y + ξ ω)‖ ≤ (L : ℝ) * dist x y := by
    simpa only [add_sub_add_right_eq_sub, dist_eq_norm] using hf.norm_sub_le (x + ξ ω) (y + ξ ω)
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω ↦ f (x + ξ ω) - f (y + ξ ω))
      (Filter.Eventually.of_forall hpoint)

variable [NormedSpace ℝ E]

/-- The actual Fréchet differential passes through the genuine probability integral. -/
theorem hasFDerivAt_average (hξ : StronglyMeasurable ξ) {f : E → F}
    (hf : ContDiff ℝ 1 f) {L : ℝ≥0} (hL : LipschitzWith L f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (x : E) :
    HasFDerivAt (average μ ξ f) (∫ ω, fderiv ℝ f (x + ξ ω) ∂μ) x := by
  have hdf : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hlip : ∀ᵐ ω ∂μ, LipschitzOnWith (Real.nnabs (L : ℝ)) (fun y ↦ f (y + ξ ω)) univ := by
    filter_upwards [] with ω
    simpa only [Real.nnabs_coe, mul_one, Function.comp_def] using (hL.comp (isometry_add_right (ξ ω)).lipschitz).lipschitzOnWith
  have hdiff : ∀ᵐ ω ∂μ, HasFDerivAt (fun y ↦ f (y + ξ ω)) (fderiv ℝ f (x + ξ ω)) x := by
    filter_upwards [] with ω
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using ((hf.differentiable (by norm_num)) (x + ξ ω)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).add_const (ξ ω))
  exact (hasFDerivAt_integral_of_dominated_loc_of_lip (μ := μ)
    (F := fun y ω ↦ f (y + ξ ω)) (F' := fun ω ↦ fderiv ℝ f (x + ξ ω))
    (bound := fun _ ↦ (L : ℝ)) (s := univ) (by simp)
    (Filter.Eventually.of_forall fun y ↦
      (hf.continuous.comp_stronglyMeasurable (stronglyMeasurable_const.add hξ)).aestronglyMeasurable)
    (integrable_translate μ ξ hξ hf.continuous hC x)
    (hdf.comp_stronglyMeasurable (stronglyMeasurable_const.add hξ)).aestronglyMeasurable
    hlip (integrable_const _) hdiff).2

/-- C¹ regularity is preserved, with continuity of the actual derivative integral. -/
theorem contDiff_one_average (hξ : StronglyMeasurable ξ) {f : E → F}
    (hf : ContDiff ℝ 1 f) {L : ℝ≥0} (hL : LipschitzWith L f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) : ContDiff ℝ 1 (average μ ξ f) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun x ↦ ∫ ω, fderiv ℝ f (x + ξ ω) ∂μ, ?_, hasFDerivAt_average μ ξ hξ hf hL hC⟩
  exact continuous_average μ ξ hξ (hf.continuous_fderiv (by norm_num))
    (fun _ ↦ norm_fderiv_le_of_lipschitz ℝ hL)

end SharpWasserstein.NoiseAverage
