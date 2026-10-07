module

public import SharpWasserstein.Compat
public import SharpWasserstein.WeakTestContinuity
public import SharpWasserstein.ConfigurationEuclidean
public import SharpWasserstein.MarginalMoments

@[expose] public section

/-! Narrow continuity of every actual `Dynamics.WeakEvolution` is derived from
its compact smooth test continuity and finite-horizon second moment bound.
Negative times are extended constantly by the initial law. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal
namespace SharpWasserstein
open WeightedTangent
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]

theorem integrable_norm_sq_euclideanLaw {P : Measure (Configuration d N)} (hP : HasSecondMoment P) :
    Integrable (fun x : Point (N*d) ↦ ‖x‖^2) (euclideanLaw P) := by
  apply (integrable_map_measure (by fun_prop) (configurationEuclidean d N).continuous.measurable.aemeasurable).mpr
  change Integrable (fun x ↦ ‖configurationEuclidean d N x‖^2) P
  simpa only [Function.comp_apply, configurationEuclidean_norm_sq, productCost, sub_zero, Pi.zero_apply]
    using (hasSecondMoment_iff_integrable P).mp hP

theorem integral_norm_sq_euclideanLaw (P : Measure (Configuration d N)) :
    (∫ x : Point (N*d), ‖x‖^2 ∂euclideanLaw P) = ∫ x, productCost x 0 ∂P := by
  rw [integral_euclideanLaw]
  simp only [configurationEuclidean_norm_sq, productCost, Pi.zero_apply, sub_zero]

namespace WeakEvolution
variable {v : ℝ → Configuration d N → Configuration d N}
  {P : ℝ → Measure (Configuration d N)} (h : WeakEvolution v P)

/-- The probability-valued weak solution, extended by its initial value to negative times. -/
def probabilityCurve (t : ℝ) : ProbabilityMeasure (Configuration d N) :=
  ⟨P (max 0 t), h.probability _ (le_max_left _ _)⟩

/-- Its exact Euclidean coordinate presentation. -/
def euclideanProbabilityCurve (t : ℝ) : ProbabilityMeasure (Point (N*d)) := by
  letI := h.probability (max 0 t) (le_max_left _ _)
  exact ⟨euclideanLaw (P (max 0 t)), inferInstance⟩

/-- The finite-horizon restriction, constantly extended beyond the horizon. -/
def clippedEuclideanCurve (U : ℝ) (hU : 0 ≤ U) (t : ℝ) : ProbabilityMeasure (Point (N*d)) := by
  letI := h.probability (min (max 0 t) U) (le_min (le_max_left _ _) hU)
  exact ⟨euclideanLaw (P (min (max 0 t) U)), inferInstance⟩

theorem continuous_clippedEuclideanCurve {U : ℝ} (hU : 0 < U) :
    Continuous (clippedEuclideanCurve h U hU.le) := by
  obtain ⟨C, hCfin, hC⟩ := h.momentBound U hU
  apply WeakTestContinuity.continuous_probabilityMeasure_of_uniformMoment
    (C := C.toReal) (hμ := fun t ↦ integrable_norm_sq_euclideanLaw
      (h.secondMoment _ (le_min (le_max_left _ _) hU.le)))
  · intro t
    change (∫ x, ‖x‖^2 ∂euclideanLaw (P (min (max 0 t) U))) ≤ _
    rw [integral_norm_sq_euclideanLaw,
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x ↦ productCost_nonneg x 0)
        ((measurable_productCost.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)]
    exact ENNReal.toReal_mono hCfin.ne (hC _ ⟨le_min (le_max_left _ _) hU.le, min_le_right _ _⟩)
  · intro φ
    change Continuous (fun t ↦ ∫ x, (φ : Point (N*d) → ℝ) x ∂euclideanLaw (P (min (max 0 t) U)))
    simp_rw [integral_euclideanLaw]
    let ψ : ConfigurationTest d N := (configurationTestEuclidean d N).symm φ
    have hp := continuousOn_iff_continuous_restrict.mp (h.testContinuous ψ.val ψ.property)
    have hc : Continuous (fun t : ℝ ↦ (⟨min (max 0 t) U, le_min (le_max_left _ _) hU.le⟩ : Ici (0 : ℝ))) :=
      (continuous_const.max continuous_id |>.min continuous_const).subtype_mk _
    exact hp.comp hc

/-- The actual Euclidean probability curve is narrowly continuous on the full
nonnegative time axis, with a constant extension before time zero. -/
theorem continuous_euclideanProbabilityCurve : Continuous (euclideanProbabilityCurve h) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let U := max 0 t + 1
  have hU : 0 < U := by dsimp [U]; linarith [le_max_left (0 : ℝ) t]
  have hc := (continuous_clippedEuclideanCurve h hU).continuousAt (x := t)
  apply hc.congr_of_eventuallyEq
  have he : ∀ᶠ s in 𝓝 t, max 0 s < U :=
    (continuous_const.max continuous_id).continuousAt.eventually_lt_const (by dsimp [U]; linarith)
  filter_upwards [he] with s hs
  apply Subtype.ext
  change euclideanLaw (P (max 0 s)) = euclideanLaw (P (min (max 0 s) U))
  rw [min_eq_left hs.le]

/-- Returning through the explicit coordinate homeomorphism gives narrow
continuity of the original configuration-valued weak solution itself. -/
theorem continuous_probabilityCurve : Continuous (probabilityCurve h) := by
  have hc := (ProbabilityMeasure.continuous_map (configurationEuclidean d N).symm.continuous).comp
    (continuous_euclideanProbabilityCurve h)
  convert hc using 1
  funext t
  apply Subtype.ext
  change P (max 0 t) = (euclideanLaw (P (max 0 t))).map (configurationEuclidean d N).symm
  unfold euclideanLaw
  rw [Measure.map_map (configurationEuclidean d N).symm.continuous.measurable
    (configurationEuclidean d N).continuous.measurable]
  simp only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply, Measure.map_id']

end WeakEvolution
end SharpWasserstein
