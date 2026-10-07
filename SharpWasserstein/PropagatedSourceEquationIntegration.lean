module

public import SharpWasserstein.Compat
public import SharpWasserstein.PropagatedSourceEquationDifferentiation

@[expose] public section

/-! Integrating the differentiated primal identity against a genuine L²
initial vector field, with joint measurability and time Fubini proved. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ContDiff Topology Interval
namespace SharpWasserstein.PropagatedSourceEquation
open FlowSemigroupDerivative FlowInitialDerivative NoiseAverage
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {b : E → E} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)
  {T : ℝ} [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)] (hT : 0 ≤ T)
  (ξ : Measure C(Icc 0 T,E)) [IsProbabilityMeasure ξ]
  (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  (μ : Measure E) [IsFiniteMeasure μ]

include hbs hB

theorem integrable_initial_pairing
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) {u : E → E} (hu : MemLp u 2 μ) (r : ℝ) :
    Integrable (fun x => fderiv ℝ (clampedExpectation hv hb hl hT ξ F r) x (u x)) μ := by
  have hm : AEStronglyMeasurable
      (fun x => fderiv ℝ (clampedExpectation hv hb hl hT ξ F r) x) μ :=
    ((clampedExpectation_fderiv_measurable hv hb hl hT ξ hF.continuous hC).comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  apply Integrable.mono' ((hu.integrable (by norm_num)).norm.const_mul ((L:ℝ)*Real.exp ((K:ℝ)*T)))
    ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hm.prodMk hu.aestronglyMeasurable))
  exact Eventually.of_forall (fun x => (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (clampedExpectation_fderiv_norm_le hv hb hl hT ξ hbs hB hF hC hL r x) (norm_nonneg _)))

/-- The genuine differentiated expectation is jointly integrable in time and
initial point under the original L² hypothesis. -/
theorem integrable_time_initial_pairing
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) {u : E → E} (hu : MemLp u 2 μ) (s t : ℝ) :
    Integrable (fun q : ℝ × E => fderiv ℝ (clampedExpectation hv hb hl hT ξ F q.1) q.2 (u q.2))
      ((volume.restrict (uIoc s t)).prod μ) := by
  letI : IsFiniteMeasure (volume.restrict (uIoc s t)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_Ioc_lt_top⟩
  have hup : MemLp (fun q : ℝ × E => u q.2) 2 ((volume.restrict (uIoc s t)).prod μ) :=
    hu.comp_snd (volume.restrict (uIoc s t))
  have hm : AEStronglyMeasurable
      (fun q : ℝ × E => fderiv ℝ (clampedExpectation hv hb hl hT ξ F q.1) q.2)
      ((volume.restrict (uIoc s t)).prod μ) :=
    (clampedExpectation_fderiv_measurable hv hb hl hT ξ hF.continuous hC).aestronglyMeasurable
  apply Integrable.mono' ((hup.integrable (by norm_num)).norm.const_mul ((L:ℝ)*Real.exp ((K:ℝ)*T)))
    ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hm.prodMk hup.aestronglyMeasurable))
  exact Eventually.of_forall (fun q => (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (clampedExpectation_fderiv_norm_le hv hb hl hT ξ hbs hB hF hC hL q.1 q.2) (norm_nonneg _)))

/-- The source action is integrable in time on every bounded interval. -/
theorem intervalIntegrable_initial_pairing
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) {u : E → E} (hu : MemLp u 2 μ) (s t : ℝ) :
    IntervalIntegrable (fun r => ∫ x, fderiv ℝ (clampedExpectation hv hb hl hT ξ F r) x (u x) ∂μ) volume s t := by
  rw [intervalIntegrable_iff]
  exact (integrable_time_initial_pairing hv hb hl hT ξ hbs hB μ hF hC hL hu s t).integral_prod_left

/-- The proved primal identity yields the integrated equation for the actual
source action. The Brownian instantiation supplies the primal identity. -/
theorem integrated_source_identity
    {F G : E → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L)
    (hG : ContDiff ℝ 1 G) {D : ℝ} (hD : ∀ x, ‖G x‖ ≤ D)
    {L' : ℝ≥0} (hL' : ∀ x, ‖fderiv ℝ G x‖ ≤ L')
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T)
    (heq : ∀ x, expectation hv hb hl hT ξ (t := t) F x -
      expectation hv hb hl hT ξ (t := s) F x =
        ∫ r in s..t,clampedExpectation hv hb hl hT ξ G r x)
    {u : E → E} (hu : MemLp u 2 μ) :
    (∫ x, fderiv ℝ (expectation hv hb hl hT ξ (t := t) F) x (u x) ∂μ) -
      (∫ x, fderiv ℝ (expectation hv hb hl hT ξ (t := s) F) x (u x) ∂μ) =
        ∫ r in s..t, ∫ x, fderiv ℝ (clampedExpectation hv hb hl hT ξ G r) x (u x) ∂μ := by
  have hi (r : ℝ) (hr : r ∈ Icc 0 T) : Integrable
      (fun x => fderiv ℝ (expectation hv hb hl hT ξ (t := r) F) x (u x)) μ := by
    simpa only [clampedExpectation_of_mem hv hb hl hT ξ F hr] using
      integrable_initial_pairing hv hb hl hT ξ hbs hB μ hF hC hL hu r
  rw [← integral_sub (hi t ht) (hi s hs)]
  calc
    _ = ∫ x, (∫ r in s..t, fderiv ℝ (clampedExpectation hv hb hl hT ξ G r) x (u x)) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => differentiated_primal_identity hv hb hl hT ξ hbs hB
        hF hC hL hG hD hL' hs ht heq x (u x))
    _ = _ := (intervalIntegral_integral_swap
      (integrable_time_initial_pairing hv hb hl hT ξ hbs hB μ hG hD hL' hu s t)).symm

end SharpWasserstein.PropagatedSourceEquation
