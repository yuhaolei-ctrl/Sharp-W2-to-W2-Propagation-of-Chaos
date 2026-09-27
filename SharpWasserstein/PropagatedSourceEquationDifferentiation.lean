import SharpWasserstein.PropagatedSourceEquationMeasurable

/-! Actual spatial differentiation under the finite time integral of the
constructed probability expectation. The primal weak identity can therefore
be differentiated without postulating its source equation. -/
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

include hbs hB

/-- Spatial differentiation commutes with the actual finite time integral.
Both the operator integral's integrability and its derivative identity are proved. -/
theorem hasFDerivAt_timeIntegral
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (s t : ℝ) (x : E) :
    IntervalIntegrable (fun r => fderiv ℝ (clampedExpectation hv hb hl hT ξ F r) x) volume s t ∧
      HasFDerivAt (fun y => ∫ r in s..t,clampedExpectation hv hb hl hT ξ F r y)
        (∫ r in s..t,fderiv ℝ (clampedExpectation hv hb hl hT ξ F r) x) x := by
  have hcont := clampedExpectation_continuous hv hb hl hT ξ hF.continuous hC
  have hdiff (r : ℝ) (y : E) :
      HasFDerivAt (clampedExpectation hv hb hl hT ξ F r)
        (fderiv ℝ (clampedExpectation hv hb hl hT ξ F r) y) y :=
    (expectation_contDiff_one hv hb hl hT ξ (projIcc 0 T hT r).property hbs hB hF hC hL).differentiable (by norm_num) y |>.hasFDerivAt
  have hLip (r : ℝ) : LipschitzWith (NNReal.mk ((L:ℝ)*Real.exp ((K:ℝ)*T)) (by positivity))
      (clampedExpectation hv hb hl hT ξ F r) :=
    lipschitzWith_of_nnnorm_fderiv_le (fun y => (hdiff r y).differentiableAt)
      (clampedExpectation_fderiv_norm_le hv hb hl hT ξ hbs hB hF hC hL r)
  apply hasFDerivAt_integral_of_dominated_loc_of_lip_interval (μ := volume)
    (F := fun y r => clampedExpectation hv hb hl hT ξ F r y)
    (bound := fun _ => (L:ℝ)*Real.exp ((K:ℝ)*T)) (s := univ) (by simp)
  · exact Eventually.of_forall (fun y =>
      (hcont.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
  · exact (hcont.comp (continuous_id.prodMk continuous_const)).intervalIntegrable s t
  · exact ((clampedExpectation_fderiv_measurable hv hb hl hT ξ hF.continuous hC).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [] with r
    have he : Real.nnabs ((L:ℝ)*Real.exp ((K:ℝ)*T)) =
        NNReal.mk ((L:ℝ)*Real.exp ((K:ℝ)*T)) (by positivity) := by
      apply NNReal.eq
      exact abs_of_nonneg (by positivity)
    rw [he]
    exact (hLip r).lipschitzOnWith
  · exact intervalIntegrable_const
  · exact Eventually.of_forall (fun r => hdiff r x)

/-- Differentiating a proved primal integral identity yields the pointwise
source identity. The hypothesis is the original scalar evolution, not a
postulated equation for the derivative or propagated source. -/
theorem differentiated_primal_identity
    {F G : E → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L)
    (hG : ContDiff ℝ 1 G) {D : ℝ} (hD : ∀ x, ‖G x‖ ≤ D)
    {L' : ℝ≥0} (hL' : ∀ x, ‖fderiv ℝ G x‖ ≤ L')
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T)
    (heq : ∀ x, expectation hv hb hl hT ξ (t := t) F x -
      expectation hv hb hl hT ξ (t := s) F x =
        ∫ r in s..t,clampedExpectation hv hb hl hT ξ G r x) (x u : E) :
    fderiv ℝ (expectation hv hb hl hT ξ (t := t) F) x u -
      fderiv ℝ (expectation hv hb hl hT ξ (t := s) F) x u =
        ∫ r in s..t,fderiv ℝ (clampedExpectation hv hb hl hT ξ G r) x u := by
  have hleft := ((expectation_contDiff_one hv hb hl hT ξ ht hbs hB hF hC hL).differentiable
    (by norm_num) x).hasFDerivAt.sub
      ((expectation_contDiff_one hv hb hl hT ξ hs hbs hB hF hC hL).differentiable (by norm_num) x).hasFDerivAt
  have he : (fun y => expectation hv hb hl hT ξ (t := t) F y -
      expectation hv hb hl hT ξ (t := s) F y) =
        fun y => ∫ r in s..t,clampedExpectation hv hb hl hT ξ G r y := funext heq
  simp only [Pi.sub_def] at hleft
  rw [he] at hleft
  have hright := hasFDerivAt_timeIntegral hv hb hl hT ξ hbs hB hG hD hL' s t x
  have hd := congrArg (fun A : E →L[ℝ] ℝ => A u) (hleft.unique hright.2)
  simpa only [sub_apply,ContinuousLinearMap.intervalIntegral_apply hright.1] using hd

end SharpWasserstein.PropagatedSourceEquation
