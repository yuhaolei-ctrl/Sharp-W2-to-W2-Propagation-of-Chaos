module

public import SharpWasserstein.Compat
public import SharpWasserstein.PropagatedSourceEquationIntegration

@[expose] public section

/-! Quantitative estimates for the actual propagated source action on bounded
smooth tests. The action is the differentiated genuine flow expectation;
its integral equation is deduced from the primal flow equation. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff Topology Interval
namespace SharpWasserstein.PeriodicSourceConvolution
open FlowSemigroupDerivative PropagatedSourceEquation NoiseAverage
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {b : E → E} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ,∀ x,‖b x‖ ≤ M) (hl : ∀ _ : ℝ,LipschitzWith K b)
  {T : ℝ} [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)] (hT : 0 ≤ T)
  (ξ : Measure C(Icc 0 T,E)) [IsProbabilityMeasure ξ]
  (μ : Measure E) [IsFiniteMeasure μ]

/-- The actual propagated distribution, evaluated on a bounded smooth test.
Clamping extends the fixed-horizon construction outside its physical interval. -/
def action (u : E → E) (F : E → ℝ) (t : ℝ) : ℝ :=
  ∫ x,fderiv ℝ (clampedExpectation hv hb hl hT ξ F t) x (u x) ∂μ

omit [IsFiniteMeasure μ] [FiniteDimensional ℝ E] [BorelSpace E]
  [BorelSpace C(Icc 0 T,E)] [IsProbabilityMeasure ξ] in
theorem action_of_mem (u : E → E) (F : E → ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    action hv hb hl hT ξ μ u F t =
      ∫ x,fderiv ℝ (expectation hv hb hl hT ξ (t := t) F) x (u x) ∂μ := by
  unfold action
  rw [clampedExpectation_of_mem hv hb hl hT ξ F ht]

variable (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
include hbs hB

/-- The action is the literal integral of the pushed Jacobian vector against
the test differential, including for noncompact bounded smooth tests. -/
theorem action_eq_randomFlux
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x,‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x,‖fderiv ℝ F x‖ ≤ L)
    {u : E → E} (hu : MemLp u 2 μ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    action hv hb hl hT ξ μ u F t =
      ∫ q : E × C(Icc 0 T,E),fderiv ℝ F (BoundedFlow.flow hv hb hl hT q.1 q.2 t)
        (fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y q.2 t) q.1 (u q.1)) ∂μ.prod ξ := by
  rw [action_of_mem hv hb hl hT ξ μ u F ht]
  exact integral_fderiv_expectation_eq hv hb hl hT ξ ht hbs hB μ hF hC hL hu

/-- The source action has a proved bound uniform over the whole time horizon. -/
theorem norm_action_le
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x,‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x,‖fderiv ℝ F x‖ ≤ L)
    {u : E → E} (hu : MemLp u 2 μ) (t : ℝ) :
    ‖action hv hb hl hT ξ μ u F t‖ ≤ (L:ℝ)*Real.exp ((K:ℝ)*T)*(∫ x,‖u x‖ ∂μ) := by
  have hi := integrable_initial_pairing hv hb hl hT ξ hbs hB μ hF hC hL hu t
  calc
    _ ≤ ∫ x,‖fderiv ℝ (clampedExpectation hv hb hl hT ξ F t) x (u x)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x,(L:ℝ)*Real.exp ((K:ℝ)*T)*‖u x‖ ∂μ := by
      apply integral_mono hi.norm ((hu.integrable (by norm_num)).norm.const_mul _)
      intro x
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right
          (clampedExpectation_fderiv_norm_le hv hb hl hT ξ hbs hB hF hC hL t x) (norm_nonneg _))
    _ = _ := integral_const_mul _ _

/-- The underlying scalar primal equation implies the source action's actual
integral equation. No source equation is postulated. -/
theorem action_interval_eq
    {F G : E → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x,‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x,‖fderiv ℝ F x‖ ≤ L)
    (hG : ContDiff ℝ 1 G) {D : ℝ} (hD : ∀ x,‖G x‖ ≤ D)
    {L' : ℝ≥0} (hL' : ∀ x,‖fderiv ℝ G x‖ ≤ L')
    {u : E → E} (hu : MemLp u 2 μ) {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T)
    (heq : ∀ x,expectation hv hb hl hT ξ (t := t) F x-
      expectation hv hb hl hT ξ (t := s) F x =
        ∫ r in s..t,clampedExpectation hv hb hl hT ξ G r x) :
    IntervalIntegrable (action hv hb hl hT ξ μ u G) volume s t ∧
      action hv hb hl hT ξ μ u F t-action hv hb hl hT ξ μ u F s =
        ∫ r in s..t,action hv hb hl hT ξ μ u G r := by
  refine ⟨intervalIntegrable_initial_pairing hv hb hl hT ξ hbs hB μ hG hD hL' hu s t,?_⟩
  rw [action_of_mem hv hb hl hT ξ μ u F ht,action_of_mem hv hb hl hT ξ μ u F hs]
  exact integrated_source_identity hv hb hl hT ξ hbs hB μ hF hC hL hG hD hL' hs ht heq hu

/-- A uniform time Lipschitz estimate follows from the actual integral equation
and the initial vector's integrability, without a presumed temporal modulus. -/
theorem action_sub_norm_le
    {F G : E → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x,‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x,‖fderiv ℝ F x‖ ≤ L)
    (hG : ContDiff ℝ 1 G) {D : ℝ} (hD : ∀ x,‖G x‖ ≤ D)
    {L' : ℝ≥0} (hL' : ∀ x,‖fderiv ℝ G x‖ ≤ L')
    {u : E → E} (hu : MemLp u 2 μ) {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T)
    (heq : ∀ x,expectation hv hb hl hT ξ (t := t) F x-
      expectation hv hb hl hT ξ (t := s) F x =
        ∫ r in s..t,clampedExpectation hv hb hl hT ξ G r x) :
    ‖action hv hb hl hT ξ μ u F t-action hv hb hl hT ξ μ u F s‖ ≤
      |t-s| *((L':ℝ)*Real.exp ((K:ℝ)*T)*(∫ x,‖u x‖ ∂μ)) := by
  rw [(action_interval_eq hv hb hl hT ξ μ hbs hB hF hC hL hG hD hL' hu hs ht heq).2]
  simpa only [mul_comm] using intervalIntegral.norm_integral_le_of_norm_le_const
    (fun r _ => norm_action_le hv hb hl hT ξ μ hbs hB hG hD hL' hu r)

end SharpWasserstein.PeriodicSourceConvolution
