import SharpWasserstein.FlowSemigroupDerivativePairing
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! Joint time/initial/path measurability of the actual Jacobian, and joint
time/initial measurability of the differentiated actual flow expectation.
The finite-dimensional parameter theorem applies to the proved continuous
flow; no derivative continuity in time is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ContDiff Topology
namespace SharpWasserstein.PropagatedSourceEquation
open FlowSemigroupDerivative FlowInitialDerivative NoiseAverage
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {b : E → E} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)
  {T : ℝ} [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)] (hT : 0 ≤ T)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)] in
/-- The actual flow evaluated at clamped time, jointly continuous in all parameters. -/
theorem clampedFlow_continuous :
    Continuous (fun q : (C(Icc 0 T,E) × ℝ) × E =>
      BoundedFlow.flow hv hb hl hT q.2 q.1.1 (projIcc 0 T hT q.1.2)) := by
  have hm : Continuous (fun q : (C(Icc 0 T,E) × ℝ) × E =>
      ((q.2,q.1.1),projIcc 0 T hT q.1.2)) :=
    (continuous_snd.prodMk (continuous_fst.comp continuous_fst)).prodMk
      (continuous_projIcc.comp (continuous_snd.comp continuous_fst))
  exact (BoundedFlow.flow_joint_continuous hv hb hl hT).comp hm

/-- Joint measurability in initial point, continuous path, and time of the
actual initial Jacobian. At clamped time it is everywhere a genuine derivative. -/
theorem clampedJacobian_measurable :
    Measurable (fun q : (C(Icc 0 T,E) × ℝ) × E =>
      fderiv ℝ (fun x => BoundedFlow.flow hv hb hl hT x q.1.1
        (projIcc 0 T hT q.1.2)) q.2) :=
  measurable_fderiv_with_param ℝ
    (f := fun q : C(Icc 0 T,E) × ℝ => fun x => BoundedFlow.flow hv hb hl hT x q.1
      (projIcc 0 T hT q.2)) (clampedFlow_continuous hv hb hl hT)

variable (ξ : Measure C(Icc 0 T,E)) [IsProbabilityMeasure ξ]

/-- Clamping time only extends the existing fixed-horizon expectation. -/
def clampedExpectation (F : E → ℝ) (r : ℝ) (x : E) : ℝ :=
  expectation hv hb hl hT ξ (t := projIcc 0 T hT r) F x

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [BorelSpace C(Icc 0 T,E)] [IsProbabilityMeasure ξ] in
theorem clampedExpectation_of_mem (F : E → ℝ) {r : ℝ} (hr : r ∈ Icc 0 T) :
    clampedExpectation hv hb hl hT ξ F r = expectation hv hb hl hT ξ (t := r) F := by
  funext x
  change expectation hv hb hl hT ξ (t := projIcc 0 T hT r) F x = _
  rw [projIcc_of_mem _ hr]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Bounded continuous observables give a genuinely jointly continuous time
and initial-value expectation. -/
theorem clampedExpectation_continuous {F : E → ℝ} (hF : Continuous F)
    {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) :
    Continuous (fun q : ℝ × E => clampedExpectation hv hb hl hT ξ F q.1 q.2) := by
  apply continuous_of_dominated (bound := fun _ => C)
  · intro q
    exact (integrable_observable hv hb hl hT ξ (projIcc 0 T hT q.1).property hF hC q.2).1
  · intro q
    exact Eventually.of_forall (fun _ => hC _)
  · exact integrable_const _
  · filter_upwards [] with w
    exact hF.comp ((clampedFlow_continuous hv hb hl hT).comp
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd))

/-- The derivative of the actual expectation is jointly measurable in time
and the initial point, with no presumed semigroup regularity. -/
theorem clampedExpectation_fderiv_measurable {F : E → ℝ} (hF : Continuous F)
    {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) :
    Measurable (fun q : ℝ × E =>
      fderiv ℝ (clampedExpectation hv hb hl hT ξ F q.1) q.2) :=
  measurable_fderiv_with_param ℝ (clampedExpectation_continuous hv hb hl hT ξ hF hC)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The true derivative has a uniform finite-horizon bound. -/
theorem clampedExpectation_fderiv_norm_le
    (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (r : ℝ) (x : E) :
    ‖fderiv ℝ (clampedExpectation hv hb hl hT ξ F r) x‖ ≤ (L:ℝ)*Real.exp ((K:ℝ)*T) := by
  apply (norm_fderiv_expectation_le hv hb hl hT ξ (projIcc 0 T hT r).property
    hbs hB hF hC hL x).trans
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (projIcc 0 T hT r).property.2 K.coe_nonneg)) L.coe_nonneg

end SharpWasserstein.PropagatedSourceEquation
