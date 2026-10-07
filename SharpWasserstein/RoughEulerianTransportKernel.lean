module

public import SharpWasserstein.Compat
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

@[expose] public section

/-! Narrowly continuous probability curves give genuine measurable Markov kernels.
No measurability of a tangent field is included in this construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace SharpWasserstein.RoughEulerianTransport
variable {α E : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E]

/-- Narrow continuity supplies measurability for every Borel set, using actual
bounded continuous approximations of indicators of closed sets. -/
theorem measurable_measure_of_continuous_probability {μ : α → ProbabilityMeasure E}
    (hμ : Continuous μ) : Measurable (fun t => (μ t : Measure E)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_isClosed (α := E))) isPiSystem_isClosed
  intro s hs
  apply measurable_of_tendsto_metrizable
    (fun n => ((ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction
      (hs.apprSeq n)).comp hμ).measurable)
  apply tendsto_pi_nhds.2
  intro t
  exact HasOuterApproxClosed.tendsto_lintegral_apprSeq hs (μ t : Measure E)

/-- The actual probability curve, as a Markov kernel into physical space. -/
def probabilityCurveKernel (μ : α → ProbabilityMeasure E) (hμ : Continuous μ) : Kernel α E where
  toFun t := μ t
  measurable' := measurable_measure_of_continuous_probability hμ

@[simp] theorem probabilityCurveKernel_apply (μ : α → ProbabilityMeasure E) (hμ : Continuous μ)
    (t : α) : probabilityCurveKernel μ hμ t = (μ t : Measure E) := rfl

instance probabilityCurveKernel_markov (μ : α → ProbabilityMeasure E) (hμ : Continuous μ) :
    IsMarkovKernel (probabilityCurveKernel μ hμ) := ⟨fun t => by
  change IsProbabilityMeasure (μ t : Measure E)
  infer_instance⟩

end SharpWasserstein.RoughEulerianTransport
