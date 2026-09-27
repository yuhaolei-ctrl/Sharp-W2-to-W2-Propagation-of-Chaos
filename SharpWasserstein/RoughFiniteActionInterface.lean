import SharpWasserstein.RoughEulerianTransportContinuity
import SharpWasserstein.RoughCommonLabelLift
import SharpWasserstein.ConfigurationEuclidean
import SharpWasserstein.TransportTriangle
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! Exact constant-action interface needed by the final manuscript assembly.
This is a proposition, not an assertion of a rough transport theorem. Its
inhabitant must be supplied by the time/space regularization construction. -/
noncomputable section
open Set MeasureTheory
namespace SharpWasserstein.RoughEulerianTransport
open WeightedTangent

/-- The actual finite-action estimate for a narrowly continuous compact-test
curve with a uniform tangent-energy bound and a genuine common-label
mean-square continuous realization. Every law and cost is literal. -/
def UniformFiniteActionTransport : Prop :=
  ∀ d k : ℕ,∀ (μ : ℝ → ProbabilityMeasure (Point (k*d)))
    (σ : ℝ → Test (k*d) →ₗ[ℝ] ℝ) (T E : ℝ),
    0 ≤ T → 0 ≤ E → CompactDistributionContinuity μ σ T →
    Nonempty (CommonLabelLift d k μ) →
    (∀ t ∈ Icc 0 T,Integrable (fun x : Point (k*d) => ‖x‖^2) (μ t : Measure _)) →
    (∀ t ∈ Icc 0 T,∀ φ : Test (k*d),testObjective (μ t : Measure _) (σ t) φ ≤ E) →
    wassersteinSq ((μ 0 : Measure _).map (configurationEuclidean d k).symm)
      ((μ T : Measure _).map (configurationEuclidean d k).symm) ≤ ENNReal.ofReal (T^2*E)

end SharpWasserstein.RoughEulerianTransport
