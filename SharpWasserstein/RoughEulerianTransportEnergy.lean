module

public import SharpWasserstein.Compat
public import SharpWasserstein.WeightedTangentLimit
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

@[expose] public section

/-! Scalar continuity of the source makes its genuine varying-weight variational
energy measurable. This requires no measurability of canonical tangent vectors. -/
noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal
namespace SharpWasserstein.RoughEulerianTransport
open WeightedTangent
variable {α : Type*} [TopologicalSpace α] {d : ℕ}
  [MeasurableSpace (Point d)] [BorelSpace (Point d)]
  {μ : α → ProbabilityMeasure (Point d)} {σ : α → Test d →ₗ[ℝ] ℝ}

/-- The genuine extended energy is lower semicontinuous along a narrowly
continuous law curve with continuous scalar compact-test source pairings. -/
theorem lowerSemicontinuous_extendedEnergy (hμ : Continuous μ)
    (hσ : ∀ φ : Test d, Continuous (fun t => σ t φ)) :
    LowerSemicontinuous (fun t => extendedEnergy (μ t : Measure (Point d)) (σ t)) := by
  apply lowerSemicontinuous_iSup
  intro φ
  have hc : Continuous (fun t => testObjective (μ t : Measure (Point d)) (σ t) φ) :=
    ((hσ φ).const_mul 2).sub
      ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction (gradientSquare φ)).comp hμ)
  exact (ENNReal.continuous_ofReal.comp hc).lowerSemicontinuous

/-- Measurability of the energy follows from scalar continuity, even when it is infinite. -/
theorem measurable_extendedEnergy [MeasurableSpace α] [OpensMeasurableSpace α]
    (hμ : Continuous μ) (hσ : ∀ φ : Test d, Continuous (fun t => σ t φ)) :
    Measurable (fun t => extendedEnergy (μ t : Measure (Point d)) (σ t)) :=
  (lowerSemicontinuous_extendedEnergy hμ hσ).measurable

/-- At finite energy, the actual real variational energy is a measurable function. -/
theorem measurable_finite_energy [MeasurableSpace α] [OpensMeasurableSpace α]
    (hμ : Continuous μ) (hσ : ∀ φ : Test d, Continuous (fun t => σ t φ))
    (hfin : ∀ t, FiniteEnergy (μ t : Measure (Point d)) (σ t)) :
    Measurable (fun t => energy (μ t : Measure (Point d)) (σ t)) := by
  have hn (t : α) : 0 ≤ energy (μ t : Measure (Point d)) (σ t) := by
    rw [energy_eq_norm_sq _ _ (hfin t)]
    positivity
  have he : (fun t => energy (μ t : Measure (Point d)) (σ t)) =
      fun t => (extendedEnergy (μ t : Measure (Point d)) (σ t)).toReal := by
    funext t
    rw [extendedEnergy_eq_ofReal _ _ (hfin t),ENNReal.toReal_ofReal (hn t)]
  rw [he]
  exact (measurable_extendedEnergy hμ hσ).ennreal_toReal

end SharpWasserstein.RoughEulerianTransport
