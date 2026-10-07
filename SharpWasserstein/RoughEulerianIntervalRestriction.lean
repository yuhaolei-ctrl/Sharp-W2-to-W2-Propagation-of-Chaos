module

public import SharpWasserstein.Compat
public import SharpWasserstein.RoughEulerianTransportContinuity

@[expose] public section

/-! Restriction and time translation of the genuine compact-test continuity
equation. This allows finite-action transport on every positive-time interval
without assuming integrability of the source energy at the initial endpoint. -/
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace SharpWasserstein.RoughEulerianTransport
open WeightedTangent
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]
  {μ : ℝ → ProbabilityMeasure (Point d)} {σ : ℝ → Test d →ₗ[ℝ] ℝ} {T : ℝ}

/-- The exact scalar equation is preserved on an arbitrary subinterval. -/
theorem CompactDistributionContinuity.translate
    (h : CompactDistributionContinuity μ σ T) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ T) :
    CompactDistributionContinuity (fun t => μ (a+t)) (fun t => σ (a+t)) (b-a) := by
  refine ⟨h.continuous.comp (continuous_const.add continuous_id),?_⟩
  intro φ s hs t ht
  have hs' : a+s ∈ Icc 0 T := ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have ht' : a+t ∈ Icc 0 T := ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have he := h.equation φ (a+s) hs' (a+t) ht'
  refine ⟨?_,?_⟩
  · simpa only [add_sub_cancel_left] using he.1.comp_add_left a
  · exact he.2.trans (intervalIntegral.integral_comp_add_left (fun r => σ r φ) a).symm

end SharpWasserstein.RoughEulerianTransport
