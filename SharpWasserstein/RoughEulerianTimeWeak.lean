module

public import SharpWasserstein.Compat
public import SharpWasserstein.RoughEulerianTimeKernel
public import SharpWasserstein.RoughEulerianTransportContinuity

@[expose] public section

/-! The actual compact-test probability curve and its constructed joint L²
flux satisfy the genuine differentiated time-mollified weak equation. There
is no assumption of pointwise differentiability of the original curve. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval ContDiff InnerProductSpace
namespace SharpWasserstein.RoughEulerianTime
open WeightedTangent RoughEulerianTransport
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

def compactTestBCF (φ : Test d) : BoundedContinuousFunction (Point d) ℝ where
  toFun := (φ : Point d → ℝ)
  continuous_toFun := φ.property.1.continuous
  map_bounded' := Metric.isBounded_range_iff.mp
    (φ.property.2.isCompact_range φ.property.1.continuous).isBounded

theorem continuous_compact_test_pairing {μ : ℝ → ProbabilityMeasure (Point d)}
    (hμ : Continuous μ) (φ : Test d) :
    Continuous (fun t => ∫ x, (φ : Point d → ℝ) x ∂(μ t : Measure (Point d))) :=
  (ProbabilityMeasure.continuous_integral_boundedContinuousFunction (compactTestBCF φ)).comp hμ

theorem compact_curve_timeKernel_hasDerivAt
    {μ : ℝ → ProbabilityMeasure (Point d)} {σ : ℝ → Test d →ₗ[ℝ] ℝ} {T ε t : ℝ}
    (h : CompactDistributionContinuity μ σ T) (hε : 0 < ε) (ht : ε ≤ t) (htT : t+ε ≤ T)
    (φ : Test d) :
    HasDerivAt (timeConvolution (timeKernel ε hε) 0 T
      (fun s => ∫ x, (φ : Point d → ℝ) x ∂(μ s : Measure (Point d))))
      (timeConvolution (timeKernel ε hε) 0 T (fun s => σ s φ) t) t := by
  have hT : 0 ≤ T := by linarith
  apply timeKernel_hasDerivAt_source hε (by simpa using ht) htT
    (continuous_compact_test_pairing h.continuous φ).continuousOn (source_integrable_horizon h hT φ)
  intro s hs
  exact (h.equation φ 0 ⟨le_rfl,hT⟩ s hs).2

/-- This version uses the actual jointly measurable Riesz flux, hence is ready
for spatial mollification and the smooth Eulerian transport theorem. -/
theorem compact_curve_timeKernel_hasDerivAt_flux
    {μ : ℝ → ProbabilityMeasure (Point d)} {σ : ℝ → Test d →ₗ[ℝ] ℝ} {T ε t : ℝ}
    (h : CompactDistributionContinuity μ σ T) (hε : 0 < ε) (ht : ε ≤ t) (htT : t+ε ≤ T)
    {E : ℝ → ℝ} (hE : IntegrableOn E (Icc 0 T))
    (hbound : ∀ᵐ s ∂volume.restrict (Icc 0 T), ∀ φ : Test d,
      testObjective (μ s : Measure (Point d)) (σ s) φ ≤ E s) (φ : Test d) :
    HasDerivAt (timeConvolution (timeKernel ε hε) 0 T
      (fun s => ∫ x, (φ : Point d → ℝ) x ∂(μ s : Measure (Point d))))
      (timeConvolution (timeKernel ε hε) 0 T (fun s =>
        ∫ x, ⟪gradient (φ : Point d → ℝ) x,curveFlux h (s,x)⟫_ℝ
          ∂(μ s : Measure (Point d))) t) t := by
  have hT : 0 ≤ T := by linarith
  apply timeKernel_hasDerivAt_source hε (by simpa using ht) htT
    (continuous_compact_test_pairing h.continuous φ).continuousOn (curveFlux_pairing_integrable h hT φ)
  intro s hs
  exact (curveFlux_continuity_equation h hT hE hbound φ ⟨le_rfl,hT⟩ hs hs.1).2

end SharpWasserstein.RoughEulerianTime
