import SharpWasserstein.RoughEulerianTransportLocalization
import SharpWasserstein.RoughEulerianTransportEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! A finite-energy distributional continuity equation supplies an actual measurable
space-time flux, including singular varying probability measures. This closes the
measurable-selection step; it does not assert the remaining rough transport theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace ENNReal ProbabilityTheory Interval Topology
namespace SharpWasserstein.RoughEulerianTransport
open WeightedTangent
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

/-- The literal compact-test equation with a scalar linear distribution at each time. -/
structure CompactDistributionContinuity (μ : ℝ → ProbabilityMeasure (Point d))
    (σ : ℝ → Test d →ₗ[ℝ] ℝ) (T : ℝ) : Prop where
  continuous : Continuous μ
  equation : ∀ φ : Test d, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
    IntervalIntegrable (fun r => σ r φ) volume s t ∧
      (∫ x, (φ : Point d → ℝ) x ∂(μ t : Measure (Point d)))-(∫ x,(φ : Point d → ℝ) x ∂(μ s : Measure (Point d))) =
        ∫ r in s..t, σ r φ

variable {μ : ℝ → ProbabilityMeasure (Point d)} {σ : ℝ → Test d →ₗ[ℝ] ℝ} {T : ℝ}
  (h : CompactDistributionContinuity μ σ T) (hT : 0 ≤ T)

/-- The actual joint time-space measure associated to the probability curve. -/
def curveSpaceTimeMeasure : Measure (ℝ × Point d) :=
  (volume.restrict (Icc 0 T)) ⊗ₘ probabilityCurveKernel μ h.continuous

/-- A single L² Riesz representative in the actual time-space measure. -/
def curveFlux : Lp (Point d) 2 (curveSpaceTimeMeasure h) :=
  spaceTimeFlux (volume.restrict (Icc 0 T)) (probabilityCurveKernel μ h.continuous) σ

/-- The chosen joint representative is strongly measurable on the actual product Borel space. -/
theorem curveFlux_stronglyMeasurable : StronglyMeasurable (fun z => curveFlux h z) :=
  Lp.stronglyMeasurable (curveFlux h)

include h hT

/-- Scalar compact-test pairings are integrable over the horizon by the actual weak equation. -/
theorem source_integrable_horizon (φ : Test d) :
    Integrable (fun t => σ t φ) (volume.restrict (Icc 0 T)) :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp
    (h.equation φ 0 ⟨le_rfl,hT⟩ T ⟨hT,le_rfl⟩).1

omit hT in
/-- The joint flux has the supplied finite-action bound without any constant loss. -/
theorem curveFlux_energy_le {E : ℝ → ℝ} (hE : IntegrableOn E (Icc 0 T))
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 T), ∀ φ : Test d,
      testObjective (μ t : Measure (Point d)) (σ t) φ ≤ E t) :
    (∫ z, ‖curveFlux h z‖^2 ∂curveSpaceTimeMeasure h) ≤ ∫ t in Icc 0 T,E t :=
  spaceTimeFlux_energy_le _ _ _ hE hbound

/-- Actual time integrability of the represented compact-test action. -/
theorem curveFlux_pairing_integrable (φ : Test d) :
    Integrable (fun t => ∫ x, ⟪gradient (φ : Point d → ℝ) x,curveFlux h (t,x)⟫_ℝ
      ∂(μ t : Measure (Point d))) (volume.restrict (Icc 0 T)) := by
  have hi := spaceTimeFlux_test_integrable (volume.restrict (Icc 0 T))
    (probabilityCurveKernel μ h.continuous) σ φ (source_integrable_horizon h hT φ)
  have hj := hi.integral_compProd
  convert hj using 1 <;> rfl

/-- The originally scalar compact-test continuity equation is represented by a
jointly measurable finite-energy vector field, with the exact divergence sign. -/
theorem curveFlux_continuity_equation {E : ℝ → ℝ} (hE : IntegrableOn E (Icc 0 T))
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 T), ∀ φ : Test d,
      testObjective (μ t : Measure (Point d)) (σ t) φ ≤ E t)
    (φ : Test d) {a b : ℝ} (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) (hab : a ≤ b) :
    IntervalIntegrable (fun t => ∫ x,⟪gradient (φ : Point d → ℝ) x,curveFlux h (t,x)⟫_ℝ
      ∂(μ t : Measure (Point d))) volume a b ∧
    (∫ x,(φ : Point d → ℝ) x ∂(μ b : Measure (Point d)))-(∫ x,(φ : Point d → ℝ) x ∂(μ a : Measure (Point d))) =
      ∫ t in a..b,∫ x,⟪gradient (φ : Point d → ℝ) x,curveFlux h (t,x)⟫_ℝ
        ∂(μ t : Measure (Point d)) := by
  have hsub : Ioc a b ⊆ Icc 0 T := fun t ht => ⟨ha.1.trans ht.1.le,ht.2.trans hb.2⟩
  have hp := spaceTimeFlux_set_pairing (volume.restrict (Icc 0 T))
    (probabilityCurveKernel μ h.continuous) σ hE hbound (Ioc a b) measurableSet_Ioc φ
    (source_integrable_horizon h hT φ)
  simp only [Measure.restrict_restrict_of_subset hsub] at hp
  have hg : IntegrableOn (fun t => ∫ x,⟪gradient (φ : Point d → ℝ) x,curveFlux h (t,x)⟫_ℝ
      ∂(μ t : Measure (Point d))) (Icc 0 T) := curveFlux_pairing_integrable h hT φ
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (hg.mono_set hsub),?_⟩
  rw [(h.equation φ a ha b hb).2,intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab]
  exact hp

/-- The resulting measurable field has finite joint action; no canonical timewise
representative or measurable selection is among the hypotheses. -/
theorem exists_measurable_finiteAction_flux {E : ℝ → ℝ} (hE : IntegrableOn E (Icc 0 T))
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 T), ∀ φ : Test d,
      testObjective (μ t : Measure (Point d)) (σ t) φ ≤ E t) :
    ∃ U : ℝ × Point d → Point d, StronglyMeasurable U ∧ MemLp U 2 (curveSpaceTimeMeasure h) ∧
      (∫ z,‖U z‖^2 ∂curveSpaceTimeMeasure h) ≤ ∫ t in Icc 0 T,E t ∧
      ∀ φ : Test d,∀ a ∈ Icc 0 T,∀ b ∈ Icc 0 T,a ≤ b →
        (∫ x,(φ : Point d → ℝ) x ∂(μ b : Measure (Point d)))-(∫ x,(φ : Point d → ℝ) x ∂(μ a : Measure (Point d))) =
          ∫ t in a..b,∫ x,⟪gradient (φ : Point d → ℝ) x,U (t,x)⟫_ℝ
            ∂(μ t : Measure (Point d)) := by
  refine ⟨curveFlux h,curveFlux_stronglyMeasurable h,Lp.memLp (curveFlux h),
    curveFlux_energy_le h hE hbound,?_⟩
  intro φ a ha b hb hab
  exact (curveFlux_continuity_equation h hT hE hbound φ ha hb hab).2

/-- Actual finite weighted tangent energy is enough; the vector field is constructed,
not supplied as a measurable family of timewise canonical representatives. -/
theorem exists_flux_of_finite_tangent_energy
    (hfin : ∀ᵐ t ∂volume.restrict (Icc 0 T), FiniteEnergy (μ t : Measure (Point d)) (σ t))
    (hE : IntegrableOn (fun t => energy (μ t : Measure (Point d)) (σ t)) (Icc 0 T)) :
    ∃ U : ℝ × Point d → Point d, StronglyMeasurable U ∧ MemLp U 2 (curveSpaceTimeMeasure h) ∧
      (∫ z,‖U z‖^2 ∂curveSpaceTimeMeasure h) ≤
        ∫ t in Icc 0 T,energy (μ t : Measure (Point d)) (σ t) ∧
      ∀ φ : Test d,∀ a ∈ Icc 0 T,∀ b ∈ Icc 0 T,a ≤ b →
        (∫ x,(φ : Point d → ℝ) x ∂(μ b : Measure (Point d)))-
          (∫ x,(φ : Point d → ℝ) x ∂(μ a : Measure (Point d))) =
          ∫ t in a..b,∫ x,⟪gradient (φ : Point d → ℝ) x,U (t,x)⟫_ℝ
            ∂(μ t : Measure (Point d)) := by
  apply exists_measurable_finiteAction_flux h hT hE
  filter_upwards [hfin] with t ht φ
  exact le_csSup ht ⟨φ,rfl⟩

end SharpWasserstein.RoughEulerianTransport
