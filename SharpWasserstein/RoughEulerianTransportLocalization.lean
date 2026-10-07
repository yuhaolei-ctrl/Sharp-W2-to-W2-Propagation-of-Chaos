module

public import SharpWasserstein.Compat
public import SharpWasserstein.RoughEulerianTransportSpaceTime
public import SharpWasserstein.RoughEulerianTransportKernel

@[expose] public section

/-! Measurable time-localized compact tests belong to the joint gradient space.
The Riesz flux therefore represents every integrated scalar source pairing, not
just an abstract completion of an unspecified collection of test functions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace ENNReal ProbabilityTheory
namespace SharpWasserstein.RoughEulerianTransport
open WeightedTangent
variable {α : Type*} [MeasurableSpace α] {d : ℕ}
  [MeasurableSpace (Point d)] [BorelSpace (Point d)]
  (ν : Measure α) [IsFiniteMeasure ν] (κ : Kernel α (Point d)) [IsMarkovKernel κ]
  (σ : α → Test d →ₗ[ℝ] ℝ)

/-- A fixed genuine compact smooth test, localized to a measurable time set. -/
def localizedTest (s : Set α) (φ : Test d) : α → Test d := s.indicator (fun _ => φ)

omit [MeasurableSpace α] [MeasurableSpace (Point d)] [BorelSpace (Point d)] in
theorem fieldGradient_localizedTest (s : Set α) (φ : Test d) :
    fieldGradient (localizedTest s φ) =
      (s ×ˢ univ).indicator (fun z : α × Point d => gradient (φ : Point d → ℝ) z.2) := by
  classical
  funext z
  by_cases hz : z.1 ∈ s
  · simp [fieldGradient,localizedTest,hz]
  · simp [fieldGradient,localizedTest,hz,gradient]

/-- Time localization is admissible whenever the actual scalar source pairing is integrable. -/
def localizedField (s : Set α) (hs : MeasurableSet s) (φ : Test d)
    (hσ : Integrable (fun t => σ t φ) ν) : Field ν κ σ := by
  refine ⟨localizedTest s φ,?_,?_⟩
  · rw [fieldGradient_localizedTest]
    obtain ⟨C,hC⟩ := (compactSupport_test_gradient φ).exists_bound_of_continuous
      (continuous_test_gradient φ)
    apply (MemLp.of_bound ((continuous_test_gradient φ).measurable.comp measurable_snd).aestronglyMeasurable
      C (Eventually.of_forall fun z => hC z.2)).indicator (hs.prod MeasurableSet.univ)
  · have he : (fun t => σ t (localizedTest s φ t)) = s.indicator (fun t => σ t φ) := by
      classical
      funext t
      by_cases ht : t ∈ s <;> simp [localizedTest,ht]
    rw [he]
    exact hσ.indicator hs

/-- Exact measurable-time localization of the scalar distribution by one joint L² flux. -/
theorem spaceTimeFlux_localized_pairing {E : α → ℝ} (hE : Integrable E ν)
    (hbound : ∀ᵐ t ∂ν, ∀ φ : Test d, testObjective (κ t) (σ t) φ ≤ E t)
    (s : Set α) (hs : MeasurableSet s) (φ : Test d)
    (hσ : Integrable (fun t => σ t φ) ν) :
    (∫ t in s, σ t φ ∂ν) = ∫ z in s ×ˢ univ,
      ⟪gradient (φ : Point d → ℝ) z.2,spaceTimeFlux ν κ σ z⟫_ℝ ∂(ν ⊗ₘ κ) := by
  have hp := spaceTimeFlux_pairing ν κ σ hE hbound (localizedField ν κ σ s hs φ hσ)
  have hleft : (fun t => σ t ((localizedField ν κ σ s hs φ hσ).val t)) =
      s.indicator (fun t => σ t φ) := by
    classical
    funext t
    by_cases ht : t ∈ s <;> simp [localizedField,localizedTest,ht]
  have hright : (fun z => ⟪fieldGradient (localizedField ν κ σ s hs φ hσ).val z,
      spaceTimeFlux ν κ σ z⟫_ℝ) = (s ×ˢ univ).indicator
      (fun z => ⟪gradient (φ : Point d → ℝ) z.2,spaceTimeFlux ν κ σ z⟫_ℝ) := by
    classical
    funext z
    change ⟪fieldGradient (localizedTest s φ) z,_⟫_ℝ = _
    rw [fieldGradient_localizedTest]
    by_cases hz : z ∈ s ×ˢ univ <;> simp [hz]
  rw [hleft,hright,integral_indicator hs,integral_indicator (hs.prod MeasurableSet.univ)] at hp
  exact hp

/-- Pairings against any fixed compact test are genuinely integrable in the joint measure. -/
theorem spaceTimeFlux_test_integrable (φ : Test d)
    (hσ : Integrable (fun t => σ t φ) ν) :
    Integrable (fun z : α × Point d => ⟪gradient (φ : Point d → ℝ) z.2,
      spaceTimeFlux ν κ σ z⟫_ℝ) (ν ⊗ₘ κ) := by
  let ψ := localizedField ν κ σ univ MeasurableSet.univ φ hσ
  apply (L2.integrable_inner (𝕜 := ℝ) (fieldGradientLp ν κ σ ψ) (spaceTimeFlux ν κ σ)).congr
  filter_upwards [fieldGradientLp_ae ν κ σ ψ] with z hz
  rw [hz]
  simp [ψ,localizedField,localizedTest,fieldGradient]

/-- The localized joint pairing is the literal iterated integral against the varying laws. -/
theorem spaceTimeFlux_set_pairing {E : α → ℝ} (hE : Integrable E ν)
    (hbound : ∀ᵐ t ∂ν, ∀ φ : Test d, testObjective (κ t) (σ t) φ ≤ E t)
    (s : Set α) (hs : MeasurableSet s) (φ : Test d)
    (hσ : Integrable (fun t => σ t φ) ν) :
    (∫ t in s, σ t φ ∂ν) = ∫ t in s, ∫ x,
      ⟪gradient (φ : Point d → ℝ) x,spaceTimeFlux ν κ σ (t,x)⟫_ℝ ∂κ t ∂ν := by
  rw [spaceTimeFlux_localized_pairing ν κ σ hE hbound s hs φ hσ,
    Measure.setIntegral_compProd hs MeasurableSet.univ
      (spaceTimeFlux_test_integrable ν κ σ φ hσ).integrableOn]
  simp only [Measure.restrict_univ]

omit [BorelSpace (Point d)] [IsMarkovKernel κ] in
/-- Genuine finite weighted negative-Sobolev energy supplies the pointwise
quadratic inequality used in the construction. -/
theorem objective_le_energy_of_finite (t : α) (hfin : FiniteEnergy (κ t) (σ t)) (φ : Test d) :
    testObjective (κ t) (σ t) φ ≤ energy (κ t) (σ t) :=
  le_csSup hfin ⟨φ,rfl⟩

end SharpWasserstein.RoughEulerianTransport
