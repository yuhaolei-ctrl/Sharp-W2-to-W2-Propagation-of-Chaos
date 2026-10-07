module

public import SharpWasserstein.Compat
public import SharpWasserstein.ParticleFlow
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

/-! Narrow continuity of the actual constructed flow laws. This is proved by
bounded continuous tests and dominated convergence, without assuming a
continuity property of the output measures. -/

noncomputable section
open Set MeasureTheory

namespace SharpWasserstein

/-- Turn a genuine measurable random map into its probability law. -/
def randomProbabilityLaw {Ω E I : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : I → Ω → E)
    (hF : ∀ t, Measurable (F t)) (t : I) : ProbabilityMeasure E :=
  ⟨Measure.map (F t) P, Measure.isProbabilityMeasure_map (hF t).aemeasurable⟩

/-- Continuous random paths induce a narrowly continuous probability curve. -/
theorem randomProbabilityLaw_continuous {Ω E I : Type*}
    [MeasurableSpace Ω] [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace I] [FirstCountableTopology I]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : I → Ω → E)
    (hF : ∀ t, Measurable (F t)) (hpath : ∀ᵐ ω ∂P, Continuous (fun t => F t ω)) :
    Continuous (randomProbabilityLaw P F hF) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro φ
  have heq : (fun t => ∫ x, φ x ∂(randomProbabilityLaw P F hF t)) =
      (fun t => ∫ ω, φ (F t ω) ∂P) := by
    funext t
    exact integral_map (hF t).aemeasurable φ.continuous.measurable.aestronglyMeasurable
  rw [heq]
  apply continuous_of_dominated (bound := fun _ => ‖φ‖)
  · intro t
    exact (φ.continuous.measurable.comp (hF t)).aestronglyMeasurable
  · intro t
    exact Filter.Eventually.of_forall fun ω => φ.norm_coe_le_norm (F t ω)
  · exact integrable_const ‖φ‖
  · filter_upwards [hpath] with ω hω
    exact φ.continuous.comp hω

namespace ParticleFlow

variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {T : ℝ} [MeasurableSpace C(Icc 0 T, Configuration d N)]
  [BorelSpace C(Icc 0 T, Configuration d N)]

/-- The constructed particle law as a probability-valued curve on its horizon. -/
def probabilityCurve (hT : 0 ≤ T) (μ : Measure (Configuration d N))
    (ξ : Measure C(Icc 0 T, Configuration d N))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ξ] (t : Icc 0 T) :
    ProbabilityMeasure (Configuration d N) :=
  ⟨law hN hb hbound hM hL₁ hL₂ hT μ ξ t,
    law_probability hN hb hbound hM hL₁ hL₂ hT μ ξ t.property⟩

theorem probabilityCurve_continuous (hT : 0 ≤ T) (μ : Measure (Configuration d N))
    (ξ : Measure C(Icc 0 T, Configuration d N))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ξ] :
    Continuous (probabilityCurve hN hb hbound hM hL₁ hL₂ hT μ ξ) := by
  apply randomProbabilityLaw_continuous (μ.prod ξ)
    (fun (t : Icc 0 T) p => solution hN hb hbound hM hL₁ hL₂ hT p.1 p.2 t)
    (fun t => solution_measurable hN hb hbound hM hL₁ hL₂ hT t.property)
  exact Filter.Eventually.of_forall fun p =>
    (solution_trajectory hN hb hbound hM hL₁ hL₂ hT p.1 p.2).continuous.restrict

end ParticleFlow
end SharpWasserstein
