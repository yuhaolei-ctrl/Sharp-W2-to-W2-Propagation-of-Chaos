module

public import SharpWasserstein.Compat
public import SharpWasserstein.BrownianHorizon
public import SharpWasserstein.ParticleMomentBounds
public import SharpWasserstein.TestGenerator

@[expose] public section

/-! Global moment and test-function regularity of the actual particle law.
The weak generator equation is a separate analytic theorem. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Interval Topology
namespace SharpWasserstein.BrownianParticle

variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)

theorem globalLaw_momentBound (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (hμ : HasSecondMoment μ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ t ∈ Icc 0 T,
      (∫⁻ x, ENNReal.ofReal (productCost x 0) ∂globalLaw hN hb hbound hM hL₁ hL₂ μ t) ≤ C := by
  obtain ⟨C,hC,hct⟩ := law_momentBound hN hb hbound hM hL₁ hL₂ hT μ hμ
  refine ⟨C,hC,fun t ht => ?_⟩
  rw [globalLaw_eq hN hb hbound hM hL₁ hL₂ hT μ ht]
  exact hct t ht

theorem globalLaw_compactExpectation_continuousOn_Icc
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {f : Configuration d N → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t => ∫ x, f x ∂globalLaw hN hb hbound hM hL₁ hL₂ μ t) (Icc 0 T) := by
  apply continuousOn_iff_continuous_restrict.mpr
  have h := CompactGenerator.expectation_continuous hf hc
    (law_narrowContinuous hN hb hbound hM hL₁ hL₂ hT μ)
  convert h using 1
  funext t
  change (∫ x, f x ∂globalLaw hN hb hbound hM hL₁ hL₂ μ t) =
    ∫ x, f x ∂law hN hb hbound hM hL₁ hL₂ hT μ t
  rw [globalLaw_eq hN hb hbound hM hL₁ hL₂ hT μ t.property]

theorem globalLaw_compactExpectation_continuous
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {f : Configuration d N → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    ContinuousOn (fun t => ∫ x, f x ∂globalLaw hN hb hbound hM hL₁ hL₂ μ t) (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  have hT : 0 ≤ t+1 := by linarith [ht]
  have h := globalLaw_compactExpectation_continuousOn_Icc hN hb hbound hM hL₁ hL₂ μ hf hc hT
    t ⟨ht,by linarith⟩
  apply h.mono_of_mem_nhdsWithin
  rw [← Ici_inter_Iic]
  exact inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iic_mem_nhds (by linarith : t < t+1)))

theorem globalLaw_generatorIntegrable
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (generator (particleDrift b) φ) (globalLaw hN hb hbound hM hL₁ hL₂ μ t) := by
  letI := globalLaw_probability hN hb hbound hM hL₁ hL₂ μ ht
  exact CompactGenerator.integrable
    (CompactGenerator.generator_continuous hφ (particleDrift_lipschitz hN hb hbound hL₁ hL₂).continuous)
    (CompactGenerator.generator_compact hφ _) _

theorem globalLaw_timeIntegrable
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => ∫ x, generator (particleDrift b) φ x
      ∂globalLaw hN hb hbound hM hL₁ hL₂ μ s) volume 0 t :=
  (globalLaw_compactExpectation_continuousOn_Icc hN hb hbound hM hL₁ hL₂ μ
    (CompactGenerator.generator_continuous hφ (particleDrift_lipschitz hN hb hbound hL₁ hL₂).continuous)
    (CompactGenerator.generator_compact hφ _) ht).intervalIntegrable_of_Icc ht

end SharpWasserstein.BrownianParticle
