module

public import SharpWasserstein.Compat
public import SharpWasserstein.EulerWeakLimit
public import SharpWasserstein.BrownianGlobalProperties

@[expose] public section

/-! The constructed Brownian particle laws satisfy the manuscript's actual
weak Fokker--Planck equation, including all probability, moment and
integrability fields. The diffusion generator is precisely the coordinate
Laplacian, corresponding to the proved sqrt-two Brownian construction. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators Interval
namespace SharpWasserstein

theorem particleDrift_smooth {d N : ℕ} {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) : ContDiff ℝ (⊤ : ℕ∞) (particleDrift (N := N) b) := by
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.const_smul
  apply ContDiff.sum
  intro j _
  exact hb.smooth.comp ((contDiff_apply ℝ (Position d) i).prodMk
    (contDiff_apply ℝ (Position d) j))

namespace BrownianParticle
variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)

theorem law_integral_eq {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {f : Configuration d N → ℝ} (hf : Continuous f) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ x, f x ∂law hN hb hbound hM hL₁ hL₂ hT μ t) =
      ∫ p : Configuration d N × C(Icc 0 T, Configuration d N),
        f (ParticleFlow.solution hN hb hbound hM hL₁ hL₂ hT p.1 p.2 t)
          ∂μ.prod (BrownianNoise.configurationLaw d N T) :=
  integral_map (ParticleFlow.solution_measurable hN hb hbound hM hL₁ hL₂ hT ht).aemeasurable
    hf.aestronglyMeasurable

/-- Finite-horizon weak equation for the actual solution law. -/
theorem law_equation {T : ℝ} (hT : 0 < T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) :
    (∫ x, φ x ∂law hN hb hbound hM hL₁ hL₂ hT.le μ T) - (∫ x, φ x ∂μ) =
      ∫ s in (0 : ℝ)..T, ∫ x, generator (particleDrift b) φ x
        ∂law hN hb hbound hM hL₁ hL₂ hT.le μ s := by
  have he := EulerWeak.brownian_trajectory_weak_equation hT μ (particleDrift b)
    (particleDrift_smooth hb) ⟨M,hM⟩ ⟨L₁+L₂,add_nonneg hL₁ hL₂⟩
    (particleDrift_norm_bound hN hbound hM)
    (particleDrift_lipschitz hN hb hbound hL₁ hL₂)
    (fun t p => ParticleFlow.solution hN hb hbound hM hL₁ hL₂ hT.le p.1 p.2 t)
    (fun p => ParticleFlow.solution_trajectory hN hb hbound hM hL₁ hL₂ hT.le p.1 p.2)
    (fun _ ht => ParticleFlow.solution_measurable hN hb hbound hM hL₁ hL₂ hT.le ht) hφ
  rw [law_integral_eq hN hb hbound hM hL₁ hL₂ hT.le μ hφ.1.continuous ⟨hT.le,le_rfl⟩]
  rw [he]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hT.le] at hs
  exact (law_integral_eq hN hb hbound hM hL₁ hL₂ hT.le μ
    (CompactGenerator.generator_continuous hφ
      (particleDrift_lipschitz hN hb hbound hL₁ hL₂).continuous) hs).symm

/-- The global law has the genuine integrated generator equation at every
nonnegative time, with the original initial law. -/
theorem globalLaw_equation (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, φ x ∂globalLaw hN hb hbound hM hL₁ hL₂ μ t) -
      (∫ x, φ x ∂globalLaw hN hb hbound hM hL₁ hL₂ μ 0) =
      ∫ s in (0 : ℝ)..t, ∫ x, generator (particleDrift b) φ x
        ∂globalLaw hN hb hbound hM hL₁ hL₂ μ s := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  · rw [globalLaw_initial hN hb hbound hM hL₁ hL₂ μ,
      globalLaw_eq hN hb hbound hM hL₁ hL₂ ht.le μ ⟨ht.le,le_rfl⟩,
      law_equation hN hb hbound hM hL₁ hL₂ ht μ hφ]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.le] at hs
    dsimp only
    rw [globalLaw_eq hN hb hbound hM hL₁ hL₂ ht.le μ hs]

/-- All fields of the manuscript's weak evolution hold for the constructed
Brownian particle law from any probability initial law with a second moment. -/
theorem globalLaw_weakEvolution (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (hμ : HasSecondMoment μ) :
    WeakEvolution (fun _ => particleDrift b) (globalLaw hN hb hbound hM hL₁ hL₂ μ) where
  probability := fun _ ht => globalLaw_probability hN hb hbound hM hL₁ hL₂ μ ht
  secondMoment := fun _ ht => globalLaw_secondMoment hN hb hbound hM hL₁ hL₂ μ hμ ht
  momentBound := fun _ hT => globalLaw_momentBound hN hb hbound hM hL₁ hL₂ μ hμ hT.le
  testContinuous := fun _ hφ => globalLaw_compactExpectation_continuous hN hb hbound hM hL₁ hL₂ μ
    hφ.1.continuous hφ.2
  generatorIntegrable := fun _ hφ _ ht => globalLaw_generatorIntegrable hN hb hbound hM hL₁ hL₂ μ hφ ht
  timeIntegrable := fun _ hφ _ ht => globalLaw_timeIntegrable hN hb hbound hM hL₁ hL₂ μ hφ ht
  equation := fun _ hφ _ ht => globalLaw_equation hN hb hbound hM hL₁ hL₂ μ hφ ht

/-- Exchangeable initial laws give the precise particle-evolution predicate. -/
theorem globalLaw_isParticleEvolution (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (hμ : HasSecondMoment μ) (hex : Exchangeable μ) :
    IsParticleEvolution b (globalLaw hN hb hbound hM hL₁ hL₂ μ) := by
  refine ⟨globalLaw_weakEvolution hN hb hbound hM hL₁ hL₂ μ hμ, ?_⟩
  rwa [globalLaw_initial hN hb hbound hM hL₁ hL₂ μ]

end BrownianParticle
end SharpWasserstein
