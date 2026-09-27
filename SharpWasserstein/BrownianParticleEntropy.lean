import SharpWasserstein.BrownianEntropyTransport
import SharpWasserstein.BrownianHorizon
import SharpWasserstein.FlattenedEuclidean

/-! The constructed interacting particle evolution satisfies the exact
entropy-cost bound with a Lipschitz constant independent of particle number. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal NNReal
namespace SharpWasserstein

theorem euclidean_flattenedDrift {d N : ℕ}
    (v : ℝ → Configuration d N → Configuration d N) (t : ℝ) :
    GaussianBridge.euclideanDrift (flattenedDrift v) t =
      fun z => configurationEuclidean d N (v t ((configurationEuclidean d N).symm z)) := by
  funext z
  have hi : (configurationFlatten d N).symm (WithLp.ofLp z) =
      (configurationEuclidean d N).symm z := by
    funext i a
    rw [configurationFlatten_symm_apply]
    rfl
  simp only [GaussianBridge.euclideanDrift,flattenedDrift,hi,
    configurationFlatten_eq_euclidean,WithLp.toLp_ofLp]

namespace BrownianParticle

variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)

theorem law_entropy_le_wassersteinSq {T : ℝ} (hT : 0 < T)
    (μ ν : Measure (Configuration d N)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : HasSecondMoment μ) (hν : HasSecondMoment ν) :
    klDiv (law hN hb hbound hM hL₁ hL₂ hT.le μ T)
      (law hN hb hbound hM hL₁ hL₂ hT.le ν T) ≤
      ENNReal.ofReal (RegularizationRates.bridgeCost
        (Real.sqrt (2 * d * (L₁ ^ 2 + L₂ ^ 2))) T) * wassersteinSq μ ν := by
  have he : ∀ t, LipschitzWith
      ⟨Real.sqrt (2 * d * (L₁ ^ 2 + L₂ ^ 2)), Real.sqrt_nonneg _⟩
      (GaussianBridge.euclideanDrift (flattenedDrift (N := N) (fun _ => particleDrift b)) t) := by
    intro t
    rw [euclidean_flattenedDrift]
    exact euclidean_particleDrift_lipschitz hN hb hbound hL₁ hL₂
  exact BrownianEntropy.flow_entropy_le_wassersteinSq
    (v := fun _ => particleDrift (N := N) b) μ ν hμ hν
    ((particleDrift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (M := ⟨M,hM⟩) (fun _ x => particleDrift_norm_bound hN hbound hM x)
    (fun _ => particleDrift_lipschitz hN hb hbound hL₁ hL₂) he hT

theorem globalLaw_entropy_le_wassersteinSq {t : ℝ} (ht : 0 < t)
    (μ ν : Measure (Configuration d N)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : HasSecondMoment μ) (hν : HasSecondMoment ν) :
    klDiv (globalLaw hN hb hbound hM hL₁ hL₂ μ t)
      (globalLaw hN hb hbound hM hL₁ hL₂ ν t) ≤
      ENNReal.ofReal (RegularizationRates.bridgeCost
        (Real.sqrt (2 * d * (L₁ ^ 2 + L₂ ^ 2))) t) * wassersteinSq μ ν := by
  rw [globalLaw_eq hN hb hbound hM hL₁ hL₂ ht.le μ ⟨ht.le,le_rfl⟩,
    globalLaw_eq hN hb hbound hM hL₁ hL₂ ht.le ν ⟨ht.le,le_rfl⟩]
  exact law_entropy_le_wassersteinSq hN hb hbound hM hL₁ hL₂ ht μ ν hμ hν

end BrownianParticle
end SharpWasserstein
