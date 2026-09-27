import SharpWasserstein.ConfigurationBrownian
import SharpWasserstein.NarrowFlow

/-! Actual finite-horizon Brownian-driven particle laws. These are constructed
from continuous integral solutions and independently generated Brownian paths.
Identification with every weak Fokker–Planck solution is a separate obligation. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace SharpWasserstein.BrownianParticle

variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {T : ℝ} (hT : 0 ≤ T)

def law (μ : Measure (Configuration d N)) (t : ℝ) : Measure (Configuration d N) :=
  ParticleFlow.law hN hb hbound hM hL₁ hL₂ hT μ
    (BrownianNoise.configurationLaw d N T) t

theorem law_probability (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    IsProbabilityMeasure (law hN hb hbound hM hL₁ hL₂ hT μ t) :=
  ParticleFlow.law_probability hN hb hbound hM hL₁ hL₂ hT μ _ ht

theorem law_initial (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] :
    law hN hb hbound hM hL₁ hL₂ hT μ 0 = μ := by
  have hw := (measurePreserving_snd (μ := μ)
    (ν := BrownianNoise.configurationLaw d N T)).quasiMeasurePreserving.ae
      (BrownianNoise.configurationLaw_zero_ae hT)
  have heq : (fun p : Configuration d N × C(Icc 0 T, Configuration d N) =>
      ParticleFlow.solution hN hb hbound hM hL₁ hL₂ hT p.1 p.2 0) =ᵐ[
        μ.prod (BrownianNoise.configurationLaw d N T)] Prod.fst := by
    filter_upwards [hw] with p hp
    apply (ParticleFlow.solution_trajectory hN hb hbound hM hL₁ hL₂ hT p.1 p.2).initial hT
    simpa only [BoundedFlow.noiseExtension, projIcc_of_mem _ (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)] using hp
  unfold law ParticleFlow.law randomMapLaw
  rw [Measure.map_congr heq]
  exact (measurePreserving_fst (μ := μ) (ν := BrownianNoise.configurationLaw d N T)).map_eq

theorem law_secondMoment (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (hμ : HasSecondMoment μ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasSecondMoment (law hN hb hbound hM hL₁ hL₂ hT μ t) :=
  ParticleFlow.law_secondMoment hN hb hbound hM hL₁ hL₂ hT μ _ hμ ht
    (BrownianNoise.configurationLaw_memLp ⟨t, ht⟩ 2 (by norm_num))

theorem law_exchangeable (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (hμ : Exchangeable μ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Exchangeable (law hN hb hbound hM hL₁ hL₂ hT μ t) :=
  ParticleFlow.law_exchangeable hN hb hbound hM hL₁ hL₂ hT μ _ hμ
    (fun e => BrownianNoise.configurationLaw_permutation e) ht

theorem law_wassersteinSq_le (μ ν : Measure (Configuration d N))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {t : ℝ} (ht : t ∈ Icc 0 T) :
    wassersteinSq (law hN hb hbound hM hL₁ hL₂ hT μ t)
      (law hN hb hbound hM hL₁ hL₂ hT ν t) ≤
      ENNReal.ofReal (Real.exp (Real.sqrt (2 * d * (L₁ ^ 2 + L₂ ^ 2)) * t) ^ 2) *
        wassersteinSq μ ν :=
  ParticleFlow.law_wassersteinSq_le hN hb hbound hM hL₁ hL₂ hT μ ν _ ht

def probabilityCurve (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (t : Icc 0 T) : ProbabilityMeasure (Configuration d N) :=
  ⟨law hN hb hbound hM hL₁ hL₂ hT μ t,
    law_probability hN hb hbound hM hL₁ hL₂ hT μ t.property⟩

theorem law_narrowContinuous (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] :
    Continuous (probabilityCurve hN hb hbound hM hL₁ hL₂ hT μ) :=
  ParticleFlow.probabilityCurve_continuous hN hb hbound hM hL₁ hL₂ hT μ _

end SharpWasserstein.BrownianParticle
