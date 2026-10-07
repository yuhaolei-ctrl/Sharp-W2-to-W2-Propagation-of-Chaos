module

public import SharpWasserstein.Compat
public import SharpWasserstein.SwitchCurve

@[expose] public section

/-! P₂ continuity, marginal endpoint continuity and identification of the
switch construction with the prescribed reference and particle global laws. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace SharpWasserstein.SwitchCurve

variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {v : ℝ → Configuration d N → Configuration d N} {A K : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hvb : ∀ t x, ‖v t x‖ ≤ A)
  (hvl : ∀ t, LipschitzWith K (v t)) {T : ℝ} (hT : 0 ≤ T)

def quadraticCurve (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (hμ : HasSecondMoment μ) (s : Icc 0 T) : QuadraticProbabilityLaw d N :=
  ⟨law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ s,
    law_probability hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ s.property,
    law_secondMoment hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ hμ s.property⟩

theorem continuous_quadraticCurve (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (hμ : HasSecondMoment μ) :
    Continuous (quadraticCurve hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ hμ) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hz := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (law_wassersteinSq_tendsto hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ t)
  simpa only [ENNReal.toReal_zero,Real.sqrt_zero,quadraticProbability_dist_eq,
    quadraticCurve,Function.comp_def] using hz.sqrt

theorem marginal_wassersteinSq_tendsto (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {k : ℕ} (hk : k ≤ N) (t : Icc 0 T) :
    Tendsto (fun s : Icc 0 T => wassersteinSq
      (marginal hk (law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ s))
      (marginal hk (law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ t))) (𝓝 t) (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (law_wassersteinSq_tendsto hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ t)
    (fun _ => zero_le) (fun _ => wassersteinSq_marginal_le hk _ _)

theorem law_eq_global (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : s ∈ Icc 0 T) :
    law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ s =
      BrownianParticle.globalLaw hN hb hbound hM hL₁ hL₂
        (BrownianFlow.globalLaw hv hvb hvl μ s) (T-s) := by
  letI := BrownianFlow.globalLaw_probability hv hvb hvl μ hs.1
  rw [BrownianParticle.globalLaw_eq hN hb hbound hM hL₁ hL₂ hT _
    ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩,
    BrownianFlow.globalLaw_eq hv hvb hvl hT μ hs]
  rfl

end SharpWasserstein.SwitchCurve

namespace SharpWasserstein.PrescribedSwitchCurve
variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ) {T : ℝ} (hT : 0 ≤ T)

def law (P : Measure (Configuration d N)) (s : ℝ) : Measure (Configuration d N) :=
  SwitchCurve.law hN hb hbound hM hL₁ hL₂
    (DecoupledFlow.liftDrift_continuous N (PrescribedReference.singleDrift_continuous hb hbound hL₁ hμ))
    (DecoupledFlow.liftDrift_bound N (PrescribedReference.singleDrift_bound hbound hM hμ))
    (DecoupledFlow.liftDrift_lipschitz N (PrescribedReference.singleDrift_lipschitz hb hbound hL₁ hμ)) hT P s

theorem law_eq_composition (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    {s : ℝ} (hs : s ∈ Icc 0 T) :
    law hN hb hbound hM hL₁ hL₂ hμ hT P s =
      BrownianParticle.globalLaw hN hb hbound hM hL₁ hL₂
        (PrescribedReference.law hb hbound hM hL₁ hμ N P s) (T-s) :=
  SwitchCurve.law_eq_global hN hb hbound hM hL₁ hL₂ _ _ _ hT P hs

theorem law_zero (P : Measure (Configuration d N)) [IsProbabilityMeasure P] :
    law hN hb hbound hM hL₁ hL₂ hμ hT P 0 =
      BrownianParticle.globalLaw hN hb hbound hM hL₁ hL₂ P T := by
  rw [law_eq_composition hN hb hbound hM hL₁ hL₂ hμ hT P ⟨le_rfl,hT⟩,
    PrescribedReference.law_initial,sub_zero]

theorem law_terminal (P : Measure (Configuration d N)) [IsProbabilityMeasure P] :
    law hN hb hbound hM hL₁ hL₂ hμ hT P T = PrescribedReference.law hb hbound hM hL₁ hμ N P T := by
  letI : IsProbabilityMeasure (PrescribedReference.law hb hbound hM hL₁ hμ N P T) :=
    BrownianFlow.globalLaw_probability _ _ _ P hT
  rw [law_eq_composition hN hb hbound hM hL₁ hL₂ hμ hT P ⟨hT,le_rfl⟩,
    sub_self,BrownianParticle.globalLaw_initial]

theorem law_wassersteinSq_tendsto (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (t : Icc 0 T) :
    Tendsto (fun s : Icc 0 T => wassersteinSq (law hN hb hbound hM hL₁ hL₂ hμ hT P s)
      (law hN hb hbound hM hL₁ hL₂ hμ hT P t)) (𝓝 t) (𝓝 0) :=
  SwitchCurve.law_wassersteinSq_tendsto hN hb hbound hM hL₁ hL₂ _ _ _ hT P t

end SharpWasserstein.PrescribedSwitchCurve
