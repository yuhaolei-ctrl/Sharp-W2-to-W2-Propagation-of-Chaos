module

public import SharpWasserstein.Compat
public import SharpWasserstein.BrownianTimeTransport
public import SharpWasserstein.TransportTriangle
public import SharpWasserstein.PrescribedReference

@[expose] public section

/-! The genuine switch-time probability curve: first the prescribed reference
flow, then the interacting flow for the remaining time. Its endpoints are
actual diffusion laws. Differentiation and the sharp length estimate are
separate obligations, not hypotheses hidden in this construction. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace SharpWasserstein
namespace BrownianParticle

theorem law_time_wassersteinSq_le {d N : ℕ} {b : Position d → Position d → Position d}
    {M L₁ L₂ : ℝ} (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (s t : Icc 0 T) :
    wassersteinSq (law hN hb hbound hM hL₁ hL₂ hT μ t) (law hN hb hbound hM hL₁ hL₂ hT μ s) ≤
      ENNReal.ofReal (BrownianFlow.timeCost d N M s t) :=
  BrownianFlow.law_time_wassersteinSq_le
    (v := fun _ => particleDrift (N := N) b)
    ((particleDrift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (M := ⟨M,hM⟩) (fun _ x => particleDrift_norm_bound hN hbound hM x)
    (fun _ => particleDrift_lipschitz hN hb hbound hL₁ hL₂) hT μ s t

end BrownianParticle
namespace SwitchCurve

variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {v : ℝ → Configuration d N → Configuration d N} {A K : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hvb : ∀ t x, ‖v t x‖ ≤ A)
  (hvl : ∀ t, LipschitzWith K (v t)) {T : ℝ} (hT : 0 ≤ T)

def law (μ : Measure (Configuration d N)) (s : ℝ) : Measure (Configuration d N) :=
  BrownianParticle.law hN hb hbound hM hL₁ hL₂ hT
    (BrownianFlow.law hv hvb hvl hT μ s) (T-s)

theorem law_probability (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : s ∈ Icc 0 T) :
    IsProbabilityMeasure (law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ s) := by
  letI := BrownianFlow.law_probability hv hvb hvl hT μ hs
  exact BrownianParticle.law_probability hN hb hbound hM hL₁ hL₂ hT _
    ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩

theorem law_secondMoment (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (hμ : HasSecondMoment μ) {s : ℝ} (hs : s ∈ Icc 0 T) :
    HasSecondMoment (law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ s) := by
  letI := BrownianFlow.law_probability hv hvb hvl hT μ hs
  exact BrownianParticle.law_secondMoment hN hb hbound hM hL₁ hL₂ hT _
    (BrownianFlow.law_secondMoment hv hvb hvl hT μ hμ hs)
    ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩

theorem law_zero (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] :
    law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ 0 =
      BrownianParticle.law hN hb hbound hM hL₁ hL₂ hT μ T := by
  simp only [law,BrownianFlow.law_initial,sub_zero]

theorem law_terminal (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] :
    law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ T =
      BrownianFlow.law hv hvb hvl hT μ T := by
  letI := BrownianFlow.law_probability hv hvb hvl hT μ (show T ∈ Icc 0 T from ⟨hT,le_rfl⟩)
  simp only [law,sub_self,BrownianParticle.law_initial]

theorem law_root_modulus (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (s t : Icc 0 T) :
    wassersteinSq (law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ s)
      (law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ t) ^ (1/2 : ℝ) ≤
      (ENNReal.ofReal (Real.exp (Real.sqrt (2*d*(L₁^2+L₂^2))*T)^2) *
        ENNReal.ofReal (BrownianFlow.timeCost d N A t s)) ^ (1/2 : ℝ) +
      ENNReal.ofReal (BrownianFlow.timeCost d N M (T-t) (T-s)) ^ (1/2 : ℝ) := by
  let R := fun r => BrownianFlow.law hv hvb hvl hT μ r
  letI := BrownianFlow.law_probability hv hvb hvl hT μ s.property
  letI := BrownianFlow.law_probability hv hvb hvl hT μ t.property
  have hs : T-(s : ℝ) ∈ Icc 0 T := ⟨sub_nonneg.mpr s.property.2,sub_le_self _ s.property.1⟩
  have ht : T-(t : ℝ) ∈ Icc 0 T := ⟨sub_nonneg.mpr t.property.2,sub_le_self _ t.property.1⟩
  have hstability := BrownianParticle.law_wassersteinSq_le hN hb hbound hM hL₁ hL₂ hT
    (R s) (R t) hs
  have hfactor : ENNReal.ofReal (Real.exp (Real.sqrt (2*d*(L₁^2+L₂^2))*(T-s))^2) ≤
      ENNReal.ofReal (Real.exp (Real.sqrt (2*d*(L₁^2+L₂^2))*T)^2) := by
    apply ENNReal.ofReal_le_ofReal
    apply (sq_le_sq₀ (Real.exp_pos _).le (Real.exp_pos _).le).mpr
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hs.2 (Real.sqrt_nonneg _)
  have hfirst := hstability.trans (mul_le_mul' hfactor
    (BrownianFlow.law_time_wassersteinSq_le hv hvb hvl hT μ t s))
  have hsecond := BrownianParticle.law_time_wassersteinSq_le hN hb hbound hM hL₁ hL₂ hT
    (R t) ⟨T-t,ht⟩ ⟨T-s,hs⟩
  exact (wassersteinSq_root_triangle _
    (BrownianParticle.law hN hb hbound hM hL₁ hL₂ hT (R t) (T-s)) _).trans
      (add_le_add (ENNReal.rpow_le_rpow hfirst (by norm_num))
        (ENNReal.rpow_le_rpow hsecond (by norm_num)))

set_option maxHeartbeats 800000 in
theorem law_wassersteinSq_tendsto (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (t : Icc 0 T) :
    Tendsto (fun s : Icc 0 T => wassersteinSq
      (law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ s)
      (law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ t)) (𝓝 t) (𝓝 0) := by
  let C := ENNReal.ofReal (Real.exp (Real.sqrt (2*d*(L₁^2+L₂^2))*T)^2)
  have h₁ : Tendsto (fun s : Icc 0 T => ENNReal.ofReal (BrownianFlow.timeCost d N A t s))
      (𝓝 t) (𝓝 0) := by
    have hc : Continuous (fun s : Icc 0 T => ENNReal.ofReal (BrownianFlow.timeCost d N A t s)) :=
      ENNReal.continuous_ofReal.comp ((BrownianFlow.timeCost_continuous d N A).comp
        (continuous_const.prodMk continuous_subtype_val))
    simpa only [BrownianFlow.timeCost_self,ENNReal.ofReal_zero] using hc.tendsto t
  have h₂ : Tendsto (fun s : Icc 0 T => ENNReal.ofReal (BrownianFlow.timeCost d N M (T-t) (T-s)))
      (𝓝 t) (𝓝 0) := by
    have hc : Continuous (fun s : Icc 0 T => ENNReal.ofReal (BrownianFlow.timeCost d N M (T-t) (T-s))) :=
      ENNReal.continuous_ofReal.comp ((BrownianFlow.timeCost_continuous d N M).comp
        (continuous_const.prodMk (continuous_const.sub continuous_subtype_val)))
    simpa only [BrownianFlow.timeCost_self,ENNReal.ofReal_zero] using hc.tendsto t
  have h₁' : Tendsto (fun s : Icc 0 T => (C*ENNReal.ofReal (BrownianFlow.timeCost d N A t s)) ^ (1/2 : ℝ))
      (𝓝 t) (𝓝 0) := by
    have hm := ENNReal.Tendsto.const_mul h₁ (a := C) (Or.inr ENNReal.ofReal_ne_top)
    simpa only [mul_zero,ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1/2)] using
      hm.ennrpow_const (1/2 : ℝ)
  have h₂' : Tendsto (fun s : Icc 0 T => ENNReal.ofReal (BrownianFlow.timeCost d N M (T-t) (T-s)) ^ (1/2 : ℝ))
      (𝓝 t) (𝓝 0) := by
    simpa only [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1/2)] using h₂.ennrpow_const (1/2 : ℝ)
  have hz := h₁'.add h₂'
  rw [zero_add] at hz
  have hr : Tendsto (fun s : Icc 0 T => wassersteinSq
      (law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ s)
      (law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ t) ^ (1/2 : ℝ)) (𝓝 t) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz (fun _ => zero_le)
      (fun s => law_root_modulus hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ s t)
  simpa only [← ENNReal.rpow_mul,show (1/2 : ℝ)*2 = 1 by norm_num,ENNReal.rpow_one,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] using hr.ennrpow_const (2 : ℝ)

end SwitchCurve
end SharpWasserstein
