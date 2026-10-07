module

public import SharpWasserstein.Compat
public import SharpWasserstein.SwitchCurveProperties

@[expose] public section

/-! Narrow continuity of the actual switch law, proved by a common probability
space with two independent Brownian path inputs. No regularity of densities is
required. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal
namespace SharpWasserstein.SwitchCurve
variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {v : ℝ → Configuration d N → Configuration d N} {A K : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hvb : ∀ t x, ‖v t x‖ ≤ A)
  (hvl : ∀ t, LipschitzWith K (v t)) {T : ℝ} (hT : 0 ≤ T)

def jointEndpoint (s : Icc 0 T)
    (p : (Configuration d N × C(Icc 0 T,Configuration d N)) × C(Icc 0 T,Configuration d N)) :
    Configuration d N :=
  ParticleFlow.solution hN hb hbound hM hL₁ hL₂ hT
    (BoundedFlow.flow hv hvb hvl hT p.1.1 p.1.2 s) p.2 (T-s)

theorem jointEndpoint_continuous :
    Continuous (fun p : Icc 0 T × ((Configuration d N × C(Icc 0 T,Configuration d N)) × C(Icc 0 T,Configuration d N)) => jointEndpoint hN hb hbound hM hL₁ hL₂ hv hvb hvl hT p.1 p.2) := by
  have hr : Continuous (fun s : Icc 0 T => (⟨T-s,⟨sub_nonneg.mpr s.property.2,
      sub_le_self _ s.property.1⟩⟩ : Icc 0 T)) :=
    (continuous_const.sub continuous_subtype_val).subtype_mk _
  have hf : Continuous (fun p : Icc 0 T × ((Configuration d N × C(Icc 0 T,Configuration d N)) × C(Icc 0 T,Configuration d N)) =>
      BoundedFlow.flow hv hvb hvl hT p.2.1.1 p.2.1.2 p.1) :=
    (BoundedFlow.flow_joint_continuous hv hvb hvl hT).comp
      (continuous_snd.fst.prodMk continuous_fst)
  exact (BoundedFlow.flow_joint_continuous (v := fun _ : ℝ => particleDrift (N := N) b)
    ((particleDrift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (M := NNReal.mk M hM) (fun _ => particleDrift_norm_bound hN hbound hM)
    (fun _ => particleDrift_lipschitz hN hb hbound hL₁ hL₂) hT).comp
      ((hf.prodMk continuous_snd.snd).prodMk (hr.comp continuous_fst))

theorem law_eq_jointEndpoint (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (s : Icc 0 T) :
    law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ s =
      ((μ.prod (BrownianNoise.configurationLaw d N T)).prod
        (BrownianNoise.configurationLaw d N T)).map
        (jointEndpoint hN hb hbound hM hL₁ hL₂ hv hvb hvl hT s) := by
  have hf := (BoundedFlow.flow_continuous hv hvb hvl hT s.property).measurable
  have hg := ParticleFlow.solution_measurable hN hb hbound hM hL₁ hL₂ hT
    ⟨sub_nonneg.mpr s.property.2,sub_le_self _ s.property.1⟩
  unfold law BrownianParticle.law ParticleFlow.law randomMapLaw BrownianFlow.law
  have he := Measure.map_prod_map (μ.prod (BrownianNoise.configurationLaw d N T))
    (BrownianNoise.configurationLaw d N T) hf measurable_id
  simp only [Measure.map_id] at he
  rw [he]
  rw [Measure.map_map hg (hf.prodMap measurable_id)]
  rfl

def probabilityCurve (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (s : Icc 0 T) : ProbabilityMeasure (Configuration d N) :=
  ⟨law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ s,
    law_probability hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ s.property⟩

theorem probabilityCurve_continuous (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] :
    Continuous (probabilityCurve hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ) := by
  have hc := jointEndpoint_continuous hN hb hbound hM hL₁ hL₂ hv hvb hvl hT
  have hp := randomProbabilityLaw_continuous
    ((μ.prod (BrownianNoise.configurationLaw d N T)).prod (BrownianNoise.configurationLaw d N T))
    (jointEndpoint hN hb hbound hM hL₁ hL₂ hv hvb hvl hT)
    (fun s => (hc.comp (continuous_const.prodMk continuous_id)).measurable)
    (Eventually.of_forall fun p => hc.comp (continuous_id.prodMk continuous_const))
  convert hp using 1
  funext s
  apply Subtype.ext
  exact law_eq_jointEndpoint hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ s

end SharpWasserstein.SwitchCurve
