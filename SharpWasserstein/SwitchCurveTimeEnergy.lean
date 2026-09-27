import SharpWasserstein.SwitchCurveNarrow
import SharpWasserstein.BrownianFlowTimeEnergy

/-! Actual common-label mean-square continuity of the switch curve. The
coupling uses the same two Brownian path inputs at every switch time and
does not invoke a measurable choice of optimal transport plans. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace SharpWasserstein.SwitchCurve

theorem integral_three_terms {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {g w : Ω → ℝ} (hg : Integrable g P) (hw : Integrable w P)
    (A B C : ℝ) :
    (∫ p,A*g p+B+C*w p ∂P) = A*(∫ p,g p ∂P)+B+C*(∫ p,w p ∂P) := by
  rw [integral_add (f := fun p => A*g p+B) (g := fun p => C*w p)
      ((hg.const_mul A).add (integrable_const B)) (hw.const_mul C),
    integral_add (f := fun p => A*g p) (g := fun _ => B)
      (hg.const_mul A) (integrable_const B),integral_const_mul,integral_const_mul,
    integral_const]
  simp only [probReal_univ,one_smul]

theorem productCost_triangle_sq {d N : ℕ} (x y z : Configuration d N) :
    productCost x z ≤ 2*productCost x y+2*productCost y z := by
  unfold productCost
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro a _
  nlinarith [sq_nonneg ((x i a-y i a)-(y i a-z i a))]

variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {v : ℝ → Configuration d N → Configuration d N} {A K : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hvb : ∀ t x, ‖v t x‖ ≤ A)
  (hvl : ∀ t,LipschitzWith K (v t)) {T : ℝ} (hT : 0 ≤ T)

def jointTimeCost (s t : ℝ) : ℝ :=
  2*Real.exp (Real.sqrt (2*d*(L₁^2+L₂^2))*T)^2*BrownianFlow.timeCost d N A t s+
    2*BrownianFlow.timeCost d N M (T-t) (T-s)

theorem jointEndpoint_cost_le (s t : Icc 0 T)
    (p : (Configuration d N × C(Icc 0 T,Configuration d N)) × C(Icc 0 T,Configuration d N)) :
    productCost (jointEndpoint hN hb hbound hM hL₁ hL₂ hv hvb hvl hT s p)
      (jointEndpoint hN hb hbound hM hL₁ hL₂ hv hvb hvl hT t p) ≤
    2*Real.exp (Real.sqrt (2*d*(L₁^2+L₂^2))*T)^2*
      productCost (BoundedFlow.flow hv hvb hvl hT p.1.1 p.1.2 s)
        (BoundedFlow.flow hv hvb hvl hT p.1.1 p.1.2 t)+
      4*((N:ℝ)*d*(M*|(T-(s:ℝ))-(T-t)|)^2)+
        4*productCost (p.2 ⟨T-s,⟨sub_nonneg.mpr s.property.2,sub_le_self _ s.property.1⟩⟩)
          (p.2 ⟨T-t,⟨sub_nonneg.mpr t.property.2,sub_le_self _ t.property.1⟩⟩) := by
  let X := fun r : ℝ => BoundedFlow.flow hv hvb hvl hT p.1.1 p.1.2 r
  let Y := fun x r => ParticleFlow.solution hN hb hbound hM hL₁ hL₂ hT x p.2 r
  have hs : T-(s:ℝ) ∈ Icc 0 T := ⟨sub_nonneg.mpr s.property.2,sub_le_self _ s.property.1⟩
  have ht : T-(t:ℝ) ∈ Icc 0 T := ⟨sub_nonneg.mpr t.property.2,sub_le_self _ t.property.1⟩
  have hfirst := particleTrajectory_productCost_le hN hb hbound hL₁ hL₂
    (ParticleFlow.solution_trajectory hN hb hbound hM hL₁ hL₂ hT (X s) p.2)
    (ParticleFlow.solution_trajectory hN hb hbound hM hL₁ hL₂ hT (X t) p.2) hs
  have he : Real.exp (Real.sqrt (2*d*(L₁^2+L₂^2))*(T-s))^2 ≤
      Real.exp (Real.sqrt (2*d*(L₁^2+L₂^2))*T)^2 := by
    apply (sq_le_sq₀ (Real.exp_pos _).le (Real.exp_pos _).le).mpr
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 (Real.sqrt_nonneg _))
  have hfirst' := hfirst.trans (mul_le_mul_of_nonneg_right he (productCost_nonneg _ _))
  have hsecond := (ParticleFlow.solution_trajectory hN hb hbound hM hL₁ hL₂ hT (X t) p.2).increment_productCost_le
    hM (fun _ _ => particleDrift_norm_bound hN hbound hM) ht hs
  simp only [BoundedFlow.noiseExtension,projIcc_of_mem _ ht,projIcc_of_mem _ hs] at hsecond
  have hh := productCost_triangle_sq (Y (X s) (T-s)) (Y (X t) (T-s)) (Y (X t) (T-t))
  change productCost (Y (X s) (T-s)) (Y (X t) (T-t)) ≤ _
  dsimp only [Y] at hh ⊢
  dsimp only [X] at hfirst' hsecond hh ⊢
  linarith

set_option maxHeartbeats 1200000 in
theorem jointEndpoint_energy_le (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (s t : Icc 0 T) :
    Integrable (fun p => productCost
      (jointEndpoint hN hb hbound hM hL₁ hL₂ hv hvb hvl hT s p)
      (jointEndpoint hN hb hbound hM hL₁ hL₂ hv hvb hvl hT t p))
      ((μ.prod (BrownianNoise.configurationLaw d N T)).prod
        (BrownianNoise.configurationLaw d N T)) ∧
    (∫ p,productCost
      (jointEndpoint hN hb hbound hM hL₁ hL₂ hv hvb hvl hT s p)
      (jointEndpoint hN hb hbound hM hL₁ hL₂ hv hvb hvl hT t p)
      ∂((μ.prod (BrownianNoise.configurationLaw d N T)).prod
        (BrownianNoise.configurationLaw d N T))) ≤ jointTimeCost (d := d) (N := N)
          (M := M) (L₁ := L₁) (L₂ := L₂) (A := A) (T := T) s t := by
  let ξ := BrownianNoise.configurationLaw d N T
  let Λ := (μ.prod ξ).prod ξ
  let R := Real.exp (Real.sqrt (2*d*(L₁^2+L₂^2))*T)^2
  let τs : Icc 0 T := ⟨T-s,⟨sub_nonneg.mpr s.property.2,sub_le_self _ s.property.1⟩⟩
  let τt : Icc 0 T := ⟨T-t,⟨sub_nonneg.mpr t.property.2,sub_le_self _ t.property.1⟩⟩
  let g := fun p : Configuration d N × C(Icc 0 T,Configuration d N) =>
    productCost (BoundedFlow.flow hv hvb hvl hT p.1 p.2 s)
      (BoundedFlow.flow hv hvb hvl hT p.1 p.2 t)
  let w := fun p : C(Icc 0 T,Configuration d N) => productCost (p τs) (p τt)
  have hg := BrownianFlow.flow_increment_energy_le hv hvb hvl hT μ t s
  have hgf : Integrable (fun p => g p.1) Λ :=
    ((measurePreserving_fst (μ := μ.prod ξ) (ν := ξ)).integrable_comp
      hg.1.aestronglyMeasurable).mpr hg.1
  have hw := BrownianNoise.configurationLaw_increment_cost_integrable (d := d) (N := N) τt τs
  have hws : Integrable (fun p => w p.2) Λ :=
    ((measurePreserving_snd (μ := μ.prod ξ) (ν := ξ)).integrable_comp
      hw.aestronglyMeasurable).mpr hw
  have hge : (∫ p,g p.1 ∂Λ) ≤ BrownianFlow.timeCost d N A t s := by
    exact ((measurePreserving_fst (μ := μ.prod ξ) (ν := ξ)).hasLaw.integral_comp
      hg.1.aestronglyMeasurable).le.trans hg.2
  have hwe : (∫ p,w p.2 ∂Λ) = (N:ℝ)*d*(2*|((τs:ℝ)-τt)|) :=
    ((measurePreserving_snd (μ := μ.prod ξ) (ν := ξ)).hasLaw.integral_comp
      hw.aestronglyMeasurable).trans
      (BrownianNoise.configurationLaw_increment_momentIntegral τt τs)
  let B := 4*((N:ℝ)*d*(M*|((τs:ℝ)-τt)|)^2)
  have hu : Integrable (fun p => 2*R*g p.1+B+4*w p.2) Λ :=
    ((hgf.const_mul (2*R)).add (integrable_const B)).add (hws.const_mul 4)
  have hc := jointEndpoint_continuous hN hb hbound hM hL₁ hL₂ hv hvb hvl hT
  have hk : Integrable (fun p => productCost
      (jointEndpoint hN hb hbound hM hL₁ hL₂ hv hvb hvl hT s p)
      (jointEndpoint hN hb hbound hM hL₁ hL₂ hv hvb hvl hT t p)) Λ := by
    refine hu.mono' (measurable_productCost.comp
      ((hc.comp (continuous_const.prodMk continuous_id)).measurable.prodMk
        (hc.comp (continuous_const.prodMk continuous_id)).measurable)).aestronglyMeasurable ?_
    exact Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (productCost_nonneg _ _)]
      exact jointEndpoint_cost_le hN hb hbound hM hL₁ hL₂ hv hvb hvl hT s t p
  refine ⟨hk,?_⟩
  calc
    _ ≤ ∫ p,2*R*g p.1+B+4*w p.2 ∂Λ :=
      integral_mono hk hu (jointEndpoint_cost_le hN hb hbound hM hL₁ hL₂ hv hvb hvl hT s t)
    _ = 2*R*(∫ p,g p.1 ∂Λ)+B+4*((N:ℝ)*d*(2*|((τs:ℝ)-τt)|)) := by
      exact (integral_three_terms Λ hgf hws (2*R) B 4).trans (by rw [hwe])
    _ ≤ 2*R*BrownianFlow.timeCost d N A t s+B+4*((N:ℝ)*d*(2*|((τs:ℝ)-τt)|)) := by
      gcongr
    _ = _ := by
      dsimp only [jointTimeCost,BrownianFlow.timeCost,R,B,τs,τt]
      ring

theorem jointEndpoint_cost_tendsto (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (t : Icc 0 T) :
    Tendsto (fun s : Icc 0 T => ∫⁻ p,ENNReal.ofReal (productCost
      (jointEndpoint hN hb hbound hM hL₁ hL₂ hv hvb hvl hT s p)
      (jointEndpoint hN hb hbound hM hL₁ hL₂ hv hvb hvl hT t p))
      ∂((μ.prod (BrownianNoise.configurationLaw d N T)).prod
        (BrownianNoise.configurationLaw d N T))) (𝓝 t) (𝓝 0) := by
  have hc : Continuous (fun s : Icc 0 T => ENNReal.ofReal
      (jointTimeCost (d := d) (N := N) (M := M) (L₁ := L₁) (L₂ := L₂)
        (A := A) (T := T) s t)) := by
    apply ENNReal.continuous_ofReal.comp
    unfold jointTimeCost BrownianFlow.timeCost
    fun_prop
  have ht : Tendsto (fun s : Icc 0 T => ENNReal.ofReal
      (jointTimeCost (d := d) (N := N) (M := M) (L₁ := L₁) (L₂ := L₂)
        (A := A) (T := T) s t)) (𝓝 t) (𝓝 0) := by
    simpa only [jointTimeCost,BrownianFlow.timeCost_self,mul_zero,add_zero,
      ENNReal.ofReal_zero] using hc.tendsto t
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro s
  have he := jointEndpoint_energy_le hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ s t
  exact (ofReal_integral_eq_lintegral_ofReal he.1
    (Eventually.of_forall fun p => productCost_nonneg _ _)).symm.le.trans
      (ENNReal.ofReal_le_ofReal he.2)

theorem jointEndpoint_marginal_cost_tendsto (μ : Measure (Configuration d N))
    [IsProbabilityMeasure μ] {k : ℕ} (hk : k ≤ N) (t : Icc 0 T) :
    Tendsto (fun s : Icc 0 T => ∫⁻ p,ENNReal.ofReal (productCost
      (restrictCoordinates hk (jointEndpoint hN hb hbound hM hL₁ hL₂ hv hvb hvl hT s p))
      (restrictCoordinates hk (jointEndpoint hN hb hbound hM hL₁ hL₂ hv hvb hvl hT t p)))
      ∂((μ.prod (BrownianNoise.configurationLaw d N T)).prod
        (BrownianNoise.configurationLaw d N T))) (𝓝 t) (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (jointEndpoint_cost_tendsto hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ t) (fun _ => zero_le)
  intro s
  exact lintegral_mono fun p => ENNReal.ofReal_le_ofReal (productCost_restrict_le hk _ _)

end SharpWasserstein.SwitchCurve
