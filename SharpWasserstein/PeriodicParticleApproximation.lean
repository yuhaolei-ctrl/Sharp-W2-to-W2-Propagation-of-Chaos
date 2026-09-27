import SharpWasserstein.PeriodicKernelBounds
import SharpWasserstein.DriftFlowConvergence
import SharpWasserstein.BrownianParticle

/-! Actual periodic particle approximations and their quadratic transport limit.
The zeroth and first derivative constants are uniform in the period and in N. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology BigOperators
namespace SharpWasserstein.PeriodicParticle

def interaction {d : ℕ} (b : Position d → Position d → Position d) (n : ℕ) :=
  SinePeriodization.kernel ((n : ℝ)+1) b

variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}

theorem interaction_smooth (hb : BoundedSmoothKernel b) (n : ℕ) :
    BoundedSmoothKernel (interaction b n) :=
  SinePeriodization.kernel_boundedSmooth (by positivity) hb.smooth

theorem interaction_bounds (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (n : ℕ) :
    KernelBounds (interaction b n) M L₁ L₂ :=
  SinePeriodization.kernel_bounds (by positivity) hb hbound hL₁ hL₂

theorem particleDrift_kernel_error {c : Position d → Position d → Position d}
    (hN : 0 < N) {δ : ℝ} (hδ : 0 ≤ δ) (x : Configuration d N)
    (hc : ∀ i j, ‖c (x i) (x j)-b (x i) (x j)‖ ≤ δ) :
    ‖particleDrift c x-particleDrift b x‖ ≤ δ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply (pi_norm_le_iff_of_nonneg hδ).mpr
  intro i
  change ‖(N : ℝ)⁻¹ • ∑ j, c (x i) (x j)-(N : ℝ)⁻¹ • ∑ j, b (x i) (x j)‖ ≤ δ
  rw [← smul_sub,← Finset.sum_sub_distrib,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hNr)]
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ j, ‖c (x i) (x j)-b (x i) (x j)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (N : ℝ)⁻¹ * ∑ _j : Fin N, δ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hc i j)) (by positivity)
    _ = δ := by simp [hNr.ne']

theorem drift_error (hN : 0 < N) (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    {A : ℝ} (hA : 0 ≤ A) (n : ℕ) (x : Configuration d N) (hx : ‖x‖ ≤ A) :
    ‖particleDrift (interaction b n) x-particleDrift b x‖ ≤
      (L₁+L₂)*(A^3/(6*((n : ℝ)+1)^2)) := by
  apply particleDrift_kernel_error hN (by positivity)
  intro i j
  exact SinePeriodization.kernel_error (by positivity) hA hb hbound hL₁ hL₂ _ _
    ((norm_le_pi_norm x i).trans hx) ((norm_le_pi_norm x j).trans hx)

theorem drift_uniformOn_ball (hN : 0 < N) (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    {A : ℝ} (hA : 0 ≤ A) :
    TendstoUniformlyOn (fun n => particleDrift (N := N) (interaction b n))
      (particleDrift b) atTop (Metric.ball 0 A) := by
  have hz : Tendsto (fun n : ℕ => ((L₁+L₂)*A^3/6)*(1/((n : ℝ)+1))^2)
      atTop (𝓝 0) := by
    simpa using ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).const_mul ((L₁+L₂)*A^3/6)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hz.eventually (gt_mem_nhds hε)] with n hn x hx
  have hxn : ‖x‖ ≤ A := (by simpa only [Metric.mem_ball,dist_zero_right] using hx : ‖x‖ < A).le
  calc
    dist (particleDrift b x) (particleDrift (interaction b n) x) =
        ‖particleDrift (interaction b n) x-particleDrift b x‖ := by rw [dist_eq_norm,norm_sub_rev]
    _ ≤ (L₁+L₂)*(A^3/(6*((n : ℝ)+1)^2)) := drift_error hN hb hbound hL₁ hL₂ hA n x hxn
    _ = ((L₁+L₂)*A^3/6)*(1/((n : ℝ)+1))^2 := by field_simp
    _ < ε := hn

theorem drift_locallyUniform (hN : 0 < N) (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    TendstoLocallyUniformly (fun n => particleDrift (N := N) (interaction b n))
      (particleDrift b) atTop := by
  apply tendstoLocallyUniformly_of_forall_exists_nhds
  intro x
  refine ⟨Metric.ball 0 (‖x‖+1),Metric.isOpen_ball.mem_nhds ?_,
    drift_uniformOn_ball hN hb hbound hL₁ hL₂ (by positivity)⟩
  simp only [Metric.mem_ball,dist_zero_right]
  linarith

set_option maxHeartbeats 800000 in
theorem law_wassersteinSq_tendsto (hN : 0 < N) (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂) (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    {T : ℝ} [MeasurableSpace C(Icc 0 T,Configuration d N)]
    [BorelSpace C(Icc 0 T,Configuration d N)] (hT : 0 ≤ T)
    (μ : Measure (Configuration d N)) (ξ : Measure C(Icc 0 T,Configuration d N))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ξ] {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => wassersteinSq
      (ParticleFlow.law hN (interaction_smooth hb n) (interaction_bounds hb hbound hL₁ hL₂ n)
        hM hL₁ hL₂ hT μ ξ t)
      (ParticleFlow.law hN hb hbound hM hL₁ hL₂ hT μ ξ t)) atTop (𝓝 0) := by
  let P : ProbabilityMeasure (Configuration d N × C(Icc 0 T,Configuration d N)) :=
    ⟨μ.prod ξ,inferInstance⟩
  have hul (n : ℕ) : LipschitzWith ⟨L₁+L₂,add_nonneg hL₁ hL₂⟩
      (particleDrift (N := N) (interaction b n)) :=
    particleDrift_lipschitz hN (interaction_smooth hb n)
      (interaction_bounds hb hbound hL₁ hL₂ n) hL₁ hL₂
  have hvl := particleDrift_lipschitz hN hb hbound hL₁ hL₂
  have hd : TendstoLocallyUniformly
      (fun n => Function.uncurry (fun _ : ℝ => particleDrift (N := N) (interaction b n)))
      (Function.uncurry (fun _ : ℝ => particleDrift b)) atTop :=
    (drift_locallyUniform hN hb hbound hL₁ hL₂).comp Prod.snd continuous_snd
  have he := BoundedFlow.flow_drift_wassersteinSq_tendsto
    (d := d) (N := N) (M := ⟨M,hM⟩) (K := ⟨L₁+L₂,add_nonneg hL₁ hL₂⟩)
    (u := fun n _ => particleDrift (interaction b n)) (v := fun _ => particleDrift b)
    (fun n => (hul n).continuous.comp continuous_snd)
    (fun n _ x => particleDrift_norm_bound hN (interaction_bounds hb hbound hL₁ hL₂ n) hM x)
    (fun n _ => hul n) (hvl.continuous.comp continuous_snd)
    (fun _ x => particleDrift_norm_bound hN hbound hM x) (fun _ => hvl) hT hd P ht
  change Tendsto (fun n => wassersteinSq
    (ParticleFlow.law hN (interaction_smooth hb n) (interaction_bounds hb hbound hL₁ hL₂ n)
      hM hL₁ hL₂ hT μ ξ t)
    (ParticleFlow.law hN hb hbound hM hL₁ hL₂ hT μ ξ t)) atTop (𝓝 0) at he
  exact he

theorem brownianLaw_wassersteinSq_tendsto (hN : 0 < N) (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂) (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    {T : ℝ} (hT : 0 ≤ T) (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => wassersteinSq
      (BrownianParticle.law hN (interaction_smooth hb n) (interaction_bounds hb hbound hL₁ hL₂ n)
        hM hL₁ hL₂ hT μ t)
      (BrownianParticle.law hN hb hbound hM hL₁ hL₂ hT μ t)) atTop (𝓝 0) :=
  law_wassersteinSq_tendsto hN hb hbound hM hL₁ hL₂ hT μ
    (BrownianNoise.configurationLaw d N T) ht

end SharpWasserstein.PeriodicParticle
