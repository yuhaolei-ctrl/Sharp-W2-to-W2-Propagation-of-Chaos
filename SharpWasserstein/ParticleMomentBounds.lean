module

public import SharpWasserstein.Compat
public import SharpWasserstein.BrownianParticle
public import SharpWasserstein.TransportConvergence

@[expose] public section

/-! Quantitative compact-time second-moment control for the actual constructed
particle laws. No maximal Brownian inequality is needed. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Interval

namespace SharpWasserstein

theorem productCost_add_zero_le {d N : ℕ} (x y : Configuration d N) :
    productCost (x+y) 0 ≤ 2 * productCost x 0 + 2 * productCost y 0 := by
  simp only [productCost, Pi.add_apply, Pi.zero_apply, sub_zero,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro a _
  nlinarith [sq_nonneg (x i a-y i a)]

theorem HasSecondMoment.integrable_cost {d N : ℕ} {μ : Measure (Configuration d N)}
    (hμ : HasSecondMoment μ) : Integrable (fun x => productCost x 0) μ := by
  refine ⟨(measurable_productCost.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun x => productCost_nonneg x 0))).mpr hμ

theorem FiniteAdditiveTrajectory.productCost_bound {d N : ℕ}
    {v : ℝ → Configuration d N → Configuration d N} {w X : ℝ → Configuration d N}
    {x : Configuration d N} {T t M : ℝ} (h : FiniteAdditiveTrajectory v w x T X)
    (hM : 0 ≤ M) (hb : ∀ s ∈ Icc 0 T, ∀ z, ‖v s z‖ ≤ M) (ht : t ∈ Icc 0 T) :
    productCost (X t) 0 ≤ 4 * productCost x 0 +
      4 * ((N : ℝ)*d*(M*t)^2) + 2 * productCost (w t) 0 := by
  let I := ∫ s in (0 : ℝ)..t, v s (X s)
  have hi : ‖I‖ ≤ M*t := by
    have hg := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := t) (f := fun s => v s (X s)) (fun s hs => by
        rw [uIoc_of_le ht.1] at hs
        exact hb s ⟨hs.1.le,hs.2.trans ht.2⟩ (X s))
    simpa [I,abs_of_nonneg ht.1] using hg
  have hcost : productCost I 0 ≤ (N : ℝ)*d*(M*t)^2 := by
    have hc := productCost_le_dimension_norm I 0
    simp only [sub_zero] at hc
    exact hc.trans (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM ht.1)).mpr hi) (by positivity))
  rw [h.equation t ht]
  have h1 := productCost_add_zero_le (x+I) (w t)
  have h2 := productCost_add_zero_le x I
  change productCost (x+I+w t) 0 ≤ _
  nlinarith

namespace BrownianNoise

theorem configurationLaw_cost_integrable {d N : ℕ} {T : ℝ} (t : Icc 0 T) :
    Integrable (fun w : C(Icc 0 T, Configuration d N) => productCost (w t) 0)
      (configurationLaw d N T) := by
  simp only [productCost,Pi.zero_apply,sub_zero]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ =>
    (((configurationLaw_memLp t 2 (by norm_num)).eval i).eval a).integrable_sq))

theorem configurationLaw_secondMoment_value {d N : ℕ} {T : ℝ} (t : Icc 0 T) :
    (∫⁻ w : C(Icc 0 T, Configuration d N), ENNReal.ofReal (productCost (w t) 0)
      ∂configurationLaw d N T) = ENNReal.ofReal ((N : ℝ)*d*(2*(t : ℝ))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (configurationLaw_cost_integrable t)
    (Eventually.of_forall (fun w => productCost_nonneg (w t) 0)),configurationLaw_momentIntegral]

end BrownianNoise

namespace BrownianParticle

variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {T : ℝ} (hT : 0 ≤ T)

theorem randomMap_momentIntegral_le (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (hμ : HasSecondMoment μ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (F : Configuration d N × C(Icc 0 T, Configuration d N) → Configuration d N)
    (hF : Measurable F)
    (hF₂ : HasSecondMoment (Measure.map F (μ.prod (BrownianNoise.configurationLaw d N T))))
    (hpoint : ∀ p, productCost (F p) 0 ≤ 4 * productCost p.1 0 +
      4 * ((N : ℝ)*d*(M*t)^2) + 2 * productCost (p.2 ⟨t, ht⟩) 0) :
    (∫ x, productCost x 0 ∂Measure.map F (μ.prod (BrownianNoise.configurationLaw d N T))) ≤
      4 * (∫ x, productCost x 0 ∂μ) + 4 * ((N : ℝ)*d*(M*t)^2) +
        2 * ((N : ℝ)*d*(2*t)) := by
  let ξ := BrownianNoise.configurationLaw d N T
  let P := μ.prod ξ
  have hm : Measurable (fun x : Configuration d N => productCost x 0) := by
    unfold productCost
    fun_prop
  have hx : Integrable (fun p : Configuration d N × C(Icc 0 T, Configuration d N) =>
      productCost p.1 0) P :=
    ((measurePreserving_fst (μ := μ) (ν := ξ)).integrable_comp
      hμ.integrable_cost.aestronglyMeasurable).mpr hμ.integrable_cost
  have hw : Integrable (fun p : Configuration d N × C(Icc 0 T, Configuration d N) =>
      productCost (p.2 ⟨t, ht⟩) 0) P :=
    ((measurePreserving_snd (μ := μ) (ν := ξ)).integrable_comp
      (BrownianNoise.configurationLaw_cost_integrable ⟨t, ht⟩).aestronglyMeasurable).mpr
      (BrownianNoise.configurationLaw_cost_integrable ⟨t, ht⟩)
  have hcost : Integrable (fun p => productCost (F p) 0) P := by
    apply (integrable_map_measure hm.aestronglyMeasurable hF.aemeasurable).mp
    exact hF₂.integrable_cost
  have hc : Integrable (fun _ : Configuration d N × C(Icc 0 T, Configuration d N) =>
      4 * ((N : ℝ)*d*(M*t)^2)) P := integrable_const _
  have hac : Integrable (fun p : Configuration d N × C(Icc 0 T, Configuration d N) =>
      4 * productCost p.1 0 + 4 * ((N : ℝ)*d*(M*t)^2)) P := (hx.const_mul 4).add hc
  have hineq : (∫ p, productCost (F p) 0 ∂P) ≤
      ∫ p : Configuration d N × C(Icc 0 T, Configuration d N),
        4 * productCost p.1 0 + 4 * ((N : ℝ)*d*(M*t)^2) + 2 * productCost (p.2 ⟨t, ht⟩) 0 ∂P := by
    apply integral_mono hcost (((hx.const_mul 4).add hc).add (hw.const_mul 2))
    intro p
    change productCost (F p) 0 ≤ 4 * productCost p.1 0 + 4 * ((N : ℝ)*d*(M*t)^2) +
      2 * productCost (p.2 ⟨t, ht⟩) 0
    exact hpoint p
  have hex : (∫ p, productCost p.1 0 ∂P) = ∫ x, productCost x 0 ∂μ :=
    (measurePreserving_fst (μ := μ) (ν := ξ)).hasLaw.integral_comp
      hμ.integrable_cost.aestronglyMeasurable
  have hew : (∫ p : Configuration d N × C(Icc 0 T, Configuration d N),
      productCost (p.2 ⟨t, ht⟩) 0 ∂P) = (N : ℝ)*d*(2*t) := by
    exact ((measurePreserving_snd (μ := μ) (ν := ξ)).hasLaw.integral_comp
      (BrownianNoise.configurationLaw_cost_integrable ⟨t, ht⟩).aestronglyMeasurable).trans
      (BrownianNoise.configurationLaw_momentIntegral ⟨t, ht⟩)
  change (∫ x, productCost x 0 ∂Measure.map F P) ≤ _
  rw [integral_map hF.aemeasurable hm.aestronglyMeasurable]
  calc
    _ ≤ _ := hineq
    _ = _ := by
      rw [integral_add hac (hw.const_mul 2),
        integral_add (hx.const_mul 4) hc]
      simp_rw [integral_const_mul]
      rw [integral_const,hex,hew]
      simp [P,ξ]

theorem law_momentIntegral_le (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (hμ : HasSecondMoment μ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ x, productCost x 0 ∂law hN hb hbound hM hL₁ hL₂ hT μ t) ≤
      4 * (∫ x, productCost x 0 ∂μ) + 4 * ((N : ℝ)*d*(M*t)^2) +
        2 * ((N : ℝ)*d*(2*t)) := by
  apply randomMap_momentIntegral_le μ hμ ht
    (fun p => ParticleFlow.solution hN hb hbound hM hL₁ hL₂ hT p.1 p.2 t)
    (ParticleFlow.solution_measurable hN hb hbound hM hL₁ hL₂ hT ht)
    (law_secondMoment hN hb hbound hM hL₁ hL₂ hT μ hμ ht)
  intro p
  have hp := (ParticleFlow.solution_trajectory hN hb hbound hM hL₁ hL₂ hT p.1 p.2).productCost_bound
    hM (fun _ _ x => particleDrift_norm_bound hN hbound hM x) ht
  simpa only [BoundedFlow.noiseExtension,projIcc_of_mem _ ht] using hp

theorem law_momentBound (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (hμ : HasSecondMoment μ) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ t ∈ Icc 0 T,
      (∫⁻ x, ENNReal.ofReal (productCost x 0) ∂law hN hb hbound hM hL₁ hL₂ hT μ t) ≤ C := by
  refine ⟨ENNReal.ofReal (4 * (∫ x, productCost x 0 ∂μ) +
    4 * ((N : ℝ)*d*(M*T)^2) + 2 * ((N : ℝ)*d*(2*T))), ENNReal.ofReal_lt_top, ?_⟩
  intro t ht
  rw [← ofReal_integral_eq_lintegral_ofReal
    (law_secondMoment hN hb hbound hM hL₁ hL₂ hT μ hμ ht).integrable_cost
    (Eventually.of_forall (fun x => productCost_nonneg x 0))]
  apply ENNReal.ofReal_le_ofReal
  refine (law_momentIntegral_le hN hb hbound hM hL₁ hL₂ hT μ hμ ht).trans ?_
  have hsq : (M*t)^2 ≤ (M*T)^2 := by
    apply (sq_le_sq₀ (mul_nonneg hM ht.1) (mul_nonneg hM hT)).mpr
    exact mul_le_mul_of_nonneg_left ht.2 hM
  have ha : (N : ℝ)*d*(M*t)^2 ≤ (N : ℝ)*d*(M*T)^2 :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have hb' : (N : ℝ)*d*(2*t) ≤ (N : ℝ)*d*(2*T) :=
    mul_le_mul_of_nonneg_left (by linarith [ht.2]) (by positivity)
  linarith

end BrownianParticle
end SharpWasserstein
