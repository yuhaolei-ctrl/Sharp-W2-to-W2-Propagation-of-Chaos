module

public import SharpWasserstein.Compat
public import SharpWasserstein.BrownianTimeMoments
public import SharpWasserstein.BrownianFlow

@[expose] public section

/-! A quantitative time modulus for the actual Brownian flow law, measured
with the unnormalized Euclidean quadratic transport cost. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace SharpWasserstein.BrownianFlow

def timeCost (d N : ℕ) (M s t : ℝ) : ℝ :=
  2*((N : ℝ)*d*(M*|t-s|)^2)+4*((N : ℝ)*d*|t-s|)

theorem timeCost_nonneg (d N : ℕ) (M s t : ℝ) : 0 ≤ timeCost d N M s t := by
  unfold timeCost
  positivity

theorem timeCost_continuous (d N : ℕ) (M : ℝ) :
    Continuous (fun p : ℝ × ℝ => timeCost d N M p.1 p.2) := by
  unfold timeCost
  fun_prop

@[simp] theorem timeCost_self (d N : ℕ) (M t : ℝ) : timeCost d N M t t = 0 := by
  simp [timeCost]

variable {d N : ℕ} {v : ℝ → Configuration d N → Configuration d N} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
  (hl : ∀ t, LipschitzWith K (v t))

theorem law_time_wassersteinSq_le {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (s t : Icc 0 T) :
    wassersteinSq (law hv hb hl hT μ t) (law hv hb hl hT μ s) ≤
      ENNReal.ofReal (timeCost d N M s t) := by
  let ξ := BrownianNoise.configurationLaw d N T
  let P := μ.prod ξ
  let F := fun p : Configuration d N × C(Icc 0 T,Configuration d N) =>
    BoundedFlow.flow hv hb hl hT p.1 p.2 t
  let G := fun p : Configuration d N × C(Icc 0 T,Configuration d N) =>
    BoundedFlow.flow hv hb hl hT p.1 p.2 s
  have hF : Measurable F := (BoundedFlow.flow_continuous hv hb hl hT t.property).measurable
  have hG : Measurable G := (BoundedFlow.flow_continuous hv hb hl hT s.property).measurable
  have hw : Integrable (fun p : Configuration d N × C(Icc 0 T,Configuration d N) =>
      productCost (p.2 t) (p.2 s)) P :=
    ((measurePreserving_snd (μ := μ) (ν := ξ)).integrable_comp
      (BrownianNoise.configurationLaw_increment_cost_integrable s t).aestronglyMeasurable).mpr
      (BrownianNoise.configurationLaw_increment_cost_integrable s t)
  have hu : Integrable (fun p : Configuration d N × C(Icc 0 T,Configuration d N) =>
      2*((N : ℝ)*d*((M : ℝ)*|(t : ℝ)-s|)^2)+2*productCost (p.2 t) (p.2 s)) P :=
    (integrable_const _).add (hw.const_mul 2)
  have hp (p : Configuration d N × C(Icc 0 T,Configuration d N)) :
      productCost (F p) (G p) ≤
        2*((N : ℝ)*d*((M : ℝ)*|(t : ℝ)-s|)^2)+2*productCost (p.2 t) (p.2 s) := by
    have he := (BoundedFlow.flow_trajectory hv hb hl hT p.1 p.2).increment_productCost_le
      M.coe_nonneg (fun r _ z => hb r z) s.property t.property
    simpa only [F,G,BoundedFlow.noiseExtension,projIcc_of_mem _ s.property,
      projIcc_of_mem _ t.property] using he
  have hi : Integrable (fun p => productCost (F p) (G p)) P :=
    Integrable.mono' hu (measurable_productCost.comp (hF.prodMk hG)).aestronglyMeasurable
      (Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs,abs_of_nonneg (productCost_nonneg _ _)]
        exact hp p))
  have hew : (∫ p : Configuration d N × C(Icc 0 T,Configuration d N),
      productCost (p.2 t) (p.2 s) ∂P) = (N : ℝ)*d*(2*|(t : ℝ)-s|) :=
    ((measurePreserving_snd (μ := μ) (ν := ξ)).hasLaw.integral_comp
      (BrownianNoise.configurationLaw_increment_cost_integrable s t).aestronglyMeasurable).trans
      (BrownianNoise.configurationLaw_increment_momentIntegral s t)
  change wassersteinSq (Measure.map F P) (Measure.map G P) ≤ _
  calc
    _ ≤ ∫⁻ p, ENNReal.ofReal (productCost (F p) (G p)) ∂P := wassersteinSq_commonLabel_le P hF hG
    _ = ENNReal.ofReal (∫ p, productCost (F p) (G p) ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun p => productCost_nonneg _ _))).symm
    _ ≤ ENNReal.ofReal (∫ p : Configuration d N × C(Icc 0 T,Configuration d N),
        2*((N : ℝ)*d*((M : ℝ)*|(t : ℝ)-s|)^2)+2*productCost (p.2 t) (p.2 s) ∂P) :=
      ENNReal.ofReal_le_ofReal (integral_mono hi hu hp)
    _ = _ := by
      rw [integral_add (integrable_const _) (hw.const_mul 2)]
      simp_rw [integral_const_mul]
      rw [hew,integral_const]
      simp only [probReal_univ,one_smul,timeCost]
      congr 1
      ring

theorem law_time_wassersteinSq_tendsto {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (t : Icc 0 T) :
    Tendsto (fun s : Icc 0 T => wassersteinSq (law hv hb hl hT μ s) (law hv hb hl hT μ t))
      (𝓝 t) (𝓝 0) := by
  have hc : Continuous (fun s : Icc 0 T => ENNReal.ofReal (timeCost d N M t s)) :=
    ENNReal.continuous_ofReal.comp ((timeCost_continuous d N M).comp
      (continuous_const.prodMk continuous_subtype_val))
  have hz : Tendsto (fun s : Icc 0 T => ENNReal.ofReal (timeCost d N M t s)) (𝓝 t) (𝓝 0) := by
    simpa only [timeCost_self,ENNReal.ofReal_zero] using hc.tendsto t
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
    (fun _ => zero_le) (fun s => law_time_wassersteinSq_le hv hb hl hT μ t s)

end SharpWasserstein.BrownianFlow
