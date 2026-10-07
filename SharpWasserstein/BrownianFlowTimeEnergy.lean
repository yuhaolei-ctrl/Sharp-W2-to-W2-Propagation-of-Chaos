module

public import SharpWasserstein.Compat
public import SharpWasserstein.BrownianTimeTransport

@[expose] public section

/-! Actual common-label Brownian flow increment energy, before taking the
transport infimum. This supplies explicit couplings for time averaging. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace SharpWasserstein.BrownianFlow

variable {d N : ℕ} {v : ℝ → Configuration d N → Configuration d N} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
  (hl : ∀ t, LipschitzWith K (v t))

theorem flow_increment_energy_le {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (s t : Icc 0 T) :
    Integrable (fun p : Configuration d N × C(Icc 0 T,Configuration d N) =>
      productCost (BoundedFlow.flow hv hb hl hT p.1 p.2 t)
        (BoundedFlow.flow hv hb hl hT p.1 p.2 s)) (μ.prod (BrownianNoise.configurationLaw d N T)) ∧
    (∫ p : Configuration d N × C(Icc 0 T,Configuration d N),
      productCost (BoundedFlow.flow hv hb hl hT p.1 p.2 t)
        (BoundedFlow.flow hv hb hl hT p.1 p.2 s) ∂μ.prod (BrownianNoise.configurationLaw d N T)) ≤
      timeCost d N M s t := by
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
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ p : Configuration d N × C(Icc 0 T,Configuration d N),
        2*((N : ℝ)*d*((M : ℝ)*|(t : ℝ)-s|)^2)+2*productCost (p.2 t) (p.2 s) ∂P :=
      integral_mono hi hu hp
    _ = _ := by
      rw [integral_add (integrable_const _) (hw.const_mul 2)]
      simp_rw [integral_const_mul]
      rw [hew,integral_const]
      simp only [probReal_univ,one_smul,timeCost]
      ring

end SharpWasserstein.BrownianFlow
