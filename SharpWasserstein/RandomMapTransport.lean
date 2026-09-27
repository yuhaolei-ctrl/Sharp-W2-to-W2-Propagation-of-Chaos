import SharpWasserstein.TransportMoments

/-! Synchronous coupling of genuine random maps. A pointwise quadratic-cost
bound is transported through a common-noise coupling and the infimum over
initial couplings. No transport metric inequality is assumed. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace SharpWasserstein

variable {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]

def randomMapLaw (F : Configuration d N × Ω → Configuration d N)
    (μ : Measure (Configuration d N)) (ξ : Measure Ω) : Measure (Configuration d N) :=
  Measure.map F (μ.prod ξ)

theorem randomMapLaw_probability (F : Configuration d N × Ω → Configuration d N)
    (hF : Measurable F) (μ : Measure (Configuration d N)) (ξ : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ξ] :
    IsProbabilityMeasure (randomMapLaw F μ ξ) :=
  Measure.isProbabilityMeasure_map hF.aemeasurable

def synchronousMap (F : Configuration d N × Ω → Configuration d N)
    (z : (Configuration d N × Configuration d N) × Ω) :
    Configuration d N × Configuration d N := (F (z.1.1, z.2), F (z.1.2, z.2))

theorem measurable_synchronousMap (F : Configuration d N × Ω → Configuration d N)
    (hF : Measurable F) : Measurable (synchronousMap F) :=
  (hF.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
    (hF.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

theorem coupling_synchronousMap (F : Configuration d N × Ω → Configuration d N)
    (hF : Measurable F) (ξ : Measure Ω) [IsProbabilityMeasure ξ]
    {μ ν : Measure (Configuration d N)}
    {γ : Measure (Configuration d N × Configuration d N)} (hγ : IsCoupling μ ν γ) :
    IsCoupling (randomMapLaw F μ ξ) (randomMapLaw F ν ξ)
      (Measure.map (synchronousMap F) (γ.prod ξ)) := by
  letI : IsProbabilityMeasure γ := hγ.1
  have hleft : Measure.map (fun z : (Configuration d N × Configuration d N) × Ω =>
      (z.1.1, z.2)) (γ.prod ξ) = μ.prod ξ := by
    change Measure.map (Prod.map Prod.fst id) (γ.prod ξ) = _
    rw [← Measure.map_prod_map γ ξ measurable_fst measurable_id,
      hγ.2.1, Measure.map_id]
  have hright : Measure.map (fun z : (Configuration d N × Configuration d N) × Ω =>
      (z.1.2, z.2)) (γ.prod ξ) = ν.prod ξ := by
    change Measure.map (Prod.map Prod.snd id) (γ.prod ξ) = _
    rw [← Measure.map_prod_map γ ξ measurable_snd measurable_id,
      hγ.2.2, Measure.map_id]
  have hlm : Measurable (fun z : (Configuration d N × Configuration d N) × Ω =>
      (z.1.1, z.2)) := (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hrm : Measurable (fun z : (Configuration d N × Configuration d N) × Ω =>
      (z.1.2, z.2)) := (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hsm := measurable_synchronousMap F hF
  refine ⟨Measure.isProbabilityMeasure_map hsm.aemeasurable, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hsm]
    change Measure.map (F ∘ (fun z : (Configuration d N × Configuration d N) × Ω =>
      (z.1.1, z.2))) (γ.prod ξ) = _
    rw [← Measure.map_map hF hlm,
      hleft]
    rfl
  · rw [Measure.map_map measurable_snd hsm]
    change Measure.map (F ∘ (fun z : (Configuration d N × Configuration d N) × Ω =>
      (z.1.2, z.2))) (γ.prod ξ) = _
    rw [← Measure.map_map hF hrm,
      hright]
    rfl

theorem transportCost_synchronousMap_le (F : Configuration d N × Ω → Configuration d N)
    (hF : Measurable F) (ξ : Measure Ω) [IsProbabilityMeasure ξ]
    (γ : Measure (Configuration d N × Configuration d N)) [IsProbabilityMeasure γ]
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x y ω, productCost (F (x, ω)) (F (y, ω)) ≤ C * productCost x y) :
    transportCost (Measure.map (synchronousMap F) (γ.prod ξ)) ≤
      ENNReal.ofReal C * transportCost γ := by
  rw [transportCost, lintegral_map measurable_productCost.ennreal_ofReal
    (measurable_synchronousMap F hF)]
  calc
    (∫⁻ z, ENNReal.ofReal (productCost ((synchronousMap F z).1)
        ((synchronousMap F z).2)) ∂(γ.prod ξ)) ≤
        ∫⁻ z, ENNReal.ofReal C * ENNReal.ofReal (productCost z.1.1 z.1.2) ∂(γ.prod ξ) := by
      apply lintegral_mono
      intro z
      change ENNReal.ofReal (productCost (F (z.1.1, z.2)) (F (z.1.2, z.2))) ≤
        ENNReal.ofReal C * ENNReal.ofReal (productCost z.1.1 z.1.2)
      rw [← ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (hbound z.1.1 z.1.2 z.2)
    _ = _ := by
      have hc : Measurable (fun z : (Configuration d N × Configuration d N) × Ω =>
          ENNReal.ofReal (productCost z.1.1 z.1.2)) :=
        measurable_productCost.ennreal_ofReal.comp measurable_fst
      rw [lintegral_const_mul _ hc]
      congr 1
      exact (measurePreserving_fst (μ := γ) (ν := ξ)).lintegral_comp
        measurable_productCost.ennreal_ofReal

theorem wassersteinSq_eq_iInf_coupling {d N : ℕ}
    (μ ν : Measure (Configuration d N)) :
    wassersteinSq μ ν = ⨅ γ : {γ // IsCoupling μ ν γ}, transportCost γ.val := by
  simp only [wassersteinSq, iInf_subtype]

/-- Quadratic transport contraction for a measurable random map, using the
same random input in the two copies. The probability and quadratic-cost
objects in this statement are the concrete ones defined in Transport. -/
theorem wassersteinSq_randomMapLaw_le (F : Configuration d N × Ω → Configuration d N)
    (hF : Measurable F) (ξ : Measure Ω) [IsProbabilityMeasure ξ]
    (μ ν : Measure (Configuration d N)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x y ω, productCost (F (x, ω)) (F (y, ω)) ≤ C * productCost x y) :
    wassersteinSq (randomMapLaw F μ ξ) (randomMapLaw F ν ξ) ≤
      ENNReal.ofReal C * wassersteinSq μ ν := by
  letI : Nonempty {γ // IsCoupling μ ν γ} := ⟨⟨μ.prod ν, product_isCoupling μ ν⟩⟩
  rw [wassersteinSq_eq_iInf_coupling μ ν,
    ENNReal.mul_iInf (by simp : ENNReal.ofReal C = ∞ →
      (⨅ γ : {γ // IsCoupling μ ν γ}, transportCost γ.val) = 0 →
        ∃ γ : {γ // IsCoupling μ ν γ}, transportCost γ.val = 0)]
  apply le_iInf
  intro γ
  letI : IsProbabilityMeasure γ.val := γ.property.1
  exact (wassersteinSq_le_cost (coupling_synchronousMap F hF ξ γ.property)).trans
    (transportCost_synchronousMap_le F hF ξ γ.val hC hbound)

end SharpWasserstein
