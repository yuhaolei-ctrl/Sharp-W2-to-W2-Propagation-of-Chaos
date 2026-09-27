import SharpWasserstein.Transport
import Mathlib.Tactic.Linarith

/-! Finite-cost probability couplings for the actual transport infimum.
This proves finiteness on P₂; the gluing and metric triangle arguments remain open. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace SharpWasserstein

theorem product_isCoupling {d N : ℕ} (μ ν : Measure (Configuration d N))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsCoupling μ ν (μ.prod ν) := by
  refine ⟨inferInstance, ?_, ?_⟩ <;> simp

theorem productCost_le_moments {d N : ℕ} (x y : Configuration d N) :
    productCost x y ≤ 2 * productCost x 0 + 2 * productCost y 0 := by
  simp only [productCost, Pi.zero_apply, sub_zero, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro a _
  nlinarith [sq_nonneg (x i a + y i a)]

theorem measurable_secondMoment {d N : ℕ} :
    Measurable (fun x : Configuration d N => ENNReal.ofReal (productCost x 0)) :=
  (measurable_productCost.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal

theorem transportCost_product_le {d N : ℕ} (μ ν : Measure (Configuration d N))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    transportCost (μ.prod ν) ≤
      2 * (∫⁻ x, ENNReal.ofReal (productCost x 0) ∂μ) +
      2 * (∫⁻ y, ENNReal.ofReal (productCost y 0) ∂ν) := by
  let f : Configuration d N → ℝ≥0∞ := fun x => ENNReal.ofReal (productCost x 0)
  have hf : Measurable f := measurable_secondMoment
  calc
    transportCost (μ.prod ν) ≤ ∫⁻ z, 2 * f z.1 + 2 * f z.2 ∂(μ.prod ν) := by
      apply lintegral_mono
      intro z
      calc
        ENNReal.ofReal (productCost z.1 z.2) ≤
            ENNReal.ofReal (2 * productCost z.1 0 + 2 * productCost z.2 0) :=
          ENNReal.ofReal_le_ofReal (productCost_le_moments z.1 z.2)
        _ ≤ 2 * f z.1 + 2 * f z.2 := by
          simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_ofNat, f] using (ENNReal.ofReal_add_le
              (p := 2 * productCost z.1 0) (q := 2 * productCost z.2 0))
    _ = _ := by
      have hfst : Measurable (fun z : Configuration d N × Configuration d N => f z.1) :=
        hf.comp measurable_fst
      have hsnd : Measurable (fun z : Configuration d N × Configuration d N => f z.2) :=
        hf.comp measurable_snd
      have h2fst : Measurable (fun z : Configuration d N × Configuration d N =>
          (2 : ℝ≥0∞) * f z.1) := measurable_const.mul hfst
      rw [lintegral_add_left h2fst,
        lintegral_const_mul 2 hfst, lintegral_const_mul 2 hsnd,
        (measurePreserving_fst (μ := μ) (ν := ν)).lintegral_comp hf,
        (measurePreserving_snd (μ := μ) (ν := ν)).lintegral_comp hf]

theorem wassersteinSq_lt_top {d N : ℕ} (μ ν : Measure (Configuration d N))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : HasSecondMoment μ) (hν : HasSecondMoment ν) : wassersteinSq μ ν < ∞ := by
  apply lt_of_le_of_lt ((wassersteinSq_le_cost (product_isCoupling μ ν)).trans
    (transportCost_product_le μ ν))
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) hμ,
    ENNReal.mul_lt_top (by norm_num) hν⟩

end SharpWasserstein
