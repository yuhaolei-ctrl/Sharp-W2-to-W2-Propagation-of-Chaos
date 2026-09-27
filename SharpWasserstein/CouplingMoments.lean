import SharpWasserstein.TransportTriangle
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Finite displacement energy for every coupling of the actual P₂ laws. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace SharpWasserstein

theorem integrable_productCost_iff {d N : ℕ}
    (γ : Measure (Configuration d N × Configuration d N)) :
    Integrable (fun z => productCost z.1 z.2) γ ↔ transportCost γ < ∞ := by
  have hm : AEStronglyMeasurable (fun z : Configuration d N × Configuration d N =>
      productCost z.1 z.2) γ := measurable_productCost.aestronglyMeasurable
  have he := hasFiniteIntegral_iff_ofReal (μ := γ)
    (Eventually.of_forall (fun z : Configuration d N × Configuration d N => productCost_nonneg z.1 z.2))
  exact ⟨fun h => he.mp h.2, fun h => ⟨hm,he.mpr h⟩⟩

theorem coupling_transportCost_le_moments {d N : ℕ}
    {μ ν : Measure (Configuration d N)}
    {γ : Measure (Configuration d N × Configuration d N)} (hγ : IsCoupling μ ν γ) :
    transportCost γ ≤ 2 * (∫⁻ x, ENNReal.ofReal (productCost x 0) ∂μ) +
      2 * (∫⁻ x, ENNReal.ofReal (productCost x 0) ∂ν) := by
  have hfst : (∫⁻ z, ENNReal.ofReal (productCost z.1 0) ∂γ) =
      ∫⁻ x, ENNReal.ofReal (productCost x 0) ∂μ := by
    rw [← hγ.2.1, lintegral_map measurable_secondMoment measurable_fst]
  have hsnd : (∫⁻ z, ENNReal.ofReal (productCost z.2 0) ∂γ) =
      ∫⁻ x, ENNReal.ofReal (productCost x 0) ∂ν := by
    rw [← hγ.2.2, lintegral_map measurable_secondMoment measurable_snd]
  calc
    transportCost γ ≤ ∫⁻ z, 2 * ENNReal.ofReal (productCost z.1 0) +
        2 * ENNReal.ofReal (productCost z.2 0) ∂γ := by
      apply lintegral_mono
      intro z
      have h := ENNReal.ofReal_le_ofReal (productCost_le_moments z.1 z.2)
      rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) (productCost_nonneg _ _))
        (mul_nonneg (by norm_num) (productCost_nonneg _ _)), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] at h
      exact h
    _ = _ := by
      have hf : Measurable (fun z : Configuration d N × Configuration d N => ENNReal.ofReal (productCost z.1 0)) :=
        measurable_secondMoment.comp measurable_fst
      have hs : Measurable (fun z : Configuration d N × Configuration d N => ENNReal.ofReal (productCost z.2 0)) :=
        measurable_secondMoment.comp measurable_snd
      have h2 : Measurable (fun z : Configuration d N × Configuration d N => (2 : ℝ≥0∞) * ENNReal.ofReal (productCost z.1 0)) :=
        measurable_const.mul hf
      rw [lintegral_add_left h2, lintegral_const_mul _ hf, lintegral_const_mul _ hs, hfst, hsnd]

theorem coupling_productCost_integrable {d N : ℕ}
    {μ ν : Measure (Configuration d N)}
    {γ : Measure (Configuration d N × Configuration d N)} (hγ : IsCoupling μ ν γ)
    (hμ : HasSecondMoment μ) (hν : HasSecondMoment ν) :
    Integrable (fun z => productCost z.1 z.2) γ := by
  apply (integrable_productCost_iff γ).mpr
  apply lt_of_le_of_lt (coupling_transportCost_le_moments hγ)
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) hμ,
    ENNReal.mul_lt_top (by norm_num) hν⟩

theorem coupling_displacement_memLp {d N : ℕ}
    {μ ν : Measure (Configuration d N)}
    {γ : Measure (Configuration d N × Configuration d N)} (hγ : IsCoupling μ ν γ)
    (hμ : HasSecondMoment μ) (hν : HasSecondMoment ν) :
    MemLp transportDisplacement 2 γ := by
  apply (memLp_two_iff_integrable_sq_norm continuous_transportDisplacement.aestronglyMeasurable).mpr
  have he : (fun z : Configuration d N × Configuration d N => ‖transportDisplacement z‖^2) =
      (fun z => productCost z.1 z.2) := by
    funext z
    exact (productCost_eq_displacement_norm_sq z.1 z.2).symm
  rw [he]
  exact coupling_productCost_integrable hγ hμ hν

end SharpWasserstein
