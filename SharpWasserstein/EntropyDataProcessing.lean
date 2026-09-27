import SharpWasserstein.EntropyKL
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym

/-!
# Relative entropy decreases under measurable maps

This is data processing for Mathlib's actual extended-real KL divergence.
The proof uses the Radon–Nikodym derivative of a pushforward as a conditional
expectation and conditional Jensen for the nonnegative convex function
`klFun`. Neither data processing nor the desired estimate is a hypothesis.
No standard-Borel or topological assumption is needed for the measurable map.
-/

noncomputable section

open MeasureTheory InformationTheory Real Set
open scoped ENNReal

namespace SharpWasserstein

variable {Ω Υ : Type*} [mΩ : MeasurableSpace Ω] [mΥ : MeasurableSpace Υ]
  {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Data processing for arbitrary finite measures and measurable maps. -/
theorem klDiv_map_le {f : Ω → Υ} (hf : Measurable f) :
    klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν := by
  by_cases htop : klDiv μ ν = ∞
  · simp [htop]
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp htop
  let r : Ω → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal
  have hm : mΥ.comap f ≤ mΩ := hf.comap_le
  have hr : Integrable r ν := Measure.integrable_toReal_rnDeriv
  have hkr : Integrable (klFun ∘ r) ν :=
    (integrable_klFun_rnDeriv_iff hac).mpr hint
  have hkn : 0 ≤ᵐ[ν] klFun ∘ r :=
    ae_of_all _ fun _ ↦ klFun_nonneg ENNReal.toReal_nonneg
  have hjensen : klFun ∘ ν[r | mΥ.comap f] ≤ᵐ[ν] ν[klFun ∘ r | mΥ.comap f] :=
    convexOn_klFun.map_condExp_le hm
      continuous_klFun.continuousOn.lowerSemicontinuousOn
      (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg) isClosed_Ici hr hkr
  have hmap : (fun x ↦ ((μ.map f).rnDeriv (ν.map f) (f x)).toReal) =ᵐ[ν]
      ν[r | mΥ.comap f] := toReal_rnDeriv_map hac hf
  rw [klDiv_eq_lintegral_klFun_of_ac (hac.map hf), lintegral_map (by fun_prop) hf]
  calc
    ∫⁻ x, ENNReal.ofReal (klFun ((μ.map f).rnDeriv (ν.map f) (f x)).toReal) ∂ν
        ≤ ∫⁻ x, ENNReal.ofReal (ν[klFun ∘ r | mΥ.comap f] x) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hmap, hjensen] with x hx hj
      apply ENNReal.ofReal_le_ofReal
      simpa only [hx, Function.comp_apply] using hj
    _ = ENNReal.ofReal (∫ x, ν[klFun ∘ r | mΥ.comap f] x ∂ν) :=
      (ofReal_integral_eq_lintegral_ofReal integrable_condExp (condExp_nonneg hkn)).symm
    _ = ENNReal.ofReal (∫ x, klFun (r x) ∂ν) := by
      simp only [integral_condExp hm, Function.comp_apply]
    _ = klDiv μ ν := by
      rw [klDiv_of_ac_of_integrable hac hint, ← integral_klFun_rnDeriv hac hint]

/-- A measurable observation of the laws inherits the corrected entropy-cost
bound, under the same density and mean-zero hypotheses as the full-law identity. -/
theorem klDiv_map_le_cost_of_exponential_density
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {M Q : Ω → ℝ} {f : Ω → Υ} (hf : Measurable f)
    (hdensity : (fun x ↦ (ν.rnDeriv μ x).toReal) =ᵐ[μ]
      fun x ↦ exp (-M x - Q x))
    (hM : Integrable M μ) (hQ : Integrable Q μ)
    (hmean : ∫ x, M x ∂μ = 0) :
    klDiv (μ.map f) (ν.map f) ≤ ENNReal.ofReal (∫ x, Q x ∂μ) := by
  rw [← klDiv_reverse_of_exponential_density hdensity hM hQ hmean]
  exact klDiv_map_le hf

/-- The same observed-law entropy estimate in real-valued form. Finiteness
of the full-law KL is proved from the integrability hypotheses. -/
theorem toReal_klDiv_map_le_cost_of_exponential_density
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {M Q : Ω → ℝ} {f : Ω → Υ} (hf : Measurable f)
    (hdensity : (fun x ↦ (ν.rnDeriv μ x).toReal) =ᵐ[μ]
      fun x ↦ exp (-M x - Q x))
    (hM : Integrable M μ) (hQ : Integrable Q μ)
    (hmean : ∫ x, M x ∂μ = 0) :
    (klDiv (μ.map f) (ν.map f)).toReal ≤ ∫ x, Q x ∂μ := by
  rw [← toReal_klDiv_reverse_of_exponential_density hdensity hM hQ hmean]
  exact ENNReal.toReal_mono
    (klDiv_reverse_ne_top_of_exponential_density hdensity hM hQ) (klDiv_map_le hf)

end SharpWasserstein
