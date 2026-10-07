module

public import SharpWasserstein.Compat
public import SharpWasserstein.EntropyDirection
public import Mathlib.InformationTheory.KullbackLeibler.Basic

@[expose] public section

/-!
# The corrected entropy-cost identity for the actual KL divergence

The identity is for `InformationTheory.klDiv μ ν`, where the exponential
density represents `dν/dμ` and the zero-mean identity is under `μ`.
All measures, Radon–Nikodym derivatives, integrals, and the extended-real KL
divergence are Mathlib objects. The stochastic construction of the density
and its mean-zero term remains outside these conditional statements.
-/

noncomputable section

open MeasureTheory InformationTheory Real
open scoped ENNReal

namespace SharpWasserstein

variable {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {M Q : Ω → ℝ}

/-- For probability measures the reverse likelihood identity is exactly the
extended-real relative entropy, with the cost integrated under `μ`. -/
theorem klDiv_reverse_of_exponential_density
    (hdensity : (fun x ↦ (ν.rnDeriv μ x).toReal) =ᵐ[μ]
      fun x ↦ exp (-M x - Q x))
    (hM : Integrable M μ) (hQ : Integrable Q μ)
    (hmean : ∫ x, M x ∂μ = 0) :
    klDiv μ ν = ENNReal.ofReal (∫ x, Q x ∂μ) := by
  rw [klDiv_of_ac_of_integrable
    (reverse_absoluteContinuous_of_exponential_density hdensity)
    (integrable_llr_reverse_of_exponential_density hdensity hM hQ)]
  simp only [probReal_univ, add_sub_cancel_right]
  rw [integral_llr_reverse_of_exponential_density hdensity hM hQ hmean]

/-- The entropy-cost identity gives finite relative entropy. -/
theorem klDiv_reverse_ne_top_of_exponential_density
    (hdensity : (fun x ↦ (ν.rnDeriv μ x).toReal) =ᵐ[μ]
      fun x ↦ exp (-M x - Q x))
    (hM : Integrable M μ) (hQ : Integrable Q μ) :
    klDiv μ ν ≠ ∞ :=
  klDiv_ne_top (reverse_absoluteContinuous_of_exponential_density hdensity)
    (integrable_llr_reverse_of_exponential_density hdensity hM hQ)

/-- The corresponding real-valued equality includes a proof that no infinite
KL value has been discarded by `ENNReal.toReal`. -/
theorem toReal_klDiv_reverse_of_exponential_density
    (hdensity : (fun x ↦ (ν.rnDeriv μ x).toReal) =ᵐ[μ]
      fun x ↦ exp (-M x - Q x))
    (hM : Integrable M μ) (hQ : Integrable Q μ)
    (hmean : ∫ x, M x ∂μ = 0) :
    (klDiv μ ν).toReal = ∫ x, Q x ∂μ := by
  rw [toReal_klDiv
    (reverse_absoluteContinuous_of_exponential_density hdensity)
    (integrable_llr_reverse_of_exponential_density hdensity hM hQ)]
  simp only [probReal_univ, add_sub_cancel_right]
  exact integral_llr_reverse_of_exponential_density hdensity hM hQ hmean

end SharpWasserstein
