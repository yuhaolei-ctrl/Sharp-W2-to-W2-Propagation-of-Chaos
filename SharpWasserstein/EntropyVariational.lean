import SharpWasserstein.EntropyKL
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# The entropy variational inequality

The proof tilts the reference probability measure by the observable and uses
nonnegativity of its actual KL divergence. No variational inequality is assumed.
-/

noncomputable section

open MeasureTheory InformationTheory Real
open scoped ENNReal

namespace SharpWasserstein

variable {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The expectation of an observable is bounded by relative entropy plus its
logarithmic exponential moment under the reference law. -/
theorem integral_le_klDiv_add_log_exp
    (hfinite : klDiv μ ν ≠ ∞) {F : Ω → ℝ}
    (hF : Integrable F μ) (hexp : Integrable (fun x ↦ exp (F x)) ν) :
    ∫ x, F x ∂μ ≤ (klDiv μ ν).toReal + log (∫ x, exp (F x) ∂ν) := by
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp hfinite
  haveI : IsProbabilityMeasure (ν.tilted F) := isProbabilityMeasure_tilted hexp
  have htac : μ ≪ ν.tilted F := hac.trans (absolutelyContinuous_tilted hexp)
  have htint := integrable_llr_tilted_right hac hF hint hexp
  have hn := integral_llr_add_sub_measure_univ_nonneg htac htint
  simp only [probReal_univ, add_sub_cancel_right] at hn
  rw [integral_llr_tilted_right hac hF hexp hint] at hn
  have hkl : (klDiv μ ν).toReal = ∫ x, llr μ ν x ∂μ := by
    simpa only [probReal_univ, add_sub_cancel_right] using toReal_klDiv hac hint
  rw [hkl]
  linarith

/-- A quadratic log-moment bound gives an expectation bound. The discriminant
argument covers zero variance as well as positive variance. -/
theorem integral_sq_le_entropy_of_log_mgf_bound
    (hfinite : klDiv μ ν ≠ ∞) {F : Ω → ℝ} {c : ℝ}
    (hF : Integrable F μ)
    (hexp : ∀ t : ℝ, Integrable (fun x ↦ exp (t * F x)) ν)
    (hmgf : ∀ t : ℝ, log (∫ x, exp (t * F x) ∂ν) ≤ c * t ^ 2 / 2) :
    (∫ x, F x ∂μ) ^ 2 ≤ 2 * c * (klDiv μ ν).toReal := by
  have hquad : ∀ t : ℝ, 0 ≤ (c / 2) * (t * t) + (-(∫ x, F x ∂μ)) * t
      + (klDiv μ ν).toReal := by
    intro t
    have h := integral_le_klDiv_add_log_exp hfinite (hF.const_mul t) (hexp t)
    rw [integral_const_mul] at h
    have hm := hmgf t
    nlinarith
  have hd := discrim_le_zero hquad
  simp only [discrim] at hd
  nlinarith

end SharpWasserstein
