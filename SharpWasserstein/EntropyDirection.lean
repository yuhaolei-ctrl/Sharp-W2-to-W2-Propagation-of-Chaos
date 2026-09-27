import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Tactic.Linarith

/-!
# The direction of the entropy-cost identity

This file proves a conditional statement about genuine measures and their
Radon–Nikodym derivatives. If the density of `ν` relative to `μ` is
`exp (-M - Q)`, and `M` has mean zero under `μ`, then the integral of the
*reverse* log-likelihood ratio `llr μ ν` under `μ` is the mean of `Q` under `μ`.
The absolute continuity needed to reverse the likelihood ratio follows from
the strictly positive density, and integrability is proved explicitly.

No stochastic exponential, Girsanov theorem, data-processing inequality, or
identification with Mathlib's extended-real `klDiv` is asserted here. For
probability measures, the displayed integral is the usual real-valued
relative-entropy formula; the direction and the integrating measure are
part of the statement.
-/

noncomputable section

open MeasureTheory Real

namespace SharpWasserstein

variable {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω} {M Q : Ω → ℝ}

/-- A positive exponential density implies absolute continuity in the
direction needed for the reverse log-likelihood ratio. -/
theorem reverse_absoluteContinuous_of_exponential_density
    (hdensity : (fun x ↦ (ν.rnDeriv μ x).toReal) =ᵐ[μ]
      fun x ↦ exp (-M x - Q x)) : μ ≪ ν := by
  have hne : ∀ᵐ x ∂μ, ν.rnDeriv μ x ≠ 0 := by
    filter_upwards [hdensity] with x hx
    intro hz
    rw [hz, ENNReal.toReal_zero] at hx
    exact (exp_pos (-M x - Q x)).ne' hx.symm
  exact (withDensity_absolutelyContinuous'
    (Measure.measurable_rnDeriv ν μ).aemeasurable hne).trans
      (Measure.absolutelyContinuous_of_le (Measure.withDensity_rnDeriv_le ν μ))

variable [SigmaFinite μ] [SigmaFinite ν]

/-- The density formula with a minus sign gives `M + Q` for the reverse
log-likelihood ratio, almost everywhere under the original measure `μ`. -/
theorem llr_reverse_of_exponential_density
    (hdensity : (fun x ↦ (ν.rnDeriv μ x).toReal) =ᵐ[μ]
      fun x ↦ exp (-M x - Q x)) :
    llr μ ν =ᵐ[μ] fun x ↦ M x + Q x := by
  have hac := reverse_absoluteContinuous_of_exponential_density hdensity
  filter_upwards [neg_llr hac, hdensity] with x hneg hd
  have hforward : llr ν μ x = -M x - Q x := by
    rw [llr, hd, log_exp]
  simp only [Pi.neg_apply] at hneg
  linarith

/-- The reverse log-likelihood ratio is integrable when both terms in the
exponential density representation are integrable under `μ`. -/
theorem integrable_llr_reverse_of_exponential_density
    (hdensity : (fun x ↦ (ν.rnDeriv μ x).toReal) =ᵐ[μ]
      fun x ↦ exp (-M x - Q x))
    (hM : Integrable M μ) (hQ : Integrable Q μ) :
    Integrable (llr μ ν) μ :=
  (hM.add hQ).congr (llr_reverse_of_exponential_density hdensity).symm

/-- The expectation of the reverse log-likelihood ratio is the cost under
`μ`, provided the stochastic term has zero mean under this same measure.
This does not bound the expectation of `llr ν μ` under `ν`. -/
theorem integral_llr_reverse_of_exponential_density
    (hdensity : (fun x ↦ (ν.rnDeriv μ x).toReal) =ᵐ[μ]
      fun x ↦ exp (-M x - Q x))
    (hM : Integrable M μ) (hQ : Integrable Q μ)
    (hmean : ∫ x, M x ∂μ = 0) :
    ∫ x, llr μ ν x ∂μ = ∫ x, Q x ∂μ := by
  calc
    ∫ x, llr μ ν x ∂μ = ∫ x, (M x + Q x) ∂μ :=
      integral_congr_ae (llr_reverse_of_exponential_density hdensity)
    _ = (∫ x, M x ∂μ) + ∫ x, Q x ∂μ := integral_add hM hQ
    _ = ∫ x, Q x ∂μ := by rw [hmean, zero_add]

end SharpWasserstein
