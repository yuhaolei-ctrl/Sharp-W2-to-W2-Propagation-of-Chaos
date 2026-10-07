module

public import SharpWasserstein.Compat
public import SharpWasserstein.EntropyObservable
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# Vector-valued bounded-observable entropy estimates

The scalar Pinsker estimate is lifted to real Hilbert-valued observables by
testing against the difference of their Bochner expectations. The conditional
kernel version applies to the vector-valued drift discrepancy in the source
estimate; it uses actual kernel laws and their relative entropy.
-/

noncomputable section

open MeasureTheory InformationTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace SharpWasserstein

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Hilbert-valued bounded-observable Pinsker with dimension-free coefficient. -/
theorem norm_integral_difference_sq_le_klDiv
    (hfinite : klDiv μ ν ≠ ∞) {F : Ω → E} {M : ℝ} (hM : 0 ≤ M)
    (hF : AEStronglyMeasurable F ν) (hbound : ∀ᵐ x ∂ν, ‖F x‖ ≤ M) :
    ‖(∫ x, F x ∂μ) - ∫ x, F x ∂ν‖ ^ 2 ≤ 2 * M ^ 2 * (klDiv μ ν).toReal := by
  have hac := (klDiv_ne_top_iff.mp hfinite).1
  have hiν : Integrable F ν := (integrable_const M).mono' hF hbound
  have hiμ : Integrable F μ :=
    (integrable_const M).mono' (hF.mono_ac hac) (hac hbound)
  let D := (∫ x, F x ∂μ) - ∫ x, F x ∂ν
  change ‖D‖ ^ 2 ≤ 2 * M ^ 2 * (klDiv μ ν).toReal
  by_cases hD : D = 0
  · simp only [hD, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    positivity
  have hg : ∀ᵐ x ∂ν, |⟪D, F x⟫_ℝ| ≤ ‖D‖ * M := by
    filter_upwards [hbound] with x hx
    exact (abs_real_inner_le_norm D (F x)).trans
      (mul_le_mul_of_nonneg_left hx (norm_nonneg D))
  have hs := integral_difference_sq_le_klDiv hfinite
    (mul_nonneg (norm_nonneg D) hM) (hiν.const_inner D).aestronglyMeasurable.aemeasurable hg
  rw [integral_inner hiμ D, integral_inner hiν D, ← inner_sub_right] at hs
  change (⟪D, D⟫_ℝ) ^ 2 ≤ _ at hs
  rw [real_inner_self_eq_norm_sq] at hs
  have hpos : 0 < ‖D‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hD)
  apply (mul_le_mul_iff_right₀ hpos).mp
  nlinarith only [hs]

/-- The vector-valued estimate for actual conditional probability kernels. -/
theorem kernel_norm_integral_difference_sq_le_klDiv
    {A : Type*} [MeasurableSpace A] {ρ : Measure A}
    {κ η : Kernel A Ω} [IsMarkovKernel κ] [IsMarkovKernel η]
    {F : A → Ω → E} {M : ℝ} (hM : 0 ≤ M)
    (hfinite : ∀ᵐ a ∂ρ, klDiv (κ a) (η a) ≠ ∞)
    (hF : ∀ᵐ a ∂ρ, AEStronglyMeasurable (F a) (η a))
    (hbound : ∀ᵐ a ∂ρ, ∀ᵐ x ∂η a, ‖F a x‖ ≤ M) :
    ∀ᵐ a ∂ρ, ‖(∫ x, F a x ∂κ a) - ∫ x, F a x ∂η a‖ ^ 2
      ≤ 2 * M ^ 2 * (klDiv (κ a) (η a)).toReal := by
  filter_upwards [hfinite, hF, hbound] with a ha hfa hba
  exact norm_integral_difference_sq_le_klDiv ha hM hfa hba

end SharpWasserstein
