module

public import SharpWasserstein.Compat
public import SharpWasserstein.EntropyVariational
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

/-!
# Bounded-observable Pinsker inequalities

These are estimates for integrals under genuine probability laws and Mathlib's
KL divergence. The constant is `2 M²` for an observable bounded by `M` in absolute
value. Hoeffding's lemma supplies the logarithmic moment bound; the variational
inequality is proved in `EntropyVariational`. The kernel theorem applies this
estimate to conditional laws almost everywhere under a base measure.
-/

noncomputable section

open MeasureTheory InformationTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace SharpWasserstein

variable {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- An observable that is sub-Gaussian under the reference law satisfies the
entropy bound for its expectation under another law of finite relative entropy. -/
theorem integral_sq_le_entropy_of_subGaussian
    (hfinite : klDiv μ ν ≠ ∞) {F : Ω → ℝ} {c : ℝ≥0}
    (hF : Integrable F μ) (hsg : HasSubgaussianMGF F c ν) :
    (∫ x, F x ∂μ) ^ 2 ≤ 2 * (c : ℝ) * (klDiv μ ν).toReal := by
  apply integral_sq_le_entropy_of_log_mgf_bound hfinite hF hsg.integrable_exp_mul
  intro t
  exact hsg.cgf_le t

/-- Bounded-observable Pinsker with the sharp universal coefficient `2`.
The bound and measurability need only hold almost everywhere under `ν`;
finite relative entropy transfers them to `μ`. -/
theorem integral_difference_sq_le_klDiv
    (hfinite : klDiv μ ν ≠ ∞) {F : Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hF : AEMeasurable F ν) (hbound : ∀ᵐ x ∂ν, |F x| ≤ M) :
    ((∫ x, F x ∂μ) - ∫ x, F x ∂ν) ^ 2 ≤ 2 * M ^ 2 * (klDiv μ ν).toReal := by
  have hac := (klDiv_ne_top_iff.mp hfinite).1
  have hcc : ∀ᵐ x ∂ν, F x ∈ Set.Icc (-M) M := by
    filter_upwards [hbound] with x hx using abs_le.mp hx
  have hiμ : Integrable F μ :=
    Integrable.of_mem_Icc (-M) M (hF.mono_ac hac) (hac hcc)
  have hsg := hasSubgaussianMGF_of_mem_Icc hF hcc
  have h := integral_sq_le_entropy_of_subGaussian hfinite
    (hiμ.sub (integrable_const (∫ x, F x ∂ν))) hsg
  have hc : (((‖M - -M‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = M ^ 2 := by
    change (‖M - -M‖ / 2) ^ 2 = M ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ M - -M)]
    ring
  simpa only [Pi.sub_apply, integral_sub hiμ (integrable_const _), integral_const,
    probReal_univ, smul_eq_mul, one_mul, hc] using h

/-- Conditional-kernel Pinsker, for the actual probability laws `κ a` and
`η a`. This is an almost-everywhere estimate under an arbitrary base measure. -/
theorem kernel_integral_difference_sq_le_klDiv
    {A : Type*} [MeasurableSpace A] {ρ : Measure A}
    {κ η : Kernel A Ω} [IsMarkovKernel κ] [IsMarkovKernel η]
    {F : A → Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hfinite : ∀ᵐ a ∂ρ, klDiv (κ a) (η a) ≠ ∞)
    (hF : ∀ᵐ a ∂ρ, AEMeasurable (F a) (η a))
    (hbound : ∀ᵐ a ∂ρ, ∀ᵐ x ∂η a, |F a x| ≤ M) :
    ∀ᵐ a ∂ρ, ((∫ x, F a x ∂κ a) - ∫ x, F a x ∂η a) ^ 2
      ≤ 2 * M ^ 2 * (klDiv (κ a) (η a)).toReal := by
  filter_upwards [hfinite, hF, hbound] with a ha hfa hba
  exact integral_difference_sq_le_klDiv ha hM hfa hba

end SharpWasserstein
