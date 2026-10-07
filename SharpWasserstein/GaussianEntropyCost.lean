module

public import SharpWasserstein.Compat
public import SharpWasserstein.EntropyChainRule
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-!
# Entropy cost of Gaussian mean shifts

The Gaussian likelihood and KL identities below are derived from the actual
positive densities and Gaussian moments. They supply the finite-step cost
for Euler transition kernels. No Girsanov or entropy-cost estimate is assumed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal NNReal

namespace SharpWasserstein

/-- Nondegenerate Gaussians with a common variance are mutually absolutely
continuous, through their positive Lebesgue densities. -/
theorem gaussianReal_ac_sameVariance (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal a v ≪ gaussianReal b v :=
  (gaussianReal_absolutelyContinuous a hv).trans (gaussianReal_absolutelyContinuous' b hv)

theorem gaussian_log_density_ratio (a b x : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    log (gaussianPDFReal a v x / gaussianPDFReal b v x) =
      (a - b) / v * (x - a) + (a - b) ^ 2 / (2 * v) := by
  have hva : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hp : 0 < (sqrt (2 * Real.pi * v))⁻¹ := by positivity
  rw [log_div (gaussianPDFReal_pos a v x hv).ne' (gaussianPDFReal_pos b v x hv).ne']
  simp only [gaussianPDFReal, log_mul hp.ne' (exp_pos _).ne', log_exp]
  field_simp
  ring

/-- Exact log-likelihood ratio under the first Gaussian law. -/
theorem llr_gaussianReal_sameVariance (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    llr (gaussianReal a v) (gaussianReal b v) =ᵐ[gaussianReal a v]
      fun x ↦ (a - b) / v * (x - a) + (a - b) ^ 2 / (2 * v) := by
  have hac := gaussianReal_ac_sameVariance a b hv
  have hra := gaussianReal_absolutelyContinuous a hv
  have hrb := gaussianReal_absolutelyContinuous b hv
  have hratio := Measure.rnDeriv_eq_div hra hrb
  filter_upwards [hac hratio, hra (rnDeriv_gaussianReal a v), hra (rnDeriv_gaussianReal b v)]
    with x hx ha hb
  rw [llr, hx, ha, hb, ENNReal.toReal_div]
  simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
  exact gaussian_log_density_ratio a b x hv

/-- Integrability of the actual Gaussian log-likelihood ratio. -/
theorem integrable_llr_gaussianReal_sameVariance (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (llr (gaussianReal a v) (gaussianReal b v)) (gaussianReal a v) := by
  have hi : Integrable (fun x : ℝ ↦ x) (gaussianReal a v) :=
    (memLp_id_gaussianReal (μ := a) (v := v) 1).integrable (by norm_num)
  exact (((hi.sub (integrable_const a)).const_mul ((a - b) / v)).add
    (integrable_const ((a - b) ^ 2 / (2 * v)))).congr
      (llr_gaussianReal_sameVariance a b hv).symm

/-- The entropy expectation is the squared mean displacement divided by twice
the variance, integrated under the first law in KL. -/
theorem integral_llr_gaussianReal_sameVariance (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, llr (gaussianReal a v) (gaussianReal b v) x ∂gaussianReal a v =
      (a - b) ^ 2 / (2 * v) := by
  have hi : Integrable (fun x : ℝ ↦ x) (gaussianReal a v) :=
    (memLp_id_gaussianReal (μ := a) (v := v) 1).integrable (by norm_num)
  have haff : Integrable (fun x : ℝ ↦ (a - b) / v * (x - a)) (gaussianReal a v) :=
    (hi.sub (integrable_const a)).const_mul _
  rw [integral_congr_ae (llr_gaussianReal_sameVariance a b hv),
    integral_add (f := fun x : ℝ ↦ (a - b) / v * (x - a))
      (g := fun _ ↦ (a - b) ^ 2 / (2 * v)) haff (integrable_const _),
    integral_const_mul, integral_sub (f := fun x : ℝ ↦ x) (g := fun _ ↦ a)
      hi (integrable_const a), integral_id_gaussianReal]
  simp

/-- Exact extended-real KL cost for a nondegenerate Gaussian mean shift. -/
theorem klDiv_gaussianReal_sameVariance (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (gaussianReal a v) (gaussianReal b v) = ENNReal.ofReal ((a - b) ^ 2 / (2 * v)) := by
  rw [klDiv_of_ac_of_integrable (gaussianReal_ac_sameVariance a b hv)
    (integrable_llr_gaussianReal_sameVariance a b hv)]
  simp only [probReal_univ, add_sub_cancel_right, integral_llr_gaussianReal_sameVariance a b hv]

theorem klDiv_gaussianReal_sameVariance_ne_top (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (gaussianReal a v) (gaussianReal b v) ≠ ∞ := by
  rw [klDiv_gaussianReal_sameVariance a b hv]
  exact ENNReal.ofReal_ne_top

theorem toReal_klDiv_gaussianReal_sameVariance (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (klDiv (gaussianReal a v) (gaussianReal b v)).toReal = (a - b) ^ 2 / (2 * v) := by
  rw [klDiv_gaussianReal_sameVariance a b hv, ENNReal.toReal_ofReal (by positivity)]

/-- A genuine Markov transition with a measurable state-dependent Gaussian mean. -/
def gaussianMeanKernel {A : Type*} [MeasurableSpace A]
    (a : A → ℝ) (ha : Measurable a) (v : ℝ≥0) : Kernel A ℝ where
  toFun x := gaussianReal (a x) v
  measurable' := measurable_gaussianReal.comp (ha.prodMk measurable_const)

instance gaussianMeanKernel_isMarkov {A : Type*} [MeasurableSpace A]
    (a : A → ℝ) (ha : Measurable a) (v : ℝ≥0) : IsMarkovKernel (gaussianMeanKernel a ha v) where
  isProbabilityMeasure x := by change IsProbabilityMeasure (gaussianReal (a x) v); infer_instance

/-- Same-base Gaussian transition entropy equals the integral of the pointwise
mean-shift cost, including the infinite-cost case. -/
theorem klDiv_gaussianMeanKernel_same_base {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasure μ] (a b : A → ℝ)
    (ha : Measurable a) (hb : Measurable b) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (μ ⊗ₘ gaussianMeanKernel a ha v) (μ ⊗ₘ gaussianMeanKernel b hb v) =
      ∫⁻ x, ENNReal.ofReal ((a x - b x) ^ 2 / (2 * v)) ∂μ := by
  have hac : μ ⊗ₘ gaussianMeanKernel a ha v ≪ μ ⊗ₘ gaussianMeanKernel b hb v :=
    Measure.AbsolutelyContinuous.compProd_right
      (Filter.Eventually.of_forall fun x ↦ gaussianReal_ac_sameVariance (a x) (b x) hv)
  rw [← lintegral_kernel_klDiv_eq_compProd hac]
  apply lintegral_congr
  intro x
  exact klDiv_gaussianReal_sameVariance (a x) (b x) hv

/-- One actual Gaussian transition adds its cost under the first history law
to the relative entropy of the two history laws. No finite-KL premise is needed. -/
theorem klDiv_gaussianMeanKernel_compProd {A : Type*} [MeasurableSpace A]
    (μ ν : Measure A) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (a b : A → ℝ)
    (ha : Measurable a) (hb : Measurable b) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (μ ⊗ₘ gaussianMeanKernel a ha v) (ν ⊗ₘ gaussianMeanKernel b hb v) =
      klDiv μ ν + ∫⁻ x, ENNReal.ofReal ((a x - b x) ^ 2 / (2 * v)) ∂μ := by
  rw [klDiv_compProd_eq_add, klDiv_gaussianMeanKernel_same_base μ a b ha hb hv]

/-- The finite-cost version, with actual Bochner cost and no discarded infinite
entropy in the base laws. -/
theorem klDiv_gaussianMeanKernel_compProd_of_integrable {A : Type*} [MeasurableSpace A]
    (μ ν : Measure A) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (a b : A → ℝ)
    (ha : Measurable a) (hb : Measurable b) {v : ℝ≥0} (hv : v ≠ 0)
    (hcost : Integrable (fun x ↦ (a x - b x) ^ 2 / (2 * v)) μ) :
    klDiv (μ ⊗ₘ gaussianMeanKernel a ha v) (ν ⊗ₘ gaussianMeanKernel b hb v) =
      klDiv μ ν + ENNReal.ofReal (∫ x, (a x - b x) ^ 2 / (2 * v) ∂μ) := by
  rw [klDiv_gaussianMeanKernel_compProd μ ν a b ha hb hv,
    ofReal_integral_eq_lintegral_ofReal hcost (Filter.Eventually.of_forall fun x ↦ by positivity)]

/-- Exact one-step Euler entropy cost for diffusion coefficient sqrt(2).
The history measures may differ. The expected control cost is under μ, the
first law in KL, which fixes the entropy-cost direction. -/
theorem klDiv_scalarEuler_step {A : Type*} [MeasurableSpace A]
    (μ ν : Measure A) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (state u w : A → ℝ) (hs : Measurable state) (hu : Measurable u) (hw : Measurable w)
    (δ : ℝ≥0) (hδ : δ ≠ 0) (hcost : Integrable (fun x ↦ (u x - w x) ^ 2) μ) :
    klDiv (μ ⊗ₘ gaussianMeanKernel (fun x ↦ state x + δ * u x)
        (hs.add (measurable_const.mul hu)) (2 * δ))
      (ν ⊗ₘ gaussianMeanKernel (fun x ↦ state x + δ * w x)
        (hs.add (measurable_const.mul hw)) (2 * δ)) =
      klDiv μ ν + ENNReal.ofReal ((δ : ℝ) / 4 * ∫ x, (u x - w x) ^ 2 ∂μ) := by
  have hδr : (δ : ℝ) ≠ 0 := by exact_mod_cast hδ
  have heq : (fun x ↦ ((state x + δ * u x) - (state x + δ * w x)) ^ 2 / (2 * ((2 * δ : ℝ≥0) : ℝ))) =
      fun x ↦ (δ : ℝ) / 4 * (u x - w x) ^ 2 := by
    funext x
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    field_simp
    ring
  have hi : Integrable
      (fun x ↦ ((state x + δ * u x) - (state x + δ * w x)) ^ 2 / (2 * ((2 * δ : ℝ≥0) : ℝ))) μ := by
    rw [heq]
    exact hcost.const_mul _
  rw [klDiv_gaussianMeanKernel_compProd_of_integrable μ ν _ _ _ _
    (mul_ne_zero (by norm_num) hδ) hi, heq, integral_const_mul]

end SharpWasserstein
