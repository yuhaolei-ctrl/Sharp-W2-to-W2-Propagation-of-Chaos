import SharpWasserstein.EntropyObservable
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Uniform square-exponential moments from sub-Gaussian moment bounds

A Gaussian-mixture identity converts the linear moment bound into a square-
exponential bound. Boundedness is used only to justify Fubini; the resulting
constant is independent of that bound. All measures and integrals are actual.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace SharpWasserstein

/-- A fixed finite numerical constant (equal to sqrt 2). -/
def squareExponentialConstant : ℝ := (sqrt (2 * Real.pi))⁻¹ * sqrt (4 * Real.pi)

theorem subGaussianSquare_gaussian_density_identity (x : ℝ) :
    gaussianPDFReal 0 1 x * exp (x ^ 2 / 4) =
      (sqrt (2 * Real.pi))⁻¹ * exp (-(1 / 4 : ℝ) * x ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← exp_add]
  congr 2
  ring

theorem integrable_exp_square_standardGaussian :
    Integrable (fun x : ℝ ↦ exp (x ^ 2 / 4)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  apply (integrable_withDensity_iff_integrable_smul₀'
    (measurable_gaussianPDF 0 1).aemeasurable
    (Filter.Eventually.of_forall fun x ↦ (gaussianPDF_lt_top (μ := 0) (v := 1) (x := x)))).mpr
  simpa only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _),
    smul_eq_mul, subGaussianSquare_gaussian_density_identity] using
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul (sqrt (2 * Real.pi))⁻¹

theorem integral_exp_square_standardGaussian :
    ∫ x : ℝ, exp (x ^ 2 / 4) ∂gaussianReal 0 1 = squareExponentialConstant := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul, subGaussianSquare_gaussian_density_identity]
  rw [integral_const_mul, integral_gaussian]
  unfold squareExponentialConstant
  congr 2
  ring

/-- A bounded measurable sub-Gaussian observable has a uniform exponential
square moment after any scaling satisfying `c*a² ≤ 1/2`. -/
theorem integral_exp_square_le_of_subGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {c : ℝ≥0} {a B : ℝ}
    (hX : Measurable X) (hsub : HasSubgaussianMGF X c μ)
    (_hB : 0 ≤ B) (hbound : ∀ x, |X x| ≤ B) (hscale : (c : ℝ) * a ^ 2 ≤ 1 / 2) :
    ∫ x, exp ((a * X x) ^ 2 / 2) ∂μ ≤ squareExponentialConstant := by
  have hinner (x : Ω) : ∫ z : ℝ, exp ((a * X x) * z) ∂gaussianReal 0 1 =
      exp ((a * X x) ^ 2 / 2) := by
    simpa only [mgf, zero_mul, NNReal.coe_one, one_mul, zero_add] using
      congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) (a * X x)
  have hbounded : ∀ x, exp ((a * X x) ^ 2 / 2) ≤ exp ((|a| * B) ^ 2 / 2) := by
    intro x
    apply exp_le_exp.mpr
    have hx : |a * X x| ≤ |a| * B := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hbound x) (abs_nonneg a)
    have hs := pow_le_pow_left₀ (abs_nonneg (a * X x)) hx 2
    rw [sq_abs] at hs
    linarith
  have hexp : Integrable (fun x ↦ exp ((a * X x) ^ 2 / 2)) μ :=
    (integrable_const (exp ((|a| * B) ^ 2 / 2))).mono'
      (by fun_prop) (Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact hbounded x)
  have hjoint : Integrable (fun p : Ω × ℝ ↦ exp ((a * X p.1) * p.2))
      (μ.prod (gaussianReal 0 1)) := by
    apply (integrable_prod_iff (by fun_prop)).mpr
    refine ⟨Filter.Eventually.of_forall (fun x ↦ integrable_exp_mul_gaussianReal (a * X x)), ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_pos (exp_pos _), hinner] using hexp
  calc
    _ = ∫ x, ∫ z : ℝ, exp ((a * X x) * z) ∂gaussianReal 0 1 ∂μ := by
      simp_rw [hinner]
    _ = ∫ z : ℝ, ∫ x, exp ((a * X x) * z) ∂μ ∂gaussianReal 0 1 :=
      integral_integral_swap hjoint
    _ ≤ ∫ z : ℝ, exp (z ^ 2 / 4) ∂gaussianReal 0 1 := by
      apply integral_mono_ae hjoint.integral_prod_right integrable_exp_square_standardGaussian
      exact Filter.Eventually.of_forall fun z ↦ by
        calc
          _ = mgf X μ (a * z) := by
            unfold mgf
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x ↦ congrArg exp (by ring)
          _ ≤ exp (c * (a * z) ^ 2 / 2) := hsub.mgf_le _
          _ ≤ exp (z ^ 2 / 4) := by
            apply exp_le_exp.mpr
            have h := mul_le_mul_of_nonneg_right hscale (sq_nonneg z)
            nlinarith only [h]
    _ = _ := integral_exp_square_standardGaussian

end SharpWasserstein
