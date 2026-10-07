module

public import SharpWasserstein.Compat
public import SharpWasserstein.BoundedDerivativeComposition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

@[expose] public section

/-! Smooth globally bounded tests with bounded derivatives separate finite
measures. The proof uses actual sine and cosine of continuous linear
functionals and Mathlib's characteristic-function uniqueness theorem. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace SharpWasserstein.NoiseAverage

theorem allDerivativesBounded_cos : AllDerivativesBounded Real.cos := by
  intro n
  refine ⟨1,by norm_num,fun x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs]
  exact Real.abs_iteratedDeriv_cos_le_one n x

theorem allDerivativesBounded_sin : AllDerivativesBounded Real.sin := by
  intro n
  refine ⟨1,by norm_num,fun x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs]
  exact Real.abs_iteratedDeriv_sin_le_one n x

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem allDerivativesBounded_comp_linear {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hB : AllDerivativesBounded f) (L : E →L[ℝ] ℝ) :
    AllDerivativesBounded (fun x => f (L x)) := by
  apply AllDerivativesBounded.comp_of_fderiv hf L.contDiff hB
  have he : fderiv ℝ L = fun _ => L := funext (fun x => L.fderiv)
  rw [he]
  exact allDerivativesBounded_const L

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

theorem measure_eq_of_integral_smooth_bounded_eq {μ ν : Measure E}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : E → ℝ, ContDiff ℝ ∞ f → AllDerivativesBounded f →
      (∫ x, f x ∂μ) = ∫ x, f x ∂ν) : μ = ν := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_apply,charFunDual_apply]
  have hcos := h (fun x => Real.cos (L x)) (Real.contDiff_cos.comp L.contDiff)
    (allDerivativesBounded_comp_linear Real.contDiff_cos allDerivativesBounded_cos L)
  have hsin := h (fun x => Real.sin (L x)) (Real.contDiff_sin.comp L.contDiff)
    (allDerivativesBounded_comp_linear Real.contDiff_sin allDerivativesBounded_sin L)
  have hi (σ : Measure E) [IsFiniteMeasure σ] :
      Integrable (fun x => Complex.exp ((L x:ℂ)*Complex.I)) σ := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun x => by simp)
  apply Complex.ext
  · change RCLike.re (∫ x, Complex.exp ((L x:ℂ)*Complex.I) ∂μ) =
      RCLike.re (∫ x, Complex.exp ((L x:ℂ)*Complex.I) ∂ν)
    rw [← integral_re (hi μ),← integral_re (hi ν)]
    change (∫ x, (Complex.exp ((L x:ℂ)*Complex.I)).re ∂μ) =
      ∫ x, (Complex.exp ((L x:ℂ)*Complex.I)).re ∂ν
    simpa only [Complex.exp_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,mul_one,
      sub_zero,add_zero,Real.exp_zero,one_mul] using hcos
  · change RCLike.im (∫ x, Complex.exp ((L x:ℂ)*Complex.I) ∂μ) =
      RCLike.im (∫ x, Complex.exp ((L x:ℂ)*Complex.I) ∂ν)
    rw [← integral_im (hi μ),← integral_im (hi ν)]
    change (∫ x, (Complex.exp ((L x:ℂ)*Complex.I)).im ∂μ) =
      ∫ x, (Complex.exp ((L x:ℂ)*Complex.I)).im ∂ν
    simpa only [Complex.exp_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,mul_one,
      sub_zero,add_zero,Real.exp_zero,one_mul] using hsin

end SharpWasserstein.NoiseAverage
