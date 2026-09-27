import SharpWasserstein.RoughEulerianTimePrimitive
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Differentiating an actual time convolution of a continuous weak curve.
The original source is only integrable. Its convolution is proved to be the
derivative by genuine L¹ integration by parts, with exact boundary conditions. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
namespace SharpWasserstein.RoughEulerianTime

def timeConvolution (κ : ℝ → ℝ) (a b : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in Icc a b, κ (t-s)*f s

/-- Differentiate the actual integral, using a bound on the kernel derivative
times the integrable original scalar field. -/
theorem timeConvolution_hasDerivAt {κ κ' f : ℝ → ℝ} {a b C D : ℝ}
    (hκ : ∀ x, HasDerivAt κ (κ' x) x) (hκ' : Continuous κ')
    (hC : ∀ x, ‖κ x‖ ≤ C) (hD : ∀ x, ‖κ' x‖ ≤ D)
    (hf : IntegrableOn f (Icc a b)) (t : ℝ) :
    HasDerivAt (timeConvolution κ a b f) (∫ s in Icc a b, κ' (t-s)*f s) t := by
  have hκc : Continuous κ := continuous_iff_continuousAt.mpr (fun x => (hκ x).continuousAt)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Icc a b)) (F := fun t s => κ (t-s)*f s)
    (F' := fun t s => κ' (t-s)*f s) (s := univ) (bound := fun s => D*‖f s‖)
    univ_mem ?_ ?_ ?_ ?_ (hf.norm.const_mul D) ?_).2
  · exact Eventually.of_forall fun r =>
      ((hκc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).mul hf.aestronglyMeasurable
  · exact hf.bdd_mul (hκc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun s => hC (t-s))
  · exact ((hκ'.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).mul hf.aestronglyMeasurable
  · exact Eventually.of_forall fun s r _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hD (r-s)) (norm_nonneg _)
  · exact Eventually.of_forall fun s r _ => by
      have hh := ((hκ (r-s)).comp r ((hasDerivAt_id r).sub_const s)).mul_const (f s)
      simp only [Function.comp_def, id_eq, mul_one] at hh
      exact hh

/-- Moving the derivative from the time kernel to the original L¹ source
uses the integrated weak equation and vanishing kernel at both endpoints. -/
theorem timeConvolution_derivative_eq_source {a b t : ℝ} (hab : a ≤ b)
    {f g κ κ' : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) (hg : IntegrableOn g (Icc a b))
    (heq : ∀ s ∈ Icc a b, f s-f a = ∫ r in a..s, g r)
    (hκ : ∀ x, HasDerivAt κ (κ' x) x) (hκ' : Continuous κ')
    (hκa : κ (t-a) = 0) (hκb : κ (t-b) = 0) :
    (∫ s in Icc a b, κ' (t-s)*f s) = timeConvolution κ a b g t := by
  have hd (s : ℝ) : HasDerivAt (fun r => κ (t-r)) (-κ' (t-s)) s := by
    have hh := (hκ (t-s)).comp s ((hasDerivAt_id s).const_sub t)
    simp only [Function.comp_def, mul_neg, mul_one] at hh
    exact hh
  have hh := integral_derivative_mul_weak_curve hab hf hg heq hd
    (hκ'.comp (continuous_const.sub continuous_id)).neg
  simp only [hκa, hκb, zero_mul, sub_self, zero_sub, neg_mul, integral_neg] at hh
  exact neg_injective hh

/-- A genuine derivative of the smoothed weak curve, with the correct source
sign. The premise is only the already integrated original weak equation. -/
theorem timeConvolution_hasDerivAt_source {a b t C D : ℝ} (hab : a ≤ b)
    {f g κ κ' : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) (hg : IntegrableOn g (Icc a b))
    (heq : ∀ s ∈ Icc a b, f s-f a = ∫ r in a..s, g r)
    (hκ : ∀ x, HasDerivAt κ (κ' x) x) (hκ' : Continuous κ')
    (hC : ∀ x, ‖κ x‖ ≤ C) (hD : ∀ x, ‖κ' x‖ ≤ D)
    (hκa : κ (t-a) = 0) (hκb : κ (t-b) = 0) :
    HasDerivAt (timeConvolution κ a b f) (timeConvolution κ a b g t) t := by
  have hh := timeConvolution_hasDerivAt hκ hκ' hC hD hf.integrableOn_Icc t
  rw [timeConvolution_derivative_eq_source hab hf hg heq hκ hκ' hκa hκb] at hh
  exact hh

end SharpWasserstein.RoughEulerianTime
