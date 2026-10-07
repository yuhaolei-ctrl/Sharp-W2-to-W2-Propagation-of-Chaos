module

public import SharpWasserstein.Compat
public import SharpWasserstein.RoughEulerianSmoothingAction
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section

/-! A concrete stationary probability floor: the normalized Euclidean
Gaussian exponential. Positivity, smoothness, normalization, and finite
quadratic moment are proved for the actual Lebesgue integrals. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff NNReal
namespace SharpWasserstein.RoughEulerianSmoothing
open WeightedTangent
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

theorem gaussian_exponential_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Point d => Real.exp (-c * ‖x‖^2)) := by
  have hh := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (b := (c : ℂ)) (by simpa using hc) 0 (0 : Point d)).re
  convert hh using 1
  funext x
  simp [← Complex.ofReal_pow, Complex.exp_re]

def gaussianNormalizer (d : ℕ) [MeasurableSpace (Point d)] [BorelSpace (Point d)] : ℝ :=
  ∫ x : Point d, Real.exp (-‖x‖^2)

theorem gaussianNormalizer_pos : 0 < gaussianNormalizer d := by
  apply integral_exp_pos
  simpa using (gaussian_exponential_integrable (d := d) (c := 1) (by norm_num))

def gaussianFloor (x : Point d) : ℝ := Real.exp (-‖x‖^2) / gaussianNormalizer d

theorem gaussianFloor_pos (x : Point d) : 0 < gaussianFloor x :=
  div_pos (Real.exp_pos _) gaussianNormalizer_pos

theorem gaussianFloor_smooth : ContDiff ℝ ∞ (gaussianFloor : Point d → ℝ) :=
  ((contDiff_norm_sq ℝ).neg.exp).div_const _

theorem gaussianFloor_integrable : Integrable (gaussianFloor : Point d → ℝ) := by
  have hh : Integrable (fun x : Point d => Real.exp (-‖x‖^2)) := by
    simpa using (gaussian_exponential_integrable (d := d) (c := 1) (by norm_num))
  exact hh.div_const _

theorem gaussianFloor_integral : (∫ x : Point d, gaussianFloor x) = 1 := by
  unfold gaussianFloor
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const]
  exact mul_inv_cancel₀ gaussianNormalizer_pos.ne'

omit [MeasurableSpace (Point d)] [BorelSpace (Point d)] in
theorem normsq_mul_gaussian_exponential_le (x : Point d) :
    ‖x‖^2 * Real.exp (-‖x‖^2) ≤ 2 * Real.exp (-(1/2 : ℝ) * ‖x‖^2) := by
  have hh := Real.add_one_le_exp (‖x‖^2/2)
  have hmul := mul_le_mul_of_nonneg_right (by linarith : ‖x‖^2 ≤ 2*Real.exp (‖x‖^2/2))
    (Real.exp_pos (-‖x‖^2)).le
  calc
    _ ≤ (2*Real.exp (‖x‖^2/2))*Real.exp (-‖x‖^2) := hmul
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem gaussianFloor_quadratic_integrable :
    Integrable (fun x : Point d => gaussianFloor x * ‖x‖^2) := by
  have hi : Integrable (fun x : Point d => ‖x‖^2 * Real.exp (-‖x‖^2)) := by
    apply Integrable.mono'
      ((gaussian_exponential_integrable (d := d) (c := 1/2) (by norm_num)).const_mul 2)
      (by fun_prop : Continuous (fun x : Point d => ‖x‖^2 * Real.exp (-‖x‖^2))).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
      exact normsq_mul_gaussian_exponential_le x
  convert hi.div_const (gaussianNormalizer d) using 1
  funext x
  dsimp [gaussianFloor]
  ring

end SharpWasserstein.RoughEulerianSmoothing
