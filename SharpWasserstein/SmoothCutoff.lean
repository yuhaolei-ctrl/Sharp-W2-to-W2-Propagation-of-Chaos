import SharpWasserstein.WeightedTangent
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.MulAction

/-!
# Smooth compact cutoffs for bounded smooth marginal lifts

A single smooth bump is dilated by radii `j+1`. The resulting cutoffs equal
one locally at every fixed point for all sufficiently large `j`. Their
gradient norm is bounded by a fixed constant divided by `j+1`.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff NNReal

namespace SharpWasserstein.SmoothCutoff

open WeightedTangent

def baseBump (d : ℕ) : ContDiffBump (0 : Point d) :=
  ⟨1, 2, by norm_num, by norm_num⟩

theorem base_lipschitz_exists (d : ℕ) :
    ∃ C : ℝ≥0, LipschitzWith C (baseBump d) := by
  have hb : ContDiff ℝ ∞ (baseBump d) := (baseBump d).contDiff
  exact ContDiff.lipschitzWith_of_hasCompactSupport (baseBump d).hasCompactSupport hb (by simp)

def baseLipschitzConstant (d : ℕ) : ℝ≥0 := Classical.choose (base_lipschitz_exists d)

theorem base_lipschitz (d : ℕ) : LipschitzWith (baseLipschitzConstant d) (baseBump d) :=
  Classical.choose_spec (base_lipschitz_exists d)

def cutoff (d j : ℕ) (x : Point d) : ℝ :=
  baseBump d (((j : ℝ) + 1)⁻¹ • x)

theorem cutoff_contDiff (d j : ℕ) : ContDiff ℝ ∞ (cutoff d j) := by
  exact (baseBump d).contDiff.comp (by fun_prop :
    ContDiff ℝ ∞ (fun x : Point d => ((j : ℝ) + 1)⁻¹ • x))

theorem cutoff_compact (d j : ℕ) : HasCompactSupport (cutoff d j) := by
  exact (baseBump d).hasCompactSupport.comp_smul (by positivity : ((j : ℝ) + 1)⁻¹ ≠ 0)

theorem cutoff_nonneg (d j : ℕ) (x : Point d) : 0 ≤ cutoff d j x :=
  (baseBump d).nonneg

theorem cutoff_abs_le_one (d j : ℕ) (x : Point d) : |cutoff d j x| ≤ 1 := by
  rw [abs_of_nonneg (cutoff_nonneg d j x)]
  exact (baseBump d).le_one

theorem norm_gradient_eq_fderiv {d : ℕ} (f : Point d → ℝ) (x : Point d) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  simp [gradient]

/-- The derivative bound decays with the radius and uses the Euclidean gradient. -/
theorem cutoff_gradient_bound_scaled (d j : ℕ) (x : Point d) :
    ‖gradient (cutoff d j) x‖ ≤ (baseLipschitzConstant d : ℝ) / ((j : ℝ) + 1) := by
  have hl := (base_lipschitz d).comp
    (lipschitzWith_smul (((j : ℝ) + 1)⁻¹) (β := Point d))
  have hd := norm_fderiv_le_of_lipschitz (x₀ := x) ℝ hl
  rw [norm_gradient_eq_fderiv]
  change ‖fderiv ℝ (fun y : Point d => baseBump d (((j : ℝ) + 1)⁻¹ • y)) x‖ ≤ _
  simpa only [Function.comp_def, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs,
    abs_inv, abs_of_pos (by positivity : 0 < (j : ℝ) + 1), div_eq_mul_inv] using hd

theorem cutoff_gradient_bound (d j : ℕ) (x : Point d) :
    ‖gradient (cutoff d j) x‖ ≤ (baseLipschitzConstant d : ℝ) := by
  apply (cutoff_gradient_bound_scaled d j x).trans
  apply (div_le_iff₀ (by positivity : 0 < (j : ℝ) + 1)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) j, (baseLipschitzConstant d).coe_nonneg]

/-- Every fixed point eventually has a neighborhood on which the cutoff equals one. -/
theorem cutoff_eventuallyEq_one {d : ℕ} (x : Point d) :
    ∀ᶠ j in atTop, cutoff d j =ᶠ[𝓝 x] (fun _ => 1) := by
  obtain ⟨J, hJ⟩ := exists_nat_gt ‖x‖
  filter_upwards [eventually_ge_atTop J] with j hj
  have hjpos : 0 < (j : ℝ) + 1 := by positivity
  have hnorm : ‖((j : ℝ) + 1)⁻¹ • x‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hjpos]
    rw [← div_eq_inv_mul, div_lt_one hjpos]
    exact hJ.trans (by exact_mod_cast Nat.lt_succ_of_le hj)
  have hloc := (baseBump d).eventuallyEq_one_of_mem_ball (by
    simpa only [Metric.mem_ball, dist_zero_right, baseBump] using hnorm)
  exact hloc.comp_tendsto ((show Continuous (fun y : Point d => ((j : ℝ) + 1)⁻¹ • y)
    from by fun_prop).tendsto x)

/-- Multiplying a smooth function by the cutoff gives an actual compact smooth test. -/
def approximate {d : ℕ} (f : Point d → ℝ) (hf : ContDiff ℝ ∞ f) (j : ℕ) : Test d :=
  ⟨cutoff d j * f, (cutoff_contDiff d j).mul hf, (cutoff_compact d j).mul_right⟩

theorem approximate_gradient_bound {d : ℕ} (f : Point d → ℝ) (hf : ContDiff ℝ ∞ f)
    {A B : ℝ} (hA : 0 ≤ A) (hfa : ∀ x, |f x| ≤ A)
    (hfb : ∀ x, ‖gradient f x‖ ≤ B) (j : ℕ) (x : Point d) :
    ‖gradient (approximate f hf j : Point d → ℝ) x‖ ≤
      B + A * (baseLipschitzConstant d : ℝ) := by
  rw [norm_gradient_eq_fderiv]
  change ‖fderiv ℝ (cutoff d j * f) x‖ ≤ _
  rw [fderiv_mul ((cutoff_contDiff d j).differentiable (by simp) x)
    (hf.differentiable (by simp) x)]
  calc
    ‖cutoff d j x • fderiv ℝ f x + f x • fderiv ℝ (cutoff d j) x‖ ≤
        ‖cutoff d j x • fderiv ℝ f x‖ + ‖f x • fderiv ℝ (cutoff d j) x‖ :=
      norm_add_le _ _
    _ = |cutoff d j x| * ‖gradient f x‖ + |f x| * ‖gradient (cutoff d j) x‖ := by
      simp only [norm_smul, Real.norm_eq_abs, norm_gradient_eq_fderiv]
    _ ≤ 1 * B + A * (baseLipschitzConstant d : ℝ) := add_le_add
      (mul_le_mul (cutoff_abs_le_one d j x) (hfb x) (norm_nonneg _) (by norm_num))
      (mul_le_mul (hfa x) (cutoff_gradient_bound d j x) (norm_nonneg _) hA)
    _ = B + A * (baseLipschitzConstant d : ℝ) := by ring

theorem approximate_gradient_eventuallyEq {d : ℕ} (f : Point d → ℝ)
    (hf : ContDiff ℝ ∞ f) (x : Point d) :
    ∀ᶠ j in atTop, gradient (approximate f hf j : Point d → ℝ) x = gradient f x := by
  filter_upwards [cutoff_eventuallyEq_one x] with j hj
  apply Filter.EventuallyEq.gradient_eq
  filter_upwards [hj] with y hy
  change cutoff d j y * f y = f y
  rw [hy, one_mul]

/-- Every bounded smooth function with bounded gradient has compact smooth
approximants whose gradients are uniformly bounded and eventually equal to
the original gradient at every point. This is the input to L² dominated convergence. -/
theorem exists_test_approximation {d : ℕ} (f : Point d → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfa : ∃ A : ℝ, ∀ x, |f x| ≤ A) (hfb : ∃ B : ℝ, ∀ x, ‖gradient f x‖ ≤ B) :
    ∃ (φ : ℕ → Test d) (C : ℝ), 0 ≤ C ∧
      (∀ j x, ‖gradient (φ j : Point d → ℝ) x‖ ≤ C) ∧
      (∀ x, ∀ᶠ j in atTop, gradient (φ j : Point d → ℝ) x = gradient f x) := by
  obtain ⟨A, hA⟩ := hfa
  obtain ⟨B, hB⟩ := hfb
  have hA₀ : 0 ≤ A := (abs_nonneg (f 0)).trans (hA 0)
  have hB₀ : 0 ≤ B := (norm_nonneg (gradient f 0)).trans (hB 0)
  refine ⟨approximate f hf, B + A * (baseLipschitzConstant d : ℝ), by positivity, ?_, ?_⟩
  · exact approximate_gradient_bound f hf hA₀ hA hB
  · exact approximate_gradient_eventuallyEq f hf

end SharpWasserstein.SmoothCutoff
