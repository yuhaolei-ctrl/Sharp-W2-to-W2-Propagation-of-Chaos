/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Statement
public import SharpWasserstein.Sharp.ConvolutionDerivBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Smooth approximation of the coefficients

This file proves Lemma 7.1 (`lem:mollify`) of the paper *Sharp Wasserstein propagation of chaos
from correlated initial data*: under Assumption A there are coefficients `aⁿ ∈ C^∞_b` and
`Kⁿ ∈ C^∞_b` satisfying Assumption A with the same constants, such that `aⁿ → a` locally
uniformly, `‖Kⁿ - K‖ ≤ (L₁ + L₂) / (n + 1)`, and `‖aⁿ x‖ ≤ ‖a 0‖ + L_a (‖x‖ + 1)`.

Here `C^∞_b` is expressed by `ContDiff ℝ ∞` together with uniform bounds on the function and on
every `iteratedFDeriv`. The paper's `|Kⁿ - K| ≤ (L₁ + L₂) / n` is shifted to `n + 1` so that
`n = 0` is allowed.

## Construction

Following the paper, we use the coordinatewise sine map `θ_c(x)ₗ = c sin(xₗ / c)`
(`SharpWasserstein.Sharp.sinMap`), with `c = n + 1`. It is `1`-Lipschitz, has bounded image,
satisfies `‖θ_c x‖ ≤ ‖x‖`, and `‖θ_c x - x‖ ≤ ‖x‖³ / (6 c²)`. We set

* `aⁿ = (a ∘ θ_{n+1}) ⋆ ηₙ` (`SharpWasserstein.Sharp.smoothDrift`), and
* `Kⁿ = K ⋆ ηₙ` (`SharpWasserstein.Sharp.smoothKernel`), where the convolution is taken on the
  product space `ℝᵈ × ℝᵈ`,

where `ηₙ` is a normalized smooth bump function supported in the ball of radius `1 / (n + 1)`
(`SharpWasserstein.Sharp.mollifierBump`). Since the norm on `ℝᵈ × ℝᵈ` is the maximum norm, the
interaction bound `‖K(x, y) - K(x', y')‖ ≤ L₁ ‖x - x'‖ + L₂ ‖y - y'‖` gives
`‖Kⁿ - K‖ ≤ (L₁ + L₂) / (n + 1)`.

## Main result

* `SharpWasserstein.Sharp.exists_smooth_approx`: Lemma 7.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Function ContinuousLinearMap Filter Topology
open scoped Convolution ContDiff

namespace SharpWasserstein.Sharp

variable {d : ℕ}

/-! ### Coordinatewise bounds in `EuclideanSpace` -/

/-- If every coordinate of `u` is bounded in absolute value by the corresponding coordinate of
`v`, then `‖u‖ ≤ ‖v‖`. -/
theorem norm_le_norm_of_forall_abs_apply_le {u v : EuclideanSpace ℝ (Fin d)}
    (h : ∀ l, |u l| ≤ |v l|) : ‖u‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  gcongr with l
  simpa only [Real.norm_eq_abs] using h l

/-- A function satisfying `‖f x - f y‖ ≤ L ‖x - y‖` is continuous. -/
private theorem continuous_of_norm_sub_le {α β : Type*} [SeminormedAddCommGroup α]
    [SeminormedAddCommGroup β] {f : α → β} {L : ℝ} (h : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) :
    Continuous f := by
  refine (LipschitzWith.of_dist_le_mul (K := L.toNNReal) fun x y => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  exact (h x y).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (norm_nonneg _))

/-! ### The coordinatewise sine map -/

/-- The coordinatewise sine map `θ_c(x)ₗ = c sin(xₗ / c)`. For `c > 0` it is `1`-Lipschitz, has
bounded image and is close to the identity on bounded sets when `c` is large. -/
def sinMap (c : ℝ) (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun l => c * Real.sin (x l / c)

/-- The coordinates of the sine map. -/
@[simp]
theorem sinMap_apply (c : ℝ) (x : EuclideanSpace ℝ (Fin d)) (l : Fin d) :
    sinMap c x l = c * Real.sin (x l / c) :=
  rfl

/-- The sine map is `1`-Lipschitz. -/
theorem norm_sinMap_sub_sinMap_le {c : ℝ} (hc : 0 < c) (x y : EuclideanSpace ℝ (Fin d)) :
    ‖sinMap c x - sinMap c y‖ ≤ ‖x - y‖ := by
  refine norm_le_norm_of_forall_abs_apply_le fun l => ?_
  simp only [PiLp.sub_apply, sinMap_apply]
  rw [← mul_sub, abs_mul, abs_of_pos hc]
  calc c * |Real.sin (x l / c) - Real.sin (y l / c)| ≤ c * |x l / c - y l / c| :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le _ _) hc.le
    _ = |x l - y l| := by
        rw [← sub_div, abs_div, abs_of_pos hc]
        field_simp

/-- The sine map fixes the origin. -/
@[simp]
theorem sinMap_zero (c : ℝ) : sinMap c (0 : EuclideanSpace ℝ (Fin d)) = 0 := by
  ext l
  simp

/-- The sine map does not increase norms. -/
theorem norm_sinMap_le {c : ℝ} (hc : 0 < c) (x : EuclideanSpace ℝ (Fin d)) :
    ‖sinMap c x‖ ≤ ‖x‖ := by
  simpa using norm_sinMap_sub_sinMap_le hc x 0

/-- The sine map has bounded image. -/
theorem exists_norm_sinMap_le (c : ℝ) :
    ∃ B, ∀ x : EuclideanSpace ℝ (Fin d), ‖sinMap c x‖ ≤ B := by
  refine ⟨‖(WithLp.toLp 2 fun _ => c : EuclideanSpace ℝ (Fin d))‖, fun x =>
    norm_le_norm_of_forall_abs_apply_le fun l => ?_⟩
  rw [sinMap_apply, PiLp.toLp_apply, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg c) (Real.abs_sin_le_one _)

/-- The sine map is close to the identity: `‖θ_c x - x‖ ≤ ‖x‖³ / (6 c²)`. -/
theorem norm_sinMap_sub_self_le {c : ℝ} (hc : 0 < c) (x : EuclideanSpace ℝ (Fin d)) :
    ‖sinMap c x - x‖ ≤ ‖x‖ ^ 3 / (6 * c ^ 2) := by
  have key : ∀ l, |(sinMap c x - x) l| ≤ |((‖x‖ ^ 2 / (6 * c ^ 2)) • x) l| := by
    intro l
    have hxl : |x l| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x l
    have h₁ : c * Real.sin (x l / c) - x l = -(c * (x l / c - Real.sin (x l / c))) := by
      field_simp
      ring
    rw [PiLp.sub_apply, sinMap_apply, h₁, abs_neg, abs_mul, abs_of_pos hc, PiLp.smul_apply,
      smul_eq_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2 / (6 * c ^ 2))]
    calc c * |x l / c - Real.sin (x l / c)| ≤ c * (|x l / c| ^ 3 / 6) :=
          mul_le_mul_of_nonneg_left (Real.abs_sub_sin_le _) hc.le
      _ = |x l| ^ 2 / (6 * c ^ 2) * |x l| := by
          rw [abs_div, abs_of_pos hc]
          field_simp
      _ ≤ ‖x‖ ^ 2 / (6 * c ^ 2) * |x l| := by gcongr
  calc ‖sinMap c x - x‖ ≤ ‖(‖x‖ ^ 2 / (6 * c ^ 2)) • x‖ := norm_le_norm_of_forall_abs_apply_le key
    _ = ‖x‖ ^ 3 / (6 * c ^ 2) := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        ring

/-! ### The mollifiers -/

/-- The smooth bump function with inner radius `1 / (2 (n + 1))` and outer radius `1 / (n + 1)`.
Its normalization `(mollifierBump G n).normed μ` is the mollifier `ηₙ`: a smooth nonnegative
function supported in the ball of radius `1 / (n + 1)` with integral `1`. -/
def mollifierBump (G : Type*) [NormedAddCommGroup G] (n : ℕ) : ContDiffBump (0 : G) where
  rIn := 1 / (2 * (n + 1))
  rOut := 1 / (n + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := one_div_lt_one_div_of_lt (by positivity) (by linarith [n.cast_nonneg (α := ℝ)])

/-- The outer radius of `ηₙ` is `1 / (n + 1)`. -/
@[simp]
theorem mollifierBump_rOut (G : Type*) [NormedAddCommGroup G] (n : ℕ) :
    (mollifierBump G n).rOut = 1 / (n + 1) :=
  rfl

/-- The smooth approximation `aⁿ = (a ∘ θ_{n+1}) ⋆ ηₙ` of the drift `a`. -/
def smoothDrift (a : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
  (mollifierBump _ n).normed volume ⋆[lsmul ℝ ℝ, volume] (a ∘ sinMap (n + 1))

/-- The smooth approximation `Kⁿ = K ⋆ ηₙ` of the interaction `K`, where the convolution is
taken on the product space `ℝᵈ × ℝᵈ` with the product Lebesgue measure. -/
def smoothKernel
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (n : ℕ) (x y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ((mollifierBump _ n).normed ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume)
    ⋆[lsmul ℝ ℝ, (volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume] uncurry K) (x, y)

/-- As a function on `ℝᵈ × ℝᵈ`, the approximate interaction `Kⁿ` is the convolution of
`uncurry K` with `ηₙ`. -/
theorem uncurry_smoothKernel
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (n : ℕ) :
    uncurry (smoothKernel K n) =
      (mollifierBump _ n).normed ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume)
        ⋆[lsmul ℝ ℝ, (volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume] uncurry K :=
  rfl

/-! ### Properties of the approximations -/

section Properties

variable {a : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
  {K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
  {La L₁ L₂ M : ℝ}

/-- Under Assumption A, `a ∘ θ_c` is continuous. -/
theorem continuous_comp_sinMap (hA : SharpChaos.AssumptionA a K La L₁ L₂ M) {c : ℝ}
    (hc : 0 < c) : Continuous (a ∘ sinMap c) :=
  continuous_of_norm_sub_le (L := La) fun x y =>
    (hA.lipschitz_a _ _).trans
      (mul_le_mul_of_nonneg_left (norm_sinMap_sub_sinMap_le hc x y) hA.La_nonneg)

/-- Under Assumption A, `K` is jointly continuous. -/
theorem continuous_uncurry_of_assumptionA (hA : SharpChaos.AssumptionA a K La L₁ L₂ M) :
    Continuous (uncurry K) := by
  refine continuous_of_norm_sub_le (L := L₁ + L₂) fun z z' => ?_
  calc ‖K z.1 z.2 - K z'.1 z'.2‖ ≤ L₁ * ‖z.1 - z'.1‖ + L₂ * ‖z.2 - z'.2‖ :=
        hA.lipschitz_K _ _ _ _
    _ ≤ L₁ * ‖z - z'‖ + L₂ * ‖z - z'‖ := by
        gcongr
        · exact hA.L₁_nonneg
        · exact norm_fst_le (z - z')
        · exact hA.L₂_nonneg
        · exact norm_snd_le (z - z')
    _ = (L₁ + L₂) * ‖z - z'‖ := by ring

private theorem one_div_nat_add_one_le_one (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ 1 := by
  rw [div_le_one (by positivity)]
  linarith [n.cast_nonneg (α := ℝ)]

/-- The approximate drift `aⁿ` is `L_a`-Lipschitz. -/
theorem norm_smoothDrift_sub_smoothDrift_le (hA : SharpChaos.AssumptionA a K La L₁ L₂ M)
    (n : ℕ) (x x' : EuclideanSpace ℝ (Fin d)) :
    ‖smoothDrift a n x - smoothDrift a n x'‖ ≤ La * ‖x - x'‖ := by
  have hg := (continuous_comp_sinMap hA (c := n + 1) (by positivity)).locallyIntegrable
    (μ := volume)
  refine norm_normed_convolution_sub_le _ hg hg fun t _ => ?_
  calc ‖a (sinMap (n + 1) (x - t)) - a (sinMap (n + 1) (x' - t))‖
      ≤ La * ‖sinMap (n + 1) (x - t) - sinMap (n + 1) (x' - t)‖ := hA.lipschitz_a _ _
    _ ≤ La * ‖(x - t) - (x' - t)‖ := by
        gcongr
        · exact hA.La_nonneg
        · exact norm_sinMap_sub_sinMap_le (by positivity) _ _
    _ = La * ‖x - x'‖ := by rw [sub_sub_sub_cancel_right]

/-- The growth bound `‖aⁿ x‖ ≤ ‖a 0‖ + L_a (‖x‖ + 1)`. -/
theorem norm_smoothDrift_le (hA : SharpChaos.AssumptionA a K La L₁ L₂ M) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : ‖smoothDrift a n x‖ ≤ ‖a 0‖ + La * (‖x‖ + 1) := by
  refine norm_normed_convolution_le _ fun t ht => ?_
  have ht' : ‖t‖ ≤ 1 := by
    rw [mem_ball_zero_iff, mollifierBump_rOut] at ht
    exact ht.le.trans (one_div_nat_add_one_le_one n)
  calc ‖a (sinMap (n + 1) (x - t))‖ ≤ ‖a 0‖ + ‖a (sinMap (n + 1) (x - t)) - a 0‖ :=
        norm_le_norm_add_norm_sub' _ _
    _ ≤ ‖a 0‖ + La * ‖sinMap (n + 1) (x - t) - 0‖ := by
        gcongr
        exact hA.lipschitz_a _ _
    _ ≤ ‖a 0‖ + La * (‖x‖ + 1) := by
        gcongr
        · exact hA.La_nonneg
        rw [sub_zero]
        calc ‖sinMap (n + 1) (x - t)‖ ≤ ‖x - t‖ := norm_sinMap_le (by positivity) _
          _ ≤ ‖x‖ + ‖t‖ := norm_sub_le _ _
          _ ≤ ‖x‖ + 1 := by gcongr

/-- The approximate drift is close to `a`: `‖aⁿ x - a x‖ ≤ L_a (1 + ‖x‖³) / (n + 1)`. -/
theorem norm_smoothDrift_sub_le (hA : SharpChaos.AssumptionA a K La L₁ L₂ M) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖smoothDrift a n x - a x‖ ≤ La * (1 + ‖x‖ ^ 3) / (n + 1) := by
  set c : ℝ := n + 1 with hc_def
  have hc : 1 ≤ c := by linarith [n.cast_nonneg (α := ℝ)]
  have hc0 : 0 < c := by positivity
  have hLa := hA.La_nonneg
  have h₁ : ‖smoothDrift a n x - a (sinMap c x)‖ ≤ La / c := by
    rw [← dist_eq_norm]
    refine (mollifierBump _ n).dist_normed_convolution_le
      (continuous_comp_sinMap hA hc0).aestronglyMeasurable fun y hy => ?_
    rw [mem_ball, mollifierBump_rOut] at hy
    rw [dist_eq_norm]
    calc ‖a (sinMap c y) - a (sinMap c x)‖ ≤ La * ‖sinMap c y - sinMap c x‖ :=
          hA.lipschitz_a _ _
      _ ≤ La * ‖y - x‖ := by gcongr; exact norm_sinMap_sub_sinMap_le hc0 _ _
      _ ≤ La * (1 / c) := by gcongr; rw [← dist_eq_norm]; exact hy.le
      _ = La / c := by ring
  have h₂ : ‖a (sinMap c x) - a x‖ ≤ La * ‖x‖ ^ 3 / c := by
    calc ‖a (sinMap c x) - a x‖ ≤ La * ‖sinMap c x - x‖ := hA.lipschitz_a _ _
      _ ≤ La * (‖x‖ ^ 3 / (6 * c ^ 2)) := by gcongr; exact norm_sinMap_sub_self_le hc0 x
      _ ≤ La * (‖x‖ ^ 3 / c) := by
          gcongr
          nlinarith
      _ = La * ‖x‖ ^ 3 / c := by ring
  calc ‖smoothDrift a n x - a x‖
      ≤ ‖smoothDrift a n x - a (sinMap c x)‖ + ‖a (sinMap c x) - a x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ La / c + La * ‖x‖ ^ 3 / c := add_le_add h₁ h₂
    _ = La * (1 + ‖x‖ ^ 3) / c := by ring

/-- The approximate drifts converge to `a` locally uniformly. -/
theorem tendstoLocallyUniformly_smoothDrift (hA : SharpChaos.AssumptionA a K La L₁ L₂ M) :
    TendstoLocallyUniformly (smoothDrift a) a atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  refine ⟨ball x 1, ball_mem_nhds x one_pos, ?_⟩
  set R := ‖x‖ + 1
  have hlim : Tendsto (fun n : ℕ => La * (1 + R ^ 3) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (La * (1 + R ^ 3))
    rwa [mul_zero] at this
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn y hy
  have hyR : ‖y‖ ≤ R := by
    rw [mem_ball, dist_eq_norm] at hy
    calc ‖y‖ ≤ ‖x‖ + ‖y - x‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ R := by simp only [R]; gcongr
  rw [dist_comm, dist_eq_norm]
  calc ‖smoothDrift a n y - a y‖ ≤ La * (1 + ‖y‖ ^ 3) / (n + 1) := norm_smoothDrift_sub_le hA n y
    _ ≤ La * (1 + R ^ 3) / (n + 1) := by
        gcongr
        · exact hA.La_nonneg
    _ = La * (1 + R ^ 3) * (1 / ((n : ℝ) + 1)) := by ring
    _ < ε := hn

/-- The approximate drift `aⁿ` is smooth. -/
theorem contDiff_smoothDrift (hA : SharpChaos.AssumptionA a K La L₁ L₂ M) (n : ℕ) :
    ContDiff ℝ ∞ (smoothDrift a n) :=
  contDiff_normed_convolution _
    ((continuous_comp_sinMap hA (c := n + 1) (by positivity)).locallyIntegrable)

/-- The approximate drift `aⁿ` has bounded derivatives of all orders. -/
theorem exists_bound_iteratedFDeriv_smoothDrift (hA : SharpChaos.AssumptionA a K La L₁ L₂ M)
    (n k : ℕ) : ∃ C, ∀ x, ‖iteratedFDeriv ℝ k (smoothDrift a n) x‖ ≤ C := by
  obtain ⟨B, hB⟩ := exists_norm_sinMap_le (d := d) (n + 1)
  refine exists_bound_iteratedFDeriv_normed_convolution _
    ((continuous_comp_sinMap hA (c := n + 1) (by positivity)).locallyIntegrable)
    ⟨‖a 0‖ + La * B, fun y => ?_⟩ k
  calc ‖a (sinMap (n + 1) y)‖ ≤ ‖a 0‖ + ‖a (sinMap (n + 1) y) - a 0‖ :=
        norm_le_norm_add_norm_sub' _ _
    _ ≤ ‖a 0‖ + La * ‖sinMap (n + 1) y - 0‖ := by
        gcongr
        exact hA.lipschitz_a _ _
    _ ≤ ‖a 0‖ + La * B := by
        gcongr
        · exact hA.La_nonneg
        · rw [sub_zero]; exact hB y

/-- The approximate interaction `Kⁿ` is bounded by `M`. -/
theorem norm_smoothKernel_le (hA : SharpChaos.AssumptionA a K La L₁ L₂ M) (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin d)) : ‖smoothKernel K n x y‖ ≤ M :=
  norm_normed_convolution_le _ fun _ _ => hA.norm_K_le _ _

/-- The approximate interaction `Kⁿ` satisfies the Lipschitz bound of Assumption A. -/
theorem norm_smoothKernel_sub_smoothKernel_le (hA : SharpChaos.AssumptionA a K La L₁ L₂ M)
    (n : ℕ) (x x' y y' : EuclideanSpace ℝ (Fin d)) :
    ‖smoothKernel K n x y - smoothKernel K n x' y'‖ ≤ L₁ * ‖x - x'‖ + L₂ * ‖y - y'‖ := by
  have hg := (continuous_uncurry_of_assumptionA hA).locallyIntegrable
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume)
  refine norm_normed_convolution_sub_le _ hg hg fun t _ => ?_
  simpa only [uncurry_def, Prod.fst_sub, Prod.snd_sub, sub_sub_sub_cancel_right] using
    hA.lipschitz_K (x - t.1) (x' - t.1) (y - t.2) (y' - t.2)

/-- The approximate interaction is uniformly close to `K`:
`‖Kⁿ x y - K x y‖ ≤ (L₁ + L₂) / (n + 1)`. -/
theorem norm_smoothKernel_sub_le (hA : SharpChaos.AssumptionA a K La L₁ L₂ M) (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    ‖smoothKernel K n x y - K x y‖ ≤ (L₁ + L₂) / (n + 1) := by
  rw [← dist_eq_norm]
  refine (mollifierBump _ n).dist_normed_convolution_le (x₀ := (x, y))
    (continuous_uncurry_of_assumptionA hA).aestronglyMeasurable fun z hz => ?_
  rw [mem_ball, mollifierBump_rOut, Prod.dist_eq, max_lt_iff] at hz
  rw [dist_eq_norm]
  calc ‖K z.1 z.2 - K x y‖ ≤ L₁ * ‖z.1 - x‖ + L₂ * ‖z.2 - y‖ := hA.lipschitz_K _ _ _ _
    _ ≤ L₁ * (1 / (n + 1)) + L₂ * (1 / (n + 1)) := by
        rw [← dist_eq_norm, ← dist_eq_norm]
        gcongr
        · exact hA.L₁_nonneg
        · exact hz.1.le
        · exact hA.L₂_nonneg
        · exact hz.2.le
    _ = (L₁ + L₂) / (n + 1) := by ring

/-- The approximate interaction `Kⁿ` is jointly smooth. -/
theorem contDiff_uncurry_smoothKernel (hA : SharpChaos.AssumptionA a K La L₁ L₂ M) (n : ℕ) :
    ContDiff ℝ ∞ (uncurry (smoothKernel K n)) := by
  rw [uncurry_smoothKernel]
  exact contDiff_normed_convolution _ (continuous_uncurry_of_assumptionA hA).locallyIntegrable

/-- The approximate interaction `Kⁿ` has bounded derivatives of all orders. -/
theorem exists_bound_iteratedFDeriv_uncurry_smoothKernel
    (hA : SharpChaos.AssumptionA a K La L₁ L₂ M) (n k : ℕ) :
    ∃ C, ∀ z, ‖iteratedFDeriv ℝ k (uncurry (smoothKernel K n)) z‖ ≤ C := by
  rw [uncurry_smoothKernel]
  exact exists_bound_iteratedFDeriv_normed_convolution _
    (continuous_uncurry_of_assumptionA hA).locallyIntegrable ⟨M, fun z => hA.norm_K_le z.1 z.2⟩ k

/-- The approximations satisfy Assumption A with the same constants. -/
theorem assumptionA_smoothDrift_smoothKernel (hA : SharpChaos.AssumptionA a K La L₁ L₂ M)
    (n : ℕ) :
    SharpChaos.AssumptionA (smoothDrift a n) (smoothKernel K n) La L₁ L₂ M where
  La_nonneg := hA.La_nonneg
  L₁_nonneg := hA.L₁_nonneg
  L₂_nonneg := hA.L₂_nonneg
  M_nonneg := hA.M_nonneg
  lipschitz_a := norm_smoothDrift_sub_smoothDrift_le hA n
  norm_K_le := norm_smoothKernel_le hA n
  lipschitz_K := norm_smoothKernel_sub_smoothKernel_le hA n

end Properties

/-! ### Lemma 7.1 -/

/-- **Lemma 7.1** (`lem:mollify`). Under Assumption A there are smooth coefficients `aⁿ` and
`Kⁿ`, bounded together with all their derivatives, satisfying Assumption A with the same
constants, such that `aⁿ → a` locally uniformly, `‖Kⁿ - K‖ ≤ (L₁ + L₂) / (n + 1)`, and
`‖aⁿ x‖ ≤ ‖a 0‖ + L_a (‖x‖ + 1)` for all `n` and `x`. -/
theorem exists_smooth_approx {a : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {La L₁ L₂ M : ℝ} (hA : SharpChaos.AssumptionA a K La L₁ L₂ M) :
    ∃ (aₙ : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (Kₙ : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →
        EuclideanSpace ℝ (Fin d)),
      (∀ n, SharpChaos.AssumptionA (aₙ n) (Kₙ n) La L₁ L₂ M) ∧
      (∀ n, ContDiff ℝ ∞ (aₙ n)) ∧ (∀ n, ContDiff ℝ ∞ (uncurry (Kₙ n))) ∧
      (∀ n, ∃ C, ∀ x, ‖aₙ n x‖ ≤ C) ∧
      (∀ n k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k (aₙ n) x‖ ≤ C) ∧
      (∀ n k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ k (uncurry (Kₙ n)) z‖ ≤ C) ∧
      TendstoLocallyUniformly aₙ a atTop ∧
      (∀ n x y, ‖Kₙ n x y - K x y‖ ≤ (L₁ + L₂) / (n + 1)) ∧
      (∀ n x, ‖aₙ n x‖ ≤ ‖a 0‖ + La * (‖x‖ + 1)) := by
  refine ⟨smoothDrift a, smoothKernel K, assumptionA_smoothDrift_smoothKernel hA,
    contDiff_smoothDrift hA, contDiff_uncurry_smoothKernel hA, fun n => ?_,
    exists_bound_iteratedFDeriv_smoothDrift hA,
    exists_bound_iteratedFDeriv_uncurry_smoothKernel hA, tendstoLocallyUniformly_smoothDrift hA,
    norm_smoothKernel_sub_le hA, norm_smoothDrift_le hA⟩
  obtain ⟨C, hC⟩ := exists_bound_iteratedFDeriv_smoothDrift hA n 0
  exact ⟨C, fun x => by simpa using hC x⟩

end SharpWasserstein.Sharp
