/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Minkowski's inequality for square-integrable configuration fields

The source estimate of the paper (proof of Proposition 3.6, `prop:source`) combines its two
terms by Minkowski's inequality in `L²(R^{(m)}_s; (ℝᵈ)^m)`: the norm of the sum of the internal
and the external part of the representing field is at most the sum of their norms. A field on
`(ℝᵈ)^m` is a function `f : X → Fin m → E`, and its squared `L²` norm is
`∫ ∑ᵢ ‖f(x)ᵢ‖² dμ`, the norm on `(ℝᵈ)^m` being the unnormalized one of the paper.

This file proves this form of Minkowski's inequality for bounded measurable fields, through the
`L²` seminorm `eLpNorm · 2 μ` of the field regarded as a function with values in
`PiLp 2 (fun _ : Fin m => E)`.

## Main statements

* `eLpNorm_two_eq_ofReal_sqrt`: `‖f‖_{L²} = √(∫ ‖f‖² dμ)` for `f ∈ L²`.
* `eLpNorm_toLp_eq`: the `L²` seminorm of a bounded measurable field is `√(∫ ∑ᵢ ‖fᵢ‖² dμ)`.
* `sqrt_integral_sum_norm_sq_add_le`: **Minkowski's inequality**
  `√(∫ ∑ᵢ ‖fᵢ + gᵢ‖²) ≤ √(∫ ∑ᵢ ‖fᵢ‖²) + √(∫ ∑ᵢ ‖gᵢ‖²)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SharpWasserstein.Sharp.Source

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The `L²` seminorm of a square-integrable function is the square root of the integral of
its squared norm. -/
theorem eLpNorm_two_eq_ofReal_sqrt {F : Type*} [NormedAddCommGroup F] {f : X → F}
    (hf : MemLp f 2 μ) : eLpNorm f 2 μ = ENNReal.ofReal (√(∫ x, ‖f x‖ ^ 2 ∂μ)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow, one_div]

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {m : ℕ}

/-- A measurable field with values in `(ℝᵈ)^m`, regarded as a function with values in the
`ℓ²` product, is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_toLp {f : X → Fin m → E} (hf : ∀ i, Measurable fun x => f x i) :
    AEStronglyMeasurable (fun x => WithLp.toLp 2 (f x)) μ :=
  (PiLp.continuous_toLp 2 _).comp_aestronglyMeasurable
    (Measurable.of_eval hf).aestronglyMeasurable

/-- A bounded measurable field is square integrable for a finite measure. -/
theorem memLp_toLp [IsFiniteMeasure μ] {f : X → Fin m → E} (hf : ∀ i, Measurable fun x => f x i)
    {C : ℝ} (hC : ∀ x i, ‖f x i‖ ≤ C) :
    MemLp (fun x => WithLp.toLp 2 (f x)) 2 μ := by
  refine MemLp.of_bound (aestronglyMeasurable_toLp hf) (√(∑ _i : Fin m, C ^ 2))
    (ae_of_all _ fun x => ?_)
  rw [PiLp.norm_eq_of_L2]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  exact pow_le_pow_left₀ (norm_nonneg _) (hC x i) 2

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The squared norm of a field in the `ℓ²` product is the sum of the squared norms of its
components. -/
theorem norm_toLp_sq_eq_sum (f : Fin m → E) :
    ‖(WithLp.toLp 2 f : PiLp 2 (fun _ : Fin m => E))‖ ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]

/-- The `L²` seminorm of a bounded measurable field is `√(∫ ∑ᵢ ‖fᵢ‖² dμ)`. -/
theorem eLpNorm_toLp_eq [IsFiniteMeasure μ] {f : X → Fin m → E}
    (hf : ∀ i, Measurable fun x => f x i) {C : ℝ} (hC : ∀ x i, ‖f x i‖ ≤ C) :
    eLpNorm (fun x => WithLp.toLp 2 (f x)) 2 μ =
      ENNReal.ofReal (√(∫ x, ∑ i, ‖f x i‖ ^ 2 ∂μ)) := by
  rw [eLpNorm_two_eq_ofReal_sqrt (memLp_toLp hf hC)]
  simp_rw [norm_toLp_sq_eq_sum]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The integral `∫ ∑ᵢ ‖fᵢ‖² dμ` is nonnegative. -/
theorem integral_sum_norm_sq_nonneg (f : X → Fin m → E) :
    0 ≤ ∫ x, ∑ i, ‖f x i‖ ^ 2 ∂μ :=
  integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Scaling a field by `c` multiplies `∫ ∑ᵢ ‖fᵢ‖² dμ` by `c²`. -/
theorem integral_sum_norm_smul_sq [NormedSpace ℝ E] (c : ℝ) (f : X → Fin m → E) :
    ∫ x, ∑ i, ‖c • f x i‖ ^ 2 ∂μ = c ^ 2 * ∫ x, ∑ i, ‖f x i‖ ^ 2 ∂μ := by
  simp_rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← Finset.mul_sum]
  exact integral_const_mul _ _

/-- **Minkowski's inequality** in `L²(μ; (ℝᵈ)^m)` for bounded measurable fields:
`√(∫ ∑ᵢ ‖fᵢ + gᵢ‖²) ≤ √(∫ ∑ᵢ ‖fᵢ‖²) + √(∫ ∑ᵢ ‖gᵢ‖²)`. -/
theorem sqrt_integral_sum_norm_sq_add_le [IsFiniteMeasure μ] {f g : X → Fin m → E}
    (hf : ∀ i, Measurable fun x => f x i) (hg : ∀ i, Measurable fun x => g x i) {Cf Cg : ℝ}
    (hCf : ∀ x i, ‖f x i‖ ≤ Cf) (hCg : ∀ x i, ‖g x i‖ ≤ Cg) :
    √(∫ x, ∑ i, ‖f x i + g x i‖ ^ 2 ∂μ) ≤
      √(∫ x, ∑ i, ‖f x i‖ ^ 2 ∂μ) + √(∫ x, ∑ i, ‖g x i‖ ^ 2 ∂μ) := by
  have hfg : ∀ i, Measurable fun x => f x i + g x i := fun i => (hf i).add (hg i)
  have hCfg : ∀ x i, ‖f x i + g x i‖ ≤ Cf + Cg := fun x i =>
    (norm_add_le _ _).trans (add_le_add (hCf x i) (hCg x i))
  have h := eLpNorm_add_le (μ := μ) (p := 2) (f := fun x => WithLp.toLp 2 (f x))
    (g := fun x => WithLp.toLp 2 (g x)) one_le_two
  have hsum : (fun x => WithLp.toLp 2 (f x)) + (fun x => WithLp.toLp 2 (g x)) =
      fun x => (WithLp.toLp 2 (fun i => f x i + g x i) : PiLp 2 (fun _ : Fin m => E)) := by
    funext x
    rfl
  rw [hsum, eLpNorm_toLp_eq hfg hCfg, eLpNorm_toLp_eq hf hCf, eLpNorm_toLp_eq hg hCg,
    ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

end SharpWasserstein.Sharp.Source
