/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Pathwise estimates for integral equations with additive forcing

The stability Lemma 7.2 (`lem:stability`) of the paper compares, path by path, solutions of
stochastic differential equations driven by the same Brownian motion. With the noise frozen, a
strong solution is a continuous path `x : ℝ → V` solving the integral equation with additive
forcing
`x t = x₀ + ∫₀ᵗ u s (x s) ds + w t`, `t ∈ [0, T]`,
where `u` is the drift, `x₀` the initial value and `w = √2 W` the (continuous) forcing. This file
proves the deterministic estimates for such equations used in the paper, for a general real
normed space `V` (in the paper `V = (ℝ^d)^N` or `V = ℝ^d`).

* Grönwall's inequality in integral form: `f ≤ c + K ∫₀ᵗ f + ∫₀ᵗ g` on `[0, T]` with `K ≥ 0` and
  `g ≥ 0` gives `f t ≤ (c + ∫₀ᵗ g) e^{Kt}`. It is derived from the differential form
  `le_gronwallBound_of_liminf_deriv_right_le` of Mathlib.
* Integrated drift stability: if `x` and `y` solve with drifts `u` and `v`, the same forcing,
  and `u s` is `Λ`-Lipschitz, then
  `‖x t - y t‖ ≤ (‖x₀ - y₀‖ + ∫₀ᵗ ‖u s (y s) - v s (y s)‖ ds) e^{Λt}`.
  The forcing cancels in `x - y`, and only `u` needs to be Lipschitz. This is the bound behind
  the first claim of Lemma 7.2, with `u = b^n_N`, `v = b_N`; with `x₀ = y₀`, its squared form
  `‖x t - y t‖² ≤ T e^{2ΛT} ∫₀ᵀ ‖u s (y s) - v s (y s)‖² ds` (Cauchy–Schwarz) is the pathwise
  version of the display in the proof of Lemma 7.2. The same estimate with a constant majorant
  gives the bound `|Δ_t| ≤ 2MTe^{ΛT}/√N` in the proof of `prop:offdiag`.
* An a priori bound under the linear growth `‖u s p‖ ≤ β + Λ ‖p‖`, which controls the paths
  (and, after squaring, their second moments) by the initial value and the forcing, as needed
  for the dominated convergence argument of Lemma 7.2:
  `‖x t‖ ≤ (‖x₀‖ + β t + Λ ∫₀ᵗ ‖w s‖ ds) e^{Λt} + ‖w t‖`.
* Pathwise uniqueness for a Lipschitz drift, as in `lem:wellposed`.

## Main definitions

* `IsForcedSolution u w x₀ T x`: `x` solves `x t = x₀ + ∫₀ᵗ u s (x s) ds + w t` on `[0, T]`.

## Main statements

* `le_mul_exp_of_le_add_mul_integral`, `le_add_integral_mul_exp_of_le`,
  `le_add_integral_mul_exp_of_le_integral_add`: Grönwall's inequality in integral form, without
  and with a source term.
* `sq_integral_le_mul_integral_sq`: `(∫₀ᵗ g)² ≤ t ∫₀ᵗ g²`.
* `IsForcedSolution.norm_sub_le_of_le`, `IsForcedSolution.norm_sub_le`: integrated drift
  stability.
* `IsForcedSolution.eqOn`: uniqueness.
* `IsForcedSolution.norm_le`: the a priori bound.
* `IsForcedSolution.norm_sub_sq_le`, `IsForcedSolution.norm_sub_sq_le_horizon`,
  `IsForcedSolution.norm_sub_sq_le_horizon_same_initial`, `IsForcedSolution.norm_sq_le`,
  `IsForcedSolution.norm_sq_le_horizon`: squared forms, at time `t` and uniformly on `[0, T]`.
-/

@[expose] public section

open Set MeasureTheory Real

namespace SharpWasserstein.Sharp

/-! ### Grönwall's inequality in integral form -/

/-- For `t ∈ [0, T]`, the interval `[[0, t]]` is contained in `[0, T]`. -/
theorem uIcc_zero_subset_Icc_zero {t T : ℝ} (ht : t ∈ Icc 0 T) : uIcc 0 t ⊆ Icc 0 T := by
  rw [uIcc_of_le ht.1]
  exact Icc_subset_Icc_right ht.2

/-- A function continuous on `[0, T]` is interval integrable on `[0, t]` for `t ∈ [0, T]`. -/
theorem intervalIntegrable_of_continuousOn_Icc {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {t T : ℝ} (hf : ContinuousOn f (Icc 0 T)) (ht : t ∈ Icc 0 T) :
    IntervalIntegrable f volume 0 t :=
  (hf.mono (uIcc_zero_subset_Icc_zero ht)).intervalIntegrable

/-- If `g` is interval integrable on `[0, T]` and nonnegative there, then `t ↦ ∫₀ᵗ g` is
monotone on `[0, T]`: `∫₀ˢ g ≤ ∫₀ᵗ g` for `0 ≤ s ≤ t ≤ T`. -/
theorem integral_le_integral_of_nonneg {g : ℝ → ℝ} {s t T : ℝ}
    (hg : IntervalIntegrable g volume 0 T) (hg0 : ∀ r ∈ Icc 0 T, 0 ≤ g r) (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t ≤ T) :
    ∫ r in (0 : ℝ)..s, g r ≤ ∫ r in (0 : ℝ)..t, g r :=
  intervalIntegral.integral_mono_interval le_rfl hs hst
    (ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => hg0 r ⟨hr.1.le, hr.2.trans ht⟩)
    (hg.mono_set (uIcc_subset_uIcc_left (by
      rw [uIcc_of_le (hs.trans (hst.trans ht))]; exact ⟨hs.trans hst, ht⟩)))

/-- **Grönwall's inequality**, integral form, for a function continuous on `[0, T]`. Let `K ≥ 0`
and let `f : ℝ → ℝ` be continuous on `[0, T]` with `f s ≤ c + K ∫₀ˢ f` for `s ∈ [0, T]`. Then
`f t ≤ c e^{Kt}` for `t ∈ [0, T]`. See `le_mul_exp_of_le_add_mul_integral` for integrable `f`.

No sign condition on `f` or `c` is needed. The proof applies the differential form
`le_gronwallBound_of_liminf_deriv_right_le` to the primitive `s ↦ c + K ∫₀ˢ f`, after extending
`f` continuously to `ℝ` by `Set.projIcc`. -/
theorem le_mul_exp_of_le_add_mul_integral_of_continuousOn {f : ℝ → ℝ} {c K T t : ℝ}
    (hK : 0 ≤ K) (hf : ContinuousOn f (Icc 0 T))
    (h : ∀ s ∈ Icc 0 T, f s ≤ c + K * ∫ r in (0 : ℝ)..s, f r) (ht : t ∈ Icc 0 T) :
    f t ≤ c * exp (K * t) := by
  have hT : (0 : ℝ) ≤ T := ht.1.trans ht.2
  set g : ℝ → ℝ := fun s => f (projIcc 0 T hT s)
  have hg : Continuous g :=
    hf.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun s => (projIcc 0 T hT s).2)
  have hfg : ∀ s ∈ Icc 0 T, ∫ r in (0 : ℝ)..s, f r = ∫ r in (0 : ℝ)..s, g r := by
    intro s hs
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hs.1] at hr
    simp [g, projIcc_of_mem hT ⟨hr.1, hr.2.trans hs.2⟩]
  have hgf : ∀ s ∈ Icc 0 T, g s = f s := fun s hs => by simp [g, projIcc_of_mem hT hs]
  set F : ℝ → ℝ := fun s => c + K * ∫ r in (0 : ℝ)..s, g r
  have hFderiv : ∀ s, HasDerivAt F (K * g s) s := fun s =>
    ((hg.integral_hasStrictDerivAt 0 s).hasDerivAt.const_mul K).const_add c
  have hFcont : Continuous F :=
    continuous_iff_continuousAt.2 fun s => (hFderiv s).continuousAt
  have hfF : ∀ s ∈ Icc 0 T, f s ≤ F s := fun s hs => by
    simpa [F, hfg s hs] using h s hs
  have key := le_gronwallBound_of_liminf_deriv_right_le (f := F) (f' := fun s => K * g s)
    (δ := c) (K := K) (ε := 0) (a := 0) (b := T) hFcont.continuousOn
    (fun s _ r hr => by
      simpa only [slope, vsub_eq_sub, smul_eq_mul] using
        (hFderiv s).hasDerivWithinAt.liminf_right_slope_le hr)
    (by simp [F])
    (fun s hs => by
      rw [add_zero, hgf s (Ico_subset_Icc_self hs)]
      exact mul_le_mul_of_nonneg_left (hfF s (Ico_subset_Icc_self hs)) hK) t ht
  rw [sub_zero, gronwallBound_ε0] at key
  exact (hfF t ht).trans key

/-- **Grönwall's inequality**, integral form. Let `K ≥ 0` and let `f : ℝ → ℝ` be interval
integrable on `[0, T]` with `f s ≤ c + K ∫₀ˢ f` for `s ∈ [0, T]`. Then `f t ≤ c e^{Kt}` for
`t ∈ [0, T]`.

The primitive `F s = c + K ∫₀ˢ f` is continuous on `[0, T]`, dominates `f`, and therefore
satisfies `F s ≤ c + K ∫₀ˢ F`; `le_mul_exp_of_le_add_mul_integral_of_continuousOn` applies to
`F`. -/
theorem le_mul_exp_of_le_add_mul_integral {f : ℝ → ℝ} {c K T t : ℝ} (hK : 0 ≤ K)
    (hf : IntervalIntegrable f volume 0 T)
    (h : ∀ s ∈ Icc 0 T, f s ≤ c + K * ∫ r in (0 : ℝ)..s, f r) (ht : t ∈ Icc 0 T) :
    f t ≤ c * exp (K * t) := by
  have hT : (0 : ℝ) ≤ T := ht.1.trans ht.2
  set F : ℝ → ℝ := fun s => c + K * ∫ r in (0 : ℝ)..s, f r with hF
  have hFc : ContinuousOn F (Icc 0 T) := by
    have hprim := intervalIntegral.continuousOn_primitive_interval' hf left_mem_uIcc
    rw [uIcc_of_le hT] at hprim
    exact continuousOn_const.add (continuousOn_const.mul hprim)
  refine (h t ht).trans (le_mul_exp_of_le_add_mul_integral_of_continuousOn hK hFc
    (fun s hs => ?_) ht)
  have hmono : ∫ r in (0 : ℝ)..s, f r ≤ ∫ r in (0 : ℝ)..s, F r :=
    intervalIntegral.integral_mono_on hs.1
      (hf.mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le hT]; exact hs)))
      (intervalIntegrable_of_continuousOn_Icc hFc hs)
      (fun r hr => h r ⟨hr.1, hr.2.trans hs.2⟩)
  have := mul_le_mul_of_nonneg_left hmono hK
  simp only [hF]
  linarith

/-- **Grönwall's inequality** in integral form with a nonnegative source. Let `K ≥ 0`, let `f` be
interval integrable on `[0, T]`, let `g` be interval integrable and nonnegative on `[0, T]`, and
assume `f s ≤ c + K ∫₀ˢ f + ∫₀ˢ g` for `s ∈ [0, T]`. Then `f t ≤ (c + ∫₀ᵗ g) e^{Kt}` for
`t ∈ [0, T]`.

Since `s ↦ ∫₀ˢ g` is nondecreasing, on `[0, t]` the hypothesis holds with the constant
`c + ∫₀ᵗ g`, and `le_mul_exp_of_le_add_mul_integral` applies on `[0, t]`. -/
theorem le_add_integral_mul_exp_of_le {f g : ℝ → ℝ} {c K T t : ℝ} (hK : 0 ≤ K)
    (hf : IntervalIntegrable f volume 0 T) (hg : IntervalIntegrable g volume 0 T)
    (hg0 : ∀ s ∈ Icc 0 T, 0 ≤ g s)
    (h : ∀ s ∈ Icc 0 T, f s ≤ c + K * (∫ r in (0 : ℝ)..s, f r) + ∫ r in (0 : ℝ)..s, g r)
    (ht : t ∈ Icc 0 T) :
    f t ≤ (c + ∫ s in (0 : ℝ)..t, g s) * exp (K * t) := by
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hf' : IntervalIntegrable f volume 0 t :=
    hf.mono_set (uIcc_subset_uIcc_left (by
      rw [uIcc_of_le (ht.1.trans ht.2)]; exact ht))
  refine le_mul_exp_of_le_add_mul_integral hK hf' (fun s hs => ?_) ⟨ht.1, le_rfl⟩
  have := integral_le_integral_of_nonneg hg hg0 hs.1 hs.2 ht.2
  linarith [h s (hsub hs)]

/-- **Grönwall's inequality** in integral form with a nonnegative source, with the hypothesis
written as `f s ≤ c + ∫₀ˢ (K f + g)`; see `le_add_integral_mul_exp_of_le`. -/
theorem le_add_integral_mul_exp_of_le_integral_add {f g : ℝ → ℝ} {c K T t : ℝ} (hK : 0 ≤ K)
    (hf : IntervalIntegrable f volume 0 T) (hg : IntervalIntegrable g volume 0 T)
    (hg0 : ∀ s ∈ Icc 0 T, 0 ≤ g s)
    (h : ∀ s ∈ Icc 0 T, f s ≤ c + ∫ r in (0 : ℝ)..s, (K * f r + g r)) (ht : t ∈ Icc 0 T) :
    f t ≤ (c + ∫ s in (0 : ℝ)..t, g s) * exp (K * t) := by
  refine le_add_integral_mul_exp_of_le hK hf hg hg0 (fun s hs => ?_) ht
  have hsub : uIcc 0 s ⊆ uIcc 0 T :=
    uIcc_subset_uIcc_left (by rw [uIcc_of_le (hs.1.trans hs.2)]; exact hs)
  have := h s hs
  rw [intervalIntegral.integral_add ((hf.mono_set hsub).const_mul K) (hg.mono_set hsub),
    intervalIntegral.integral_const_mul] at this
  linarith

/-- `(e^{Λt})² = e^{2Λt}`. -/
theorem sq_exp_mul (Λ t : ℝ) : exp (Λ * t) ^ 2 = exp (2 * Λ * t) := by
  rw [sq, ← exp_add]
  ring_nf

/-- **Cauchy–Schwarz inequality** on `[0, t]`: `(∫₀ᵗ g)² ≤ t ∫₀ᵗ g²`, provided `g` and `g²` are
interval integrable on `[0, t]`. It follows by integrating `2 m g ≤ g² + m²` with
`m = t⁻¹ ∫₀ᵗ g`. -/
theorem sq_integral_le_mul_integral_sq {g : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hg : IntervalIntegrable g volume 0 t)
    (hg2 : IntervalIntegrable (fun s => g s ^ 2) volume 0 t) :
    (∫ s in (0 : ℝ)..t, g s) ^ 2 ≤ t * ∫ s in (0 : ℝ)..t, g s ^ 2 := by
  rcases ht.eq_or_lt with rfl | ht'
  · simp
  set I := ∫ s in (0 : ℝ)..t, g s with hI
  set J := ∫ s in (0 : ℝ)..t, g s ^ 2 with hJ
  set m := I / t
  have hm : m * t = I := div_mul_cancel₀ _ ht'.ne'
  have hpt : ∀ s, 2 * m * g s ≤ g s ^ 2 + m ^ 2 := fun s => by
    nlinarith [sq_nonneg (g s - m)]
  have hint := intervalIntegral.integral_mono ht (hg.const_mul (2 * m))
    (hg2.add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hg2
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint
  rw [← hI, ← hJ, ← hm] at hint
  have h1 : m ^ 2 * t ≤ J := by nlinarith
  rw [← hm]
  nlinarith [mul_le_mul_of_nonneg_left h1 ht]

/-! ### Integral equations with additive forcing -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `IsForcedSolution u w x₀ T x` states that the path `x : ℝ → V` solves on `[0, T]` the integral
equation with drift `u`, initial value `x₀` and additive forcing `w`,
`x t = x₀ + ∫₀ᵗ u s (x s) ds + w t` for `t ∈ [0, T]`,
and that `x`, `w` and `s ↦ u s (x s)` are continuous on `[0, T]`.

For the stochastic differential equations of the paper, `w = √2 W` is a continuous Brownian path
and `x` is the corresponding path of the strong solution. The space `V` is meant to be complete
(otherwise the Bochner integral vanishes), but none of the estimates below uses completeness. -/
structure IsForcedSolution (u : ℝ → V → V) (w : ℝ → V) (x₀ : V) (T : ℝ) (x : ℝ → V) :
    Prop where
  /-- The path is continuous on `[0, T]`. -/
  continuousOn : ContinuousOn x (Icc 0 T)
  /-- The forcing is continuous on `[0, T]`. -/
  continuousOn_forcing : ContinuousOn w (Icc 0 T)
  /-- The drift along the path is continuous on `[0, T]`. -/
  continuousOn_drift : ContinuousOn (fun s => u s (x s)) (Icc 0 T)
  /-- The integral equation `x t = x₀ + ∫₀ᵗ u s (x s) ds + w t`. -/
  eq_add_integral : ∀ t ∈ Icc 0 T, x t = x₀ + (∫ s in (0 : ℝ)..t, u s (x s)) + w t

namespace IsForcedSolution

variable {u v : ℝ → V → V} {w : ℝ → V} {x₀ y₀ : V} {T t Λ β : ℝ} {x y : ℝ → V}

/-- The drift along a solution is interval integrable on `[0, t]` for `t ∈ [0, T]`. -/
theorem intervalIntegrable_drift (hx : IsForcedSolution u w x₀ T x) (ht : t ∈ Icc 0 T) :
    IntervalIntegrable (fun s => u s (x s)) volume 0 t :=
  intervalIntegrable_of_continuousOn_Icc hx.continuousOn_drift ht

/-- The forcing cancels in the difference of two solutions with the same forcing:
`x t - y t = x₀ - y₀ + ∫₀ᵗ (u s (x s) - v s (y s)) ds`. -/
theorem sub_eq (hx : IsForcedSolution u w x₀ T x) (hy : IsForcedSolution v w y₀ T y)
    (ht : t ∈ Icc 0 T) :
    x t - y t = x₀ - y₀ + ∫ s in (0 : ℝ)..t, (u s (x s) - v s (y s)) := by
  rw [hx.eq_add_integral t ht, hy.eq_add_integral t ht,
    intervalIntegral.integral_sub (hx.intervalIntegrable_drift ht)
      (hy.intervalIntegrable_drift ht)]
  abel

/-- **Integrated drift stability**, with a majorant. Let `x` solve with drift `u` and `y` with
drift `v`, with the same forcing `w`, and assume that `u s` is `Λ`-Lipschitz for `s ∈ [0, T]`.
If `δ` is interval integrable on `[0, T]` and `‖u s (y s) - v s (y s)‖ ≤ δ s` there, then
`‖x t - y t‖ ≤ (‖x₀ - y₀‖ + ∫₀ᵗ δ) e^{Λt}` for `t ∈ [0, T]`. No regularity of `v` is needed. -/
theorem norm_sub_le_of_le {δ : ℝ → ℝ} (hx : IsForcedSolution u w x₀ T x)
    (hy : IsForcedSolution v w y₀ T y) (hΛ : 0 ≤ Λ)
    (hu : ∀ s ∈ Icc 0 T, ∀ p q, ‖u s p - u s q‖ ≤ Λ * ‖p - q‖)
    (hδ : IntervalIntegrable δ volume 0 T)
    (hδle : ∀ s ∈ Icc 0 T, ‖u s (y s) - v s (y s)‖ ≤ δ s) (ht : t ∈ Icc 0 T) :
    ‖x t - y t‖ ≤ (‖x₀ - y₀‖ + ∫ s in (0 : ℝ)..t, δ s) * exp (Λ * t) := by
  have hcont : ContinuousOn (fun s => ‖x s - y s‖) (Icc 0 T) :=
    (hx.continuousOn.sub hy.continuousOn).norm
  refine le_add_integral_mul_exp_of_le hΛ
    (intervalIntegrable_of_continuousOn_Icc hcont ⟨ht.1.trans ht.2, le_rfl⟩) hδ
    (fun s hs => (norm_nonneg _).trans (hδle s hs)) (fun s hs => ?_) ht
  have hδs : IntervalIntegrable δ volume 0 s :=
    hδ.mono_set (uIcc_subset_uIcc_left (by
      rw [uIcc_of_le (hs.1.trans hs.2)]; exact hs))
  have hfs : IntervalIntegrable (fun r => ‖x r - y r‖) volume 0 s :=
    intervalIntegrable_of_continuousOn_Icc hcont hs
  have hds : IntervalIntegrable (fun r => u r (x r) - v r (y r)) volume 0 s :=
    (hx.intervalIntegrable_drift hs).sub (hy.intervalIntegrable_drift hs)
  have hmono : ∫ r in (0 : ℝ)..s, ‖u r (x r) - v r (y r)‖ ≤
      ∫ r in (0 : ℝ)..s, (Λ * ‖x r - y r‖ + δ r) := by
    refine intervalIntegral.integral_mono_on hs.1 hds.norm ((hfs.const_mul Λ).add hδs)
      fun r hr => ?_
    have hr' : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans hs.2⟩
    calc ‖u r (x r) - v r (y r)‖
        ≤ ‖u r (x r) - u r (y r)‖ + ‖u r (y r) - v r (y r)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ Λ * ‖x r - y r‖ + δ r := add_le_add (hu r hr' _ _) (hδle r hr')
  rw [intervalIntegral.integral_add (hfs.const_mul Λ) hδs,
    intervalIntegral.integral_const_mul] at hmono
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (f := fun r => u r (x r) - v r (y r)) (μ := volume) hs.1
  rw [hx.sub_eq hy hs]
  linarith [norm_add_le (x₀ - y₀) (∫ r in (0 : ℝ)..s, (u r (x r) - v r (y r)))]

/-- **Integrated drift stability** (the estimate behind Lemma 7.2 of the paper). Let `x` solve
with drift `u` and `y` with drift `v`, with the same forcing `w`, and assume that `u s` is
`Λ`-Lipschitz for `s ∈ [0, T]` and that `s ↦ u s (y s)` is interval integrable on `[0, T]`. Then
for `t ∈ [0, T]`,
`‖x t - y t‖ ≤ (‖x₀ - y₀‖ + ∫₀ᵗ ‖u s (y s) - v s (y s)‖ ds) e^{Λt}`. -/
theorem norm_sub_le (hx : IsForcedSolution u w x₀ T x) (hy : IsForcedSolution v w y₀ T y)
    (hΛ : 0 ≤ Λ) (hu : ∀ s ∈ Icc 0 T, ∀ p q, ‖u s p - u s q‖ ≤ Λ * ‖p - q‖)
    (huy : IntervalIntegrable (fun s => u s (y s)) volume 0 T) (ht : t ∈ Icc 0 T) :
    ‖x t - y t‖ ≤ (‖x₀ - y₀‖ + ∫ s in (0 : ℝ)..t, ‖u s (y s) - v s (y s)‖) * exp (Λ * t) :=
  hx.norm_sub_le_of_le hy hΛ hu
    (huy.sub (hy.intervalIntegrable_drift ⟨ht.1.trans ht.2, le_rfl⟩)).norm
    (fun _ _ => le_rfl) ht

/-- **Uniqueness**: two solutions with the same Lipschitz drift, the same forcing and the same
initial value coincide on `[0, T]`. -/
theorem eqOn (hx : IsForcedSolution u w x₀ T x) (hy : IsForcedSolution u w x₀ T y)
    (hΛ : 0 ≤ Λ) (hu : ∀ s ∈ Icc 0 T, ∀ p q, ‖u s p - u s q‖ ≤ Λ * ‖p - q‖) :
    EqOn x y (Icc 0 T) := by
  intro t ht
  have h := hx.norm_sub_le_of_le hy hΛ hu (δ := fun _ => 0) intervalIntegrable_const
    (fun s _ => by simp) ht
  simp only [sub_self, norm_zero, intervalIntegral.integral_zero, add_zero, zero_mul] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

/-- **A priori bound** under linear growth. If `x` solves with drift `u` and forcing `w`, and
`‖u s p‖ ≤ β + Λ ‖p‖` with `Λ ≥ 0` for `s ∈ [0, T]`, then for `t ∈ [0, T]`
`‖x t‖ ≤ (‖x₀‖ + β t + Λ ∫₀ᵗ ‖w s‖ ds) e^{Λt} + ‖w t‖`.

The path `z = x - w` satisfies `z t = x₀ + ∫₀ᵗ u s (z s + w s) ds`, hence
`‖z t‖ ≤ ‖x₀‖ + ∫₀ᵗ (Λ ‖z s‖ + β + Λ ‖w s‖) ds`, and Grönwall's inequality applies. -/
theorem norm_le (hx : IsForcedSolution u w x₀ T x) (hΛ : 0 ≤ Λ)
    (hgrowth : ∀ s ∈ Icc 0 T, ∀ p, ‖u s p‖ ≤ β + Λ * ‖p‖) (ht : t ∈ Icc 0 T) :
    ‖x t‖ ≤ (‖x₀‖ + β * t + Λ * ∫ s in (0 : ℝ)..t, ‖w s‖) * exp (Λ * t) + ‖w t‖ := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hβ : 0 ≤ β := by
    have h0 := hgrowth 0 ⟨le_rfl, hT⟩ 0
    rw [norm_zero, mul_zero, add_zero] at h0
    exact (norm_nonneg _).trans h0
  have hzc : ContinuousOn (fun s => ‖x s - w s‖) (Icc 0 T) :=
    (hx.continuousOn.sub hx.continuousOn_forcing).norm
  have hwc : ContinuousOn (fun s => ‖w s‖) (Icc 0 T) := hx.continuousOn_forcing.norm
  have hgc : ContinuousOn (fun s => β + Λ * ‖w s‖) (Icc 0 T) :=
    continuousOn_const.add (continuousOn_const.mul hwc)
  have key := le_add_integral_mul_exp_of_le (f := fun s => ‖x s - w s‖)
    (g := fun s => β + Λ * ‖w s‖) (c := ‖x₀‖) hΛ
    (intervalIntegrable_of_continuousOn_Icc hzc ⟨hT, le_rfl⟩)
    (intervalIntegrable_of_continuousOn_Icc hgc ⟨hT, le_rfl⟩) (fun s _ => by positivity)
    (fun s hs => ?_) ht
  · have hint : ∫ s in (0 : ℝ)..t, (β + Λ * ‖w s‖) = β * t + Λ * ∫ s in (0 : ℝ)..t, ‖w s‖ := by
      rw [intervalIntegral.integral_add intervalIntegrable_const
        ((intervalIntegrable_of_continuousOn_Icc hwc ht).const_mul Λ),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul,
        sub_zero, mul_comm t β]
    rw [hint, ← add_assoc] at key
    linarith [norm_le_norm_add_norm_sub' (x t) (w t)]
  · have hzs : IntervalIntegrable (fun r => ‖x r - w r‖) volume 0 s :=
      intervalIntegrable_of_continuousOn_Icc hzc hs
    have hgs : IntervalIntegrable (fun r => β + Λ * ‖w r‖) volume 0 s :=
      intervalIntegrable_of_continuousOn_Icc hgc hs
    have hmono : ∫ r in (0 : ℝ)..s, ‖u r (x r)‖ ≤
        ∫ r in (0 : ℝ)..s, (Λ * ‖x r - w r‖ + (β + Λ * ‖w r‖)) := by
      refine intervalIntegral.integral_mono_on hs.1 (hx.intervalIntegrable_drift hs).norm
        ((hzs.const_mul Λ).add hgs) fun r hr => ?_
      have hr' : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans hs.2⟩
      have h1 := hgrowth r hr' (x r)
      have h2 := norm_le_norm_add_norm_sub' (x r) (w r)
      have h3 := mul_le_mul_of_nonneg_left h2 hΛ
      linarith
    rw [intervalIntegral.integral_add (hzs.const_mul Λ) hgs,
      intervalIntegral.integral_const_mul] at hmono
    have hnorm := intervalIntegral.norm_integral_le_integral_norm
      (f := fun r => u r (x r)) (μ := volume) hs.1
    have heq : x s - w s = x₀ + ∫ r in (0 : ℝ)..s, u r (x r) := by
      rw [hx.eq_add_integral s hs]; abel
    rw [heq]
    linarith [norm_add_le x₀ (∫ r in (0 : ℝ)..s, u r (x r))]

/-! ### Squared forms -/

/-- **Squared integrated drift stability**. Under the hypotheses of `norm_sub_le`, with
`s ↦ u s (y s)` continuous on `[0, T]`, for `t ∈ [0, T]`
`‖x t - y t‖² ≤ 2 e^{2Λt} (‖x₀ - y₀‖² + t ∫₀ᵗ ‖u s (y s) - v s (y s)‖² ds)`. -/
theorem norm_sub_sq_le (hx : IsForcedSolution u w x₀ T x) (hy : IsForcedSolution v w y₀ T y)
    (hΛ : 0 ≤ Λ) (hu : ∀ s ∈ Icc 0 T, ∀ p q, ‖u s p - u s q‖ ≤ Λ * ‖p - q‖)
    (huy : ContinuousOn (fun s => u s (y s)) (Icc 0 T)) (ht : t ∈ Icc 0 T) :
    ‖x t - y t‖ ^ 2 ≤ 2 * exp (2 * Λ * t) *
      (‖x₀ - y₀‖ ^ 2 + t * ∫ s in (0 : ℝ)..t, ‖u s (y s) - v s (y s)‖ ^ 2) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hgc : ContinuousOn (fun s => ‖u s (y s) - v s (y s)‖) (Icc 0 T) :=
    (huy.sub hy.continuousOn_drift).norm
  have h1 := hx.norm_sub_le hy hΛ hu (intervalIntegrable_of_continuousOn_Icc huy ⟨hT, le_rfl⟩) ht
  have hCS := sq_integral_le_mul_integral_sq ht.1 (intervalIntegrable_of_continuousOn_Icc hgc ht)
    (intervalIntegrable_of_continuousOn_Icc (hgc.pow 2) ht)
  set I := ∫ s in (0 : ℝ)..t, ‖u s (y s) - v s (y s)‖
  calc ‖x t - y t‖ ^ 2 ≤ ((‖x₀ - y₀‖ + I) * exp (Λ * t)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (‖x₀ - y₀‖ + I) ^ 2 * exp (2 * Λ * t) := by rw [mul_pow, sq_exp_mul]
    _ ≤ (2 * (‖x₀ - y₀‖ ^ 2 + I ^ 2)) * exp (2 * Λ * t) := by
        gcongr
        nlinarith [sq_nonneg (‖x₀ - y₀‖ - I)]
    _ ≤ (2 * (‖x₀ - y₀‖ ^ 2 + t * ∫ s in (0 : ℝ)..t, ‖u s (y s) - v s (y s)‖ ^ 2)) *
        exp (2 * Λ * t) := by gcongr
    _ = _ := by ring

/-- **Squared integrated drift stability, uniformly on `[0, T]`**. Under the hypotheses of
`norm_sub_sq_le`, for every `t ∈ [0, T]`
`‖x t - y t‖² ≤ 2 e^{2ΛT} (‖x₀ - y₀‖² + T ∫₀ᵀ ‖u s (y s) - v s (y s)‖² ds)`. -/
theorem norm_sub_sq_le_horizon (hx : IsForcedSolution u w x₀ T x)
    (hy : IsForcedSolution v w y₀ T y) (hΛ : 0 ≤ Λ)
    (hu : ∀ s ∈ Icc 0 T, ∀ p q, ‖u s p - u s q‖ ≤ Λ * ‖p - q‖)
    (huy : ContinuousOn (fun s => u s (y s)) (Icc 0 T)) (ht : t ∈ Icc 0 T) :
    ‖x t - y t‖ ^ 2 ≤ 2 * exp (2 * Λ * T) *
      (‖x₀ - y₀‖ ^ 2 + T * ∫ s in (0 : ℝ)..T, ‖u s (y s) - v s (y s)‖ ^ 2) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hgc : ContinuousOn (fun s => ‖u s (y s) - v s (y s)‖ ^ 2) (Icc 0 T) :=
    (huy.sub hy.continuousOn_drift).norm.pow 2
  have hJ := integral_le_integral_of_nonneg
    (intervalIntegrable_of_continuousOn_Icc hgc ⟨hT, le_rfl⟩) (fun s _ => sq_nonneg _)
    ht.1 ht.2 le_rfl
  have hJ0 : 0 ≤ ∫ s in (0 : ℝ)..t, ‖u s (y s) - v s (y s)‖ ^ 2 :=
    intervalIntegral.integral_nonneg ht.1 fun s _ => sq_nonneg _
  have hE : exp (2 * Λ * t) ≤ exp (2 * Λ * T) :=
    exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 (by positivity))
  refine (hx.norm_sub_sq_le hy hΛ hu huy ht).trans ?_
  exact mul_le_mul (mul_le_mul_of_nonneg_left hE zero_le_two)
    (add_le_add le_rfl (mul_le_mul ht.2 hJ hJ0 hT))
    (add_nonneg (sq_nonneg _) (mul_nonneg ht.1 hJ0)) (by positivity)

/-- **Squared integrated drift stability for equal initial values, uniformly on `[0, T]`**. Let
`x` and `y` solve with drifts `u` and `v`, the same forcing and the same initial value, with
`u s` `Λ`-Lipschitz and `s ↦ u s (y s)` continuous on `[0, T]`. Then for every `t ∈ [0, T]`
`‖x t - y t‖² ≤ T e^{2ΛT} ∫₀ᵀ ‖u s (y s) - v s (y s)‖² ds`.

This is the pathwise form of the display in the proof of Lemma 7.2, with `u = b^n_N` and
`v = b_N`; taking expectations gives `E sup_{t ≤ T} |X^n_t - X_t|² ≤ T e^{2ΛT} ∫₀ᵀ E|…|²`. -/
theorem norm_sub_sq_le_horizon_same_initial (hx : IsForcedSolution u w x₀ T x)
    (hy : IsForcedSolution v w x₀ T y) (hΛ : 0 ≤ Λ)
    (hu : ∀ s ∈ Icc 0 T, ∀ p q, ‖u s p - u s q‖ ≤ Λ * ‖p - q‖)
    (huy : ContinuousOn (fun s => u s (y s)) (Icc 0 T)) (ht : t ∈ Icc 0 T) :
    ‖x t - y t‖ ^ 2 ≤ T * exp (2 * Λ * T) * ∫ s in (0 : ℝ)..T, ‖u s (y s) - v s (y s)‖ ^ 2 := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hgc : ContinuousOn (fun s => ‖u s (y s) - v s (y s)‖) (Icc 0 T) :=
    (huy.sub hy.continuousOn_drift).norm
  have h1 := hx.norm_sub_le hy hΛ hu (intervalIntegrable_of_continuousOn_Icc huy ⟨hT, le_rfl⟩) ht
  rw [sub_self, norm_zero, zero_add] at h1
  have hCS := sq_integral_le_mul_integral_sq ht.1 (intervalIntegrable_of_continuousOn_Icc hgc ht)
    (intervalIntegrable_of_continuousOn_Icc (hgc.pow 2) ht)
  have hJ := integral_le_integral_of_nonneg
    (intervalIntegrable_of_continuousOn_Icc (hgc.pow 2) ⟨hT, le_rfl⟩) (fun s _ => sq_nonneg _)
    ht.1 ht.2 le_rfl
  have hJ0 : 0 ≤ ∫ s in (0 : ℝ)..t, ‖u s (y s) - v s (y s)‖ ^ 2 :=
    intervalIntegral.integral_nonneg ht.1 fun s _ => sq_nonneg _
  have hE : exp (Λ * t) ^ 2 ≤ exp (2 * Λ * T) := by
    rw [sq_exp_mul]
    exact exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 (by positivity))
  calc ‖x t - y t‖ ^ 2
      ≤ ((∫ s in (0 : ℝ)..t, ‖u s (y s) - v s (y s)‖) * exp (Λ * t)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (∫ s in (0 : ℝ)..t, ‖u s (y s) - v s (y s)‖) ^ 2 * exp (Λ * t) ^ 2 := mul_pow _ _ _
    _ ≤ (T * ∫ s in (0 : ℝ)..T, ‖u s (y s) - v s (y s)‖ ^ 2) * exp (2 * Λ * T) :=
        mul_le_mul (hCS.trans (mul_le_mul ht.2 hJ hJ0 hT)) hE (by positivity)
          (mul_nonneg hT (hJ0.trans hJ))
    _ = _ := by ring

/-- **Squared a priori bound** under linear growth. Under the hypotheses of `norm_le`, for
`t ∈ [0, T]`
`‖x t‖² ≤ 6 e^{2Λt} (‖x₀‖² + β² t² + Λ² t ∫₀ᵗ ‖w s‖² ds) + 2 ‖w t‖²`. -/
theorem norm_sq_le (hx : IsForcedSolution u w x₀ T x) (hΛ : 0 ≤ Λ)
    (hgrowth : ∀ s ∈ Icc 0 T, ∀ p, ‖u s p‖ ≤ β + Λ * ‖p‖) (ht : t ∈ Icc 0 T) :
    ‖x t‖ ^ 2 ≤ 6 * exp (2 * Λ * t) *
      (‖x₀‖ ^ 2 + β ^ 2 * t ^ 2 + Λ ^ 2 * t * ∫ s in (0 : ℝ)..t, ‖w s‖ ^ 2) +
        2 * ‖w t‖ ^ 2 := by
  have h1 := hx.norm_le hΛ hgrowth ht
  have hwc : ContinuousOn (fun s => ‖w s‖) (Icc 0 T) := hx.continuousOn_forcing.norm
  have hCS := sq_integral_le_mul_integral_sq ht.1 (intervalIntegrable_of_continuousOn_Icc hwc ht)
    (intervalIntegrable_of_continuousOn_Icc (hwc.pow 2) ht)
  set W := ∫ s in (0 : ℝ)..t, ‖w s‖
  set W₂ := ∫ s in (0 : ℝ)..t, ‖w s‖ ^ 2
  set E := exp (Λ * t)
  set A := ‖x₀‖ + β * t + Λ * W
  have hA : A ^ 2 ≤ 3 * (‖x₀‖ ^ 2 + β ^ 2 * t ^ 2 + Λ ^ 2 * W ^ 2) := by
    nlinarith [sq_nonneg (‖x₀‖ - β * t), sq_nonneg (‖x₀‖ - Λ * W), sq_nonneg (β * t - Λ * W)]
  have hW : Λ ^ 2 * W ^ 2 ≤ Λ ^ 2 * (t * W₂) := mul_le_mul_of_nonneg_left hCS (sq_nonneg Λ)
  calc ‖x t‖ ^ 2 ≤ (A * E + ‖w t‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ 2 * (A ^ 2 * E ^ 2) + 2 * ‖w t‖ ^ 2 := by nlinarith [sq_nonneg (A * E - ‖w t‖)]
    _ ≤ 2 * (3 * (‖x₀‖ ^ 2 + β ^ 2 * t ^ 2 + Λ ^ 2 * (t * W₂)) * E ^ 2) + 2 * ‖w t‖ ^ 2 := by
        gcongr
        linarith
    _ = _ := by rw [sq_exp_mul]; ring

/-- **Squared a priori bound, uniformly on `[0, T]`**. Under the hypotheses of `norm_le`, for
every `t ∈ [0, T]`
`‖x t‖² ≤ 6 e^{2ΛT} (‖x₀‖² + β² T² + Λ² T ∫₀ᵀ ‖w s‖² ds) + 2 ‖w t‖²`. -/
theorem norm_sq_le_horizon (hx : IsForcedSolution u w x₀ T x) (hΛ : 0 ≤ Λ)
    (hgrowth : ∀ s ∈ Icc 0 T, ∀ p, ‖u s p‖ ≤ β + Λ * ‖p‖) (ht : t ∈ Icc 0 T) :
    ‖x t‖ ^ 2 ≤ 6 * exp (2 * Λ * T) *
      (‖x₀‖ ^ 2 + β ^ 2 * T ^ 2 + Λ ^ 2 * T * ∫ s in (0 : ℝ)..T, ‖w s‖ ^ 2) +
        2 * ‖w t‖ ^ 2 := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hwc : ContinuousOn (fun s => ‖w s‖ ^ 2) (Icc 0 T) := hx.continuousOn_forcing.norm.pow 2
  have hW := integral_le_integral_of_nonneg
    (intervalIntegrable_of_continuousOn_Icc hwc ⟨hT, le_rfl⟩) (fun s _ => sq_nonneg _)
    ht.1 ht.2 le_rfl
  have hW0 : 0 ≤ ∫ s in (0 : ℝ)..t, ‖w s‖ ^ 2 :=
    intervalIntegral.integral_nonneg ht.1 fun s _ => sq_nonneg _
  have h1 : β ^ 2 * t ^ 2 ≤ β ^ 2 * T ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1 ht.2 2) (sq_nonneg β)
  have h2 : Λ ^ 2 * t * ∫ s in (0 : ℝ)..t, ‖w s‖ ^ 2 ≤
      Λ ^ 2 * T * ∫ s in (0 : ℝ)..T, ‖w s‖ ^ 2 :=
    mul_le_mul (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg Λ)) hW hW0
      (mul_nonneg (sq_nonneg Λ) hT)
  have hE : exp (2 * Λ * t) ≤ exp (2 * Λ * T) :=
    exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 (by positivity))
  have hX : 0 ≤ ‖x₀‖ ^ 2 + β ^ 2 * t ^ 2 + Λ ^ 2 * t * ∫ s in (0 : ℝ)..t, ‖w s‖ ^ 2 :=
    add_nonneg (by positivity) (mul_nonneg (mul_nonneg (sq_nonneg Λ) ht.1) hW0)
  have key := mul_le_mul hE (add_le_add (add_le_add le_rfl h1) h2) hX (exp_pos _).le
  refine (hx.norm_sq_le hΛ hgrowth ht).trans ?_
  linarith

end IsForcedSolution

end SharpWasserstein.Sharp
