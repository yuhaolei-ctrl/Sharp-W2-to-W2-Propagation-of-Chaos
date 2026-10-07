/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Lengths of curves with an integrable `s^{-1/2}` speed

In the proof of Theorem 2.1 (Section 3.4, `sec:proof-main`), the length lemma `lem:length` is
applied to a curve `s ↦ ν_s` on `[0, t]` whose speed is bounded by
`g(s) = e^{ω(t-s)/2} (A₀ + A₁ / √s) m / N`, a function which is integrable but unbounded at
`s = 0`. On every interval `[a, b] ⊆ (0, t]` the lemma gives the bound `(b - a) max_{[a,b]} g`,
and the integral `∫₀ᵗ (A₀ + A₁ / √s) ds = A₀ t + 2 A₁ √t` is recovered at the endpoint `0` by
continuity of the curve.

This file proves this last step in an arbitrary pseudometric space, without integrals: if
`dist (f a) (f b) ≤ (b - a) (K₀ + K₁ / √a)` for `0 < a ≤ b ≤ T` and `f` is continuous at `0`
within `[0, T]`, then `dist (f 0) (f T) ≤ K₀ T + 2 K₁ √T`.

The proof sums the hypothesis along the geometric times `tₙ = T qⁿ`, `0 < q < 1`, for which
`(tₙ - tₙ₊₁) / √tₙ₊₁ = (1 + 1/√q) (√tₙ - √tₙ₊₁)` telescopes, lets `n → ∞` and then `q → 1`.

## Main statements

* `endpoint_of_sqrt_action`: the bound `dist (f 0) (f T) ≤ K₀ T + 2 K₁ √T`.
* `endpoint_of_sqrt_action_mul`: the same bound with a common factor `c ≥ 0`, in the form used
  in Section 3.4.
-/

@[expose] public section

open Filter Set Topology

namespace SharpWasserstein.Sharp

variable {X : Type*} [PseudoMetricSpace X]

/-- One step of the geometric partition: if `a = q b` with `0 < q`, `0 < b`, then
`(b - a) (K₀ + K₁ / √a) = K₀ (b - a) + (1 + 1/√q) K₁ (√b - √a)`. -/
theorem geometric_step_eq {q b K₀ K₁ : ℝ} (hq : 0 < q) (hb : 0 < b) :
    (b - q * b) * (K₀ + K₁ / Real.sqrt (q * b)) =
      K₀ * (b - q * b) + (1 + 1 / Real.sqrt q) * K₁ * (Real.sqrt b - Real.sqrt (q * b)) := by
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hq' := (Real.sq_sqrt hq.le).symm
  have hb' := (Real.sq_sqrt hb.le).symm
  rw [Real.sqrt_mul hq.le]
  generalize Real.sqrt q = u at hq' hsq ⊢
  generalize Real.sqrt b = v at hb' hsb ⊢
  subst hq' hb'
  field_simp
  ring

/-- The bound along the geometric times `T qⁿ`: for `0 < q < 1` and every `n`,
`dist (f (T qⁿ)) (f T) ≤ K₀ (T - T qⁿ) + (1 + 1/√q) K₁ (√T - √(T qⁿ))`. -/
theorem dist_geometric_le {f : ℝ → X} {T K₀ K₁ q : ℝ} (hT : 0 < T) (hq₀ : 0 < q) (hq₁ : q < 1)
    (h : ∀ a b, 0 < a → a ≤ b → b ≤ T → dist (f a) (f b) ≤ (b - a) * (K₀ + K₁ / Real.sqrt a))
    (n : ℕ) :
    dist (f (T * q ^ n)) (f T) ≤ K₀ * (T - T * q ^ n) +
      (1 + 1 / Real.sqrt q) * K₁ * (Real.sqrt T - Real.sqrt (T * q ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    set b := T * q ^ n with hb_def
    have hb : 0 < b := mul_pos hT (pow_pos hq₀ n)
    have hbT : b ≤ T := mul_le_of_le_one_right hT.le (pow_le_one₀ hq₀.le hq₁.le)
    have hab : T * q ^ (n + 1) = q * b := by rw [hb_def, pow_succ]; ring
    have hstep := h (q * b) b (mul_pos hq₀ hb) (mul_le_of_le_one_left hb.le hq₁.le) hbT
    rw [geometric_step_eq hq₀ hb] at hstep
    rw [hab]
    calc dist (f (q * b)) (f T) ≤ dist (f (q * b)) (f b) + dist (f b) (f T) := dist_triangle _ _ _
      _ ≤ _ := add_le_add hstep ih
      _ = _ := by ring

/-- Bound on `dist (f 0) (f T)` with the constant `1 + 1/√q` for a fixed `0 < q < 1`, obtained
by letting `n → ∞` in `dist_geometric_le`. -/
theorem dist_le_of_geometric {f : ℝ → X} {T K₀ K₁ q : ℝ} (hT : 0 < T) (hK₀ : 0 ≤ K₀)
    (hK₁ : 0 ≤ K₁) (hq₀ : 0 < q) (hq₁ : q < 1) (hc : ContinuousWithinAt f (Icc 0 T) 0)
    (h : ∀ a b, 0 < a → a ≤ b → b ≤ T → dist (f a) (f b) ≤ (b - a) * (K₀ + K₁ / Real.sqrt a)) :
    dist (f 0) (f T) ≤ K₀ * T + (1 + 1 / Real.sqrt q) * K₁ * Real.sqrt T := by
  have ht : Tendsto (fun n : ℕ => T * q ^ n) atTop (𝓝[Icc 0 T] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ⟨?_, ?_⟩⟩
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀.le hq₁).const_mul T
    · positivity
    · exact mul_le_of_le_one_right hT.le (pow_le_one₀ hq₀.le hq₁.le)
  have hlim : Tendsto (fun n : ℕ => dist (f (T * q ^ n)) (f T)) atTop
      (𝓝 (dist (f 0) (f T))) :=
    (hc.tendsto.comp ht).dist tendsto_const_nhds
  refine le_of_tendsto' hlim fun n => (dist_geometric_le hT hq₀ hq₁ h n).trans ?_
  have hc₁ : 0 ≤ (1 + 1 / Real.sqrt q) * K₁ := by positivity
  have h₁ : 0 ≤ T * q ^ n := by positivity
  have h₂ : 0 ≤ Real.sqrt (T * q ^ n) := Real.sqrt_nonneg _
  nlinarith

/-- **Endpoint bound for a curve with speed `K₀ + K₁ / √s`.** Let `f` be continuous at `0`
within `[0, T]`, and assume that `dist (f a) (f b) ≤ (b - a) (K₀ + K₁ / √a)` whenever
`0 < a ≤ b ≤ T`. Then `dist (f 0) (f T) ≤ K₀ T + 2 K₁ √T = ∫₀ᵀ (K₀ + K₁ / √s) ds`. -/
theorem endpoint_of_sqrt_action {f : ℝ → X} {T K₀ K₁ : ℝ} (hT : 0 < T) (hK₀ : 0 ≤ K₀)
    (hK₁ : 0 ≤ K₁) (hc : ContinuousWithinAt f (Icc 0 T) 0)
    (h : ∀ a b, 0 < a → a ≤ b → b ≤ T → dist (f a) (f b) ≤ (b - a) * (K₀ + K₁ / Real.sqrt a)) :
    dist (f 0) (f T) ≤ K₀ * T + 2 * K₁ * Real.sqrt T := by
  have hcont : ContinuousAt
      (fun q : ℝ => K₀ * T + (1 + 1 / Real.sqrt q) * K₁ * Real.sqrt T) 1 := by
    fun_prop (disch := simp)
  have hlim : Tendsto (fun q : ℝ => K₀ * T + (1 + 1 / Real.sqrt q) * K₁ * Real.sqrt T)
      (𝓝[<] 1) (𝓝 (K₀ * T + 2 * K₁ * Real.sqrt T)) := by
    have : Tendsto (fun q : ℝ => K₀ * T + (1 + 1 / Real.sqrt q) * K₁ * Real.sqrt T) (𝓝[<] 1)
        (𝓝 (K₀ * T + (1 + 1 / Real.sqrt 1) * K₁ * Real.sqrt T)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    norm_num at this
    convert this using 2
    ring
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with q hq
  exact dist_le_of_geometric hT hK₀ hK₁ hq.1 hq.2 hc h

/-- The form of `endpoint_of_sqrt_action` used in Section 3.4: if `c ≥ 0`, `A₀ ≥ 0`, `A₁ ≥ 0`,
`f` is continuous at `0` within `[0, T]` and `dist (f a) (f b) ≤ (b - a) (c (A₀ + A₁ / √a))` for
`0 < a ≤ b ≤ T`, then `dist (f 0) (f T) ≤ c (A₀ T + 2 A₁ √T)`. -/
theorem endpoint_of_sqrt_action_mul {f : ℝ → X} {T c A₀ A₁ : ℝ} (hT : 0 < T) (hc_nonneg : 0 ≤ c)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hc : ContinuousWithinAt f (Icc 0 T) 0)
    (h : ∀ a b, 0 < a → a ≤ b → b ≤ T →
      dist (f a) (f b) ≤ (b - a) * (c * (A₀ + A₁ / Real.sqrt a))) :
    dist (f 0) (f T) ≤ c * (A₀ * T + 2 * A₁ * Real.sqrt T) := by
  have key := endpoint_of_sqrt_action (K₀ := c * A₀) (K₁ := c * A₁) hT
    (mul_nonneg hc_nonneg hA₀) (mul_nonneg hc_nonneg hA₁) hc fun a b ha hab hbT => by
      simpa only [mul_add, mul_div_assoc] using h a b ha hab hbT
  linarith

end SharpWasserstein.Sharp
