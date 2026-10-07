/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Statement

/-!
# The constants of Theorem 2.1

This file defines, one by one, the explicit constants of Theorem 2.1 (`thm:main`) of the paper,
displayed right after the theorem (labels `eq:const1`, `eq:const2`, `eq:const3` and `eq:CT`), and
proves the elementary facts about them that are used in the proof.

Given the constants `L_a, L₁, L₂, M ≥ 0` of Assumption A, the initial constant `C₀ ≥ 0` and the
horizon `T`, the paper sets
* `L = L_a + L₁`, `Λ = L_a + L₁ + L₂`, `L_c = 2L₁ + L₂` (`eq:const1`);
* `G = 2L₁² + L₂² + 2M²`, `λ = 2G`, `D = 2Λ + 2L₁ + 1`, `ω = D + 3λ` (`eq:const2`);
* `D_T = (1 + LT + L²T²/3)/4`, `A₀ = 2M + L_c e^{LT} √C₀`, `A₁ = √8 M √(C₀ D_T)`
  (`eq:const3`);
* `C_T = (e^{LT} √C₀ + e^{ωT/2} (A₀ T + 2 A₁ √T))²` (`eq:CT`).

Each constant is a separate definition taking only the parameters it depends on, in the order
`C₀ T La L₁ L₂ M` of `SharpChaos.sharpConstant`.

## Main definitions

* `lipL`, `lipΛ`, `lipC`: the Lipschitz constants `L`, `Λ` and `L_c`.
* `gConst`, `birthRate`, `driftRate`, `omega`: the constants `G`, `λ`, `D` and `ω`.
* `jumpRate`: the rates `q_m = λ m (1 - m/N)` of the tangent hierarchy (`prop:hierarchy`).
* `horizonFactor`, `sourceA₀`, `sourceA₁`: the constants `D_T`, `A₀` and `A₁`.
* `sharpC`: the constant `C_T`.

## Main statements

* `sharpConstant_eq_sharpC`: `SharpChaos.sharpConstant` is `sharpC`.
* `le_sharpC`: `C₀ ≤ C_T`, used for `t = 0` in Section 3.4 (`sec:proof-main`).
* `add_le_sqrt_sharpC`: `e^{Lt} √C₀ + e^{ωt/2} (A₀ t + 2 A₁ √t) ≤ √C_T` for `0 ≤ t ≤ T`, the
  final step of Section 3.4.
* `jumpRate_le`, `yule_supersolution`, `profile_supersolution`: the inequalities behind the
  comparison with a Yule process in the proof of Proposition 3.7 (`prop:profile`, Section 5.4).
* `bridgeCost_le_horizonFactor_div`: `β_L(s) ≤ D_T / s` for `0 < s ≤ T`, from the entropy–cost
  inequality of Lemma 4.1 (`lem:entropy-cost`).
-/

@[expose] public section

noncomputable section

namespace SharpWasserstein.Sharp

/-! ### Definitions -/

/-- The Lipschitz constant `L = L_a + L₁` of the reference drift (`eq:const1`). -/
def lipL (La L₁ : ℝ) : ℝ := La + L₁

/-- The Lipschitz constant `Λ = L_a + L₁ + L₂` of the particle drift (`eq:const1`). -/
def lipΛ (La L₁ L₂ : ℝ) : ℝ := La + L₁ + L₂

/-- The Lipschitz constant `L_c = 2L₁ + L₂` of the centred interaction (`eq:const1`). -/
def lipC (L₁ L₂ : ℝ) : ℝ := 2 * L₁ + L₂

/-- The constant `G = 2L₁² + L₂² + 2M²` (`eq:const2`). -/
def gConst (L₁ L₂ M : ℝ) : ℝ := 2 * L₁ ^ 2 + L₂ ^ 2 + 2 * M ^ 2

/-- The birth rate `λ = 2G` of the comparison Yule process (`eq:const2`). -/
def birthRate (L₁ L₂ M : ℝ) : ℝ := 2 * gConst L₁ L₂ M

/-- The growth rate `D = 2Λ + 2L₁ + 1` of the tangent hierarchy (`eq:const2`). -/
def driftRate (La L₁ L₂ : ℝ) : ℝ := 2 * lipΛ La L₁ L₂ + 2 * L₁ + 1

/-- The exponential rate `ω = D + 3λ` of Proposition 3.7 (`eq:const2`). -/
def omega (La L₁ L₂ M : ℝ) : ℝ := driftRate La L₁ L₂ + 3 * birthRate L₁ L₂ M

/-- The jump rate `q_m = 2mG α_m = λ m (1 - m/N)` of level `m` of the tangent hierarchy
(`eq:gal-ode`, `eq:hierarchy`) of a system of `N` particles, where `α_m = 1 - m/N`. -/
def jumpRate (L₁ L₂ M : ℝ) (N m : ℕ) : ℝ := birthRate L₁ L₂ M * m * (1 - (m : ℝ) / N)

/-- The constant `D_T = (1 + LT + L²T²/3)/4` of the entropy–cost inequality (`eq:const3`). -/
def horizonFactor (T La L₁ : ℝ) : ℝ :=
  (1 + lipL La L₁ * T + lipL La L₁ ^ 2 * T ^ 2 / 3) / 4

/-- The constant `A₀ = 2M + L_c e^{LT} √C₀` of the source estimate (`eq:const3`). -/
def sourceA₀ (C₀ T La L₁ L₂ M : ℝ) : ℝ :=
  2 * M + lipC L₁ L₂ * Real.exp (lipL La L₁ * T) * Real.sqrt C₀

/-- The constant `A₁ = √8 M √(C₀ D_T)` of the source estimate (`eq:const3`). -/
def sourceA₁ (C₀ T La L₁ M : ℝ) : ℝ :=
  Real.sqrt 8 * M * Real.sqrt (C₀ * horizonFactor T La L₁)

/-- The constant `C_T = (e^{LT} √C₀ + e^{ωT/2} (A₀ T + 2 A₁ √T))²` of Theorem 2.1 (`eq:CT`). -/
def sharpC (C₀ T La L₁ L₂ M : ℝ) : ℝ :=
  (Real.exp (lipL La L₁ * T) * Real.sqrt C₀ + Real.exp (omega La L₁ L₂ M * T / 2) *
    (sourceA₀ C₀ T La L₁ L₂ M * T + 2 * sourceA₁ C₀ T La L₁ M * Real.sqrt T)) ^ 2

/-- The constant `SharpChaos.sharpConstant` of the public statement is `sharpC`. -/
theorem sharpConstant_eq_sharpC (C₀ T La L₁ L₂ M : ℝ) :
    SharpChaos.sharpConstant C₀ T La L₁ L₂ M = sharpC C₀ T La L₁ L₂ M :=
  rfl

/-! ### Nonnegativity -/

section Nonneg

variable {C₀ T La L₁ L₂ M : ℝ}

/-- `L ≥ 0`. -/
theorem lipL_nonneg (hLa : 0 ≤ La) (hL₁ : 0 ≤ L₁) : 0 ≤ lipL La L₁ :=
  add_nonneg hLa hL₁

/-- `Λ ≥ 0`. -/
theorem lipΛ_nonneg (hLa : 0 ≤ La) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) : 0 ≤ lipΛ La L₁ L₂ := by
  unfold lipΛ; positivity

/-- `L_c ≥ 0`. -/
theorem lipC_nonneg (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) : 0 ≤ lipC L₁ L₂ := by
  unfold lipC; positivity

/-- `G ≥ 0`. -/
theorem gConst_nonneg (L₁ L₂ M : ℝ) : 0 ≤ gConst L₁ L₂ M := by
  unfold gConst; positivity

/-- `λ ≥ 0`. -/
theorem birthRate_nonneg (L₁ L₂ M : ℝ) : 0 ≤ birthRate L₁ L₂ M :=
  mul_nonneg zero_le_two (gConst_nonneg L₁ L₂ M)

/-- `D > 0`. -/
theorem driftRate_pos (hLa : 0 ≤ La) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    0 < driftRate La L₁ L₂ := by
  have := lipΛ_nonneg hLa hL₁ hL₂
  unfold driftRate; positivity

/-- `D ≥ 0`. -/
theorem driftRate_nonneg (hLa : 0 ≤ La) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    0 ≤ driftRate La L₁ L₂ :=
  (driftRate_pos hLa hL₁ hL₂).le

/-- `ω - D = 3λ`. -/
theorem omega_sub_driftRate (La L₁ L₂ M : ℝ) :
    omega La L₁ L₂ M - driftRate La L₁ L₂ = 3 * birthRate L₁ L₂ M := by
  unfold omega; ring

/-- `D ≤ ω`. -/
theorem driftRate_le_omega (La L₁ L₂ M : ℝ) : driftRate La L₁ L₂ ≤ omega La L₁ L₂ M := by
  have := birthRate_nonneg L₁ L₂ M
  unfold omega; linarith

/-- `ω > 0`. -/
theorem omega_pos (hLa : 0 ≤ La) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (M : ℝ) :
    0 < omega La L₁ L₂ M :=
  (driftRate_pos hLa hL₁ hL₂).trans_le (driftRate_le_omega La L₁ L₂ M)

/-- `ω ≥ 0`. -/
theorem omega_nonneg (hLa : 0 ≤ La) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (M : ℝ) :
    0 ≤ omega La L₁ L₂ M :=
  (omega_pos hLa hL₁ hL₂ M).le

/-- `D_T > 0`, for all values of the parameters, since `1 + x + x²/3 > 0` for every real `x`. -/
theorem horizonFactor_pos (T La L₁ : ℝ) : 0 < horizonFactor T La L₁ := by
  unfold horizonFactor
  have := sq_nonneg (lipL La L₁ * T + 3 / 2)
  nlinarith

/-- `D_T ≥ 0`. -/
theorem horizonFactor_nonneg (T La L₁ : ℝ) : 0 ≤ horizonFactor T La L₁ :=
  (horizonFactor_pos T La L₁).le

/-- `A₀ ≥ 0`. -/
theorem sourceA₀_nonneg (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hM : 0 ≤ M) :
    0 ≤ sourceA₀ C₀ T La L₁ L₂ M := by
  have := lipC_nonneg hL₁ hL₂
  unfold sourceA₀; positivity

/-- `A₁ ≥ 0`. -/
theorem sourceA₁_nonneg (hM : 0 ≤ M) : 0 ≤ sourceA₁ C₀ T La L₁ M := by
  unfold sourceA₁; positivity

/-- `C_T ≥ 0`. -/
theorem sharpC_nonneg (C₀ T La L₁ L₂ M : ℝ) : 0 ≤ sharpC C₀ T La L₁ L₂ M := by
  unfold sharpC; positivity

/-- `e^{LT} √C₀ + e^{ωT/2} (A₀ T + 2 A₁ √T) ≥ 0`: the square root of `C_T` before squaring. -/
theorem sharpC_base_nonneg (hT : 0 ≤ T) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hM : 0 ≤ M) :
    0 ≤ Real.exp (lipL La L₁ * T) * Real.sqrt C₀ + Real.exp (omega La L₁ L₂ M * T / 2) *
      (sourceA₀ C₀ T La L₁ L₂ M * T + 2 * sourceA₁ C₀ T La L₁ M * Real.sqrt T) := by
  have := sourceA₀_nonneg (C₀ := C₀) (T := T) (La := La) hL₁ hL₂ hM
  have := sourceA₁_nonneg (C₀ := C₀) (T := T) (La := La) (L₁ := L₁) hM
  positivity

end Nonneg

/-! ### The bound of Section 3.4 -/

section ProofMain

variable {C₀ T La L₁ L₂ M : ℝ}

/-- `√C_T = e^{LT} √C₀ + e^{ωT/2} (A₀ T + 2 A₁ √T)`. -/
theorem sqrt_sharpC (hT : 0 ≤ T) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hM : 0 ≤ M) :
    Real.sqrt (sharpC C₀ T La L₁ L₂ M) =
      Real.exp (lipL La L₁ * T) * Real.sqrt C₀ + Real.exp (omega La L₁ L₂ M * T / 2) *
        (sourceA₀ C₀ T La L₁ L₂ M * T + 2 * sourceA₁ C₀ T La L₁ M * Real.sqrt T) :=
  Real.sqrt_sq (sharpC_base_nonneg hT hL₁ hL₂ hM)

/-- The final step of Section 3.4: for `0 ≤ t ≤ T`, the bound
`e^{Lt} √C₀ + e^{ωt/2} (A₀ t + 2 A₁ √t)` obtained at time `t` (with the constants `A₀`, `A₁`
of the horizon `T`) is at most `√C_T`. -/
theorem add_le_sqrt_sharpC {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (hLa : 0 ≤ La) (hL₁ : 0 ≤ L₁)
    (hL₂ : 0 ≤ L₂) (hM : 0 ≤ M) :
    Real.exp (lipL La L₁ * t) * Real.sqrt C₀ + Real.exp (omega La L₁ L₂ M * t / 2) *
        (sourceA₀ C₀ T La L₁ L₂ M * t + 2 * sourceA₁ C₀ T La L₁ M * Real.sqrt t) ≤
      Real.sqrt (sharpC C₀ T La L₁ L₂ M) := by
  have hT : 0 ≤ T := ht.trans htT
  rw [sqrt_sharpC hT hL₁ hL₂ hM]
  have hA₀ := sourceA₀_nonneg (C₀ := C₀) (T := T) (La := La) hL₁ hL₂ hM
  have hA₁ := sourceA₁_nonneg (C₀ := C₀) (T := T) (La := La) (L₁ := L₁) hM
  have hL := lipL_nonneg hLa hL₁
  have hω := omega_nonneg hLa hL₁ hL₂ M
  gcongr

/-- `C₀ ≤ C_T`; this is the case `t = 0` of Theorem 2.1. -/
theorem le_sharpC (hT : 0 ≤ T) (hLa : 0 ≤ La) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hM : 0 ≤ M) :
    C₀ ≤ sharpC C₀ T La L₁ L₂ M := by
  have h := add_le_sqrt_sharpC (C₀ := C₀) (L₂ := L₂) le_rfl hT hLa hL₁ hL₂ hM
  simp only [mul_zero, zero_div, Real.exp_zero, one_mul, Real.sqrt_zero, add_zero] at h
  exact (Real.sqrt_le_sqrt_iff (sharpC_nonneg _ _ _ _ _ _)).1 h

end ProofMain

/-! ### The comparison with a Yule process (Section 5.4) -/

section Yule

/-- `q_m ≥ 0` for `m ≤ N`. -/
theorem jumpRate_nonneg (L₁ L₂ M : ℝ) {N m : ℕ} (hmN : m ≤ N) : 0 ≤ jumpRate L₁ L₂ M N m := by
  unfold jumpRate
  have := birthRate_nonneg L₁ L₂ M
  have : (m : ℝ) / N ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hmN) (Nat.cast_nonneg N)
  have : 0 ≤ 1 - (m : ℝ) / N := by linarith
  positivity

/-- `q_m ≤ λ m`. -/
theorem jumpRate_le (L₁ L₂ M : ℝ) (N m : ℕ) : jumpRate L₁ L₂ M N m ≤ birthRate L₁ L₂ M * m := by
  unfold jumpRate
  have : 0 ≤ birthRate L₁ L₂ M * m := mul_nonneg (birthRate_nonneg L₁ L₂ M) (Nat.cast_nonneg m)
  have : 0 ≤ (m : ℝ) / N := by positivity
  nlinarith

/-- `q_N = 0`: the top level of the hierarchy has no coupling term. -/
theorem jumpRate_self (L₁ L₂ M : ℝ) {N : ℕ} (hN : N ≠ 0) : jumpRate L₁ L₂ M N N = 0 := by
  have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN
  simp [jumpRate, div_self this]

/-- The supersolution inequality of Section 5.4: if `m ≥ 1` and `0 ≤ q ≤ λ m`, then
`3λ m² - q (2m + 1) ≥ 0`. -/
theorem yule_supersolution {lam q m : ℝ} (hm : 1 ≤ m) (hq : 0 ≤ q) (hqm : q ≤ lam * m) :
    0 ≤ 3 * lam * m ^ 2 - q * (2 * m + 1) := by
  have hlam : 0 ≤ lam * m := hq.trans hqm
  have h1 : q * (2 * m + 1) ≤ lam * m * (2 * m + 1) :=
    mul_le_mul_of_nonneg_right hqm (by linarith)
  nlinarith

/-- The profile `u_m(r) = A e^{ωr} m²/N²` is a supersolution of the hierarchy (`eq:hierarchy`):
for `1 ≤ m ≤ N`, `(D - q_m) m² + q_m (m + 1)² ≤ ω m²`. The difference of the two sides is
`3λ m² - q_m (2m + 1)`, see `yule_supersolution`. -/
theorem profile_supersolution (La L₁ L₂ M : ℝ) {N m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    (driftRate La L₁ L₂ - jumpRate L₁ L₂ M N m) * (m : ℝ) ^ 2 +
        jumpRate L₁ L₂ M N m * ((m : ℝ) + 1) ^ 2 ≤ omega La L₁ L₂ M * (m : ℝ) ^ 2 := by
  have h := yule_supersolution (lam := birthRate L₁ L₂ M) (by exact_mod_cast hm)
    (jumpRate_nonneg L₁ L₂ M hmN) (jumpRate_le L₁ L₂ M N m)
  have hω := omega_sub_driftRate La L₁ L₂ M
  nlinarith

end Yule

/-! ### The entropy–cost coefficient (Lemma 4.1) -/

/-- The coefficient `β_L(s) = (1 + Ls + L²s²/3)/(4s)` of the entropy–cost inequality
(`eq:entropy-cost`) satisfies `β_L(s) ≤ T β_L(T) / s` for `0 < s ≤ T` and `L ≥ 0`. -/
theorem bridgeCost_le_div {L s T : ℝ} (hL : 0 ≤ L) (hs : 0 < s) (hsT : s ≤ T) :
    (1 + L * s + L ^ 2 * s ^ 2 / 3) / (4 * s) ≤ (1 + L * T + L ^ 2 * T ^ 2 / 3) / 4 / s := by
  rw [div_div]
  gcongr

/-- The bound `β_L(s) ≤ D_T / s` of Lemma 4.1 (`lem:entropy-cost`) for `0 < s ≤ T`, where
`L = L_a + L₁`. -/
theorem bridgeCost_le_horizonFactor_div {T La L₁ s : ℝ} (hLa : 0 ≤ La) (hL₁ : 0 ≤ L₁)
    (hs : 0 < s) (hsT : s ≤ T) :
    (1 + lipL La L₁ * s + lipL La L₁ ^ 2 * s ^ 2 / 3) / (4 * s) ≤ horizonFactor T La L₁ / s :=
  bridgeCost_le_div (lipL_nonneg hLa hL₁) hs hsT

end SharpWasserstein.Sharp
