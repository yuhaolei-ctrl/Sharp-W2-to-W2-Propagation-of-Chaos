/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.BrownianModification
public import SharpWasserstein.Sharp.McKeanVlasovPicard

/-!
# Stability of the particle system under smooth approximation

This file proves the first claim of the stability Lemma 7.2 (`lem:stability`) of the paper: if
the coefficients `a, K` are replaced by approximations `aⁿ, Kⁿ` as in Lemma 7.1
(`SharpWasserstein.Sharp.exists_smooth_approx`), then the particle systems driven by the same
initial configuration and the same Brownian motions converge in mean square at every time.

Let `X` be a strong solution of the particle system (`SharpChaos.IsParticleSolution`). We replace
the initial configuration `X(0)` by a measurable version `ξ` and the forcing `√2 W` by a regular
version `w` (`exists_particle_forcing`), and construct `Xⁿ` path by path with
`exists_isForcedSolution`:
`Xⁿ(t) = ξ + ∫₀ᵗ b^n_N(Xⁿ(s)) ds + w(t)` for every `ω` and `t ≥ 0`.

* The particle drift `b_N` is `(L_a + L₁ + L₂)`-Lipschitz for the sup norm on `(ℝᵈ)ᴺ`
  (`norm_particleDrift_sub_le`, as in the proof of Lemma 3.1) and has linear growth.
* Almost surely, the path of `X` solves the same integral equation with drift `b_N`
  (`SharpChaos.IsParticleSolution.ae_isForcedSolution`), so the pathwise stability estimate
  `IsForcedSolution.norm_sub_le` gives `‖Xⁿ(t) - X(t)‖ ≤ e^{Λt} ∫₀ᵗ ‖b^n_N(X(s)) - b_N(X(s))‖ ds`.
* The integrand tends to `0` uniformly on `[0, t]`, because `aⁿ → a` uniformly on the compact
  set swept by the path and `‖Kⁿ - K‖ ≤ (L₁ + L₂) / (n + 1)`.
* The a priori bound `IsForcedSolution.norm_sq_le_horizon` dominates `‖Xⁿ(t) - X(t)‖²` by an
  integrable function of `ξ` and of the forcing, which only involves `‖w(t)‖²` and
  `∫₀ᵗ ‖w(s)‖² ds` (no supremum of the Brownian motion). Dominated convergence concludes.

## Main statements

* `tendsto_integral_sum_norm_sub_sq_of_isForcedSolution`: mean square convergence for given
  versions `ξ`, `w` and given approximate solutions `Xⁿ`.
* `exists_approx_particle`: construction of `ξ`, `w` and `Xⁿ`, with all their properties.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function Real
open scoped NNReal

namespace SharpWasserstein.Sharp

/-! ### Uniform convergence along a path -/

/-- If `Gₙ → g` locally uniformly on a locally compact space and `γ` is continuous on `[0, T]`,
then `Gₙ ∘ γ → g ∘ γ` uniformly on `[0, T]`. -/
theorem eventually_forall_norm_sub_comp_lt {E F : Type*} [NormedAddCommGroup E]
    [LocallyCompactSpace E] [NormedAddCommGroup F] {G : ℕ → E → F} {g : E → F}
    (h : TendstoLocallyUniformly G g atTop) {γ : ℝ → E} {T : ℝ} (hγ : ContinuousOn γ (Icc 0 T))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n in atTop, ∀ s ∈ Icc 0 T, ‖G n (γ s) - g (γ s)‖ < ε := by
  have hu := tendstoLocallyUniformly_iff_forall_isCompact.1 h _
    (isCompact_Icc.image_of_continuousOn hγ)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hu ε hε] with n hn s hs
  rw [← dist_eq_norm, dist_comm]
  exact hn _ (mem_image_of_mem γ hs)

/-- If `fₙ → 0` uniformly on `[0, T]`, then `∫₀ᵀ fₙ → 0`. -/
theorem tendsto_intervalIntegral_of_eventually_norm_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℕ → ℝ → F} {T : ℝ} (hT : 0 ≤ T)
    (h : ∀ ε > 0, ∀ᶠ n in atTop, ∀ s ∈ Icc 0 T, ‖f n s‖ ≤ ε) :
    Tendsto (fun n => ∫ s in (0 : ℝ)..T, f n s) atTop (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hT1 : 0 < T + 1 := by linarith
  filter_upwards [h (ε / (T + 1)) (div_pos hε hT1)] with n hn
  rw [dist_zero_right]
  calc ‖∫ s in (0 : ℝ)..T, f n s‖ ≤ ε / (T + 1) * |T - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => by
          rw [uIoc_of_le hT] at hs
          exact hn s (Ioc_subset_Icc_self hs)
    _ < ε := by
        rw [sub_zero, abs_of_nonneg hT, div_mul_eq_mul_div, div_lt_iff₀ hT1]
        nlinarith

/-- `c / (n + 1) → 0`. -/
theorem tendsto_div_natCast_add_one (c : ℝ) :
    Tendsto (fun n : ℕ => c / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul c
  rw [mul_zero] at h
  exact h.congr fun n => mul_one_div _ _

/-- `‖x - y‖² ≤ 2 ‖x‖² + 2 ‖y‖²`. -/
theorem norm_sub_sq_le_two_mul {V : Type*} [SeminormedAddCommGroup V] (x y : V) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h : ‖x - y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-! ### The particle drift -/

section ParticleDrift

variable {d N : ℕ} {a a' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
  {K K' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
  {La L₁ L₂ M : ℝ}

/-- An average of `N` vectors of norm at most `c ≥ 0` has norm at most `c` (also for
`N = 0`). -/
theorem norm_inv_smul_sum_le {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    {v : Fin N → V} {c : ℝ} (hc : 0 ≤ c) (hv : ∀ j, ‖v j‖ ≤ c) :
    ‖(N : ℝ)⁻¹ • ∑ j, v j‖ ≤ c := by
  rw [norm_smul, norm_inv, Real.norm_natCast]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [hc]
  · rw [inv_mul_le_iff₀ (by exact_mod_cast hN)]
    calc ‖∑ j, v j‖ ≤ ∑ j, ‖v j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin N, c := Finset.sum_le_sum fun j _ => hv j
      _ = N * c := by simp

/-- Under Assumption A, `‖a x‖ ≤ ‖a 0‖ + L_a ‖x‖`. -/
theorem norm_le_of_assumptionA (hA : SharpChaos.AssumptionA a K La L₁ L₂ M)
    (x : EuclideanSpace ℝ (Fin d)) : ‖a x‖ ≤ ‖a 0‖ + La * ‖x‖ := by
  have h := hA.lipschitz_a x 0
  rw [sub_zero] at h
  linarith [norm_sub_norm_le (a x) (a 0)]

/-- **Lipschitz bound for the particle drift** (proof of Lemma 3.1 of the paper). Under
Assumption A, `b_N` is `(L_a + L₁ + L₂)`-Lipschitz for the sup norm on `(ℝᵈ)ᴺ`. -/
theorem norm_particleDrift_sub_le (hA : SharpChaos.AssumptionA a K La L₁ L₂ M)
    (x y : Fin N → EuclideanSpace ℝ (Fin d)) :
    ‖SharpChaos.particleDrift a K x - SharpChaos.particleDrift a K y‖ ≤
      (La + L₁ + L₂) * ‖x - y‖ := by
  have hL : 0 ≤ L₁ + L₂ := add_nonneg hA.L₁_nonneg hA.L₂_nonneg
  have hΛ : 0 ≤ La + L₁ + L₂ := by linarith [hA.La_nonneg]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hΛ (norm_nonneg _))).2 fun i => ?_
  have hxi : ‖x i - y i‖ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) i
  have heq : (SharpChaos.particleDrift a K x - SharpChaos.particleDrift a K y) i =
      (a (x i) - a (y i)) + (N : ℝ)⁻¹ • ∑ j, (K (x i) (x j) - K (y i) (y j)) := by
    simp only [SharpChaos.particleDrift, Pi.sub_apply, Finset.sum_sub_distrib, smul_sub]
    abel
  have hK : ‖(N : ℝ)⁻¹ • ∑ j, (K (x i) (x j) - K (y i) (y j))‖ ≤ (L₁ + L₂) * ‖x - y‖ :=
    norm_inv_smul_sum_le (mul_nonneg hL (norm_nonneg _)) fun j => by
      have hxj : ‖x j - y j‖ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) j
      calc _ ≤ L₁ * ‖x i - y i‖ + L₂ * ‖x j - y j‖ := hA.lipschitz_K _ _ _ _
        _ ≤ L₁ * ‖x - y‖ + L₂ * ‖x - y‖ :=
            add_le_add (mul_le_mul_of_nonneg_left hxi hA.L₁_nonneg)
              (mul_le_mul_of_nonneg_left hxj hA.L₂_nonneg)
        _ = (L₁ + L₂) * ‖x - y‖ := by ring
  rw [heq]
  calc _ ≤ ‖a (x i) - a (y i)‖ + ‖(N : ℝ)⁻¹ • ∑ j, (K (x i) (x j) - K (y i) (y j))‖ :=
        norm_add_le _ _
    _ ≤ La * ‖x - y‖ + (L₁ + L₂) * ‖x - y‖ :=
        add_le_add ((hA.lipschitz_a _ _).trans (mul_le_mul_of_nonneg_left hxi hA.La_nonneg)) hK
    _ = (La + L₁ + L₂) * ‖x - y‖ := by ring

/-- Under Assumption A, the particle drift is continuous. -/
theorem continuous_particleDrift (hA : SharpChaos.AssumptionA a K La L₁ L₂ M) :
    Continuous (SharpChaos.particleDrift (N := N) a K) := by
  have hΛ : 0 ≤ La + L₁ + L₂ := by linarith [hA.La_nonneg, hA.L₁_nonneg, hA.L₂_nonneg]
  refine (LipschitzWith.of_dist_le_mul (K := ⟨La + L₁ + L₂, hΛ⟩) fun x y => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  exact norm_particleDrift_sub_le hA x y

/-- **Linear growth of the particle drift.** If `‖a x‖ ≤ α + L_a ‖x‖` with `L_a ≥ 0` and
`‖K x y‖ ≤ M`, then `‖b_N(x)‖ ≤ α + M + L_a ‖x‖` in the sup norm. -/
theorem norm_particleDrift_le {α : ℝ} (ha : ∀ x, ‖a x‖ ≤ α + La * ‖x‖) (hLa : 0 ≤ La)
    (hK : ∀ x y, ‖K x y‖ ≤ M) (x : Fin N → EuclideanSpace ℝ (Fin d)) :
    ‖SharpChaos.particleDrift a K x‖ ≤ α + M + La * ‖x‖ := by
  have hα : 0 ≤ α := by simpa using (norm_nonneg _).trans (ha 0)
  have hM : 0 ≤ M := (norm_nonneg _).trans (hK 0 0)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have hxi : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
  calc ‖a (x i) + (N : ℝ)⁻¹ • ∑ j, K (x i) (x j)‖
      ≤ ‖a (x i)‖ + ‖(N : ℝ)⁻¹ • ∑ j, K (x i) (x j)‖ := norm_add_le _ _
    _ ≤ (α + La * ‖x i‖) + M := add_le_add (ha _) (norm_inv_smul_sum_le hM fun j => hK _ _)
    _ ≤ α + M + La * ‖x‖ := by nlinarith

/-- If `a` is bounded by `C` and `K` by `M`, then the particle drift is bounded by `C + M`. -/
theorem norm_particleDrift_le_of_forall_norm_le {C : ℝ} (ha : ∀ x, ‖a x‖ ≤ C)
    (hK : ∀ x y, ‖K x y‖ ≤ M) (x : Fin N → EuclideanSpace ℝ (Fin d)) :
    ‖SharpChaos.particleDrift a K x‖ ≤ C + M := by
  simpa using norm_particleDrift_le (La := 0) (α := C) (fun y => by simpa using ha y) le_rfl hK x

/-- The distance between two particle drifts: if `‖a' (xᵢ) - a (xᵢ)‖ ≤ δ` for every `i` and
`‖K' - K‖ ≤ ε`, then `‖b'_N(x) - b_N(x)‖ ≤ δ + ε` in the sup norm. -/
theorem norm_particleDrift_sub_particleDrift_le {δ ε : ℝ}
    (x : Fin N → EuclideanSpace ℝ (Fin d)) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (ha : ∀ i, ‖a' (x i) - a (x i)‖ ≤ δ) (hK : ∀ y z, ‖K' y z - K y z‖ ≤ ε) :
    ‖SharpChaos.particleDrift a' K' x - SharpChaos.particleDrift a K x‖ ≤ δ + ε := by
  refine (pi_norm_le_iff_of_nonneg (add_nonneg hδ hε)).2 fun i => ?_
  have heq : (SharpChaos.particleDrift a' K' x - SharpChaos.particleDrift a K x) i =
      (a' (x i) - a (x i)) + (N : ℝ)⁻¹ • ∑ j, (K' (x i) (x j) - K (x i) (x j)) := by
    simp only [SharpChaos.particleDrift, Pi.sub_apply, Finset.sum_sub_distrib, smul_sub]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add (ha i) (norm_inv_smul_sum_le hε fun j => hK _ _))

end ParticleDrift

/-! ### The particle system along its paths -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {d N : ℕ}
  {a : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
  {K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
  {La L₁ L₂ M : ℝ} {X : ℝ → Ω → Fin N → EuclideanSpace ℝ (Fin d)}
  {W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}

/-- **Pathwise form of the particle system.** Let `X` solve the particle system, let `ξ` be a
version of `X(0)` and let `w` be a forcing with continuous paths that almost surely equals
`√2 W` at nonnegative times. Then almost surely, for every `T`, the path of `X` solves on
`[0, T]` the integral equation with drift `b_N`, initial value `ξ` and forcing `w`. -/
theorem _root_.SharpChaos.IsParticleSolution.ae_isForcedSolution
    (hA : SharpChaos.AssumptionA a K La L₁ L₂ M) (hX : SharpChaos.IsParticleSolution a K X W P)
    {ξ : Ω → Fin N → EuclideanSpace ℝ (Fin d)} (hξ : ξ =ᵐ[P] X 0)
    {w : ℝ → Ω → Fin N → EuclideanSpace ℝ (Fin d)}
    (hwW : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → w t ω = fun i => Real.sqrt 2 • W i t.toNNReal ω)
    (hwc : ∀ ω, Continuous fun t => w t ω) :
    ∀ᵐ ω ∂P, ∀ T, IsForcedSolution (fun _ => SharpChaos.particleDrift a K) (fun t => w t ω)
      (ξ ω) T fun t => X t ω := by
  filter_upwards [hX.solves, hξ, hwW] with ω hω hξω hwω T
  have hc : ContinuousOn (fun t => X t ω) (Icc 0 T) := hω.1.mono Icc_subset_Ici_self
  refine ⟨hc, (hwc ω).continuousOn, (continuous_particleDrift hA).comp_continuousOn hc,
    fun t ht => ?_⟩
  rw [hω.2 t ht.1, hwω t ht.1, hξω]

/-- Along a solution of the particle system, the forcing vanishes at time `0` almost surely. -/
theorem _root_.SharpChaos.IsParticleSolution.ae_forcing_zero
    (hX : SharpChaos.IsParticleSolution a K X W P) :
    ∀ᵐ ω ∂P, (fun i => Real.sqrt 2 • W i (0 : ℝ).toNNReal ω) = 0 := by
  filter_upwards [hX.solves] with ω hω
  have h := hω.2 0 le_rfl
  rw [intervalIntegral.integral_same, add_zero] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

/-! ### Mean square convergence -/

/-- **Lemma 7.2, particle system** (mean square convergence at a fixed time). Let `X` solve the
particle system with coefficients `a, K` satisfying Assumption A and square integrable initial
configuration. Let `aⁿ, Kⁿ` satisfy Assumption A with the same constants, with `aⁿ → a` locally
uniformly, `‖Kⁿ - K‖ ≤ (L₁ + L₂) / (n + 1)` and `‖aⁿ x‖ ≤ ‖a 0‖ + L_a (‖x‖ + 1)`. Let `ξ` be a
version of `X(0)`, let `w` be a regular forcing almost surely equal to `√2 W` at nonnegative times,
and let `Xⁿ` have measurable sections and solve, for every `ω`, the integral equation with drift
`b^n_N`, initial value `ξ` and forcing `w`. Then for every `t ≥ 0`,
`E ∑ᵢ ‖Xⁿᵢ(t) - Xᵢ(t)‖² → 0`. -/
theorem tendsto_integral_sum_norm_sub_sq_of_isForcedSolution [IsProbabilityMeasure P]
    (hA : SharpChaos.AssumptionA a K La L₁ L₂ M) (hX : SharpChaos.IsParticleSolution a K X W P)
    (hX0 : MemLp (X 0) 2 P) {aₙ : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {Kₙ : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hAₙ : ∀ n, SharpChaos.AssumptionA (aₙ n) (Kₙ n) La L₁ L₂ M)
    (haₙ : TendstoLocallyUniformly aₙ a atTop)
    (hKₙ : ∀ n x y, ‖Kₙ n x y - K x y‖ ≤ (L₁ + L₂) / (n + 1))
    (haₙ_le : ∀ n x, ‖aₙ n x‖ ≤ ‖a 0‖ + La * (‖x‖ + 1))
    {ξ : Ω → Fin N → EuclideanSpace ℝ (Fin d)} (hξ : ξ =ᵐ[P] X 0)
    {w : ℝ → Ω → Fin N → EuclideanSpace ℝ (Fin d)} {C : ℝ} (hw : IsRegularForcing w C P)
    (hwW : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → w t ω = fun i => Real.sqrt 2 • W i t.toNNReal ω)
    {Xₙ : ℕ → ℝ → Ω → Fin N → EuclideanSpace ℝ (Fin d)} (hXₙm : ∀ n t, Measurable (Xₙ n t))
    (hXₙ : ∀ n ω T, IsForcedSolution (fun _ => SharpChaos.particleDrift (aₙ n) (Kₙ n))
      (fun t => w t ω) (ξ ω) T fun t => Xₙ n t ω)
    {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => ∫ ω, ∑ i, ‖Xₙ n t ω i - X t ω i‖ ^ 2 ∂P) atTop (𝓝 0) := by
  have hLa := hA.La_nonneg
  have hΛ : 0 ≤ La + L₁ + L₂ := by linarith [hA.L₁_nonneg, hA.L₂_nonneg]
  have htt : t ∈ Icc 0 t := ⟨ht, le_rfl⟩
  set β := ‖a 0‖ + La + M with hβ
  have hgrowth : ∀ p : Fin N → EuclideanSpace ℝ (Fin d),
      ‖SharpChaos.particleDrift a K p‖ ≤ β + La * ‖p‖ := fun p =>
    (norm_particleDrift_le (norm_le_of_assumptionA hA) hLa hA.norm_K_le p).trans
      (by linarith)
  have hgrowthₙ : ∀ n (p : Fin N → EuclideanSpace ℝ (Fin d)),
      ‖SharpChaos.particleDrift (aₙ n) (Kₙ n) p‖ ≤ β + La * ‖p‖ := fun n p =>
    (norm_particleDrift_le (α := ‖a 0‖ + La) (fun x => (haₙ_le n x).trans_eq (by ring)) hLa
      (hAₙ n).norm_K_le p).trans (by linarith)
  have hsol := hX.ae_isForcedSolution hA hξ hwW hw.continuous
  -- The a priori bound.
  set G : Ω → ℝ := fun ω => 6 * exp (2 * La * t) *
    (‖ξ ω‖ ^ 2 + β ^ 2 * t ^ 2 + La ^ 2 * t * ∫ s in (0 : ℝ)..t, ‖w s ω‖ ^ 2) with hG
  have hXb : ∀ᵐ ω ∂P, ‖X t ω‖ ^ 2 ≤ G ω + 2 * ‖w t ω‖ ^ 2 := by
    filter_upwards [hsol] with ω hω
    exact (hω t).norm_sq_le_horizon hLa (fun s _ p => hgrowth p) htt
  have hXₙb : ∀ n ω, ‖Xₙ n t ω‖ ^ 2 ≤ G ω + 2 * ‖w t ω‖ ^ 2 := fun n ω =>
    (hXₙ n ω t).norm_sq_le_horizon hLa (fun s _ p => hgrowthₙ n p) htt
  have hGi : Integrable G P :=
    ((((hX0.ae_eq hξ.symm).integrable_norm_pow two_ne_zero).add (integrable_const _)).add
      ((hw.integrable_intervalIntegral_norm_sq ht).const_mul _)).const_mul _
  set bound : Ω → ℝ := fun ω => N * (4 * G ω + 8 * ‖w t ω‖ ^ 2) with hbound
  have hbi : Integrable bound P :=
    ((hGi.const_mul 4).add ((hw.integrable_norm_sq t ht).const_mul 8)).const_mul _
  -- Pointwise convergence.
  have hlim : ∀ᵐ ω ∂P,
      Tendsto (fun n => ∑ i, ‖Xₙ n t ω i - X t ω i‖ ^ 2) atTop (𝓝 0) := by
    filter_upwards [hsol] with ω hω
    have hXc : ContinuousOn (fun s => X s ω) (Icc 0 t) := (hω t).continuousOn
    have hI : Tendsto (fun n => ∫ s in (0 : ℝ)..t, ‖SharpChaos.particleDrift (aₙ n) (Kₙ n)
        (X s ω) - SharpChaos.particleDrift a K (X s ω)‖) atTop (𝓝 0) := by
      refine tendsto_intervalIntegral_of_eventually_norm_le ht fun ε hε => ?_
      have hc : ∀ᶠ n : ℕ in atTop, (L₁ + L₂) / ((n : ℝ) + 1) ≤ ε / 2 :=
        (tendsto_div_natCast_add_one _).eventually (eventually_le_nhds (half_pos hε))
      have hu : ∀ᶠ n in atTop, ∀ i, ∀ s ∈ Icc 0 t, ‖aₙ n (X s ω i) - a (X s ω i)‖ < ε / 2 :=
        eventually_all.2 fun i => eventually_forall_norm_sub_comp_lt haₙ
          ((continuous_apply i).comp_continuousOn hXc) (half_pos hε)
      filter_upwards [hc, hu] with n hcn hun s hs
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      calc _ ≤ ε / 2 + ε / 2 :=
            norm_particleDrift_sub_particleDrift_le _ (half_pos hε).le (half_pos hε).le
              (fun i => (hun i s hs).le) fun y z => (hKₙ n y z).trans hcn
        _ = ε := add_halves ε
    have hbn : ∀ n, ∑ i, ‖Xₙ n t ω i - X t ω i‖ ^ 2 ≤
        N * ((∫ s in (0 : ℝ)..t, ‖SharpChaos.particleDrift (aₙ n) (Kₙ n) (X s ω) -
          SharpChaos.particleDrift a K (X s ω)‖) * exp ((La + L₁ + L₂) * t)) ^ 2 := fun n => by
      have h1 := (hXₙ n ω t).norm_sub_le (hω t) hΛ
        (fun s _ p q => norm_particleDrift_sub_le (hAₙ n) p q)
        (intervalIntegrable_of_continuousOn_Icc
          ((continuous_particleDrift (hAₙ n)).comp_continuousOn hXc) htt) htt
      rw [sub_self, norm_zero, zero_add] at h1
      exact (sum_norm_sq_le_mul_norm_sq (Xₙ n t ω - X t ω)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2) (Nat.cast_nonneg _))
    refine squeeze_zero (fun n => Finset.sum_nonneg fun i _ => sq_nonneg _) hbn ?_
    simpa using ((hI.mul_const (exp ((La + L₁ + L₂) * t))).pow 2).const_mul (N : ℝ)
  -- Dominated convergence.
  have hmeas : ∀ n, AEStronglyMeasurable (fun ω => ∑ i, ‖Xₙ n t ω i - X t ω i‖ ^ 2) P :=
    fun n => ((by fun_prop : Continuous fun v : Fin N → EuclideanSpace ℝ (Fin d) =>
      ∑ i, ‖v i‖ ^ 2).measurable.comp_aemeasurable
        ((hXₙm n t).aemeasurable.sub (hX.aemeasurable t ht))).aestronglyMeasurable
  have hbd : ∀ n, ∀ᵐ ω ∂P, ‖∑ i, ‖Xₙ n t ω i - X t ω i‖ ^ 2‖ ≤ bound ω := fun n => by
    filter_upwards [hXb] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    have h2 := norm_sub_sq_le_two_mul (Xₙ n t ω) (X t ω)
    calc _ ≤ N * ‖Xₙ n t ω - X t ω‖ ^ 2 := sum_norm_sq_le_mul_norm_sq (Xₙ n t ω - X t ω)
      _ ≤ N * (4 * G ω + 8 * ‖w t ω‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith [hXₙb n ω]) (Nat.cast_nonneg _)
  simpa using tendsto_integral_of_dominated_convergence bound hmeas hbi hbd hlim

/-- **Lemma 7.2, particle system.** Let `X` solve the particle system with coefficients `a, K`
satisfying Assumption A, driven by `W`, with square integrable initial configuration, and let
`aⁿ, Kⁿ` be as in Lemma 7.1 (`exists_smooth_approx`; only boundedness of `aⁿ`, Assumption A with
the same constants, `aⁿ → a` locally uniformly, `‖Kⁿ - K‖ ≤ (L₁ + L₂) / (n + 1)` and the growth
bound `‖aⁿ x‖ ≤ ‖a 0‖ + L_a (‖x‖ + 1)` are used). Then there are

* a measurable version `ξ` of `X(0)`,
* a regular forcing `w` (`IsRegularForcing`, with `E ‖w t‖² ≤ 2 N d t`) almost surely equal to
  `t ↦ (√2 Wᵢ(t⁺))ᵢ` at all times, and
* processes `Xⁿ` with measurable sections and continuous paths solving, for every `ω`, `n` and
  `t ≥ 0`, `Xⁿ(t) = ξ + ∫₀ᵗ b^n_N(Xⁿ(s)) ds + w(t)` (also in the form of `IsForcedSolution`),

such that `Xⁿ(0) = X(0)` almost surely and `E ∑ᵢ ‖Xⁿᵢ(t) - Xᵢ(t)‖² → 0` for every `t ≥ 0`. -/
theorem exists_approx_particle [IsProbabilityMeasure P]
    (hA : SharpChaos.AssumptionA a K La L₁ L₂ M) (hX : SharpChaos.IsParticleSolution a K X W P)
    (hX0 : MemLp (X 0) 2 P) {aₙ : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {Kₙ : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hAₙ : ∀ n, SharpChaos.AssumptionA (aₙ n) (Kₙ n) La L₁ L₂ M)
    (haₙ_bdd : ∀ n, ∃ C, ∀ x, ‖aₙ n x‖ ≤ C) (haₙ : TendstoLocallyUniformly aₙ a atTop)
    (hKₙ : ∀ n x y, ‖Kₙ n x y - K x y‖ ≤ (L₁ + L₂) / (n + 1))
    (haₙ_le : ∀ n x, ‖aₙ n x‖ ≤ ‖a 0‖ + La * (‖x‖ + 1)) :
    ∃ (ξ : Ω → Fin N → EuclideanSpace ℝ (Fin d)) (w : ℝ → Ω → Fin N → EuclideanSpace ℝ (Fin d))
      (Xₙ : ℕ → ℝ → Ω → Fin N → EuclideanSpace ℝ (Fin d)),
      Measurable ξ ∧ ξ =ᵐ[P] X 0 ∧ IsRegularForcing w (2 * N * d) P ∧
      (∀ᵐ ω ∂P, ∀ t, w t ω = fun i => Real.sqrt 2 • W i t.toNNReal ω) ∧
      (∀ n t, Measurable (Xₙ n t)) ∧ (∀ n ω, Continuous fun t => Xₙ n t ω) ∧
      (∀ n ω T, IsForcedSolution (fun _ => SharpChaos.particleDrift (aₙ n) (Kₙ n))
        (fun t => w t ω) (ξ ω) T fun t => Xₙ n t ω) ∧
      (∀ n ω t, 0 ≤ t → Xₙ n t ω =
        ξ ω + (∫ s in (0 : ℝ)..t, SharpChaos.particleDrift (aₙ n) (Kₙ n) (Xₙ n s ω)) + w t ω) ∧
      (∀ n, Xₙ n 0 =ᵐ[P] X 0) ∧
      ∀ t, 0 ≤ t → Tendsto (fun n => ∫ ω, ∑ i, ‖Xₙ n t ω i - X t ω i‖ ^ 2 ∂P) atTop (𝓝 0) := by
  have hΛ : 0 ≤ La + L₁ + L₂ := by linarith [hA.La_nonneg, hA.L₁_nonneg, hA.L₂_nonneg]
  obtain ⟨ξ, w, hξm, hξ, hw, hwW⟩ := hX.exists_versions
  have hex : ∀ n, ∃ Y : ℝ → Ω → Fin N → EuclideanSpace ℝ (Fin d), (∀ t, Measurable (Y t)) ∧
      (∀ ω, Continuous fun t => Y t ω) ∧ ∀ ω T, IsForcedSolution
        (fun _ => SharpChaos.particleDrift (aₙ n) (Kₙ n)) (fun t => w t ω) (ξ ω) T
        fun t => Y t ω := fun n => by
    obtain ⟨C, hC⟩ := haₙ_bdd n
    exact exists_isForcedSolution hξm hw.continuous hw.measurable
      (norm_particleDrift_le_of_forall_norm_le hC (hAₙ n).norm_K_le)
      (norm_particleDrift_sub_le (hAₙ n)) hΛ
  choose Xₙ hXₙm hXₙc hXₙ using hex
  have hwW' : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → w t ω = fun i => Real.sqrt 2 • W i t.toNNReal ω :=
    hwW.mono fun ω h t _ => h t
  refine ⟨ξ, w, Xₙ, hξm, hξ, hw, hwW, hXₙm, hXₙc, hXₙ,
    fun n ω t ht => (hXₙ n ω t).eq_add_integral t ⟨ht, le_rfl⟩, fun n => ?_,
    fun t ht => tendsto_integral_sum_norm_sub_sq_of_isForcedSolution hA hX hX0 hAₙ haₙ hKₙ
      haₙ_le hξ hw hwW' hXₙm hXₙ ht⟩
  filter_upwards [hX.ae_forcing_zero, hwW, hξ] with ω hω0 hwω hξω
  rw [(hXₙ n ω 0).eq_add_integral 0 ⟨le_rfl, le_rfl⟩, intervalIntegral.integral_same, add_zero,
    hwω 0, hω0, add_zero, hξω]

end SharpWasserstein.Sharp
