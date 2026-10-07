/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.ApproxMcKeanVlasov

/-!
# The approximating processes are strong solutions

The stability Lemma 7.2 (`exists_approx_particle`, `exists_approx_mcKeanVlasov`) constructs, on
the probability space of a strong solution `X` of the particle system (resp. `Y` of the
McKean–Vlasov equation), processes `Xⁿ` (resp. `Yⁿ`) solving path by path the equation with the
smooth coefficients `aⁿ, Kⁿ`, a version `ξ` (resp. `ζ`) of the initial value and a regular
version `w` of the forcing `√2 W` (resp. `√2 B`).

This file shows that these processes are strong solutions in the sense of the public statement,
driven by the **same** Brownian motions (`isParticleSolution_of_forced`,
`isMcKeanVlasovSolution_of_forced`): the initial value `Xⁿ(0)` equals `X(0)` almost surely, so
independence of the noise transfers, and the forcing `w` equals `√2 W` almost surely at all
times. It also shows that the squared differences `∑ᵢ ‖Xⁿᵢ(t) - Xᵢ(t)‖²` and `‖Yⁿ(t) - Y(t)‖²`
are integrable (`integrable_sum_norm_sub_sq_of_isForcedSolution`,
`integrable_norm_sub_sq_of_isForcedSolution`), by the a priori bound
`IsForcedSolution.norm_sq_le_horizon`, so that the mean square convergence of Lemma 7.2 is a
convergence of finite expectations.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal

namespace SharpWasserstein.Sharp.Final

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {d N : ℕ}
  {a a' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
  {K K' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
  {La L₁ L₂ M : ℝ}

/-! ### The particle system -/

section Particle

variable {X X' : ℝ → Ω → Fin N → EuclideanSpace ℝ (Fin d)}
  {W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
  {ξ : Ω → Fin N → EuclideanSpace ℝ (Fin d)} {w : ℝ → Ω → Fin N → EuclideanSpace ℝ (Fin d)}

/-- **The approximating particle system is a strong solution.** Let `X` solve the particle
system driven by `W`, let `w` be a forcing almost surely equal to `√2 W` at all times, and let
`X'` have measurable sections and continuous paths and solve, for every `ω` and `t ≥ 0`,
`X'(t) = ξ + ∫₀ᵗ b'_N(X'(s)) ds + w(t)` for the drift `b'_N` of `(a', K')`. If `X'(0) = X(0)`
almost surely, then `X'` is a strong solution of the particle system with coefficients
`(a', K')`, driven by the same Brownian motions `W`. -/
theorem isParticleSolution_of_forced (hX : SharpChaos.IsParticleSolution a K X W P)
    (hwW : ∀ᵐ ω ∂P, ∀ t, w t ω = fun i => Real.sqrt 2 • W i t.toNNReal ω)
    (hX'm : ∀ t, Measurable (X' t)) (hX'c : ∀ ω, Continuous fun t => X' t ω)
    (hX'eq : ∀ ω t, 0 ≤ t → X' t ω =
      ξ ω + (∫ s in (0 : ℝ)..t, SharpChaos.particleDrift a' K' (X' s ω)) + w t ω)
    (hX'0 : X' 0 =ᵐ[P] X 0) :
    SharpChaos.IsParticleSolution a' K' X' W P where
  aemeasurable t _ := (hX'm t).aemeasurable
  brownian := hX.brownian
  iIndepFun_brownian := hX.iIndepFun_brownian
  indepFun_initial := hX.indepFun_initial.congr hX'0.symm (ae_eq_refl _)
  solves := by
    filter_upwards [hX.ae_forcing_zero, hwW] with ω hω0 hwω
    have h0 : X' 0 ω = ξ ω := by
      rw [hX'eq ω 0 le_rfl, intervalIntegral.integral_same, add_zero, hwω 0, hω0, add_zero]
    refine ⟨(hX'c ω).continuousOn, fun t ht => ?_⟩
    rw [hX'eq ω t ht, hwω t, h0]

/-- **Integrability of the squared distance to the approximating particle system.** In the
setting of Lemma 7.2 (`tendsto_integral_sum_norm_sub_sq_of_isForcedSolution`), the squared
distance `∑ᵢ ‖X'ᵢ(t) - Xᵢ(t)‖²` is integrable for every `t ≥ 0`: both processes satisfy the a
priori bound `IsForcedSolution.norm_sq_le_horizon` with the same integrable right-hand side. -/
theorem integrable_sum_norm_sub_sq_of_isForcedSolution [IsProbabilityMeasure P]
    (hA : SharpChaos.AssumptionA a K La L₁ L₂ M) (hX : SharpChaos.IsParticleSolution a K X W P)
    (hX0 : MemLp (X 0) 2 P) (hA' : SharpChaos.AssumptionA a' K' La L₁ L₂ M)
    (ha'_le : ∀ x, ‖a' x‖ ≤ ‖a 0‖ + La * (‖x‖ + 1)) (hξ : ξ =ᵐ[P] X 0) {C : ℝ}
    (hw : IsRegularForcing w C P)
    (hwW : ∀ᵐ ω ∂P, ∀ t, w t ω = fun i => Real.sqrt 2 • W i t.toNNReal ω)
    (hX'm : ∀ t, Measurable (X' t))
    (hX' : ∀ ω T, IsForcedSolution (fun _ => SharpChaos.particleDrift a' K')
      (fun t => w t ω) (ξ ω) T fun t => X' t ω)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => ∑ i, ‖X' t ω i - X t ω i‖ ^ 2) P := by
  have hLa := hA.La_nonneg
  have htt : t ∈ Icc 0 t := ⟨ht, le_rfl⟩
  set β := ‖a 0‖ + La + M with hβ
  have hgrowth : ∀ p : Fin N → EuclideanSpace ℝ (Fin d),
      ‖SharpChaos.particleDrift a K p‖ ≤ β + La * ‖p‖ := fun p =>
    (norm_particleDrift_le (norm_le_of_assumptionA hA) hLa hA.norm_K_le p).trans
      (by linarith)
  have hgrowth' : ∀ p : Fin N → EuclideanSpace ℝ (Fin d),
      ‖SharpChaos.particleDrift a' K' p‖ ≤ β + La * ‖p‖ := fun p =>
    (norm_particleDrift_le (α := ‖a 0‖ + La) (fun x => (ha'_le x).trans_eq (by ring)) hLa
      hA'.norm_K_le p).trans (by linarith)
  have hsol := hX.ae_isForcedSolution hA hξ (hwW.mono fun ω h s _ => h s) hw.continuous
  set G : Ω → ℝ := fun ω => 6 * exp (2 * La * t) *
    (‖ξ ω‖ ^ 2 + β ^ 2 * t ^ 2 + La ^ 2 * t * ∫ s in (0 : ℝ)..t, ‖w s ω‖ ^ 2) with hG
  have hXb : ∀ᵐ ω ∂P, ‖X t ω‖ ^ 2 ≤ G ω + 2 * ‖w t ω‖ ^ 2 := by
    filter_upwards [hsol] with ω hω
    exact (hω t).norm_sq_le_horizon hLa (fun s _ p => hgrowth p) htt
  have hX'b : ∀ ω, ‖X' t ω‖ ^ 2 ≤ G ω + 2 * ‖w t ω‖ ^ 2 := fun ω =>
    (hX' ω t).norm_sq_le_horizon hLa (fun s _ p => hgrowth' p) htt
  have hGi : Integrable G P :=
    ((((hX0.ae_eq hξ.symm).integrable_norm_pow two_ne_zero).add (integrable_const _)).add
      ((hw.integrable_intervalIntegral_norm_sq ht).const_mul _)).const_mul _
  have hbi : Integrable (fun ω => N * (4 * G ω + 8 * ‖w t ω‖ ^ 2)) P :=
    ((hGi.const_mul 4).add ((hw.integrable_norm_sq t ht).const_mul 8)).const_mul _
  refine hbi.mono' ?_ ?_
  · exact ((by fun_prop : Continuous fun v : Fin N → EuclideanSpace ℝ (Fin d) =>
      ∑ i, ‖v i‖ ^ 2).measurable.comp_aemeasurable
        ((hX'm t).aemeasurable.sub (hX.aemeasurable t ht))).aestronglyMeasurable
  · filter_upwards [hXb] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    have h2 := norm_sub_sq_le_two_mul (X' t ω) (X t ω)
    calc _ ≤ N * ‖X' t ω - X t ω‖ ^ 2 := sum_norm_sq_le_mul_norm_sq (X' t ω - X t ω)
      _ ≤ N * (4 * G ω + 8 * ‖w t ω‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith [hX'b ω]) (Nat.cast_nonneg _)

end Particle

/-! ### The McKean–Vlasov equation -/

section McKeanVlasov

variable {Y Y' : ℝ → Ω → EuclideanSpace ℝ (Fin d)} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
  {ζ : Ω → EuclideanSpace ℝ (Fin d)} {w : ℝ → Ω → EuclideanSpace ℝ (Fin d)}

/-- **The approximating McKean–Vlasov process is a strong solution.** Let `Y` solve the
McKean–Vlasov equation driven by `B`, let `w` be a forcing almost surely equal to `√2 B` at all
times, and let `Y'` have measurable sections and continuous paths and solve, for every `ω` and
`t ≥ 0`, `Y'(t) = ζ + ∫₀ᵗ (a'(Y'(s)) + ∫ K'(Y'(s), y) Law(Y'(s))(dy)) ds + w(t)`. If
`Y'(0) = Y(0)` almost surely, then `Y'` is a strong solution of the McKean–Vlasov equation with
coefficients `(a', K')`, driven by the same Brownian motion `B`. -/
theorem isMcKeanVlasovSolution_of_forced (hY : SharpChaos.IsMcKeanVlasovSolution a K Y B P)
    (hwB : ∀ᵐ ω ∂P, ∀ t, w t ω = Real.sqrt 2 • B t.toNNReal ω)
    (hY'm : ∀ t, Measurable (Y' t)) (hY'c : ∀ ω, Continuous fun t => Y' t ω)
    (hY'eq : ∀ ω t, 0 ≤ t → Y' t ω = ζ ω + (∫ s in (0 : ℝ)..t,
      SharpChaos.mcKeanVlasovDrift a' K' (P.map (Y' s)) (Y' s ω)) + w t ω)
    (hY'0 : Y' 0 =ᵐ[P] Y 0) :
    SharpChaos.IsMcKeanVlasovSolution a' K' Y' B P where
  aemeasurable t _ := (hY'm t).aemeasurable
  brownian := hY.brownian
  indepFun_initial := hY.indepFun_initial.congr hY'0.symm (ae_eq_refl _)
  solves := by
    filter_upwards [hY.ae_forcing_zero, hwB] with ω hω0 hwω
    have h0 : Y' 0 ω = ζ ω := by
      rw [hY'eq ω 0 le_rfl, intervalIntegral.integral_same, add_zero, hwω 0, hω0, add_zero]
    refine ⟨(hY'c ω).continuousOn, fun t ht => ?_⟩
    rw [hY'eq ω t ht, hwω t, h0]

/-- **Integrability of the squared distance to the approximating McKean–Vlasov process.** In the
setting of Lemma 7.2 (`tendsto_integral_norm_sub_sq_of_isForcedSolution`), the squared distance
`‖Y'(t) - Y(t)‖²` is integrable for every `t ≥ 0`: both processes satisfy the a priori bound
`IsForcedSolution.norm_sq_le_horizon` with the same integrable right-hand side. -/
theorem integrable_norm_sub_sq_of_isForcedSolution [IsProbabilityMeasure P]
    (hA : SharpChaos.AssumptionA a K La L₁ L₂ M)
    (hY : SharpChaos.IsMcKeanVlasovSolution a K Y B P) (hY0 : MemLp (Y 0) 2 P)
    (hA' : SharpChaos.AssumptionA a' K' La L₁ L₂ M)
    (ha'_le : ∀ x, ‖a' x‖ ≤ ‖a 0‖ + La * (‖x‖ + 1)) (hζ : ζ =ᵐ[P] Y 0) {C : ℝ}
    (hw : IsRegularForcing w C P) (hwB : ∀ᵐ ω ∂P, ∀ t, w t ω = Real.sqrt 2 • B t.toNNReal ω)
    (hY'm : ∀ t, Measurable (Y' t))
    (hY' : ∀ ω T, IsForcedSolution
      (fun s x => SharpChaos.mcKeanVlasovDrift a' K' (P.map (Y' s)) x)
      (fun t => w t ω) (ζ ω) T fun t => Y' t ω)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => ‖Y' t ω - Y t ω‖ ^ 2) P := by
  have hLa := hA.La_nonneg
  have htt : t ∈ Icc 0 t := ⟨ht, le_rfl⟩
  set β := ‖a 0‖ + La + M with hβ
  obtain ⟨Z, hZm, hZc, hZY⟩ := hY.exists_continuous_version
  have hsol := hY.ae_isForcedSolution_version hA hζ (hwB.mono fun ω h s _ => h s)
    hw.continuous hZm hZc hZY
  have hgrowth : ∀ s x, ‖SharpChaos.mcKeanVlasovDrift a K (P.map (Z s)) x‖ ≤ β + La * ‖x‖ :=
    fun s x => (norm_mcKeanVlasovDrift_le hA.norm_K_le _ x).trans
      (by linarith [norm_le_of_assumptionA hA x])
  have hgrowth' : ∀ s x,
      ‖SharpChaos.mcKeanVlasovDrift a' K' (P.map (Y' s)) x‖ ≤ β + La * ‖x‖ :=
    fun s x => (norm_mcKeanVlasovDrift_le hA'.norm_K_le _ x).trans
      (by linarith [(ha'_le x).trans_eq (by ring : _ = ‖a 0‖ + La + La * ‖x‖)])
  set G : Ω → ℝ := fun ω => 6 * exp (2 * La * t) *
    (‖ζ ω‖ ^ 2 + β ^ 2 * t ^ 2 + La ^ 2 * t * ∫ s in (0 : ℝ)..t, ‖w s ω‖ ^ 2) with hG
  have hGi : Integrable G P :=
    ((((hY0.ae_eq hζ.symm).integrable_norm_pow two_ne_zero).add (integrable_const _)).add
      ((hw.integrable_intervalIntegral_norm_sq ht).const_mul _)).const_mul _
  have hZb : ∀ᵐ ω ∂P, ‖Z t ω‖ ^ 2 ≤ G ω + 2 * ‖w t ω‖ ^ 2 := by
    filter_upwards [hsol] with ω hω
    exact (hω t).norm_sq_le_horizon hLa (fun r _ x => hgrowth r x) htt
  have hY'b : ∀ ω, ‖Y' t ω‖ ^ 2 ≤ G ω + 2 * ‖w t ω‖ ^ 2 := fun ω =>
    (hY' ω t).norm_sq_le_horizon hLa (fun r _ x => hgrowth' r x) htt
  have hbi : Integrable (fun ω => 4 * G ω + 8 * ‖w t ω‖ ^ 2) P :=
    (hGi.const_mul 4).add ((hw.integrable_norm_sq t ht).const_mul 8)
  refine hbi.mono' ?_ ?_
  · exact (((hY'm t).aemeasurable.sub (hY.aemeasurable t ht)).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards [hZb, hZY] with ω hω hZω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← hZω t ht]
    linarith [norm_sub_sq_le_two_mul (Y' t ω) (Z t ω), hY'b ω]

end McKeanVlasov

end SharpWasserstein.Sharp.Final
