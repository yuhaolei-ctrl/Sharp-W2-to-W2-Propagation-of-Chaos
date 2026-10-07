/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.ApproxParticle

/-!
# Stability of the McKean–Vlasov equation under smooth approximation

This file proves the second claim of the stability Lemma 7.2 (`lem:stability`) of the paper: if
the coefficients `a, K` are replaced by approximations `aⁿ, Kⁿ` as in Lemma 7.1
(`SharpWasserstein.Sharp.exists_smooth_approx`), then the solutions of the McKean–Vlasov equation
driven by the same initial value and the same Brownian motion converge in mean square at every
time.

Let `Y` be a strong solution of the McKean–Vlasov equation (`SharpChaos.IsMcKeanVlasovSolution`).
We replace `Y(0)` by a measurable version `ζ`, the forcing `√2 B` by a regular version `w`
(`SharpChaos.IsMcKeanVlasovSolution.exists_versions`) and `Y` itself by a version `Ỹ` with
continuous paths and measurable sections
(`SharpChaos.IsMcKeanVlasovSolution.exists_continuous_version`). The approximations `Yⁿ` are
given by `McKeanVlasov.exists_isForcedSolution`, path by path:
`Yⁿ(t) = ζ + ∫₀ᵗ (aⁿ(Yⁿ(s)) + ∫ Kⁿ(Yⁿ(s), y) μⁿ_s(dy)) ds + w(t)`, `μⁿ_s = Law(Yⁿ(s))`.

We follow the proof of the paper.

* **Natural coupling.** The laws `μⁿ_s` and `μ_s` are both images of `P`, so the law terms can be
  compared under `P`: with `m_n(s) = E ‖Yⁿ(s) - Ỹ(s)‖`,
  `‖Bⁿ_s(x) - B_s(x)‖ ≤ ‖aⁿ(x) - a(x)‖ + L₂ m_n(s) + (L₁ + L₂) / (n + 1)`
  (`norm_mcKeanVlasovDrift_map_sub_le`), and `Bⁿ_s` is `(L_a + L₁)`-Lipschitz.
* **Pathwise estimate.** `IsForcedSolution.norm_sub_le_of_le` gives, almost surely,
  `‖Yⁿ(s) - Ỹ(s)‖ ≤ (A_n + L₂ ∫₀ˢ m_n + (L₁ + L₂) T / (n + 1)) e^{(L_a + L₁) T}` for `s ≤ T`,
  where `A_n = ∫₀ᵀ ‖aⁿ(Ỹ(r)) - a(Ỹ(r))‖ dr`.
* **Grönwall's inequality in expectation.** Taking expectations and applying Grönwall's
  inequality to `m_n` gives `m_n ≤ κ_n` on `[0, T]`, with `κ_n → 0` because `E A_n → 0` by
  dominated convergence (local uniform convergence of `aⁿ` on the compact paths of `Ỹ`, and the
  growth bound `‖aⁿ x‖ ≤ ‖a 0‖ + L_a (‖x‖ + 1)` together with the a priori bound).
* **Mean square convergence.** Plugging `m_n ≤ κ_n` back into the pathwise estimate gives
  `Yⁿ(T) → Ỹ(T)` almost surely; the a priori bound `IsForcedSolution.norm_sq_le_horizon`
  dominates `‖Yⁿ(T) - Ỹ(T)‖²`, and dominated convergence concludes.

## Main statements

* `tendsto_integral_norm_sub_sq_of_isForcedSolution`: mean square convergence for given versions
  `ζ`, `w` and given approximate solutions `Yⁿ`.
* `exists_approx_mcKeanVlasov`: construction of `ζ`, `w` and `Yⁿ`, with all their properties.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function Real
open scoped NNReal

namespace SharpWasserstein.Sharp

/-! ### The McKean–Vlasov drift -/

section Drift

variable {d : ℕ} {a a' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
  {K K' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
  {La L₁ L₂ M : ℝ}

/-- Under Assumption A, the confinement `a` is continuous. -/
theorem continuous_of_assumptionA (hA : SharpChaos.AssumptionA a K La L₁ L₂ M) : Continuous a :=
  (LipschitzWith.of_dist_le_mul (K := ⟨La, hA.La_nonneg⟩) fun x y => by
    rw [dist_eq_norm, dist_eq_norm]
    exact hA.lipschitz_a x y).continuous

/-- Under Assumption A, the interaction `K x` is continuous. -/
theorem continuous_apply_of_assumptionA (hA : SharpChaos.AssumptionA a K La L₁ L₂ M)
    (x : EuclideanSpace ℝ (Fin d)) : Continuous (K x) :=
  (continuous_uncurry_of_norm_sub_le hA.L₁_nonneg hA.L₂_nonneg hA.lipschitz_K).comp
    (continuous_const.prodMk continuous_id)

/-- Under Assumption A, `K x` is integrable for every finite measure. -/
theorem integrable_apply_of_assumptionA (hA : SharpChaos.AssumptionA a K La L₁ L₂ M)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ] (x : EuclideanSpace ℝ (Fin d)) :
    Integrable (K x) μ :=
  Integrable.of_bound (continuous_apply_of_assumptionA hA x).aestronglyMeasurable M
    (ae_of_all _ (hA.norm_K_le x))

/-- The law term of the McKean–Vlasov drift for the law of a random variable `U`, written as an
integral over the underlying probability space: `B(x) = a(x) + ∫ K(x, U(ω)) dP(ω)`. -/
theorem mcKeanVlasovDrift_map (hA : SharpChaos.AssumptionA a K La L₁ L₂ M) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {U : Ω → EuclideanSpace ℝ (Fin d)}
    (hU : AEMeasurable U P) (x : EuclideanSpace ℝ (Fin d)) :
    SharpChaos.mcKeanVlasovDrift a K (P.map U) x = a x + ∫ ω, K x (U ω) ∂P := by
  rw [SharpChaos.mcKeanVlasovDrift,
    integral_map hU (continuous_apply_of_assumptionA hA x).aestronglyMeasurable]

/-- **Lipschitz bound for the McKean–Vlasov drift** (proof of Lemma 3.1 of the paper). For a
probability measure `μ`, the drift `x ↦ a(x) + ∫ K(x, y) μ(dy)` is `(L_a + L₁)`-Lipschitz. -/
theorem norm_mcKeanVlasovDrift_sub_le (hA : SharpChaos.AssumptionA a K La L₁ L₂ M)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (x y : EuclideanSpace ℝ (Fin d)) :
    ‖SharpChaos.mcKeanVlasovDrift a K μ x - SharpChaos.mcKeanVlasovDrift a K μ y‖ ≤
      (La + L₁) * ‖x - y‖ := by
  have h : ‖∫ z, K x z ∂μ - ∫ z, K y z ∂μ‖ ≤ L₁ * ‖x - y‖ := by
    rw [← integral_sub (integrable_apply_of_assumptionA hA μ x)
      (integrable_apply_of_assumptionA hA μ y)]
    simpa using norm_integral_le_of_norm_le_const (μ := μ) (C := L₁ * ‖x - y‖)
      (ae_of_all _ fun z => by simpa using hA.lipschitz_K x y z z)
  calc _ = ‖(a x - a y) + (∫ z, K x z ∂μ - ∫ z, K y z ∂μ)‖ := by
        unfold SharpChaos.mcKeanVlasovDrift
        congr 1
        abel
    _ ≤ La * ‖x - y‖ + L₁ * ‖x - y‖ := (norm_add_le _ _).trans (add_le_add (hA.lipschitz_a x y) h)
    _ = (La + L₁) * ‖x - y‖ := by ring

/-- **Growth of the McKean–Vlasov drift.** For a probability measure `μ` and `‖K‖ ≤ M`,
`‖a(x) + ∫ K(x, y) μ(dy)‖ ≤ ‖a(x)‖ + M`. -/
theorem norm_mcKeanVlasovDrift_le (hK : ∀ x y, ‖K x y‖ ≤ M)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖SharpChaos.mcKeanVlasovDrift a K μ x‖ ≤ ‖a x‖ + M :=
  (norm_add_le _ _).trans (add_le_add le_rfl
    (by simpa using norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ (hK x))))

/-- **Comparison of McKean–Vlasov drifts through the natural coupling.** Let `U, U'` be random
variables on a probability space with `‖U - U'‖` integrable, let `(a', K')` and `(a, K)` satisfy
Assumption A, and let `‖K' - K‖ ≤ ε`. Then, comparing the laws of `U` and `U'` through the
coupling `(U, U')`,
`‖B'_{Law U}(x) - B_{Law U'}(x)‖ ≤ ‖a'(x) - a(x)‖ + L₂ E ‖U - U'‖ + ε`. -/
theorem norm_mcKeanVlasovDrift_map_sub_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] (hA' : SharpChaos.AssumptionA a' K' La L₁ L₂ M)
    (hA : SharpChaos.AssumptionA a K La L₁ L₂ M) {ε : ℝ} (hK : ∀ x y, ‖K' x y - K x y‖ ≤ ε)
    {U U' : Ω → EuclideanSpace ℝ (Fin d)} (hU : AEMeasurable U P) (hU' : AEMeasurable U' P)
    (hUU' : Integrable (fun ω => ‖U ω - U' ω‖) P) (x : EuclideanSpace ℝ (Fin d)) :
    ‖SharpChaos.mcKeanVlasovDrift a' K' (P.map U) x -
        SharpChaos.mcKeanVlasovDrift a K (P.map U') x‖ ≤
      ‖a' x - a x‖ + L₂ * ∫ ω, ‖U ω - U' ω‖ ∂P + ε := by
  rw [mcKeanVlasovDrift_map hA' hU, mcKeanVlasovDrift_map hA hU']
  have hi' : Integrable (fun ω => K' x (U ω)) P :=
    Integrable.of_bound ((continuous_apply_of_assumptionA hA' x).measurable.comp_aemeasurable
      hU).aestronglyMeasurable M (ae_of_all _ fun ω => hA'.norm_K_le _ _)
  have hi : Integrable (fun ω => K x (U' ω)) P :=
    Integrable.of_bound ((continuous_apply_of_assumptionA hA x).measurable.comp_aemeasurable
      hU').aestronglyMeasurable M (ae_of_all _ fun ω => hA.norm_K_le _ _)
  have h : ‖∫ ω, K' x (U ω) ∂P - ∫ ω, K x (U' ω) ∂P‖ ≤ L₂ * ∫ ω, ‖U ω - U' ω‖ ∂P + ε := by
    rw [← integral_sub hi' hi]
    refine (norm_integral_le_of_norm_le ((hUU'.const_mul L₂).add (integrable_const ε))
      (ae_of_all _ fun ω => ?_)).trans_eq ?_
    · calc ‖K' x (U ω) - K x (U' ω)‖
          ≤ ‖K' x (U ω) - K' x (U' ω)‖ + ‖K' x (U' ω) - K x (U' ω)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ L₂ * ‖U ω - U' ω‖ + ε :=
            add_le_add (by simpa using hA'.lipschitz_K x x (U ω) (U' ω)) (hK _ _)
    · simp only [Pi.add_apply]
      rw [integral_add (hUU'.const_mul L₂) (integrable_const ε), integral_const_mul]
      simp
  calc _ = ‖(a' x - a x) + (∫ ω, K' x (U ω) ∂P - ∫ ω, K x (U' ω) ∂P)‖ := by
        congr 1
        abel
    _ ≤ ‖a' x - a x‖ + (L₂ * ∫ ω, ‖U ω - U' ω‖ ∂P + ε) := (norm_add_le _ _).trans
        (add_le_add le_rfl h)
    _ = _ := by ring

end Drift

/-- For `f : ℝ → Ω → ℝ` with continuous paths and measurable sections, `ω ↦ ∫₀ᵀ f(s, ω) ds` is
strongly measurable. -/
theorem stronglyMeasurable_intervalIntegral_of_continuous {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {f : ℝ → Ω → ℝ} (hc : ∀ ω, Continuous fun s => f s ω) (hm : ∀ s, Measurable (f s))
    (T : ℝ) : StronglyMeasurable fun ω => ∫ s in (0 : ℝ)..T, f s ω := by
  have h := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hc
    fun s => (hm s).stronglyMeasurable
  simp only [intervalIntegral]
  exact (h.integral_prod_left (μ := volume.restrict (Ioc 0 T))).sub
    (h.integral_prod_left (μ := volume.restrict (Ioc T 0)))

/-! ### The McKean–Vlasov equation along its paths -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {d : ℕ}
  {a : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
  {K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
  {La L₁ L₂ M : ℝ} {Y : ℝ → Ω → EuclideanSpace ℝ (Fin d)}
  {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}

/-- A solution of the McKean–Vlasov equation has a version `Ỹ` with measurable sections and
continuous paths for every `ω`, which almost surely coincides with `Y` at all nonnegative times.
It is a continuous modification of `t ↦ Y(max t 0)`. -/
theorem _root_.SharpChaos.IsMcKeanVlasovSolution.exists_continuous_version
    (hY : SharpChaos.IsMcKeanVlasovSolution a K Y B P) :
    ∃ Y' : ℝ → Ω → EuclideanSpace ℝ (Fin d), (∀ t, Measurable (Y' t)) ∧
      (∀ ω, Continuous fun t => Y' t ω) ∧ ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → Y' t ω = Y t ω := by
  obtain ⟨Y', hY'm, hY'c, hY'Y⟩ := exists_continuous_modification (P := P)
    (X := fun t ω => Y (max t 0) ω) (fun t => hY.aemeasurable _ (le_max_right t 0))
    (hY.solves.mono fun ω h => h.1.comp_continuous (continuous_id.max continuous_const)
      fun t => le_max_right t 0)
  refine ⟨Y', hY'm, hY'c, hY'Y.mono fun ω h t ht => ?_⟩
  rw [h t, max_eq_left ht]

/-- Along a solution of the McKean–Vlasov equation, the forcing vanishes at time `0` almost
surely. -/
theorem _root_.SharpChaos.IsMcKeanVlasovSolution.ae_forcing_zero
    (hY : SharpChaos.IsMcKeanVlasovSolution a K Y B P) :
    ∀ᵐ ω ∂P, Real.sqrt 2 • B (0 : ℝ).toNNReal ω = 0 := by
  filter_upwards [hY.solves] with ω hω
  have h := hω.2 0 le_rfl
  rw [intervalIntegral.integral_same, add_zero] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

/-- **Pathwise form of the McKean–Vlasov equation.** Let `Y` solve the McKean–Vlasov equation, let
`ζ` be a version of `Y(0)`, let `w` be a forcing with continuous paths almost surely equal to
`√2 B` at nonnegative times, and let `Ỹ` be a version of `Y` with measurable sections and
continuous paths. Then almost surely, for every `T`, the path of `Ỹ` solves on `[0, T]` the
integral equation with drift `x ↦ a(x) + ∫ K(x, y) Law(Ỹ(s))(dy)`, initial value `ζ` and
forcing `w`. -/
theorem _root_.SharpChaos.IsMcKeanVlasovSolution.ae_isForcedSolution_version
    [IsFiniteMeasure P] (hA : SharpChaos.AssumptionA a K La L₁ L₂ M)
    (hY : SharpChaos.IsMcKeanVlasovSolution a K Y B P) {ζ : Ω → EuclideanSpace ℝ (Fin d)}
    (hζ : ζ =ᵐ[P] Y 0) {w : ℝ → Ω → EuclideanSpace ℝ (Fin d)}
    (hwB : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → w t ω = Real.sqrt 2 • B t.toNNReal ω)
    (hwc : ∀ ω, Continuous fun t => w t ω) {Y' : ℝ → Ω → EuclideanSpace ℝ (Fin d)}
    (hY'm : ∀ t, Measurable (Y' t)) (hY'c : ∀ ω, Continuous fun t => Y' t ω)
    (hY'Y : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → Y' t ω = Y t ω) :
    ∀ᵐ ω ∂P, ∀ T, IsForcedSolution
      (fun s x => SharpChaos.mcKeanVlasovDrift a K (P.map (Y' s)) x) (fun t => w t ω) (ζ ω) T
      fun t => Y' t ω := by
  have hlaw : ∀ s, 0 ≤ s → P.map (Y s) = P.map (Y' s) := fun s hs =>
    Measure.map_congr (hY'Y.mono fun ω h => (h s hs).symm)
  have hdrift : ∀ ω, (fun s => SharpChaos.mcKeanVlasovDrift a K (P.map (Y' s)) (Y' s ω)) =
      fun s => a (Y' s ω) + ∫ ω', K (Y' s ω) (Y' s ω') ∂P := fun ω => by
    funext s
    exact mcKeanVlasovDrift_map hA (hY'm s).aemeasurable _
  filter_upwards [hY.solves, hζ, hwB, hY'Y] with ω hω hζω hwω hY'ω T
  refine ⟨(hY'c ω).continuousOn, (hwc ω).continuousOn, ?_, fun t ht => ?_⟩
  · rw [hdrift ω]
    exact (((continuous_of_assumptionA hA).comp (hY'c ω)).add
      (continuous_integral_comp P
        (continuous_uncurry_of_norm_sub_le hA.L₁_nonneg hA.L₂_nonneg hA.lipschitz_K) hA.norm_K_le
        (hY'c ω) hY'm hY'c)).continuousOn
  · rw [hY'ω t ht.1, hω.2 t ht.1, hζω, hwω t ht.1]
    congr 2
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs0 : 0 ≤ s := by
      rw [uIcc_of_le ht.1] at hs
      exact hs.1
    simp only [hY'ω s hs0, hlaw s hs0]

/-! ### Mean square convergence -/

/-- **Lemma 7.2, McKean–Vlasov equation** (mean square convergence at a fixed time). Let `Y`
solve the McKean–Vlasov equation with coefficients `a, K` satisfying Assumption A and square
integrable initial value. Let `aⁿ, Kⁿ` satisfy Assumption A with the same constants, with
`aⁿ → a` locally uniformly, `‖Kⁿ - K‖ ≤ (L₁ + L₂) / (n + 1)` and
`‖aⁿ x‖ ≤ ‖a 0‖ + L_a (‖x‖ + 1)`. Let `ζ` be a version of `Y(0)`, let `w` be a regular forcing
almost surely equal to `√2 B` at nonnegative times, and let `Yⁿ` have measurable sections and
continuous paths and solve, for every `ω`, the McKean–Vlasov integral equation with coefficients
`aⁿ, Kⁿ`, laws `Law(Yⁿ(s))`, initial value `ζ` and forcing `w`. Then for every `T ≥ 0`,
`E ‖Yⁿ(T) - Y(T)‖² → 0`. -/
theorem tendsto_integral_norm_sub_sq_of_isForcedSolution [IsProbabilityMeasure P]
    (hA : SharpChaos.AssumptionA a K La L₁ L₂ M)
    (hY : SharpChaos.IsMcKeanVlasovSolution a K Y B P) (hY0 : MemLp (Y 0) 2 P)
    {aₙ : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {Kₙ : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hAₙ : ∀ n, SharpChaos.AssumptionA (aₙ n) (Kₙ n) La L₁ L₂ M)
    (haₙ : TendstoLocallyUniformly aₙ a atTop)
    (hKₙ : ∀ n x y, ‖Kₙ n x y - K x y‖ ≤ (L₁ + L₂) / (n + 1))
    (haₙ_le : ∀ n x, ‖aₙ n x‖ ≤ ‖a 0‖ + La * (‖x‖ + 1))
    {ζ : Ω → EuclideanSpace ℝ (Fin d)} (hζ : ζ =ᵐ[P] Y 0)
    {w : ℝ → Ω → EuclideanSpace ℝ (Fin d)} {C : ℝ} (hw : IsRegularForcing w C P)
    (hwB : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → w t ω = Real.sqrt 2 • B t.toNNReal ω)
    {Yₙ : ℕ → ℝ → Ω → EuclideanSpace ℝ (Fin d)} (hYₙm : ∀ n t, Measurable (Yₙ n t))
    (hYₙc : ∀ n ω, Continuous fun t => Yₙ n t ω)
    (hYₙ : ∀ n ω T, IsForcedSolution
      (fun s x => SharpChaos.mcKeanVlasovDrift (aₙ n) (Kₙ n) (P.map (Yₙ n s)) x)
      (fun t => w t ω) (ζ ω) T fun t => Yₙ n t ω)
    {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun n => ∫ ω, ‖Yₙ n T ω - Y T ω‖ ^ 2 ∂P) atTop (𝓝 0) := by
  have hLa := hA.La_nonneg
  have hL₁ := hA.L₁_nonneg
  have hL₂ := hA.L₂_nonneg
  have hL : 0 ≤ La + L₁ := add_nonneg hLa hL₁
  have hTT : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  set β := ‖a 0‖ + La + M with hβ
  set c : ℕ → ℝ := fun n => (L₁ + L₂) / ((n : ℝ) + 1) with hc_def
  have hc0 : ∀ n, 0 ≤ c n := fun n => div_nonneg (add_nonneg hL₁ hL₂) (by positivity)
  -- A version of `Y` with continuous paths and measurable sections.
  obtain ⟨Y', hY'm, hY'c, hY'Y⟩ := hY.exists_continuous_version
  have hsol := hY.ae_isForcedSolution_version hA hζ hwB hw.continuous hY'm hY'c hY'Y
  have hred : ∀ n, ∫ ω, ‖Yₙ n T ω - Y T ω‖ ^ 2 ∂P = ∫ ω, ‖Yₙ n T ω - Y' T ω‖ ^ 2 ∂P := fun n =>
    integral_congr_ae (hY'Y.mono fun ω h => by simp only [h T hT])
  simp_rw [hred]
  -- Growth of the drifts and the a priori bound.
  have hgrowth : ∀ s x, ‖SharpChaos.mcKeanVlasovDrift a K (P.map (Y' s)) x‖ ≤ β + La * ‖x‖ :=
    fun s x => (norm_mcKeanVlasovDrift_le hA.norm_K_le _ x).trans
      (by linarith [norm_le_of_assumptionA hA x])
  have hgrowthₙ : ∀ n s x,
      ‖SharpChaos.mcKeanVlasovDrift (aₙ n) (Kₙ n) (P.map (Yₙ n s)) x‖ ≤ β + La * ‖x‖ :=
    fun n s x => (norm_mcKeanVlasovDrift_le (hAₙ n).norm_K_le _ x).trans
      (by linarith [(haₙ_le n x).trans_eq (by ring : _ = ‖a 0‖ + La + La * ‖x‖)])
  set G : Ω → ℝ := fun ω => 6 * exp (2 * La * T) *
    (‖ζ ω‖ ^ 2 + β ^ 2 * T ^ 2 + La ^ 2 * T * ∫ s in (0 : ℝ)..T, ‖w s ω‖ ^ 2) with hG
  have hGi : Integrable G P :=
    ((((hY0.ae_eq hζ.symm).integrable_norm_pow two_ne_zero).add (integrable_const _)).add
      ((hw.integrable_intervalIntegral_norm_sq hT).const_mul _)).const_mul _
  have hY'b : ∀ᵐ ω ∂P, ∀ s ∈ Icc 0 T, ‖Y' s ω‖ ^ 2 ≤ G ω + 2 * ‖w s ω‖ ^ 2 := by
    filter_upwards [hsol] with ω hω s hs
    exact (hω T).norm_sq_le_horizon hLa (fun r _ x => hgrowth r x) hs
  have hYₙb : ∀ n ω, ∀ s ∈ Icc 0 T, ‖Yₙ n s ω‖ ^ 2 ≤ G ω + 2 * ‖w s ω‖ ^ 2 :=
    fun n ω s hs => (hYₙ n ω T).norm_sq_le_horizon hLa (fun r _ x => hgrowthₙ n r x) hs
  have hDb : ∀ n, ∀ᵐ ω ∂P, ∀ s ∈ Icc 0 T,
      ‖Yₙ n s ω - Y' s ω‖ ^ 2 ≤ 4 * G ω + 8 * ‖w s ω‖ ^ 2 := fun n => by
    filter_upwards [hY'b] with ω hω s hs
    linarith [norm_sub_sq_le_two_mul (Yₙ n s ω) (Y' s ω), hω s hs, hYₙb n ω s hs]
  -- The mean distance `m n s = E ‖Yⁿ(s) - Ỹ(s)‖`.
  have hDm : ∀ n s, Measurable fun ω => ‖Yₙ n s ω - Y' s ω‖ := fun n s =>
    ((hYₙm n s).sub (hY'm s)).norm
  have hbi : ∀ s, 0 ≤ s → Integrable (fun ω => 1 + 4 * G ω + 8 * ‖w s ω‖ ^ 2) P := fun s hs =>
    ((integrable_const 1).add (hGi.const_mul 4)).add ((hw.integrable_norm_sq s hs).const_mul 8)
  have hDle : ∀ n, ∀ᵐ ω ∂P, ∀ s ∈ Icc 0 T,
      ‖Yₙ n s ω - Y' s ω‖ ≤ 1 + 4 * G ω + 8 * ‖w s ω‖ ^ 2 := fun n => by
    filter_upwards [hDb n] with ω hω s hs
    nlinarith [hω s hs, sq_nonneg (‖Yₙ n s ω - Y' s ω‖ - 1)]
  have hDi : ∀ n, ∀ s ∈ Icc 0 T, Integrable (fun ω => ‖Yₙ n s ω - Y' s ω‖) P := fun n s hs =>
    (hbi s hs.1).mono' (hDm n s).aestronglyMeasurable ((hDle n).mono fun ω h => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact h s hs)
  set m : ℕ → ℝ → ℝ := fun n s => ∫ ω, ‖Yₙ n s ω - Y' s ω‖ ∂P with hm_def
  set Mb : ℝ := 1 + 4 * ∫ ω, G ω ∂P + 8 * (|C| * T) with hMb
  have hm0 : ∀ n s, 0 ≤ m n s := fun n s => integral_nonneg fun ω => norm_nonneg _
  have hm_le : ∀ n, ∀ s ∈ Icc 0 T, m n s ≤ Mb := fun n s hs => by
    calc m n s ≤ ∫ ω, (1 + 4 * G ω + 8 * ‖w s ω‖ ^ 2) ∂P :=
          integral_mono_ae (hDi n s hs) (hbi s hs.1) ((hDle n).mono fun ω h => h s hs)
      _ = 1 + 4 * ∫ ω, G ω ∂P + 8 * ∫ ω, ‖w s ω‖ ^ 2 ∂P := by
          have hi1 : Integrable (fun ω => (1 : ℝ) + 4 * G ω) P :=
            (integrable_const 1).add (hGi.const_mul 4)
          rw [integral_add hi1 ((hw.integrable_norm_sq s hs.1).const_mul 8),
            integral_add (integrable_const 1) (hGi.const_mul 4)]
          simp [integral_const_mul]
      _ ≤ Mb := by
          have h1 := hw.integral_norm_sq_le s hs.1
          have h2 : C * s ≤ |C| * T :=
            (mul_le_mul_of_nonneg_right (le_abs_self C) hs.1).trans
              (mul_le_mul_of_nonneg_left hs.2 (abs_nonneg C))
          linarith
  have hm_meas : ∀ n, StronglyMeasurable (m n) := fun n =>
    (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (fun ω => ((hYₙc n ω).sub (hY'c ω)).norm)
      (fun s => (hDm n s).stronglyMeasurable)).integral_prod_right
  have hmII : ∀ n, IntervalIntegrable (m n) volume 0 T := fun n => by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    refine Integrable.of_bound (hm_meas n).aestronglyMeasurable Mb
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hm0 n s)]
    exact hm_le n s ⟨hs.1.le, hs.2⟩
  -- The error term `A n ω = ∫₀ᵀ ‖aⁿ(Ỹ(r)) - a(Ỹ(r))‖ dr` and its expectation.
  have hac : Continuous a := continuous_of_assumptionA hA
  have haₙc : ∀ n, Continuous (aₙ n) := fun n => continuous_of_assumptionA (hAₙ n)
  set A : ℕ → Ω → ℝ := fun n ω => ∫ r in (0 : ℝ)..T, ‖aₙ n (Y' r ω) - a (Y' r ω)‖ with hA_def
  have hAc : ∀ n ω, Continuous fun r => ‖aₙ n (Y' r ω) - a (Y' r ω)‖ := fun n ω =>
    (((haₙc n).comp (hY'c ω)).sub (hac.comp (hY'c ω))).norm
  have hA0 : ∀ n ω, 0 ≤ A n ω := fun n ω =>
    intervalIntegral.integral_nonneg hT fun r _ => norm_nonneg _
  have hA_meas : ∀ n, StronglyMeasurable (A n) := fun n =>
    stronglyMeasurable_intervalIntegral_of_continuous (hAc n)
      (fun r => (((haₙc n).measurable.comp (hY'm r)).sub (hac.measurable.comp (hY'm r))).norm) T
  set H : Ω → ℝ := fun ω => (2 * ‖a 0‖ + 3 * La) * T + 2 * La * T * G ω +
    4 * La * ∫ r in (0 : ℝ)..T, ‖w r ω‖ ^ 2 with hH
  have hHi : Integrable H P :=
    ((integrable_const _).add (hGi.const_mul _)).add
      ((hw.integrable_intervalIntegral_norm_sq hT).const_mul _)
  have hA_dom : ∀ n, ∀ᵐ ω ∂P, ‖A n ω‖ ≤ H ω := fun n => by
    filter_upwards [hY'b] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hA0 n ω)]
    have hwc : Continuous fun r => ‖w r ω‖ ^ 2 := (hw.continuous ω).norm.pow 2
    have hpt : ∀ r ∈ Icc 0 T, ‖aₙ n (Y' r ω) - a (Y' r ω)‖ ≤
        (2 * ‖a 0‖ + 3 * La + 2 * La * G ω) + 4 * La * ‖w r ω‖ ^ 2 := fun r hr => by
      have h1 := (haₙ_le n (Y' r ω)).trans_eq (by ring : _ = ‖a 0‖ + La + La * ‖Y' r ω‖)
      have h2 := norm_le_of_assumptionA hA (Y' r ω)
      have h3 : ‖Y' r ω‖ ≤ 1 + G ω + 2 * ‖w r ω‖ ^ 2 := by
        nlinarith [hω r hr, sq_nonneg (‖Y' r ω‖ - 1)]
      have h4 := mul_le_mul_of_nonneg_left h3 hLa
      have h5 := norm_sub_le (aₙ n (Y' r ω)) (a (Y' r ω))
      nlinarith
    calc A n ω ≤ ∫ r in (0 : ℝ)..T, ((2 * ‖a 0‖ + 3 * La + 2 * La * G ω) +
          4 * La * ‖w r ω‖ ^ 2) :=
          intervalIntegral.integral_mono_on hT ((hAc n ω).intervalIntegrable _ _)
            (intervalIntegrable_const.add ((hwc.intervalIntegrable _ _).const_mul _)) hpt
      _ = H ω := by
          rw [intervalIntegral.integral_add intervalIntegrable_const
            ((hwc.intervalIntegrable _ _).const_mul _), intervalIntegral.integral_const,
            intervalIntegral.integral_const_mul, smul_eq_mul, sub_zero]
          simp only [hH]
          ring
  have hA_lim : ∀ ω, Tendsto (fun n => A n ω) atTop (𝓝 0) := fun ω =>
    tendsto_intervalIntegral_of_eventually_norm_le hT fun ε hε =>
      (eventually_forall_norm_sub_comp_lt haₙ (hY'c ω).continuousOn hε).mono fun n hn s hs => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact (hn s hs).le
  have hEA : Tendsto (fun n => ∫ ω, A n ω ∂P) atTop (𝓝 0) := by
    simpa using tendsto_integral_of_dominated_convergence H
      (fun n => (hA_meas n).aestronglyMeasurable) hHi hA_dom (ae_of_all _ hA_lim)
  have hAi : ∀ n, Integrable (A n) P := fun n =>
    hHi.mono' (hA_meas n).aestronglyMeasurable (hA_dom n)
  -- The pathwise estimate.
  have hpath : ∀ n, ∀ᵐ ω ∂P, ∀ s ∈ Icc 0 T, ‖Yₙ n s ω - Y' s ω‖ ≤
      (A n ω + L₂ * (∫ r in (0 : ℝ)..s, m n r) + c n * T) * exp ((La + L₁) * T) := fun n => by
    filter_upwards [hsol] with ω hω s hs
    have hai : IntervalIntegrable (fun r => ‖aₙ n (Y' r ω) - a (Y' r ω)‖) volume 0 T :=
      (hAc n ω).intervalIntegrable _ _
    have hδi : IntervalIntegrable (fun r => ‖aₙ n (Y' r ω) - a (Y' r ω)‖ + L₂ * m n r + c n)
        volume 0 T := (hai.add ((hmII n).const_mul L₂)).add intervalIntegrable_const
    have h1 := (hYₙ n ω T).norm_sub_le_of_le (hω T) hL
      (fun r _ p q => norm_mcKeanVlasovDrift_sub_le (hAₙ n) _ p q) hδi
      (fun r hr => norm_mcKeanVlasovDrift_map_sub_le (hAₙ n) hA (hKₙ n)
        (hYₙm n r).aemeasurable (hY'm r).aemeasurable (hDi n r hr) _) hs
    rw [sub_self, norm_zero, zero_add] at h1
    have hsub : uIcc 0 s ⊆ uIcc 0 T := uIcc_subset_uIcc_left (by rw [uIcc_of_le hT]; exact hs)
    have hms : IntervalIntegrable (m n) volume 0 s := (hmII n).mono_set hsub
    have hais : IntervalIntegrable (fun r => ‖aₙ n (Y' r ω) - a (Y' r ω)‖) volume 0 s :=
      hai.mono_set hsub
    have hδs : ∫ r in (0 : ℝ)..s, (‖aₙ n (Y' r ω) - a (Y' r ω)‖ + L₂ * m n r + c n) =
        (∫ r in (0 : ℝ)..s, ‖aₙ n (Y' r ω) - a (Y' r ω)‖) + L₂ * (∫ r in (0 : ℝ)..s, m n r) +
          c n * s := by
      rw [intervalIntegral.integral_add (hais.add (hms.const_mul L₂)) intervalIntegrable_const,
        intervalIntegral.integral_add hais (hms.const_mul L₂),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
        sub_zero, mul_comm s]
    have hAs : ∫ r in (0 : ℝ)..s, ‖aₙ n (Y' r ω) - a (Y' r ω)‖ ≤ A n ω :=
      integral_le_integral_of_nonneg hai (fun r _ => norm_nonneg _) hs.1 hs.2 le_rfl
    have hms0 : 0 ≤ ∫ r in (0 : ℝ)..s, m n r :=
      intervalIntegral.integral_nonneg hs.1 fun r _ => hm0 n r
    have hE : exp ((La + L₁) * s) ≤ exp ((La + L₁) * T) :=
      exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2 hL)
    refine h1.trans ?_
    rw [hδs]
    refine mul_le_mul ?_ hE (exp_pos _).le
      (add_nonneg (add_nonneg (hA0 n ω) (mul_nonneg hL₂ hms0)) (mul_nonneg (hc0 n) hT))
    have := mul_le_mul_of_nonneg_left hs.2 (hc0 n)
    linarith
  -- Grönwall's inequality in expectation.
  set κ : ℕ → ℝ := fun n => exp ((La + L₁) * T) * (∫ ω, A n ω ∂P + c n * T) *
    exp (exp ((La + L₁) * T) * L₂ * T) with hκ_def
  have hmκ : ∀ n, ∀ s ∈ Icc 0 T, m n s ≤ κ n := fun n s hs => by
    have hK0 : 0 ≤ exp ((La + L₁) * T) * L₂ := mul_nonneg (exp_pos _).le hL₂
    have hc' : 0 ≤ exp ((La + L₁) * T) * (∫ ω, A n ω ∂P + c n * T) :=
      mul_nonneg (exp_pos _).le (add_nonneg (integral_nonneg (hA0 n)) (mul_nonneg (hc0 n) hT))
    have hrec : ∀ s' ∈ Icc 0 T, m n s' ≤ exp ((La + L₁) * T) * (∫ ω, A n ω ∂P + c n * T) +
        exp ((La + L₁) * T) * L₂ * ∫ r in (0 : ℝ)..s', m n r := fun s' hs' => by
      have hi : Integrable (fun ω => (A n ω + L₂ * (∫ r in (0 : ℝ)..s', m n r) + c n * T) *
          exp ((La + L₁) * T)) P :=
        (((hAi n).add (integrable_const _)).add (integrable_const _)).mul_const _
      calc m n s' ≤ ∫ ω, (A n ω + L₂ * (∫ r in (0 : ℝ)..s', m n r) + c n * T) *
            exp ((La + L₁) * T) ∂P :=
            integral_mono_ae (hDi n s' hs') hi ((hpath n).mono fun ω h => h s' hs')
        _ = _ := by
            have hi1 : Integrable (fun ω => A n ω + L₂ * ∫ r in (0 : ℝ)..s', m n r) P :=
              (hAi n).add (integrable_const _)
            rw [integral_mul_const, integral_add hi1 (integrable_const _),
              integral_add (hAi n) (integrable_const _)]
            simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
            ring
    calc m n s ≤ exp ((La + L₁) * T) * (∫ ω, A n ω ∂P + c n * T) *
          exp (exp ((La + L₁) * T) * L₂ * s) :=
          le_mul_exp_of_le_add_mul_integral hK0 (hmII n) hrec hs
      _ ≤ κ n := mul_le_mul_of_nonneg_left
          (exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2 hK0)) hc'
  have hκ : Tendsto κ atTop (𝓝 0) := by
    have h := ((hEA.add ((tendsto_div_natCast_add_one (L₁ + L₂)).mul_const T)).const_mul
      (exp ((La + L₁) * T))).mul_const (exp (exp ((La + L₁) * T) * L₂ * T))
    simpa [hκ_def, hc_def] using h
  -- Almost sure convergence and dominated convergence.
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => ‖Yₙ n T ω - Y' T ω‖ ^ 2) atTop (𝓝 0) := by
    filter_upwards [ae_all_iff.2 hpath] with ω hω
    have hb : ∀ n, ‖Yₙ n T ω - Y' T ω‖ ≤
        (A n ω + L₂ * (κ n * T) + c n * T) * exp ((La + L₁) * T) := fun n => by
      refine (hω n T hTT).trans (mul_le_mul_of_nonneg_right ?_ (exp_pos _).le)
      have hI : ∫ r in (0 : ℝ)..T, m n r ≤ κ n * T := by
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T)
          (C := κ n) (f := m n) fun r hr => by
            rw [uIoc_of_le hT] at hr
            rw [Real.norm_eq_abs, abs_of_nonneg (hm0 n r)]
            exact hmκ n r ⟨hr.1.le, hr.2⟩
        rw [sub_zero, abs_of_nonneg hT, Real.norm_eq_abs] at this
        exact (le_abs_self _).trans this
      linarith [mul_le_mul_of_nonneg_left hI hL₂]
    have hlim' : Tendsto (fun n => (A n ω + L₂ * (κ n * T) + c n * T) *
        exp ((La + L₁) * T)) atTop (𝓝 0) := by
      have h := (((hA_lim ω).add ((hκ.mul_const T).const_mul L₂)).add
        ((tendsto_div_natCast_add_one (L₁ + L₂)).mul_const T)).mul_const (exp ((La + L₁) * T))
      simpa [hc_def] using h
    refine squeeze_zero (fun n => sq_nonneg _)
      (fun n => pow_le_pow_left₀ (norm_nonneg _) (hb n) 2) ?_
    simpa using hlim'.pow 2
  have hmeas : ∀ n, AEStronglyMeasurable (fun ω => ‖Yₙ n T ω - Y' T ω‖ ^ 2) P := fun n =>
    ((hDm n T).pow_const 2).aestronglyMeasurable
  have hbd : ∀ n, ∀ᵐ ω ∂P, ‖‖Yₙ n T ω - Y' T ω‖ ^ 2‖ ≤ 4 * G ω + 8 * ‖w T ω‖ ^ 2 := fun n => by
    filter_upwards [hDb n] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hω T hTT
  simpa using tendsto_integral_of_dominated_convergence (fun ω => 4 * G ω + 8 * ‖w T ω‖ ^ 2)
    hmeas ((hGi.const_mul 4).add ((hw.integrable_norm_sq T hT).const_mul 8)) hbd hlim

/-- **Lemma 7.2, McKean–Vlasov equation.** Let `Y` solve the McKean–Vlasov equation with
coefficients `a, K` satisfying Assumption A, driven by `B`, with square integrable initial value,
and let `aⁿ, Kⁿ` be as in Lemma 7.1 (`exists_smooth_approx`; only boundedness of `aⁿ`,
Assumption A with the same constants, `aⁿ → a` locally uniformly,
`‖Kⁿ - K‖ ≤ (L₁ + L₂) / (n + 1)` and `‖aⁿ x‖ ≤ ‖a 0‖ + L_a (‖x‖ + 1)` are used). Then there are

* a measurable version `ζ` of `Y(0)`,
* a regular forcing `w` (`IsRegularForcing`, with `E ‖w t‖² ≤ 2 d t`) almost surely equal to
  `t ↦ √2 B(t⁺)` at all times, and
* processes `Yⁿ` with measurable sections and continuous paths solving, for every `ω`, `n` and
  `t ≥ 0`, `Yⁿ(t) = ζ + ∫₀ᵗ (aⁿ(Yⁿ(s)) + ∫ Kⁿ(Yⁿ(s), y) Law(Yⁿ(s))(dy)) ds + w(t)` (also in the
  form of `IsForcedSolution`),

such that `Yⁿ(0) = Y(0)` almost surely and `E ‖Yⁿ(t) - Y(t)‖² → 0` for every `t ≥ 0`. -/
theorem exists_approx_mcKeanVlasov [IsProbabilityMeasure P]
    (hA : SharpChaos.AssumptionA a K La L₁ L₂ M)
    (hY : SharpChaos.IsMcKeanVlasovSolution a K Y B P) (hY0 : MemLp (Y 0) 2 P)
    {aₙ : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {Kₙ : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hAₙ : ∀ n, SharpChaos.AssumptionA (aₙ n) (Kₙ n) La L₁ L₂ M)
    (haₙ_bdd : ∀ n, ∃ C, ∀ x, ‖aₙ n x‖ ≤ C) (haₙ : TendstoLocallyUniformly aₙ a atTop)
    (hKₙ : ∀ n x y, ‖Kₙ n x y - K x y‖ ≤ (L₁ + L₂) / (n + 1))
    (haₙ_le : ∀ n x, ‖aₙ n x‖ ≤ ‖a 0‖ + La * (‖x‖ + 1)) :
    ∃ (ζ : Ω → EuclideanSpace ℝ (Fin d)) (w : ℝ → Ω → EuclideanSpace ℝ (Fin d))
      (Yₙ : ℕ → ℝ → Ω → EuclideanSpace ℝ (Fin d)),
      Measurable ζ ∧ ζ =ᵐ[P] Y 0 ∧ IsRegularForcing w (2 * d) P ∧
      (∀ᵐ ω ∂P, ∀ t, w t ω = Real.sqrt 2 • B t.toNNReal ω) ∧
      (∀ n t, Measurable (Yₙ n t)) ∧ (∀ n ω, Continuous fun t => Yₙ n t ω) ∧
      (∀ n ω T, IsForcedSolution
        (fun s x => SharpChaos.mcKeanVlasovDrift (aₙ n) (Kₙ n) (P.map (Yₙ n s)) x)
        (fun t => w t ω) (ζ ω) T fun t => Yₙ n t ω) ∧
      (∀ n ω t, 0 ≤ t → Yₙ n t ω = ζ ω + (∫ s in (0 : ℝ)..t,
        SharpChaos.mcKeanVlasovDrift (aₙ n) (Kₙ n) (P.map (Yₙ n s)) (Yₙ n s ω)) + w t ω) ∧
      (∀ n, Yₙ n 0 =ᵐ[P] Y 0) ∧
      ∀ t, 0 ≤ t → Tendsto (fun n => ∫ ω, ‖Yₙ n t ω - Y t ω‖ ^ 2 ∂P) atTop (𝓝 0) := by
  obtain ⟨ζ, w, hζm, hζ, hw, hwB⟩ := hY.exists_versions
  have hex : ∀ n, ∃ Z : ℝ → Ω → EuclideanSpace ℝ (Fin d), (∀ t, Measurable (Z t)) ∧
      (∀ ω, Continuous fun t => Z t ω) ∧ ∀ ω T, IsForcedSolution
        (fun s x => SharpChaos.mcKeanVlasovDrift (aₙ n) (Kₙ n) (P.map (Z s)) x)
        (fun t => w t ω) (ζ ω) T fun t => Z t ω := fun n => by
    obtain ⟨C, hC⟩ := haₙ_bdd n
    exact McKeanVlasov.exists_isForcedSolution P hζm hw.continuous hw.measurable hC
      (hAₙ n).lipschitz_a (hAₙ n).La_nonneg (hAₙ n).norm_K_le (hAₙ n).lipschitz_K
      (hAₙ n).L₁_nonneg (hAₙ n).L₂_nonneg
  choose Yₙ hYₙm hYₙc hYₙ using hex
  have hwB' : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → w t ω = Real.sqrt 2 • B t.toNNReal ω :=
    hwB.mono fun ω h t _ => h t
  refine ⟨ζ, w, Yₙ, hζm, hζ, hw, hwB, hYₙm, hYₙc, hYₙ,
    fun n ω t ht => (hYₙ n ω t).eq_add_integral t ⟨ht, le_rfl⟩, fun n => ?_,
    fun t ht => tendsto_integral_norm_sub_sq_of_isForcedSolution hA hY hY0 hAₙ haₙ hKₙ haₙ_le
      hζ hw hwB' hYₙm hYₙc hYₙ ht⟩
  filter_upwards [hY.ae_forcing_zero, hwB, hζ] with ω hω0 hwω hζω
  rw [(hYₙ n ω 0).eq_add_integral 0 ⟨le_rfl, le_rfl⟩, intervalIntegral.integral_same, add_zero,
    hwω 0, hω0, add_zero, hζω]

end SharpWasserstein.Sharp
