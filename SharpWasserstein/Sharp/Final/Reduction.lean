/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.SmoothSharpCase
public import SharpWasserstein.Sharp.Transfer.Public
public import SharpWasserstein.Sharp.Final.SmoothApprox
public import SharpWasserstein.Sharp.Final.ApproxSolutions
public import SharpWasserstein.Sharp.Final.Couplings

/-!
# Reduction of Theorem 2.1 to smooth coefficients

This file proves Theorem 2.1 of the paper (`SharpChaos.sharp_propagation_of_chaos`, for general
Lipschitz coefficients and strong solutions of the SDEs) from its smooth case
`SharpWasserstein.Sharp.SmoothSharpCase`, following the second paragraph of Section 3.4
(`sec:proof-main`).

Fix `t ∈ [0, T]` and `1 ≤ k ≤ N`.

* **Smooth approximation.** Lemma 7.1 (`exists_smooth_approx`) gives smooth bounded coefficients
  `aⁿ, Kⁿ` with bounded derivatives, satisfying Assumption A with the **same** constants
  `L_a, L₁, L₂, M`; their coordinate forms satisfy `IsSmoothCoefficients`
  (`isSmoothCoefficients_coordMap`).
* **Approximating solutions.** Lemma 7.2 (`exists_approx_particle`, `exists_approx_mcKeanVlasov`)
  gives processes `Xⁿ`, `Yⁿ` on the probability spaces of `X`, `Y`, which are strong solutions
  with coefficients `aⁿ, Kⁿ` driven by the same Brownian motions (`isParticleSolution_of_forced`,
  `isMcKeanVlasovSolution_of_forced`), with `Xⁿ(0) = X(0)` and `Yⁿ(0) = Y(0)` almost surely, and
  `E ∑ᵢ ‖Xⁿᵢ(t) - Xᵢ(t)‖² → 0`, `E ‖Yⁿ(t) - Y(t)‖² → 0`.
* **Smooth case.** The initial laws are unchanged, so the initial hierarchy holds for the
  approximations, and the smooth case (applied to the weak evolutions given by
  `Transfer.isParticleEvolution_of_isParticleSolution` and
  `Transfer.isLimitEvolution_of_isMcKeanVlasovSolution`) gives
  `W₂²(Pⁿ^{(k)}_t, (μⁿ_t)^{⊗k}) ≤ C_T k² / N²` for every `n`, with `C_T` independent of `n`.
* **Passage to the limit.** By the triangle inequality, `√W₂²(P^{(k)}_t, μ_t^{⊗k})` is at most
  `√W₂²(P^{(k)}_t, Pⁿ^{(k)}_t) + √C_T k / N + √W₂²((μⁿ_t)^{⊗k}, μ_t^{⊗k})`.
  The synchronous coupling bounds the first term by `E ∑ᵢ ‖Xⁿᵢ(t) - Xᵢ(t)‖² → 0`, and the product
  coupling bounds the last one by `k E ‖Yⁿ(t) - Y(t)‖² → 0` (`wassersteinSq_le_of_tendsto`).

All Wasserstein distances are moved to coordinates with the measurable equivalences
`configurationEquiv` and `positionEquiv` (`wassersteinSq_eq_map`,
`marginal_map_configurationEquiv`, `pi_map_configurationEquiv`).

## Main statement

* `sharp_propagation_of_chaos_of_smoothSharpCase`: Theorem 2.1, with the hypotheses and the
  conclusion of `SharpChaos.sharp_propagation_of_chaos`, assuming `SmoothSharpCase`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace SharpWasserstein.Sharp.Final

/-- The public squared Wasserstein distance between a `k`-particle marginal and a tensor power,
in coordinates. -/
theorem wassersteinSq_marginal_pi_eq {d N k : ℕ} (hk : k ≤ N)
    (U : Measure (Fin N → EuclideanSpace ℝ (Fin d))) (V : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure V] :
    SharpChaos.wassersteinSq (SharpChaos.marginal hk U) (Measure.pi fun _ : Fin k => V) =
      wassersteinSq (marginal hk (U.map (configurationEquiv d N)))
        (tensorLaw (V.map (positionEquiv d)) k) := by
  rw [wassersteinSq_eq_map, marginal_map_configurationEquiv, pi_map_configurationEquiv]

/-- **Theorem 2.1 from its smooth case** (Section 3.4 of the paper, second paragraph). Assuming
the smooth case `SmoothSharpCase`, Theorem 2.1 holds for general coefficients satisfying
Assumption A and strong solutions of the SDEs: under the hypotheses of
`SharpChaos.sharp_propagation_of_chaos`, for every `T > 0`, all `0 ≤ t ≤ T` and `1 ≤ k ≤ N`,
`W₂²(P^{(k)}_{N,t}, μ_t^{⊗k}) ≤ C_T k² / N²` with `C_T = sharpConstant C₀ T L_a L₁ L₂ M`. -/
theorem sharp_propagation_of_chaos_of_smoothSharpCase (hsmooth : SmoothSharpCase) {d N : ℕ}
    (hN : 1 ≤ N)
    {a : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {La L₁ L₂ M : ℝ} (hA : SharpChaos.AssumptionA a K La L₁ L₂ M)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ → Ω → Fin N → EuclideanSpace ℝ (Fin d)}
    {W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : SharpChaos.IsParticleSolution a K X W P)
    (hX₀ : MemLp (X 0) 2 P) (hexch : SharpChaos.Exchangeable (P.map (X 0)))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : ℝ → Ω' → EuclideanSpace ℝ (Fin d)} {B : ℝ≥0 → Ω' → EuclideanSpace ℝ (Fin d)}
    (hY : SharpChaos.IsMcKeanVlasovSolution a K Y B P') (hY₀ : MemLp (Y 0) 2 P')
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hinit : ∀ k (hk : k ≤ N), 1 ≤ k →
      SharpChaos.wassersteinSq (SharpChaos.marginal hk (P.map (X 0)))
          (Measure.pi fun _ : Fin k => P'.map (Y 0)) ≤
        ENNReal.ofReal (C₀ * k ^ 2 / N ^ 2))
    {T : ℝ} (hT : 0 < T) :
    ∀ t ∈ Icc 0 T, ∀ k (hk : k ≤ N), 1 ≤ k →
      SharpChaos.wassersteinSq (SharpChaos.marginal hk (P.map (X t)))
          (Measure.pi fun _ : Fin k => P'.map (Y t)) ≤
        ENNReal.ofReal (SharpChaos.sharpConstant C₀ T La L₁ L₂ M * k ^ 2 / N ^ 2) := by
  intro t ht k hk hk1
  -- Smooth approximation of the coefficients (Lemma 7.1).
  obtain ⟨aₙ, Kₙ, hAₙ, hca, hcK, hab, hda, hdK, haₙ, hKₙ, haₙ_le⟩ := exists_smooth_approx hA
  have hS : ∀ n, IsSmoothCoefficients (coordMap (aₙ n)) (coordMap₂ (Kₙ n)) La L₁ L₂ M :=
    fun n => isSmoothCoefficients_coordMap (hAₙ n) (hca n) (hcK n) (hab n) (hda n) (hdK n)
  -- The approximating solutions (Lemma 7.2).
  obtain ⟨ξ, w, Xₙ, -, hξ, hw, hwW, hXₙm, hXₙc, hXₙF, hXₙeq, hXₙ0, hXlim⟩ :=
    exists_approx_particle hA hX hX₀ hAₙ hab haₙ hKₙ haₙ_le
  obtain ⟨ζ, w', Yₙ, -, hζ, hw', hwB, hYₙm, hYₙc, hYₙF, hYₙeq, hYₙ0, hYlim⟩ :=
    exists_approx_mcKeanVlasov hA hY hY₀ hAₙ hab haₙ hKₙ haₙ_le
  have hXsol : ∀ n, SharpChaos.IsParticleSolution (aₙ n) (Kₙ n) (Xₙ n) W P := fun n =>
    isParticleSolution_of_forced hX hwW (hXₙm n) (hXₙc n) (hXₙeq n) (hXₙ0 n)
  have hYsol : ∀ n, SharpChaos.IsMcKeanVlasovSolution (aₙ n) (Kₙ n) (Yₙ n) B P' := fun n =>
    isMcKeanVlasovSolution_of_forced hY hwB (hYₙm n) (hYₙc n) (hYₙeq n) (hYₙ0 n)
  have hlawX : ∀ n, P.map (Xₙ n 0) = P.map (X 0) := fun n => Measure.map_congr (hXₙ0 n)
  have hlawY : ∀ n, P'.map (Yₙ n 0) = P'.map (Y 0) := fun n => Measure.map_congr (hYₙ0 n)
  -- The laws of the approximating solutions are weak evolutions of the development.
  have hPev : ∀ n, IsParticleEvolution (kernelOf (coordMap (aₙ n)) (coordMap₂ (Kₙ n)))
      fun s => (P.map (Xₙ n s)).map (configurationEquiv d N) := fun n =>
    Transfer.isParticleEvolution_of_isParticleSolution (hS n) (hXsol n)
      (hX₀.ae_eq (hXₙ0 n).symm) (by rw [hlawX n]; exact hexch)
  have hμev : ∀ n, IsLimitEvolution (kernelOf (coordMap (aₙ n)) (coordMap₂ (Kₙ n)))
      fun s => (P'.map (Yₙ n s)).map (positionEquiv d) := fun n =>
    Transfer.isLimitEvolution_of_isMcKeanVlasovSolution (hS n) (hYsol n)
      (hY₀.ae_eq (hYₙ0 n).symm)
  -- The initial hierarchy for the approximating solutions: the initial laws are unchanged.
  have hinitₙ : ∀ n, ∀ k (hk : k ≤ N), 1 ≤ k →
      wassersteinSq (marginal hk ((P.map (Xₙ n 0)).map (configurationEquiv d N)))
          (tensorLaw ((P'.map (Yₙ n 0)).map (positionEquiv d)) k) ≤
        ENNReal.ofReal (C₀ * (k : ℝ) ^ 2 / (N : ℝ) ^ 2) := by
    intro n k hk hk1
    rw [hlawX n, hlawY n, ← wassersteinSq_marginal_pi_eq]
    exact hinit k hk hk1
  -- The smooth case, uniformly in `n`.
  have hsm : ∀ n, wassersteinSq (marginal hk ((P.map (Xₙ n t)).map (configurationEquiv d N)))
      (tensorLaw ((P'.map (Yₙ n t)).map (positionEquiv d)) k) ≤
        ENNReal.ofReal (sharpC C₀ T La L₁ L₂ M * (k : ℝ) ^ 2 / (N : ℝ) ^ 2) := fun n =>
    hsmooth (hS n) hN (hμev n) (hPev n) hC₀ (hinitₙ n) hT t ht k hk hk1
  -- Passage to the limit.
  rw [wassersteinSq_marginal_pi_eq, sharpConstant_eq_sharpC]
  refine wassersteinSq_le_of_tendsto (hXlim t ht.1)
    (by simpa using (hYlim t ht.1).const_mul (k : ℝ)) (fun n => ?_) hsm (fun n => ?_)
  · rw [wassersteinSq_symm]
    exact wassersteinSq_marginal_map_le hk (hXₙm n t).aemeasurable (hX.aemeasurable t ht.1)
      (integrable_sum_norm_sub_sq_of_isForcedSolution hA hX hX₀ (hAₙ n) (haₙ_le n) hξ hw hwW
        (hXₙm n) (hXₙF n) ht.1)
  · exact wassersteinSq_tensorLaw_map_le (hYₙm n t).aemeasurable (hY.aemeasurable t ht.1)
      (integrable_norm_sub_sq_of_isForcedSolution hA hY hY₀ (hAₙ n) (haₙ_le n) hζ hw' hwB
        (hYₙm n) (hYₙF n) ht.1) k

end SharpWasserstein.Sharp.Final
