/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.Transfer.NoiseLaw
public import SharpWasserstein.BrownianFlowWeak

/-!
# Law transfer for solutions with additive Brownian noise

Let `v : ℝ → Configuration d N → Configuration d N` be a jointly continuous, bounded drift which is
uniformly Lipschitz in space (the hypotheses of `BoundedFlow.flow`). Let `(Ω, P)` be a probability
space carrying independent standard Brownian motions `W i` in `ℝᵈ` and an initial value `ξ`
independent of them, and let `Z : ℝ → Ω → Configuration d N` almost surely have continuous paths
and solve
`Z t = ξ + ∫₀ᵗ v s (Z s) ds + √2 W(t)`.

By pathwise uniqueness (`BoundedFlow.flow_eq_of_trajectory`), almost surely
`Z t = BoundedFlow.flow … (ξ, noisePath W T) t`, and the joint law of `(ξ, noisePath W T)` is
`(P.map ξ).prod (BrownianNoise.configurationLaw d N T)` (`hasLaw_noisePath_prod`). Hence the law
of `Z t` is the development's constructed law `BrownianFlow.law … (P.map ξ) t`
(`map_eq_law`, `map_eq_globalLaw`), and `t ↦ P.map (Z t)` is a weak evolution of the
Fokker–Planck equation with drift `v` (`weakEvolution_map`).

No measurability of `Z t` is assumed: it follows from the almost sure identification. The
variant `hasLaw_restrictPath_prod` gives the joint law for any forcing with continuous paths which
is almost surely equal to `√2 W` on `[0, ∞)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Interval

namespace SharpWasserstein

/-- A weak evolution only depends on its laws at nonnegative times. -/
theorem WeakEvolution.congr_nonnegLaw {d N : ℕ} {v : ℝ → Configuration d N → Configuration d N}
    {P Q : ℝ → Measure (Configuration d N)} (h : WeakEvolution v P)
    (he : ∀ t, 0 ≤ t → P t = Q t) : WeakEvolution v Q where
  probability t ht := he t ht ▸ h.probability t ht
  secondMoment t ht := he t ht ▸ h.secondMoment t ht
  momentBound T hT := by
    obtain ⟨M, hM, hbound⟩ := h.momentBound T hT
    exact ⟨M, hM, fun t ht => he t ht.1 ▸ hbound t ht⟩
  testContinuous φ hφ := (h.testContinuous φ hφ).congr fun t ht => by
    simp only [he t ht]
  generatorIntegrable φ hφ t ht := he t ht ▸ h.generatorIntegrable φ hφ t ht
  timeIntegrable φ hφ t ht := by
    apply (intervalIntegrable_congr (f := fun s => ∫ x, generator (v s) φ x ∂P s) ?_).mp
      (h.timeIntegrable φ hφ t ht)
    intro s hs
    rw [uIoc_of_le ht] at hs
    simp only [he s hs.1.le]
  equation φ hφ t ht := by
    rw [← he t ht, ← he 0 le_rfl, h.equation φ hφ t ht]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    simp only [he s hs.1]

namespace Sharp.Transfer

variable {Ω : Type*} {d N : ℕ}

/-- The additive forcing `√2 W(t)` in coordinates, for `t ≥ 0` (with `W(t⁺)` at negative times). -/
def forcing (W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (t : ℝ) (ω : Ω) :
    Configuration d N :=
  fun i a => Real.sqrt 2 * W i t.toNNReal ω a

theorem noiseExtension_noisePath_eq_forcing {W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    {T : ℝ} (hT : 0 ≤ T) {ω : Ω}
    (hω : ∀ t : Icc 0 T, noisePath W T ω t =
      fun i a => Real.sqrt 2 * W i ⟨t, t.property.1⟩ ω a) {t : ℝ} (ht : t ∈ Icc 0 T) :
    BoundedFlow.noiseExtension hT (noisePath W T ω) t = forcing W t ω := by
  rw [BoundedFlow.noiseExtension, projIcc_of_mem _ ht, hω]
  show _ = fun i a => Real.sqrt 2 * W i t.toNNReal ω a
  rw [Real.toNNReal_of_nonneg ht.1]
  rfl

/-- The restriction to `[0, T]` of a forcing with continuous paths, as a continuous path. -/
def restrictPath {w : ℝ → Ω → Configuration d N} (hwc : ∀ ω, Continuous fun t => w t ω)
    (T : ℝ) (ω : Ω) : C(Icc 0 T, Configuration d N) :=
  ⟨fun t => w t ω, (hwc ω).comp continuous_subtype_val⟩

/-- **Joint law of the initial value and a continuous version of the noise.** If a forcing `w`
has continuous paths and almost surely equals `√2 W(t)` for all `t ≥ 0`, then the joint law of
`ξ` and the restriction of `w` to `[0, T]` is `(P.map ξ).prod (configurationLaw d N T)`. -/
theorem hasLaw_restrictPath_prod [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {E : Type*} [MeasurableSpace E] {ξ : Ω → E} (hξ : AEMeasurable ξ P)
    {W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : ∀ i, SharpChaos.IsStandardBrownian (W i) P)
    (hind : iIndepFun (fun (i : Fin N) (ω : Ω) (t : ℝ≥0) => W i t ω) P)
    (hξW : IndepFun ξ (fun (ω : Ω) (i : Fin N) (t : ℝ≥0) => W i t ω) P)
    {w : ℝ → Ω → Configuration d N} (hwc : ∀ ω, Continuous fun t => w t ω)
    (hw : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → w t ω = forcing W t ω) (T : ℝ) :
    HasLaw (fun ω => (ξ ω, restrictPath hwc T ω))
      ((P.map ξ).prod (BrownianNoise.configurationLaw d N T)) P := by
  refine (hasLaw_noisePath_prod hξ hW hind hξW T).congr ?_
  filter_upwards [hw, noisePath_ae_eq hW T] with ω hω hn
  refine Prod.ext rfl (ContinuousMap.ext fun t => ?_)
  change w t ω = noisePath W T ω t
  rw [hω t t.property.1, hn t]
  show (fun i a => Real.sqrt 2 * W i (t : ℝ).toNNReal ω a) = _
  rw [Real.toNNReal_of_nonneg t.property.1]
  rfl

variable {v : ℝ → Configuration d N → Configuration d N} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
  (hl : ∀ t, LipschitzWith K (v t))

include hv in
/-- A continuous solution of the integral equation with the noise path as forcing is a
trajectory in the sense of `FiniteAdditiveTrajectory`. -/
theorem finiteAdditiveTrajectory_of_solves {W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    {T : ℝ} (hT : 0 ≤ T) {ω : Ω} {x₀ : Configuration d N} {z : ℝ → Configuration d N}
    (hω : ∀ t : Icc 0 T, noisePath W T ω t =
      fun i a => Real.sqrt 2 * W i ⟨t, t.property.1⟩ ω a)
    (hcont : ContinuousOn z (Icc 0 T))
    (heq : ∀ t ∈ Icc 0 T, z t = x₀ + (∫ s in (0 : ℝ)..t, v s (z s)) + forcing W t ω) :
    FiniteAdditiveTrajectory v (BoundedFlow.noiseExtension hT (noisePath W T ω)) x₀ T z where
  continuous := hcont
  driftContinuous := hv.comp_continuousOn (continuousOn_id.prodMk hcont)
  equation t ht := by
    rw [noiseExtension_noisePath_eq_forcing hT hω ht]
    exact heq t ht

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : Ω → Configuration d N}
  {W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} {Z : ℝ → Ω → Configuration d N}

omit [IsProbabilityMeasure P] in
include hv in
/-- Pathwise uniqueness: almost surely, a solution coincides with the development's flow
evaluated at the initial value and the noise path. -/
theorem ae_eq_flow (hW : ∀ i, SharpChaos.IsStandardBrownian (W i) P) {T : ℝ} (hT : 0 ≤ T)
    (hsol : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, Z t ω = ξ ω + (∫ s in (0 : ℝ)..t, v s (Z s ω)) + forcing W t ω)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Z t =ᵐ[P] fun ω => BoundedFlow.flow hv hb hl hT (ξ ω) (noisePath W T ω) t := by
  filter_upwards [hsol, noisePath_ae_eq hW T] with ω hω hn
  exact (BoundedFlow.flow_eq_of_trajectory hv hb hl hT _ _
    (finiteAdditiveTrajectory_of_solves hv hT hn hω.1 hω.2) ht).symm

/-- **Law transfer on a finite horizon.** The law of a solution `Z t` driven by independent
Brownian motions `W` and an independent initial value `ξ` is the law constructed by the
development on its canonical Brownian space. -/
theorem map_eq_law (hξ : AEMeasurable ξ P) (hW : ∀ i, SharpChaos.IsStandardBrownian (W i) P)
    (hind : iIndepFun (fun (i : Fin N) (ω : Ω) (t : ℝ≥0) => W i t ω) P)
    (hξW : IndepFun ξ (fun (ω : Ω) (i : Fin N) (t : ℝ≥0) => W i t ω) P)
    {T : ℝ} (hT : 0 ≤ T)
    (hsol : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, Z t ω = ξ ω + (∫ s in (0 : ℝ)..t, v s (Z s ω)) + forcing W t ω)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    P.map (Z t) = BrownianFlow.law hv hb hl hT (P.map ξ) t := by
  have hlaw := hasLaw_noisePath_prod hξ hW hind hξW T
  rw [Measure.map_congr (ae_eq_flow hv hb hl hW hT hsol ht), BrownianFlow.law, ← hlaw.map_eq,
    AEMeasurable.map_map_of_aemeasurable
      (BoundedFlow.flow_continuous hv hb hl hT ht).measurable.aemeasurable hlaw.aemeasurable]
  rfl

/-- **Law transfer for all times.** -/
theorem map_eq_globalLaw (hξ : AEMeasurable ξ P)
    (hW : ∀ i, SharpChaos.IsStandardBrownian (W i) P)
    (hind : iIndepFun (fun (i : Fin N) (ω : Ω) (t : ℝ≥0) => W i t ω) P)
    (hξW : IndepFun ξ (fun (ω : Ω) (i : Fin N) (t : ℝ≥0) => W i t ω) P)
    (hsol : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Ici 0) ∧
      ∀ t, 0 ≤ t → Z t ω = ξ ω + (∫ s in (0 : ℝ)..t, v s (Z s ω)) + forcing W t ω)
    {t : ℝ} (ht : 0 ≤ t) :
    P.map (Z t) = BrownianFlow.globalLaw hv hb hl (P.map ξ) t := by
  refine map_eq_law hv hb hl hξ hW hind hξW (le_max_right t 0) ?_ ⟨ht, le_max_left t 0⟩
  filter_upwards [hsol] with ω hω
  exact ⟨hω.1.mono Icc_subset_Ici_self, fun s hs => hω.2 s hs.1⟩

include hv hb hl in
/-- The initial law of a solution is the law of `ξ`. -/
theorem map_zero_eq (hξ : AEMeasurable ξ P)
    (hW : ∀ i, SharpChaos.IsStandardBrownian (W i) P)
    (hind : iIndepFun (fun (i : Fin N) (ω : Ω) (t : ℝ≥0) => W i t ω) P)
    (hξW : IndepFun ξ (fun (ω : Ω) (i : Fin N) (t : ℝ≥0) => W i t ω) P)
    (hsol : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Ici 0) ∧
      ∀ t, 0 ≤ t → Z t ω = ξ ω + (∫ s in (0 : ℝ)..t, v s (Z s ω)) + forcing W t ω) :
    P.map (Z 0) = P.map ξ := by
  have := Measure.isProbabilityMeasure_map (μ := P) hξ
  rw [map_eq_globalLaw hv hb hl hξ hW hind hξW hsol le_rfl,
    BrownianFlow.globalLaw_initial hv hb hl]

include hv hb hl in
/-- **Weak evolution of the laws of a solution.** If the initial value has a finite second
moment, then `t ↦ P.map (Z t)` is a weak evolution of the Fokker–Planck equation with drift
`v`. -/
theorem weakEvolution_map (hξ : AEMeasurable ξ P) (hξ₂ : HasSecondMoment (P.map ξ))
    (hW : ∀ i, SharpChaos.IsStandardBrownian (W i) P)
    (hind : iIndepFun (fun (i : Fin N) (ω : Ω) (t : ℝ≥0) => W i t ω) P)
    (hξW : IndepFun ξ (fun (ω : Ω) (i : Fin N) (t : ℝ≥0) => W i t ω) P)
    (hsol : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Ici 0) ∧
      ∀ t, 0 ≤ t → Z t ω = ξ ω + (∫ s in (0 : ℝ)..t, v s (Z s ω)) + forcing W t ω) :
    WeakEvolution v fun t => P.map (Z t) := by
  have := Measure.isProbabilityMeasure_map (μ := P) hξ
  exact (BrownianFlow.globalLaw_weakEvolution hv hb hl (P.map ξ) hξ₂).congr_nonnegLaw
    fun t ht => (map_eq_globalLaw hv hb hl hξ hW hind hξW hsol ht).symm

end Sharp.Transfer

end SharpWasserstein
