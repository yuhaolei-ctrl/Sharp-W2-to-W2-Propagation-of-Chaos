/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.Transfer.LawTransfer
public import SharpWasserstein.Sharp.SmoothCoefficients
public import SharpWasserstein.ParticleFlow
public import SharpWasserstein.PrescribedReference

/-!
# Weak evolutions of the laws of strong solutions

For smooth coefficients `a, K` (`IsSmoothCoefficients`), the development works with the kernel
`b = kernelOf a K`, `b(x, y) = a(x) + K(x, y)`, and with the weak formulations
`IsParticleEvolution b` (particle system) and `IsLimitEvolution b` (McKean–Vlasov equation).
This file shows that the laws of strong solutions on an arbitrary probability space, driven by
independent standard Brownian motions, satisfy these weak formulations:

* `isParticleEvolution_map`: if `Z` solves `Z t = ξ + ∫₀ᵗ particleDrift b (Z s) ds + √2 W(t)`
  with an exchangeable initial law with finite second moment, then
  `IsParticleEvolution b (fun t => P.map (Z t))`;
* `isLimitEvolution_map`: if `Y` solves
  `Y t = ξ + ∫₀ᵗ nonlinearDrift b (P.map (Y s)) (Y s) ds + √2 B(t)`, with an initial law with finite
  second moment, then `IsLimitEvolution b (fun t => P.map (Y t))`.

Both are deduced from the law transfer `weakEvolution_map`. In the McKean–Vlasov case the drift is
frozen at the laws of the solution itself (`frozenDrift`); it is bounded and Lipschitz by the
kernel bounds, and jointly continuous by dominated convergence along the continuous paths of `Y`
(`continuous_frozenDrift`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Interval

namespace SharpWasserstein.Sharp.Transfer

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d N : ℕ}

section Drifts

variable {b : Position d → Position d → Position d} {Mb L₁ L₂ : ℝ}

/-- The particle drift is bounded by the bound of the kernel (also for `N = 0`). -/
theorem particleDrift_norm_le (hbound : KernelBounds b Mb L₁ L₂) (hM : 0 ≤ Mb)
    (x : Configuration d N) : ‖particleDrift b x‖ ≤ Mb := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact (pi_norm_le_iff_of_nonneg hM).2 fun i => i.elim0
  · exact particleDrift_norm_bound hN hbound hM x

/-- The particle drift is Lipschitz (also for `N = 0`). -/
theorem particleDrift_lipschitzWith (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b Mb L₁ L₂) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    LipschitzWith ⟨L₁ + L₂, add_nonneg hL₁ hL₂⟩ (particleDrift (N := N) b) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact LipschitzWith.of_dist_le_mul fun x y => by
      rw [Subsingleton.elim x y, dist_self, dist_self, mul_zero]
  · exact particleDrift_lipschitz hN hb hbound hL₁ hL₂

end Drifts

section Particle

variable [IsProbabilityMeasure P]

/-- **Particle system.** The laws of a strong solution of the particle system with smooth
coefficients, driven by independent standard Brownian motions independent of an exchangeable
initial value with finite second moment, form a particle evolution. -/
theorem isParticleEvolution_map {a : Position d → Position d}
    {K : Position d → Position d → Position d} {La L₁ L₂ M : ℝ}
    (hS : IsSmoothCoefficients a K La L₁ L₂ M) {ξ : Ω → Configuration d N}
    (hξ : AEMeasurable ξ P) (hξ₂ : HasSecondMoment (P.map ξ)) (hex : Exchangeable (P.map ξ))
    {W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : ∀ i, SharpChaos.IsStandardBrownian (W i) P)
    (hind : iIndepFun (fun (i : Fin N) (ω : Ω) (t : ℝ≥0) => W i t ω) P)
    (hξW : IndepFun ξ (fun (ω : Ω) (i : Fin N) (t : ℝ≥0) => W i t ω) P)
    {Z : ℝ → Ω → Configuration d N}
    (hsol : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Ici 0) ∧
      ∀ t, 0 ≤ t → Z t ω =
        ξ ω + (∫ s in (0 : ℝ)..t, particleDrift (kernelOf a K) (Z s ω)) + forcing W t ω) :
    IsParticleEvolution (kernelOf a K) fun t => P.map (Z t) := by
  obtain ⟨Mb, Lb₁, Lb₂, hMb, hLb₁, hLb₂, hbound⟩ := hS.exists_kernelBounds
  have hlip := particleDrift_lipschitzWith (N := N) hS.boundedSmoothKernel hbound hLb₁ hLb₂
  have hv : Continuous (Function.uncurry fun (_ : ℝ) => particleDrift (N := N) (kernelOf a K)) :=
    hlip.continuous.comp continuous_snd
  have hbd : ∀ (t : ℝ) (x : Configuration d N),
      ‖(fun (_ : ℝ) => particleDrift (N := N) (kernelOf a K)) t x‖ ≤ (⟨Mb, hMb⟩ : ℝ≥0) :=
    fun _ x => particleDrift_norm_le hbound hMb x
  have hl : ∀ t : ℝ, LipschitzWith _ ((fun (_ : ℝ) => particleDrift (N := N) (kernelOf a K)) t) :=
    fun _ => hlip
  refine ⟨weakEvolution_map hv hbd hl hξ hξ₂ hW hind hξW hsol, ?_⟩
  show Exchangeable (P.map (Z 0))
  rw [map_zero_eq hv hbd hl hξ hW hind hξW hsol]
  exact hex

end Particle

section McKeanVlasov

variable {b : Position d → Position d → Position d} {Mb L₁ L₂ : ℝ}

/-- The additive forcing `√2 B(t)` in coordinates for a single Brownian motion in `ℝᵈ`. -/
def forcing₁ (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (t : ℝ) (ω : Ω) : Position d :=
  fun a => Real.sqrt 2 * B t.toNNReal ω a

/-- The McKean–Vlasov drift frozen along the laws of a process `Y`, with the initial law used at
negative times. -/
def frozenDrift (P : Measure Ω) (b : Position d → Position d → Position d)
    (Y : ℝ → Ω → Position d) (t : ℝ) (x : Position d) : Position d :=
  nonlinearDrift b (P.map (Y (max t 0))) x

theorem frozenDrift_eq_integral (hb : BoundedSmoothKernel b) {Y : ℝ → Ω → Position d} {t : ℝ}
    (hY : AEMeasurable (Y (max t 0)) P) (x : Position d) :
    frozenDrift P b Y t x = ∫ ω, b x (Y (max t 0) ω) ∂P :=
  integral_map hY (hb.contDiff_second x).continuous.aestronglyMeasurable

/-- The frozen drift is jointly continuous, by dominated convergence along the continuous paths
of `Y`. -/
theorem continuous_frozenDrift [IsProbabilityMeasure P] (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b Mb L₁ L₂) {Y : ℝ → Ω → Position d}
    (hYm : ∀ t, 0 ≤ t → AEMeasurable (Y t) P)
    (hYc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Ici 0)) :
    Continuous (Function.uncurry (frozenDrift P b Y)) := by
  have heq : Function.uncurry (frozenDrift P b Y) =
      fun p : ℝ × Position d => ∫ ω, b p.2 (Y (max p.1 0) ω) ∂P := by
    funext p
    exact frozenDrift_eq_integral hb (hYm _ (le_max_right _ _)) p.2
  rw [heq]
  refine continuous_of_dominated (bound := fun _ => Mb) (fun p => ?_)
    (fun p => ae_of_all _ fun ω => hbound.value _ _) (integrable_const _) ?_
  · exact ((hb.contDiff_second p.2).continuous.measurable.comp_aemeasurable
      (hYm _ (le_max_right _ _))).aestronglyMeasurable
  · filter_upwards [hYc] with ω hω
    have hm : Continuous fun t : ℝ => Y (max t 0) ω :=
      hω.comp_continuous (continuous_id.max continuous_const) fun t => le_max_right t 0
    exact hb.smooth.continuous.comp (continuous_snd.prodMk (hm.comp continuous_fst))

theorem frozenDrift_norm_le (hbound : KernelBounds b Mb L₁ L₂) {Y : ℝ → Ω → Position d}
    [IsProbabilityMeasure P] (hYm : ∀ t, 0 ≤ t → AEMeasurable (Y t) P) (t : ℝ)
    (x : Position d) : ‖frozenDrift P b Y t x‖ ≤ Mb := by
  have := Measure.isProbabilityMeasure_map (μ := P) (hYm (max t 0) (le_max_right _ _))
  exact nonlinearDrift_bound hbound _ x

theorem frozenDrift_lipschitzWith (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b Mb L₁ L₂) (hL₁ : 0 ≤ L₁) {Y : ℝ → Ω → Position d}
    [IsProbabilityMeasure P] (hYm : ∀ t, 0 ≤ t → AEMeasurable (Y t) P) (t : ℝ) :
    LipschitzWith ⟨L₁, hL₁⟩ (frozenDrift P b Y t) := by
  have := Measure.isProbabilityMeasure_map (μ := P) (hYm (max t 0) (le_max_right _ _))
  exact nonlinearDrift_lipschitz hb hbound hL₁ _

/-- Interval integrals commute with the embedding of `ℝᵈ` into one-particle configurations. -/
theorem intervalIntegral_singleton (f : ℝ → Position d) (s t : ℝ) :
    (∫ r in s..t, (fun _ : Fin 1 => f r)) = fun _ => ∫ r in s..t, f r := by
  have h : ∀ μ : Measure ℝ, (∫ r, (fun _ : Fin 1 => f r) ∂μ) = fun _ => ∫ r, f r ∂μ :=
    fun μ => (ContinuousLinearEquiv.funUnique (Fin 1) ℝ (Position d)).symm.integral_comp_comm f
  simp only [intervalIntegral, h]
  rfl

theorem measurable_singleton : Measurable fun (x : Position d) (_ : Fin 1) => x :=
  Measurable.of_eval fun _ => measurable_id

/-- **McKean–Vlasov equation.** The laws of a strong solution of the McKean–Vlasov equation with
smooth coefficients, driven by a standard Brownian motion independent of an initial value with
finite second moment, form a limit evolution. -/
theorem isLimitEvolution_map [IsProbabilityMeasure P] {a : Position d → Position d}
    {K : Position d → Position d → Position d} {La L₁ L₂ M : ℝ}
    (hS : IsSmoothCoefficients a K La L₁ L₂ M) {Y : ℝ → Ω → Position d}
    (hYm : ∀ t, 0 ≤ t → AEMeasurable (Y t) P) {ξ : Ω → Position d} (hξ : AEMeasurable ξ P)
    (hξ₂ : HasSecondMoment (singletonLaw (P.map ξ)))
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : SharpChaos.IsStandardBrownian B P)
    (hξB : IndepFun ξ (fun (ω : Ω) (t : ℝ≥0) => B t ω) P)
    (hsol : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Ici 0) ∧
      ∀ t, 0 ≤ t → Y t ω = ξ ω +
        (∫ s in (0 : ℝ)..t, nonlinearDrift (kernelOf a K) (P.map (Y s)) (Y s ω)) +
          forcing₁ B t ω) :
    IsLimitEvolution (kernelOf a K) fun t => P.map (Y t) := by
  obtain ⟨Mb, Lb₁, Lb₂, hMb, hLb₁, hLb₂, hbound⟩ := hS.exists_kernelBounds
  have hb := hS.boundedSmoothKernel
  set u := frozenDrift P (kernelOf a K) Y with hu_def
  have hu : Continuous (Function.uncurry u) :=
    continuous_frozenDrift hb hbound hYm (hsol.mono fun _ h => h.1)
  have hub : ∀ t x, ‖u t x‖ ≤ (⟨Mb, hMb⟩ : ℝ≥0) := frozenDrift_norm_le hbound hYm
  have hul : ∀ t, LipschitzWith ⟨Lb₁, hLb₁⟩ (u t) := frozenDrift_lipschitzWith hb hbound hLb₁ hYm
  have hv := DecoupledFlow.liftDrift_continuous 1 hu
  have hvb := DecoupledFlow.liftDrift_bound 1 hub
  have hvl := DecoupledFlow.liftDrift_lipschitz 1 hul
  have hξ' : AEMeasurable (fun ω (_ : Fin 1) => ξ ω) P :=
    measurable_singleton.comp_aemeasurable hξ
  have hmap : ∀ {F : Ω → Position d}, AEMeasurable F P →
      P.map (fun ω (_ : Fin 1) => F ω) = singletonLaw (P.map F) := fun hF => by
    rw [singletonLaw, AEMeasurable.map_map_of_aemeasurable measurable_singleton.aemeasurable hF]
    rfl
  have hξ'₂ : HasSecondMoment (P.map fun ω (_ : Fin 1) => ξ ω) := by rwa [hmap hξ]
  have hW : ∀ i : Fin 1, SharpChaos.IsStandardBrownian ((fun _ => B) i) P := fun _ => hB
  have hind : iIndepFun (fun (i : Fin 1) (ω : Ω) (t : ℝ≥0) => (fun _ => B) i t ω) P :=
    iIndepFun.of_subsingleton
  have hξW : IndepFun (fun ω (_ : Fin 1) => ξ ω)
      (fun (ω : Ω) (i : Fin 1) (t : ℝ≥0) => (fun _ => B) i t ω) P :=
    hξB.comp measurable_singleton (Measurable.of_eval fun _ => measurable_id)
  have hsol' : ∀ᵐ ω ∂P, ContinuousOn (fun t (_ : Fin 1) => Y t ω) (Ici 0) ∧
      ∀ t, 0 ≤ t → (fun (_ : Fin 1) => Y t ω) = (fun _ => ξ ω) +
        (∫ s in (0 : ℝ)..t, DecoupledFlow.liftDrift 1 u s fun _ => Y s ω) +
          forcing (fun _ => B) t ω := by
    filter_upwards [hsol] with ω hω
    refine ⟨continuousOn_pi.2 fun _ => hω.1, fun t ht => ?_⟩
    have hint : (∫ s in (0 : ℝ)..t, u s (Y s ω)) =
        ∫ s in (0 : ℝ)..t, nonlinearDrift (kernelOf a K) (P.map (Y s)) (Y s ω) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le ht] at hs
      simp only [hu_def, frozenDrift, max_eq_left hs.1]
    have hlift : (∫ s in (0 : ℝ)..t, DecoupledFlow.liftDrift 1 u s fun _ => Y s ω) =
        fun _ => ∫ s in (0 : ℝ)..t, u s (Y s ω) :=
      intervalIntegral_singleton (fun s => u s (Y s ω)) 0 t
    rw [hlift, hint]
    funext i
    simp only [Pi.add_apply]
    exact hω.2 t ht
  have hWE := weakEvolution_map hv hvb hvl hξ' hξ'₂ hW hind hξW hsol'
  refine ⟨fun t ht => Measure.isProbabilityMeasure_map (hYm t ht), ?_⟩
  refine (hWE.congr_nonnegDrift fun t ht => ?_).congr_nonnegLaw fun t ht => hmap (hYm t ht)
  funext x i
  simp only [DecoupledFlow.liftDrift, hu_def, frozenDrift, max_eq_left ht]

end McKeanVlasov

end SharpWasserstein.Sharp.Transfer
