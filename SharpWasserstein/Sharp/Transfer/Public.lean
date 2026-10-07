/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.Transfer.WeakEvolutions
public import SharpWasserstein.Sharp.EuclideanBridge

/-!
# Weak evolutions from the public notion of strong solution (smooth coefficients)

The public statement describes the particle system and the McKean–Vlasov equation through strong
solutions in Euclidean coordinates (`SharpChaos.IsParticleSolution`,
`SharpChaos.IsMcKeanVlasovSolution`). For smooth coefficients `a, K` on coordinates
(`IsSmoothCoefficients`), whose Euclidean conjugates are `euclidMap a` and `euclidMap₂ K`, this
file shows that the coordinate laws of such solutions are weak evolutions of the development:

* `isParticleEvolution_of_isParticleSolution`: the laws `(P.map (X t)).map (configurationEquiv d N)`
  form an `IsParticleEvolution (kernelOf a K)`;
* `isLimitEvolution_of_isMcKeanVlasovSolution`: the laws `(P.map (Y t)).map (positionEquiv d)` form
  an `IsLimitEvolution (kernelOf a K)`.

The integral equations are moved to coordinates with the continuous linear equivalences
`positionCLE d` and `configurationCLE d N` underlying `positionEquiv d` and
`configurationEquiv d N`; the drifts of the public statement become `particleDrift (kernelOf a K)`
and `nonlinearDrift (kernelOf a K)` (`configurationEquiv_particleDrift`,
`positionEquiv_mcKeanVlasovDrift`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Interval

namespace SharpWasserstein.Sharp.Transfer

variable {d N : ℕ}

/-- The coordinate map of `ℝᵈ` as a continuous linear equivalence. -/
def positionCLE (d : ℕ) : EuclideanSpace ℝ (Fin d) ≃L[ℝ] Position d :=
  PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin d => ℝ

theorem coe_positionCLE : ⇑(positionCLE d) = positionEquiv d :=
  rfl

/-- The coordinate map of configurations as a continuous linear equivalence. -/
def configurationCLE (d N : ℕ) : (Fin N → EuclideanSpace ℝ (Fin d)) ≃L[ℝ] Configuration d N :=
  ContinuousLinearEquiv.piCongrRight fun _ => positionCLE d

theorem coe_configurationCLE : ⇑(configurationCLE d N) = configurationEquiv d N :=
  rfl

/-- Continuous linear equivalences commute with interval integrals. -/
theorem intervalIntegral_comp_continuousLinearEquiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E ≃L[ℝ] F) (f : ℝ → E) (s t : ℝ) :
    (∫ r in s..t, L (f r)) = L (∫ r in s..t, f r) := by
  simp only [intervalIntegral, L.integral_comp_comm, map_sub]

/-- A configuration-valued `L²` random variable has a law with finite second moment. -/
theorem hasSecondMoment_map_of_memLp₀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {F : Ω → Configuration d N} (h : MemLp F 2 P) : HasSecondMoment (P.map F) := by
  have hm := h.aestronglyMeasurable.aemeasurable
  rw [Measure.map_congr hm.ae_eq_mk]
  exact hasSecondMoment_map_of_memLp hm.measurable_mk (h.ae_eq hm.ae_eq_mk)

/-- In coordinates, the particle drift of the public statement is the development's particle
drift of the kernel `kernelOf a K`. -/
theorem configurationEquiv_particleDrift (a : Position d → Position d)
    (K : Position d → Position d → Position d) (x : Fin N → EuclideanSpace ℝ (Fin d)) :
    configurationEquiv d N (SharpChaos.particleDrift (euclidMap a) (euclidMap₂ K) x) =
      particleDrift (kernelOf a K) (configurationEquiv d N x) := by
  funext i
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fin.pos i).ne'
  change WithLp.ofLp (euclidMap a (x i) + (N : ℝ)⁻¹ • ∑ j, euclidMap₂ K (x i) (x j)) =
    (N : ℝ)⁻¹ • ∑ j, (a (WithLp.ofLp (x i)) + K (WithLp.ofLp (x i)) (WithLp.ofLp (x j)))
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_sum, euclidMap, euclidMap₂,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_add, smul_smul, ← Nat.cast_smul_eq_nsmul ℝ, inv_mul_cancel₀ hN,
    one_smul]

/-- In coordinates, the McKean–Vlasov drift of the public statement for a probability law `μ` is
the development's nonlinear drift of the kernel `kernelOf a K` for the coordinate law. -/
theorem positionEquiv_mcKeanVlasovDrift {a : Position d → Position d}
    {K : Position d → Position d → Position d} {La L₁ L₂ M : ℝ}
    (hS : IsSmoothCoefficients a K La L₁ L₂ M) (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] (y : EuclideanSpace ℝ (Fin d)) :
    positionEquiv d (SharpChaos.mcKeanVlasovDrift (euclidMap a) (euclidMap₂ K) μ y) =
      nonlinearDrift (kernelOf a K) (μ.map (positionEquiv d)) (positionEquiv d y) := by
  have hK : Integrable (fun w => K (positionEquiv d y) (positionEquiv d w)) μ := by
    refine Integrable.mono' (integrable_const M) ?_ (ae_of_all _ fun w => hS.norm_K_le _ _)
    exact (hS.contDiff_K.continuous.comp (continuous_const.prodMk
      (positionCLE d).continuous)).aestronglyMeasurable
  rw [nonlinearDrift, integral_map_equiv]
  simp only [kernelOf]
  rw [integral_add (integrable_const _) hK, integral_const, probReal_univ, one_smul,
    SharpChaos.mcKeanVlasovDrift, ← coe_positionCLE, map_add,
    ← (positionCLE d).integral_comp_comm]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Particle system, public form (smooth coefficients).** The coordinate laws of a strong
solution of the particle system of the public statement, with an `L²` exchangeable initial value,
form a particle evolution of the development. -/
theorem isParticleEvolution_of_isParticleSolution {a : Position d → Position d}
    {K : Position d → Position d → Position d} {La L₁ L₂ M : ℝ}
    (hS : IsSmoothCoefficients a K La L₁ L₂ M)
    {X : ℝ → Ω → Fin N → EuclideanSpace ℝ (Fin d)}
    {W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : SharpChaos.IsParticleSolution (euclidMap a) (euclidMap₂ K) X W P)
    (hX₀ : MemLp (X 0) 2 P) (hexch : SharpChaos.Exchangeable (P.map (X 0))) :
    IsParticleEvolution (kernelOf a K) fun t => (P.map (X t)).map (configurationEquiv d N) := by
  set e := configurationEquiv d N
  have hmap : ∀ t, 0 ≤ t → P.map (fun ω => e (X t ω)) = (P.map (X t)).map e := fun t ht =>
    (AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable (hX.aemeasurable t ht)).symm
  have hξ : AEMeasurable (fun ω => e (X 0 ω)) P :=
    e.measurable.comp_aemeasurable (hX.aemeasurable 0 le_rfl)
  have hξ₂ : HasSecondMoment (P.map fun ω => e (X 0 ω)) :=
    hasSecondMoment_map_of_memLp₀ ((configurationCLE d N).toContinuousLinearMap.comp_memLp' hX₀)
  have hex : Exchangeable (P.map fun ω => e (X 0 ω)) := by
    rw [hmap 0 le_rfl]
    exact exchangeable_map_configurationEquiv hexch
  have hξW : IndepFun (fun ω => e (X 0 ω)) (fun (ω : Ω) (i : Fin N) (t : ℝ≥0) => W i t ω) P :=
    hX.indepFun_initial.comp e.measurable measurable_id
  have hsol : ∀ᵐ ω ∂P, ContinuousOn (fun t => e (X t ω)) (Ici 0) ∧
      ∀ t, 0 ≤ t → e (X t ω) = e (X 0 ω) +
        (∫ s in (0 : ℝ)..t, particleDrift (kernelOf a K) (e (X s ω))) + forcing W t ω := by
    filter_upwards [hX.solves] with ω hω
    refine ⟨(configurationCLE d N).continuous.comp_continuousOn hω.1, fun t ht => ?_⟩
    have h := congrArg (configurationCLE d N) (hω.2 t ht)
    rw [map_add, map_add, ← intervalIntegral_comp_continuousLinearEquiv] at h
    rw [coe_configurationCLE] at h
    simp only [configurationEquiv_particleDrift] at h
    rw [h]
    rfl
  have h := isParticleEvolution_map hS hξ hξ₂ hex hX.brownian hX.iIndepFun_brownian hξW hsol
  refine ⟨h.1.congr_nonnegLaw hmap, ?_⟩
  show Exchangeable ((P.map (X 0)).map e)
  rw [← hmap 0 le_rfl]
  exact h.2

/-- **McKean–Vlasov equation, public form (smooth coefficients).** The coordinate laws of a
strong solution of the McKean–Vlasov equation of the public statement, with an `L²` initial
value, form a limit evolution of the development. -/
theorem isLimitEvolution_of_isMcKeanVlasovSolution {a : Position d → Position d}
    {K : Position d → Position d → Position d} {La L₁ L₂ M : ℝ}
    (hS : IsSmoothCoefficients a K La L₁ L₂ M)
    {Y : ℝ → Ω → EuclideanSpace ℝ (Fin d)} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hY : SharpChaos.IsMcKeanVlasovSolution (euclidMap a) (euclidMap₂ K) Y B P)
    (hY₀ : MemLp (Y 0) 2 P) :
    IsLimitEvolution (kernelOf a K) fun t => (P.map (Y t)).map (positionEquiv d) := by
  set e := positionEquiv d
  have hmap : ∀ t, 0 ≤ t → P.map (fun ω => e (Y t ω)) = (P.map (Y t)).map e := fun t ht =>
    (AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable (hY.aemeasurable t ht)).symm
  have hYm : ∀ t, 0 ≤ t → AEMeasurable (fun ω => e (Y t ω)) P := fun t ht =>
    e.measurable.comp_aemeasurable (hY.aemeasurable t ht)
  have hξ₂ : HasSecondMoment (singletonLaw (P.map fun ω => e (Y 0 ω))) := by
    rw [singletonLaw, AEMeasurable.map_map_of_aemeasurable measurable_singleton.aemeasurable
      (hYm 0 le_rfl)]
    exact hasSecondMoment_map_of_memLp₀
      (((ContinuousLinearEquiv.funUnique (Fin 1) ℝ (Position d)).symm.trans
        (ContinuousLinearEquiv.refl ℝ _)).toContinuousLinearMap.comp_memLp'
        ((positionCLE d).toContinuousLinearMap.comp_memLp' hY₀))
  have hξB : IndepFun (fun ω => e (Y 0 ω)) (fun (ω : Ω) (t : ℝ≥0) => B t ω) P :=
    hY.indepFun_initial.comp e.measurable measurable_id
  have hsol : ∀ᵐ ω ∂P, ContinuousOn (fun t => e (Y t ω)) (Ici 0) ∧
      ∀ t, 0 ≤ t → e (Y t ω) = e (Y 0 ω) +
        (∫ s in (0 : ℝ)..t, nonlinearDrift (kernelOf a K) (P.map fun ω => e (Y s ω))
          (e (Y s ω))) + forcing₁ B t ω := by
    filter_upwards [hY.solves] with ω hω
    refine ⟨(positionCLE d).continuous.comp_continuousOn hω.1, fun t ht => ?_⟩
    have h := congrArg (positionCLE d) (hω.2 t ht)
    rw [map_add, map_add, ← intervalIntegral_comp_continuousLinearEquiv] at h
    rw [coe_positionCLE] at h
    rw [h]
    congr 2
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht] at hs
    have := Measure.isProbabilityMeasure_map (μ := P) (hY.aemeasurable s hs.1)
    simp only [positionEquiv_mcKeanVlasovDrift hS, hmap s hs.1]
    rfl
  have h := isLimitEvolution_map hS hYm (hYm 0 le_rfl) hξ₂ hY.brownian hξB hsol
  refine ⟨fun t ht => ?_, ?_⟩
  · show IsProbabilityMeasure ((P.map (Y t)).map e)
    rw [← hmap t ht]
    exact h.1 t ht
  refine (h.2.congr_nonnegDrift fun t ht => ?_).congr_nonnegLaw fun t ht => ?_
  · simp only [hmap t ht]
  · simp only [hmap t ht]

end SharpWasserstein.Sharp.Transfer
