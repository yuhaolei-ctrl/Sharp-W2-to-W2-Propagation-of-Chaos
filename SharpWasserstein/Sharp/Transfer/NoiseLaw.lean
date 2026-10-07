/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Statement
public import SharpWasserstein.ConfigurationBrownian
public import SharpWasserstein.ContinuousPathLaw

/-!
# The joint law of the initial value and the Brownian noise

The public statement (`SharpWasserstein.Statement`) uses Brownian motions
`W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)` on an arbitrary probability space `(Ω, P)`:
the coordinates of each `W i` are independent real Brownian motions
(`SharpChaos.IsStandardBrownian`), the `W i` are independent, and they are independent of the
initial value. The development constructs its laws from the canonical noise law
`BrownianNoise.configurationLaw d N T` on `C(Icc 0 T, Configuration d N)`.

This file builds, for every `ω`, the continuous noise path `noisePath W T ω` on `[0, T]`, equal to
`t ↦ (√2 W i t ω a)_{i, a}` whenever these coordinate paths are continuous (that is, almost
surely), and proves that the joint law of `(ξ, noisePath W T)` is
`(P.map ξ).prod (BrownianNoise.configurationLaw d N T)` for every random variable `ξ`
independent of the Brownian motions (`hasLaw_noisePath_prod`).

The proof assembles the law of the coordinate paths as a product of copies of `gaussianLimit`
(nested independence, `IsPreBrownianReal.hasLaw_gaussianLimit`), and identifies laws on the space
of continuous paths through their images in the space of all paths, whose σ-algebra pulls back
to that of the continuous paths (`continuousPath_measurableSpace_eq_comap`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SharpWasserstein.Sharp.Transfer

section Comap

/-- If the σ-algebra of `β` is pulled back along `f : β → γ`, then a map `g : α → β` is
almost everywhere measurable as soon as `f ∘ g` is. -/
theorem aemeasurable_of_comp_of_eq_comap {α β γ : Type*} [MeasurableSpace α] {μ : Measure α}
    [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ] [Nonempty β] (f : β → γ)
    (hf : mβ = mγ.comap f) {g : α → β} (hg : AEMeasurable (f ∘ g) μ) : AEMeasurable g μ := by
  classical
  obtain ⟨F, hF, hgF⟩ := hg
  set S := toMeasurable μ {x | ¬(f ∘ g) x = F x} with hS_def
  have hS : MeasurableSet S := measurableSet_toMeasurable _ _
  have hS0 : μ S = 0 := by rw [measure_toMeasurable]; exact ae_iff.1 hgF
  let b : β := Classical.arbitrary β
  have hcomp : f ∘ S.piecewise (fun _ => b) g = S.piecewise (fun _ => f b) F := by
    funext x
    by_cases hx : x ∈ S
    · simp [Set.piecewise, hx]
    · have hfx : f (g x) = F x := by
        by_contra h
        exact hx (subset_toMeasurable _ _ h)
      simp [Set.piecewise, hx, hfx]
  refine ⟨S.piecewise (fun _ => b) g, ?_, ?_⟩
  · rw [measurable_iff_comap_le, hf, MeasurableSpace.comap_comp, ← measurable_iff_comap_le,
      hcomp]
    exact Measurable.piecewise hS measurable_const hF
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hS0] with x hx
    simp [Set.piecewise, hx]

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [SecondCountableTopology X] [SecondCountableTopology Y] [LocallyCompactSpace X]
  [RegularSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The σ-algebra of `E × C(X, Y)` is pulled back from that of `E × (X → Y)`. -/
theorem prod_continuousPath_measurableSpace_eq_comap {E : Type*} [MeasurableSpace E] :
    (inferInstance : MeasurableSpace (E × C(X, Y))) =
      (inferInstance : MeasurableSpace (E × (X → Y))).comap
        (Prod.map id fun f : C(X, Y) => (f : X → Y)) := by
  have hC : (inferInstance : MeasurableSpace C(X, Y)) =
      MeasurableSpace.comap (fun f : C(X, Y) => (f : X → Y)) MeasurableSpace.pi :=
    continuousPath_measurableSpace_eq_comap
  change MeasurableSpace.prod _ _ = (MeasurableSpace.prod _ _).comap _
  simp only [MeasurableSpace.prod, MeasurableSpace.comap_sup, MeasurableSpace.comap_comp]
  change _ ⊔ MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace C(X, Y)) = _
  rw [hC, MeasurableSpace.comap_comp]
  rfl

omit [SecondCountableTopology X] [SecondCountableTopology Y] [LocallyCompactSpace X]
  [RegularSpace Y] in
theorem measurable_prodMap_coe {E : Type*} [MeasurableSpace E] :
    Measurable (Prod.map (id : E → E) fun f : C(X, Y) => (f : X → Y)) :=
  measurable_id.prodMap continuousPath_coe_measurable

/-- A measure on `E × C(X, Y)` is determined by its image in `E × (X → Y)`. -/
theorem map_prodMap_coe_injective {E : Type*} [MeasurableSpace E] :
    Function.Injective
      (Measure.map (Prod.map (id : E → E) fun f : C(X, Y) => (f : X → Y))) := by
  intro μ ν h
  ext s hs
  have hs' : MeasurableSet[(inferInstance : MeasurableSpace (E × (X → Y))).comap
      (Prod.map id fun f : C(X, Y) => (f : X → Y))] s := by
    rw [← prod_continuousPath_measurableSpace_eq_comap]
    exact hs
  obtain ⟨u, hu, rfl⟩ := hs'
  have he := congrArg (fun η : Measure (E × (X → Y)) => η u) h
  simpa only [Measure.map_apply measurable_prodMap_coe hu] using he

end Comap

variable {Ω : Type*} {d N : ℕ}

/-- The coordinate paths `(i, a) ↦ (t ↦ W i t ω a)` of a family of `ℝᵈ`-valued processes. -/
def coordinatePaths (W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    Fin N → Fin d → ℝ≥0 → ℝ :=
  fun i a t => W i t ω a

/-- The restriction to `[0, T]` of `√2` times a family of coordinate paths, as a path of
configurations. -/
def scaledRestriction (T : ℝ) (w : Fin N → Fin d → ℝ≥0 → ℝ) : Icc 0 T → Configuration d N :=
  fun t i a => Real.sqrt 2 * w i a ⟨t, t.property.1⟩

theorem measurable_scaledRestriction (T : ℝ) :
    Measurable (scaledRestriction (d := d) (N := N) T) := by
  unfold scaledRestriction
  fun_prop

open Classical in
/-- The continuous noise path `t ↦ √2 W(t, ω)` on `[0, T]`, in coordinates. It is defined for
every `ω`, and replaced by `0` when the path is not continuous (a null event). -/
def noisePath (W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (T : ℝ) (ω : Ω) :
    C(Icc 0 T, Configuration d N) :=
  if h : Continuous (scaledRestriction T (coordinatePaths W ω)) then ⟨_, h⟩ else 0

theorem coe_noisePath_of_continuous {W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} {T : ℝ}
    {ω : Ω} (h : ∀ i a, Continuous fun t => W i t ω a) :
    (noisePath W T ω : Icc 0 T → Configuration d N) =
      scaledRestriction T (coordinatePaths W ω) := by
  have hc : Continuous (scaledRestriction T (coordinatePaths W ω)) :=
    continuous_pi fun i => continuous_pi fun a => continuous_const.mul
      ((h i a).comp (continuous_subtype_val.subtype_mk _))
  simp only [noisePath, hc, ↓reduceDIte]
  rfl

/-- Almost surely, the noise path is `t ↦ √2 W(t, ω)` on `[0, T]`. -/
theorem coe_noisePath_ae_eq [MeasurableSpace Ω] {P : Measure Ω}
    {W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : ∀ i, SharpChaos.IsStandardBrownian (W i) P) (T : ℝ) :
    ∀ᵐ ω ∂P, (noisePath W T ω : Icc 0 T → Configuration d N) =
      scaledRestriction T (coordinatePaths W ω) := by
  have h : ∀ᵐ ω ∂P, ∀ i a, Continuous fun t => W i t ω a :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun a => ((hW i).1 a).cont
  filter_upwards [h] with ω hω
  exact coe_noisePath_of_continuous hω

/-- Almost surely, `noisePath W T ω t = √2 W(t, ω)` (in coordinates) for all `t ∈ [0, T]`. -/
theorem noisePath_ae_eq [MeasurableSpace Ω] {P : Measure Ω}
    {W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : ∀ i, SharpChaos.IsStandardBrownian (W i) P) (T : ℝ) :
    ∀ᵐ ω ∂P, ∀ t : Icc 0 T, noisePath W T ω t =
      fun i a => Real.sqrt 2 * W i ⟨t, t.property.1⟩ ω a := by
  filter_upwards [coe_noisePath_ae_eq hW T] with ω hω t
  exact congrFun hω t

/-- The product of independent copies of the Wiener measure `gaussianLimit`, indexed by particles
and coordinates. -/
def wienerLabels (d N : ℕ) : Measure (Fin N → Fin d → ℝ≥0 → ℝ) :=
  Measure.pi fun _ => Measure.pi fun _ => gaussianLimit

instance (d N : ℕ) : IsProbabilityMeasure (wienerLabels d N) := by
  unfold wienerLabels
  infer_instance

/-- The joint law of the coordinate paths of independent standard Brownian motions. -/
theorem hasLaw_coordinatePaths [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : ∀ i, SharpChaos.IsStandardBrownian (W i) P)
    (hind : iIndepFun (fun (i : Fin N) (ω : Ω) (t : ℝ≥0) => W i t ω) P) :
    HasLaw (coordinatePaths W) (wienerLabels d N) P := by
  have hm : ∀ i a, AEMeasurable (fun ω t => W i t ω a) P := fun i a => ((hW i).1 a).aemeasurable
  have hmi : ∀ i, AEMeasurable (fun ω => coordinatePaths W ω i) P := fun i =>
    AEMeasurable.of_eval fun a => hm i a
  have hlaw : ∀ i a, P.map (fun ω t => W i t ω a) = gaussianLimit := fun i a =>
    (((hW i).1 a).toIsPreBrownianReal.hasLaw_gaussianLimit (hm i a)).map_eq
  have hlawi : ∀ i, P.map (fun ω => coordinatePaths W ω i) = Measure.pi fun _ => gaussianLimit := by
    intro i
    have h := (iIndepFun_iff_map_fun_eq_pi_map (hm i)).1 (hW i).2
    simp only [hlaw i] at h
    exact h
  have hR : ∀ i : Fin N, Measurable fun (f : ℝ≥0 → EuclideanSpace ℝ (Fin d)) (a : Fin d)
      (t : ℝ≥0) => f t a := fun i =>
    Measurable.of_eval fun a => Measurable.of_eval fun t =>
      (by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin d) => x a).comp
        (measurable_pi_apply t)
  have hindc : iIndepFun (fun (i : Fin N) (ω : Ω) => coordinatePaths W ω i) P :=
    hind.comp _ hR
  refine ⟨AEMeasurable.of_eval hmi, ?_⟩
  have h := (iIndepFun_iff_map_fun_eq_pi_map hmi).1 hindc
  simp only [hlawi] at h
  exact h

/-- The noise law, pushed to the space of all paths, is the image of `wienerLabels` under the
scaled restriction. -/
theorem map_coe_configurationLaw (T : ℝ) :
    (BrownianNoise.configurationLaw d N T).map
        (fun f : C(Icc 0 T, Configuration d N) => (f : Icc 0 T → Configuration d N)) =
      (wienerLabels d N).map (scaledRestriction T) := by
  have hS : Measurable (BrownianNoise.scalarPath (T := T)) := BrownianNoise.scalarPath_measurable
  have hS₁ : Measurable fun (x : Fin d → ℝ≥0 → ℝ) (a : Fin d) => BrownianNoise.scalarPath (T := T)
      (x a) := Measurable.of_eval fun a => hS.comp (measurable_pi_apply a)
  have hB : Measurable fun ω : ℝ≥0 → ℝ => fun t => brownian t ω :=
    Measurable.of_eval fun t => measurable_brownian t
  have hB₁ : Measurable fun (x : Fin d → ℝ≥0 → ℝ) (a : Fin d) (t : ℝ≥0) => brownian t (x a) :=
    Measurable.of_eval fun a => hB.comp (measurable_pi_apply a)
  have hB₂ : Measurable fun (w : Fin N → Fin d → ℝ≥0 → ℝ) (i : Fin N) (a : Fin d) (t : ℝ≥0) =>
      brownian t (w i a) :=
    Measurable.of_eval fun i => hB₁.comp (measurable_pi_apply i)
  have hS₂ : Measurable fun (w : Fin N → Fin d → ℝ≥0 → ℝ) (i : Fin N) (a : Fin d) =>
      BrownianNoise.scalarPath (T := T) (w i a) :=
    Measurable.of_eval fun i => hS₁.comp (measurable_pi_apply i)
  have hcoord : BrownianNoise.coordinateLaw d T =
      (Measure.pi fun _ : Fin d => gaussianLimit).map
        fun x a => BrownianNoise.scalarPath (T := T) (x a) := by
    rw [Measure.pi_map_pi (fun _ => hS.aemeasurable)]
    rfl
  have hlabels : BrownianNoise.pathLabels d N T =
      (wienerLabels d N).map fun w i a => BrownianNoise.scalarPath (T := T) (w i a) := by
    rw [wienerLabels, Measure.pi_map_pi (fun _ => hS₁.aemeasurable), ← hcoord]
    rfl
  have hcoordB : (Measure.pi fun _ : Fin d => gaussianLimit).map
      (fun (x : Fin d → ℝ≥0 → ℝ) (a : Fin d) (t : ℝ≥0) => brownian t (x a)) =
        Measure.pi fun _ : Fin d => gaussianLimit := by
    rw [Measure.pi_map_pi (fun _ => hB.aemeasurable), hasLaw_brownian.map_eq]
  have hwB : (wienerLabels d N).map
      (fun (w : Fin N → Fin d → ℝ≥0 → ℝ) (i : Fin N) (a : Fin d) (t : ℝ≥0) =>
        brownian t (w i a)) = wienerLabels d N := by
    rw [wienerLabels, Measure.pi_map_pi (fun _ => hB₁.aemeasurable), hcoordB]
  rw [BrownianNoise.configurationLaw, Measure.map_map continuousPath_coe_measurable
    BrownianNoise.configurationPath_measurable, hlabels,
    Measure.map_map (continuousPath_coe_measurable.comp
      BrownianNoise.configurationPath_measurable) hS₂]
  conv_rhs => rw [← hwB, Measure.map_map (measurable_scaledRestriction T) hB₂]
  rfl

/-- **Joint law of the initial value and the noise.** If `W` is a family of independent standard
Brownian motions in `ℝᵈ` and `ξ` is a random variable independent of `W`, then the joint law of
`ξ` and the continuous noise path `t ↦ √2 W(t)` on `[0, T]` is the product of the law of `ξ` and
the development's canonical noise law `BrownianNoise.configurationLaw d N T`. -/
theorem hasLaw_noisePath_prod [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {E : Type*} [MeasurableSpace E] {ξ : Ω → E} (hξ : AEMeasurable ξ P)
    {W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : ∀ i, SharpChaos.IsStandardBrownian (W i) P)
    (hind : iIndepFun (fun (i : Fin N) (ω : Ω) (t : ℝ≥0) => W i t ω) P)
    (hξW : IndepFun ξ (fun (ω : Ω) (i : Fin N) (t : ℝ≥0) => W i t ω) P) (T : ℝ) :
    HasLaw (fun ω => (ξ ω, noisePath W T ω))
      ((P.map ξ).prod (BrownianNoise.configurationLaw d N T)) P := by
  have hV := hasLaw_coordinatePaths hW hind
  have hR : Measurable fun (f : Fin N → ℝ≥0 → EuclideanSpace ℝ (Fin d)) (i : Fin N) (a : Fin d)
      (t : ℝ≥0) => f i t a := by fun_prop
  have hξV : IndepFun ξ (coordinatePaths W) P := hξW.comp measurable_id hR
  have hjoint : P.map (fun ω => (ξ ω, coordinatePaths W ω)) =
      (P.map ξ).prod (wienerLabels d N) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hξ hV.aemeasurable).1 hξV, hV.map_eq]
  have hae := coe_noisePath_ae_eq (P := P) hW T
  have hGm : AEMeasurable (noisePath W T) P := by
    apply aemeasurable_of_comp_of_eq_comap
      (fun f : C(Icc 0 T, Configuration d N) => (f : Icc 0 T → Configuration d N))
      continuousPath_measurableSpace_eq_comap
    exact ((measurable_scaledRestriction T).comp_aemeasurable hV.aemeasurable).congr
      (hae.mono fun ω h => h.symm)
  refine ⟨hξ.prodMk hGm, ?_⟩
  apply map_prodMap_coe_injective (X := Icc 0 T) (Y := Configuration d N) (E := E)
  have hSR : Measurable (Prod.map (id : E → E) (scaledRestriction (d := d) (N := N) T)) :=
    measurable_id.prodMap (measurable_scaledRestriction T)
  have hR2 : ((P.map ξ).prod (wienerLabels d N)).map (Prod.map id (scaledRestriction T)) =
      (P.map ξ).prod ((wienerLabels d N).map (scaledRestriction T)) := by
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_scaledRestriction T), Measure.map_id]
  rw [AEMeasurable.map_map_of_aemeasurable measurable_prodMap_coe.aemeasurable
    (hξ.prodMk hGm), ← Measure.map_prod_map _ _ measurable_id continuousPath_coe_measurable,
    Measure.map_id, map_coe_configurationLaw, ← hR2, ← hjoint,
    AEMeasurable.map_map_of_aemeasurable hSR.aemeasurable (hξ.prodMk hV.aemeasurable)]
  refine Measure.map_congr ?_
  filter_upwards [hae] with ω hω
  simp only [Function.comp_apply, Prod.map_apply, id_eq, hω]

end SharpWasserstein.Sharp.Transfer
