/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Statement
public import SharpWasserstein.Transport

/-!
# From Euclidean configurations to coordinate configurations

The public statement (`SharpWasserstein.Statement`) works with configurations
`Fin N → EuclideanSpace ℝ (Fin d)`, while the development works with the coordinate type
`SharpWasserstein.Configuration d N = Fin N → Fin d → ℝ`. The coordinate map
`configurationEquiv d N` is a measurable equivalence that carries the unnormalized squared
Euclidean distance `SharpChaos.sqDist` to `SharpWasserstein.productCost`. Consequently it
identifies the two squared Wasserstein distances, marginals, tensor powers, exchangeability and
second moments.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SharpWasserstein.Sharp

variable {d N k : ℕ}

/-- The coordinates of a point of `ℝᵈ`. -/
def positionEquiv (d : ℕ) : EuclideanSpace ℝ (Fin d) ≃ᵐ Position d :=
  (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm

/-- The coordinates of a configuration of `N` points of `ℝᵈ`. -/
def configurationEquiv (d N : ℕ) :
    (Fin N → EuclideanSpace ℝ (Fin d)) ≃ᵐ Configuration d N :=
  MeasurableEquiv.piCongrRight fun _ => positionEquiv d

@[simp] theorem positionEquiv_apply (x : EuclideanSpace ℝ (Fin d)) (a : Fin d) :
    positionEquiv d x a = x a :=
  rfl

@[simp] theorem configurationEquiv_apply (x : Fin N → EuclideanSpace ℝ (Fin d)) (i : Fin N)
    (a : Fin d) : configurationEquiv d N x i a = x i a :=
  rfl

/-- The coordinate map carries the squared Euclidean distance to the coordinate cost. -/
theorem productCost_configurationEquiv (x y : Fin N → EuclideanSpace ℝ (Fin d)) :
    productCost (configurationEquiv d N x) (configurationEquiv d N y) = SharpChaos.sqDist x y := by
  unfold productCost SharpChaos.sqDist
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Real.norm_eq_abs, sq_abs]

/-- Couplings correspond under the coordinate map. -/
theorem isCoupling_map_configurationEquiv {μ ν : Measure (Fin N → EuclideanSpace ℝ (Fin d))}
    {π : Measure ((Fin N → EuclideanSpace ℝ (Fin d)) × (Fin N → EuclideanSpace ℝ (Fin d)))}
    (hπ : SharpChaos.IsCoupling μ ν π) :
    IsCoupling (μ.map (configurationEquiv d N)) (ν.map (configurationEquiv d N))
      (π.map (Prod.map (configurationEquiv d N) (configurationEquiv d N))) := by
  have he := (configurationEquiv d N).measurable
  have := hπ.1
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst (he.prodMap he), ← hπ.2.1,
      Measure.map_map he measurable_fst]
    rfl
  · rw [Measure.map_map measurable_snd (he.prodMap he), ← hπ.2.2,
      Measure.map_map he measurable_snd]
    rfl

/-- Couplings of the coordinate laws come from couplings of the Euclidean laws. -/
theorem isCoupling_map_configurationEquiv_symm {μ ν : Measure (Fin N → EuclideanSpace ℝ (Fin d))}
    {γ : Measure (Configuration d N × Configuration d N)}
    (hγ : IsCoupling (μ.map (configurationEquiv d N)) (ν.map (configurationEquiv d N)) γ) :
    SharpChaos.IsCoupling μ ν
      (γ.map (Prod.map (configurationEquiv d N).symm (configurationEquiv d N).symm)) := by
  have he := (configurationEquiv d N).measurable
  have hs := (configurationEquiv d N).symm.measurable
  have := hγ.1
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst (hs.prodMap hs)]
    change γ.map ((configurationEquiv d N).symm ∘ Prod.fst) = μ
    rw [← Measure.map_map hs measurable_fst, hγ.2.1, Measure.map_map hs he]
    simp
  · rw [Measure.map_map measurable_snd (hs.prodMap hs)]
    change γ.map ((configurationEquiv d N).symm ∘ Prod.snd) = ν
    rw [← Measure.map_map hs measurable_snd, hγ.2.2, Measure.map_map hs he]
    simp

/-- The squared Wasserstein distance of the public statement equals the squared Wasserstein
distance of the coordinate laws. -/
theorem wassersteinSq_eq_map (μ ν : Measure (Fin N → EuclideanSpace ℝ (Fin d))) :
    SharpChaos.wassersteinSq μ ν =
      wassersteinSq (μ.map (configurationEquiv d N)) (ν.map (configurationEquiv d N)) := by
  have he := (configurationEquiv d N).measurable
  have hs := (configurationEquiv d N).symm.measurable
  have hcost : Measurable fun z : (Fin N → EuclideanSpace ℝ (Fin d)) ×
      (Fin N → EuclideanSpace ℝ (Fin d)) => ENNReal.ofReal (SharpChaos.sqDist z.1 z.2) := by
    have h := (measurable_productCost.comp (he.prodMap he)).ennreal_ofReal
    simpa [Function.comp_def, productCost_configurationEquiv] using h
  apply le_antisymm
  · refine le_iInf₂ fun γ hγ => ?_
    refine (iInf₂_le _ (isCoupling_map_configurationEquiv_symm hγ)).trans_eq ?_
    rw [lintegral_map hcost (hs.prodMap hs), transportCost]
    congr 1
    funext z
    rw [← productCost_configurationEquiv]
    simp
  · refine le_iInf₂ fun π hπ => ?_
    refine (wassersteinSq_le_cost (isCoupling_map_configurationEquiv hπ)).trans_eq ?_
    rw [transportCost, lintegral_map measurable_productCost.ennreal_ofReal (he.prodMap he)]
    congr 1
    funext z
    simp [productCost_configurationEquiv]

/-- Marginals commute with the coordinate map. -/
theorem marginal_map_configurationEquiv (hk : k ≤ N)
    (P : Measure (Fin N → EuclideanSpace ℝ (Fin d))) :
    (SharpChaos.marginal hk P).map (configurationEquiv d k) =
      marginal hk (P.map (configurationEquiv d N)) := by
  have he := (configurationEquiv d N).measurable
  have hk' := (configurationEquiv d k).measurable
  have hr : Measurable fun x : Fin N → EuclideanSpace ℝ (Fin d) => fun i : Fin k =>
      x (Fin.castLE hk i) := Measurable.of_eval fun i => measurable_pi_apply _
  rw [SharpChaos.marginal, marginal, Measure.map_map hk' hr,
    Measure.map_map (measurable_restrictCoordinates hk) he]
  rfl

/-- Tensor powers commute with the coordinate map. -/
theorem pi_map_configurationEquiv (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] :
    (Measure.pi fun _ : Fin k => μ).map (configurationEquiv d k) =
      tensorLaw (μ.map (positionEquiv d)) k := by
  rw [tensorLaw]
  exact Measure.pi_map_pi (fun _ => (positionEquiv d).measurable.aemeasurable)

/-- Exchangeability is preserved by the coordinate map. -/
theorem exchangeable_map_configurationEquiv {P : Measure (Fin N → EuclideanSpace ℝ (Fin d))}
    (hP : SharpChaos.Exchangeable P) : Exchangeable (P.map (configurationEquiv d N)) := by
  intro σ
  have he := (configurationEquiv d N).measurable
  have hσ : Measurable fun x : Fin N → EuclideanSpace ℝ (Fin d) => fun i => x (σ i) :=
    Measurable.of_eval fun i => measurable_pi_apply _
  have hσ' : Measurable fun x : Configuration d N => fun i => x (σ i) :=
    Measurable.of_eval fun i => measurable_pi_apply _
  rw [Measure.map_map hσ' he]
  conv_rhs => rw [← hP σ, Measure.map_map he hσ]
  rfl

end SharpWasserstein.Sharp
