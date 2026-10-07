/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.EuclideanBridge
public import SharpWasserstein.TransportTriangle

/-!
# Couplings for the approximation argument

The reduction of Theorem 2.1 to smooth coefficients (Section 3.4 of the paper, second paragraph)
compares the laws of the original processes with those of the approximating processes through
explicit couplings, and passes to the limit with the triangle inequality for `W₂`. This file
provides the three ingredients, for the squared Wasserstein distance `wassersteinSq` of the
development on coordinate configurations.

* **Synchronous coupling** (`wassersteinSq_marginal_map_le`): for two random configurations
  `U, V` on the same probability space, the law of the pair `(U, V)`, restricted to the first `k`
  particles, couples the `k`-particle marginals, so
  `W₂²(Law(U)^{(k)}, Law(V)^{(k)}) ≤ E ∑ᵢ ‖Uᵢ - Vᵢ‖²`.
* **Product coupling** (`wassersteinSq_tensorLaw_map_le`): for two random points `U, V` of `ℝᵈ`
  on the same probability space, the `k`-fold product of the law of `(U, V)` couples the tensor
  powers, so `W₂²(Law(U)^{⊗k}, Law(V)^{⊗k}) ≤ k E ‖U - V‖²`.
* **Passage to the limit** (`wassersteinSq_le_of_tendsto`): if `W₂²(A, Aₙ) → 0`,
  `W₂²(Bₙ, B) → 0` and `W₂²(Aₙ, Bₙ) ≤ c` for every `n`, then `W₂²(A, B) ≤ c`, by the triangle
  inequality `wassersteinSq_root_triangle` for `√W₂²`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpWasserstein.Sharp.Final

variable {d N k : ℕ}

/-! ### The synchronous coupling -/

section Synchronous

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Synchronous coupling.** For random configurations `U, V` of `N` points of `ℝᵈ` on the same
probability space with `E ∑ᵢ ‖Uᵢ - Vᵢ‖² < ∞`, the coordinate laws satisfy
`W₂²(Law(U), Law(V)) ≤ E ∑ᵢ ‖Uᵢ - Vᵢ‖²`. -/
theorem wassersteinSq_map_le {U V : Ω → Fin N → EuclideanSpace ℝ (Fin d)}
    (hU : AEMeasurable U P) (hV : AEMeasurable V P)
    (hi : Integrable (fun ω => ∑ i, ‖U ω i - V ω i‖ ^ 2) P) :
    wassersteinSq ((P.map U).map (configurationEquiv d N))
        ((P.map V).map (configurationEquiv d N)) ≤
      ENNReal.ofReal (∫ ω, ∑ i, ‖U ω i - V ω i‖ ^ 2 ∂P) := by
  set e := configurationEquiv d N
  have he := e.measurable
  have hUV : AEMeasurable (fun ω => (e (U ω), e (V ω))) P :=
    (he.comp_aemeasurable hU).prodMk (he.comp_aemeasurable hV)
  have hcpl : IsCoupling ((P.map U).map e) ((P.map V).map e)
      (P.map fun ω => (e (U ω), e (V ω))) := by
    refine ⟨inferInstance, ?_, ?_⟩
    · rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hUV,
        AEMeasurable.map_map_of_aemeasurable he.aemeasurable hU]
      rfl
    · rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hUV,
        AEMeasurable.map_map_of_aemeasurable he.aemeasurable hV]
      rfl
  refine (wassersteinSq_le_cost hcpl).trans_eq ?_
  rw [transportCost, lintegral_map' measurable_productCost.ennreal_ofReal.aemeasurable hUV,
    ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun ω => Finset.sum_nonneg fun i _ => sq_nonneg _)]
  refine lintegral_congr fun ω => ?_
  simp only [e, productCost_configurationEquiv, SharpChaos.sqDist]

/-- **Synchronous coupling of marginals.** For random configurations `U, V` of `N` points of `ℝᵈ`
on the same probability space with `E ∑ᵢ ‖Uᵢ - Vᵢ‖² < ∞`, the `k`-particle marginals of the
coordinate laws satisfy `W₂²(Law(U)^{(k)}, Law(V)^{(k)}) ≤ E ∑ᵢ ‖Uᵢ - Vᵢ‖²`. -/
theorem wassersteinSq_marginal_map_le (hk : k ≤ N) {U V : Ω → Fin N → EuclideanSpace ℝ (Fin d)}
    (hU : AEMeasurable U P) (hV : AEMeasurable V P)
    (hi : Integrable (fun ω => ∑ i, ‖U ω i - V ω i‖ ^ 2) P) :
    wassersteinSq (marginal hk ((P.map U).map (configurationEquiv d N)))
        (marginal hk ((P.map V).map (configurationEquiv d N))) ≤
      ENNReal.ofReal (∫ ω, ∑ i, ‖U ω i - V ω i‖ ^ 2 ∂P) :=
  (wassersteinSq_marginal_le hk _ _).trans (wassersteinSq_map_le hU hV hi)

end Synchronous

/-! ### The product coupling -/

/-- The squared Euclidean distance `∑ₐ (xₐ - yₐ)²` between two points given by their coordinates,
as a function of the pair. -/
def pointCost (p : Position d × Position d) : ℝ :=
  ∑ a, (p.1 a - p.2 a) ^ 2

/-- The cost `pointCost` is nonnegative. -/
theorem pointCost_nonneg (p : Position d × Position d) : 0 ≤ pointCost p :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The cost `pointCost` is measurable. -/
theorem measurable_pointCost : Measurable (pointCost (d := d)) := by
  unfold pointCost
  fun_prop

/-- In coordinates, `pointCost` is the squared Euclidean distance. -/
theorem pointCost_positionEquiv (x y : EuclideanSpace ℝ (Fin d)) :
    pointCost (positionEquiv d x, positionEquiv d y) = ‖x - y‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, pointCost]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Real.norm_eq_abs, sq_abs]

/-- Splitting a configuration of pairs into a pair of configurations. -/
def unzipConfiguration (z : Fin k → Position d × Position d) :
    Configuration d k × Configuration d k :=
  (fun i => (z i).1, fun i => (z i).2)

/-- Splitting a configuration of pairs is measurable. -/
theorem measurable_unzipConfiguration : Measurable (unzipConfiguration (d := d) (k := k)) := by
  unfold unzipConfiguration
  fun_prop

/-- **Product coupling.** If `π` couples the laws `μ, ν` on `ℝᵈ` (in coordinates), then the
`k`-fold product of `π` couples the tensor powers, and
`W₂²(μ^{⊗k}, ν^{⊗k}) ≤ k ∫ ‖x - y‖² dπ(x, y)`. -/
theorem wassersteinSq_tensorLaw_le {μ ν : Measure (Position d)}
    {π : Measure (Position d × Position d)} [IsProbabilityMeasure π] (hμ : π.map Prod.fst = μ)
    (hν : π.map Prod.snd = ν) (k : ℕ) :
    wassersteinSq (tensorLaw μ k) (tensorLaw ν k) ≤ k * ∫⁻ p, ENNReal.ofReal (pointCost p) ∂π := by
  have hu := measurable_unzipConfiguration (d := d) (k := k)
  have hcpl : IsCoupling (tensorLaw μ k) (tensorLaw ν k)
      ((Measure.pi fun _ : Fin k => π).map unzipConfiguration) := by
    refine ⟨inferInstance, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hu, tensorLaw, ← hμ]
      exact Measure.pi_map_pi (f := fun _ => Prod.fst) fun _ => measurable_fst.aemeasurable
    · rw [Measure.map_map measurable_snd hu, tensorLaw, ← hν]
      exact Measure.pi_map_pi (f := fun _ => Prod.snd) fun _ => measurable_snd.aemeasurable
  refine (wassersteinSq_le_cost hcpl).trans_eq ?_
  have hc : ∀ i : Fin k, Measurable fun z : Fin k → Position d × Position d =>
      ENNReal.ofReal (pointCost (z i)) :=
    fun i => measurable_pointCost.ennreal_ofReal.comp (measurable_pi_apply i)
  rw [transportCost, lintegral_map measurable_productCost.ennreal_ofReal hu]
  calc ∫⁻ z, ENNReal.ofReal (productCost (unzipConfiguration z).1 (unzipConfiguration z).2)
        ∂(Measure.pi fun _ : Fin k => π)
      = ∫⁻ z, ∑ i, ENNReal.ofReal (pointCost (z i)) ∂(Measure.pi fun _ : Fin k => π) := by
        refine lintegral_congr fun z => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => pointCost_nonneg _]
        rfl
    _ = ∑ i : Fin k, ∫⁻ p, ENNReal.ofReal (pointCost p) ∂π := by
        rw [lintegral_finsetSum _ fun i _ => hc i]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (measurePreserving_eval (fun _ : Fin k => π) i).lintegral_comp
          measurable_pointCost.ennreal_ofReal
    _ = k * ∫⁻ p, ENNReal.ofReal (pointCost p) ∂π := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Product coupling of laws of random points.** For random points `U, V` of `ℝᵈ` on the same
probability space with `E ‖U - V‖² < ∞`, the tensor powers of the coordinate laws satisfy
`W₂²(Law(U)^{⊗k}, Law(V)^{⊗k}) ≤ k E ‖U - V‖²`. -/
theorem wassersteinSq_tensorLaw_map_le {U V : Ω → EuclideanSpace ℝ (Fin d)}
    (hU : AEMeasurable U P) (hV : AEMeasurable V P)
    (hi : Integrable (fun ω => ‖U ω - V ω‖ ^ 2) P) (k : ℕ) :
    wassersteinSq (tensorLaw ((P.map U).map (positionEquiv d)) k)
        (tensorLaw ((P.map V).map (positionEquiv d)) k) ≤
      ENNReal.ofReal (k * ∫ ω, ‖U ω - V ω‖ ^ 2 ∂P) := by
  set e := positionEquiv d
  have he := e.measurable
  have hUV : AEMeasurable (fun ω => (e (U ω), e (V ω))) P :=
    (he.comp_aemeasurable hU).prodMk (he.comp_aemeasurable hV)
  have hμ : (P.map fun ω => (e (U ω), e (V ω))).map Prod.fst = (P.map U).map e := by
    rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hUV,
      AEMeasurable.map_map_of_aemeasurable he.aemeasurable hU]
    rfl
  have hν : (P.map fun ω => (e (U ω), e (V ω))).map Prod.snd = (P.map V).map e := by
    rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hUV,
      AEMeasurable.map_map_of_aemeasurable he.aemeasurable hV]
    rfl
  refine (wassersteinSq_tensorLaw_le hμ hν k).trans_eq ?_
  rw [lintegral_map' measurable_pointCost.ennreal_ofReal.aemeasurable hUV,
    ENNReal.ofReal_mul (Nat.cast_nonneg k), ENNReal.ofReal_natCast,
    ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ω => sq_nonneg _)]
  congr 1
  refine lintegral_congr fun ω => ?_
  rw [pointCost_positionEquiv]

/-! ### Passage to the limit -/

/-- **Passage to the limit in the triangle inequality.** If `W₂²(A, Aₙ) ≤ εₙ → 0`,
`W₂²(Bₙ, B) ≤ δₙ → 0` and `W₂²(Aₙ, Bₙ) ≤ c` for every `n`, then `W₂²(A, B) ≤ c`. -/
theorem wassersteinSq_le_of_tendsto {A B : Measure (Configuration d k)}
    {Aₙ Bₙ : ℕ → Measure (Configuration d k)} {ε δ : ℕ → ℝ} {c : ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hδ : Tendsto δ atTop (𝓝 0))
    (h₁ : ∀ n, wassersteinSq A (Aₙ n) ≤ ENNReal.ofReal (ε n))
    (h₂ : ∀ n, wassersteinSq (Aₙ n) (Bₙ n) ≤ ENNReal.ofReal c)
    (h₃ : ∀ n, wassersteinSq (Bₙ n) B ≤ ENNReal.ofReal (δ n)) :
    wassersteinSq A B ≤ ENNReal.ofReal c := by
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  have hroot : ∀ {f : ℕ → ℝ}, Tendsto f atTop (𝓝 0) →
      Tendsto (fun n => ENNReal.ofReal (f n) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := fun {f} hf => by
    have h := ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto _).comp
      (ENNReal.tendsto_ofReal hf)
    rwa [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hr] at h
  have key : ∀ n, wassersteinSq A B ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (ε n) ^ (1 / 2 : ℝ) +
      ENNReal.ofReal c ^ (1 / 2 : ℝ) + ENNReal.ofReal (δ n) ^ (1 / 2 : ℝ) := fun n =>
    calc wassersteinSq A B ^ (1 / 2 : ℝ)
        ≤ wassersteinSq A (Aₙ n) ^ (1 / 2 : ℝ) + wassersteinSq (Aₙ n) B ^ (1 / 2 : ℝ) :=
          wassersteinSq_root_triangle _ _ _
      _ ≤ wassersteinSq A (Aₙ n) ^ (1 / 2 : ℝ) + (wassersteinSq (Aₙ n) (Bₙ n) ^ (1 / 2 : ℝ) +
          wassersteinSq (Bₙ n) B ^ (1 / 2 : ℝ)) := by
          gcongr
          exact wassersteinSq_root_triangle _ _ _
      _ ≤ ENNReal.ofReal (ε n) ^ (1 / 2 : ℝ) + (ENNReal.ofReal c ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (δ n) ^ (1 / 2 : ℝ)) := by
          gcongr
          · exact h₁ n
          · exact h₂ n
          · exact h₃ n
      _ = _ := (add_assoc _ _ _).symm
  have hlim : Tendsto (fun n => ENNReal.ofReal (ε n) ^ (1 / 2 : ℝ) +
      ENNReal.ofReal c ^ (1 / 2 : ℝ) + ENNReal.ofReal (δ n) ^ (1 / 2 : ℝ)) atTop
      (𝓝 (0 + ENNReal.ofReal c ^ (1 / 2 : ℝ) + 0)) :=
    ((hroot hε).add tendsto_const_nhds).add (hroot hδ)
  have h := ge_of_tendsto' hlim key
  rw [zero_add, add_zero] at h
  exact (ENNReal.rpow_le_rpow_iff hr).1 h

end SharpWasserstein.Sharp.Final
