/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import SharpWasserstein.Sharp.PathwiseEstimates

/-!
# Existence for McKean–Vlasov equations with bounded Lipschitz coefficients

Lemma 3.1 (`lem:wellposed`) of the paper asserts the well-posedness of the particle system and of
the McKean–Vlasov equation `dX_t = (a(X_t) + ∫ K(X_t, y) μ_t(dy)) dt + √2 dW_t`,
`μ_t = Law(X_t)`. This file proves the existence part, path by path and for an arbitrary
continuous forcing. Let `(Ω, P)` be a probability space, `ξ : Ω → E` a measurable initial value
and `B : ℝ → Ω → E` a forcing with continuous paths and measurable time sections (in the paper
`B = √2 W`). Assume that `‖a x‖ ≤ Ma`, `‖a x - a x'‖ ≤ La ‖x - x'‖`, `‖K x y‖ ≤ M` and
`‖K x y - K x' y'‖ ≤ L₁ ‖x - x'‖ + L₂ ‖y - y'‖`. Then there is a process `Y : ℝ → Ω → E` with
measurable time sections and continuous paths such that for all `ω` and `t ≥ 0`
`Y t ω = ξ ω + ∫₀ᵗ (a (Y s ω) + ∫ K (Y s ω) z d(Law Y s)(z)) ds + B t ω`.
The state space `E` is a complete second countable real normed space with its Borel σ-algebra,
for instance any finite-dimensional space such as `ℝ^d` or `(ℝ^d)^N`.

The proof is an explicit Picard iteration, without solving any ODE:
`Y⁰ t ω = ξ ω + B t ω` and
`Y^{k+1} t ω = ξ ω + ∫₀ᵗ (a (Yᵏ s ω) + ∫ K (Yᵏ s ω) (Yᵏ s ω') dP(ω')) ds + B t ω`,
where the law term is written as an integral over `Ω` (`integral_map` converts it back).

* Each iterate has measurable time sections and continuous paths. The drift along an iterate is
  continuous in time by dominated convergence and measurable in `ω`, hence jointly measurable
  (`stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable`), and its time integral is
  measurable in `ω` (`StronglyMeasurable.integral_prod_left`).
* Through the natural coupling of the laws of `Y s` and `Y' s`, if `‖Y s - Y' s‖ ≤ δ` on `Ω`,
  then the drifts along `Y` and `Y'` differ by at most `(La + L₁ + L₂) δ`. By induction, uniformly
  in `ω`, `‖Y^{k+1} t ω - Yᵏ t ω‖ ≤ (Ma + M) Λᵏ t^{k+1} / (k+1)!` with `Λ = La + L₁ + L₂`.
* These bounds are summable, so the iterates converge uniformly on `(-∞, T] × Ω` for every `T`.
  The limit has measurable sections and continuous paths, and it is a fixed point of the Picard
  step because the step is Lipschitz for the uniform distance.

The drift is frozen at negative times (the Picard step integrates up to `max t 0`), so that all
the paths are defined and continuous on `ℝ`; the equation is only asserted for `t ≥ 0`.

The case `K = 0` gives pathwise solutions of `x t = x₀ + ∫₀ᵗ a (x s) ds + w t`, as used for the
particle system on `E = Fin N → EuclideanSpace ℝ (Fin d)` with drift `b_N`. The solutions are
also stated in the form of `IsForcedSolution`, so that the estimates of
`SharpWasserstein.Sharp.PathwiseEstimates` apply to them; for `K = 0`, `IsForcedSolution.eqOn`
gives pathwise uniqueness.

## Main definitions

* `McKeanVlasov.CoeffBounds a K Ma La M L₁ L₂`: the boundedness and Lipschitz assumptions.
* `McKeanVlasov.drift`: the drift `a (Y s ω) + ∫ K (Y s ω) (Y s ω') dP(ω')` along a process.
* `McKeanVlasov.picardStep`, `McKeanVlasov.picardIter`, `McKeanVlasov.picardLimit`: the Picard
  step, the Picard iterates and their limit.

## Main statements

* `McKeanVlasov.norm_drift_sub_drift_le`: the Lipschitz bound through the natural coupling.
* `McKeanVlasov.norm_picardIter_succ_sub_le`: the Picard bound.
* `McKeanVlasov.picardLimit_eq_picardStep`: the limit is a fixed point of the Picard step.
* `McKeanVlasov.exists_solution`, `McKeanVlasov.exists_isForcedSolution`: existence for the
  McKean–Vlasov equation.
* `exists_pathwise_solution`, `exists_isForcedSolution`: existence in the case `K = 0`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Real
open scoped Nat

namespace SharpWasserstein.Sharp

variable {E : Type*} [NormedAddCommGroup E]

/-- A function `K : E → E → E` with `‖K x y - K x' y'‖ ≤ L₁ ‖x - x'‖ + L₂ ‖y - y'‖`, where
`L₁, L₂ ≥ 0`, is jointly continuous. -/
theorem continuous_uncurry_of_norm_sub_le {K : E → E → E} {L₁ L₂ : ℝ} (hL₁ : 0 ≤ L₁)
    (hL₂ : 0 ≤ L₂) (hK : ∀ x x' y y', ‖K x y - K x' y'‖ ≤ L₁ * ‖x - x'‖ + L₂ * ‖y - y'‖) :
    Continuous (Function.uncurry K) := by
  refine (LipschitzWith.of_dist_le_mul (K := ⟨L₁ + L₂, by positivity⟩) fun p q => ?_).continuous
  simp only [Function.uncurry, dist_eq_norm]
  calc ‖K p.1 p.2 - K q.1 q.2‖ ≤ L₁ * ‖p.1 - q.1‖ + L₂ * ‖p.2 - q.2‖ := hK _ _ _ _
    _ ≤ L₁ * ‖p - q‖ + L₂ * ‖p - q‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (norm_fst_le (p - q)) hL₁)
          (mul_le_mul_of_nonneg_left (norm_snd_le (p - q)) hL₂)
    _ = (L₁ + L₂) * ‖p - q‖ := by ring

namespace McKeanVlasov

/-- The standing assumptions on the coefficients of the McKean–Vlasov equation: the confinement
`a` is bounded by `Ma` and `La`-Lipschitz, and the interaction `K` is bounded by `M` and
Lipschitz with constants `L₁` in the first and `L₂` in the second variable. -/
structure CoeffBounds (a : E → E) (K : E → E → E) (Ma La M L₁ L₂ : ℝ) : Prop where
  /-- `‖a x‖ ≤ Ma`. -/
  norm_a_le : ∀ x, ‖a x‖ ≤ Ma
  /-- `‖a x - a x'‖ ≤ La ‖x - x'‖`. -/
  norm_a_sub_le : ∀ x x', ‖a x - a x'‖ ≤ La * ‖x - x'‖
  /-- `‖K x y‖ ≤ M`. -/
  norm_K_le : ∀ x y, ‖K x y‖ ≤ M
  /-- `‖K x y - K x' y'‖ ≤ L₁ ‖x - x'‖ + L₂ ‖y - y'‖`. -/
  norm_K_sub_le : ∀ x x' y y', ‖K x y - K x' y'‖ ≤ L₁ * ‖x - x'‖ + L₂ * ‖y - y'‖
  /-- `La ≥ 0`. -/
  La_nonneg : 0 ≤ La
  /-- `L₁ ≥ 0`. -/
  L₁_nonneg : 0 ≤ L₁
  /-- `L₂ ≥ 0`. -/
  L₂_nonneg : 0 ≤ L₂

namespace CoeffBounds

variable {a : E → E} {K : E → E → E} {Ma La M L₁ L₂ : ℝ}

/-- The confinement is continuous. -/
theorem continuous_a (h : CoeffBounds a K Ma La M L₁ L₂) : Continuous a :=
  (LipschitzWith.of_dist_le_mul (K := ⟨La, h.La_nonneg⟩) fun x x' => by
    rw [dist_eq_norm, dist_eq_norm]
    exact h.norm_a_sub_le x x').continuous

/-- The interaction is jointly continuous. -/
theorem continuous_K (h : CoeffBounds a K Ma La M L₁ L₂) : Continuous (Function.uncurry K) :=
  continuous_uncurry_of_norm_sub_le h.L₁_nonneg h.L₂_nonneg h.norm_K_sub_le

/-- The interaction is continuous in its second variable. -/
theorem continuous_K_apply (h : CoeffBounds a K Ma La M L₁ L₂) (x : E) : Continuous (K x) :=
  h.continuous_K.comp (continuous_const.prodMk continuous_id)

/-- `Ma ≥ 0`. -/
theorem Ma_nonneg (h : CoeffBounds a K Ma La M L₁ L₂) : 0 ≤ Ma :=
  (norm_nonneg _).trans (h.norm_a_le 0)

/-- `M ≥ 0`. -/
theorem M_nonneg (h : CoeffBounds a K Ma La M L₁ L₂) : 0 ≤ M :=
  (norm_nonneg _).trans (h.norm_K_le 0 0)

/-- The Lipschitz constant `La + L₁ + L₂` of the drift is nonnegative. -/
theorem lip_nonneg (h : CoeffBounds a K Ma La M L₁ L₂) : 0 ≤ La + L₁ + L₂ := by
  linarith [h.La_nonneg, h.L₁_nonneg, h.L₂_nonneg]

/-- The bound `Ma + M` of the drift is nonnegative. -/
theorem bound_nonneg (h : CoeffBounds a K Ma La M L₁ L₂) : 0 ≤ Ma + M := by
  linarith [h.Ma_nonneg, h.M_nonneg]

end CoeffBounds

/-- The majorant `C Λᵏ T^{k+1} / (k+1)!` of the distance between the Picard iterates `k + 1`
and `k` on `[0, T]`, with `C = Ma + M` and `Λ = La + L₁ + L₂`. -/
noncomputable def picardBound (C Λ T : ℝ) (k : ℕ) : ℝ :=
  C * Λ ^ k * T ^ (k + 1) / (k + 1)!

/-- The Picard majorants are summable: `C Λᵏ T^{k+1} / (k+1)! ≤ C T (ΛT)ᵏ / k!`. -/
theorem summable_picardBound {C Λ T : ℝ} (hC : 0 ≤ C) (hΛ : 0 ≤ Λ) (hT : 0 ≤ T) :
    Summable (picardBound C Λ T) := by
  refine Summable.of_nonneg_of_le (fun k => by unfold picardBound; positivity) (fun k => ?_)
    ((Real.summable_pow_div_factorial (Λ * T)).mul_left (C * T))
  rw [picardBound, show C * T * ((Λ * T) ^ k / (k ! : ℝ)) = C * Λ ^ k * T ^ (k + 1) / (k ! : ℝ)
    by ring]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (by exact_mod_cast Nat.factorial_le (Nat.le_succ k))

variable [NormedSpace ℝ E] {Ω : Type*} [MeasurableSpace Ω]

/-- The McKean–Vlasov drift along a process `Y`, with the law of `Y s` written as an integral
over `Ω`: `drift P a K Y s ω = a (Y s ω) + ∫ K (Y s ω) (Y s ω') dP(ω')`. By `integral_map`, the
second term is `∫ K (Y s ω) z d(Law Y s)(z)`, see `drift_eq`. -/
noncomputable def drift (P : Measure Ω) (a : E → E) (K : E → E → E) (Y : ℝ → Ω → E) (s : ℝ)
    (ω : Ω) : E :=
  a (Y s ω) + ∫ ω', K (Y s ω) (Y s ω') ∂P

/-- One step of the Picard iteration:
`picardStep P a K ξ B Y t ω = ξ ω + ∫₀^{max t 0} drift P a K Y s ω ds + B t ω`.
The upper limit `max t 0` freezes the drift for negative times, where all the iterates
coincide with `ξ + B`. -/
noncomputable def picardStep (P : Measure Ω) (a : E → E) (K : E → E → E) (ξ : Ω → E)
    (B : ℝ → Ω → E) (Y : ℝ → Ω → E) (t : ℝ) (ω : Ω) : E :=
  ξ ω + (∫ s in (0 : ℝ)..max t 0, drift P a K Y s ω) + B t ω

/-- The Picard iterates, starting from `Y⁰ t ω = ξ ω + B t ω`. -/
noncomputable def picardIter (P : Measure Ω) (a : E → E) (K : E → E → E) (ξ : Ω → E)
    (B : ℝ → Ω → E) : ℕ → ℝ → Ω → E
  | 0 => fun t ω => ξ ω + B t ω
  | k + 1 => picardStep P a K ξ B (picardIter P a K ξ B k)

/-- The pointwise limit of the Picard iterates (it exists, see `tendsto_picardIter`). -/
noncomputable def picardLimit (P : Measure Ω) (a : E → E) (K : E → E → E) (ξ : Ω → E)
    (B : ℝ → Ω → E) (t : ℝ) (ω : Ω) : E :=
  limUnder atTop fun k => picardIter P a K ξ B k t ω

variable {P : Measure Ω} {a : E → E} {K : E → E → E} {Ma La M L₁ L₂ : ℝ} {ξ : Ω → E}
  {B : ℝ → Ω → E} {Y Y' : ℝ → Ω → E}

/-- The zeroth Picard iterate is `ξ + B`. -/
@[simp]
theorem picardIter_zero (t : ℝ) (ω : Ω) : picardIter P a K ξ B 0 t ω = ξ ω + B t ω :=
  rfl

/-- The Picard iterate `k + 1` is the Picard step applied to the iterate `k`. -/
theorem picardIter_succ (k : ℕ) :
    picardIter P a K ξ B (k + 1) = picardStep P a K ξ B (picardIter P a K ξ B k) :=
  rfl

/-- The drift is bounded by `Ma + M`. -/
theorem norm_drift_le [IsProbabilityMeasure P] (h : CoeffBounds a K Ma La M L₁ L₂)
    (Y : ℝ → Ω → E) (s : ℝ) (ω : Ω) : ‖drift P a K Y s ω‖ ≤ Ma + M := by
  refine (norm_add_le _ _).trans (add_le_add (h.norm_a_le _) ?_)
  simpa using norm_integral_le_of_norm_le_const (μ := P)
    (Eventually.of_forall fun ω' => h.norm_K_le (Y s ω) (Y s ω'))

end McKeanVlasov

variable [NormedSpace ℝ E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Type*} [MeasurableSpace Ω]

/-- Continuity of `x ↦ ∫ K (G x) (U x ω) dP(ω)` for a bounded continuous `K`, by dominated
convergence. -/
theorem continuous_integral_comp (P : Measure Ω) [IsFiniteMeasure P] {K : E → E → E} {M : ℝ}
    (hK : Continuous (Function.uncurry K)) (hK_bdd : ∀ x y, ‖K x y‖ ≤ M)
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] {G : X → E} (hG : Continuous G)
    {U : X → Ω → E} (hUm : ∀ x, Measurable (U x)) (hUc : ∀ ω, Continuous fun x => U x ω) :
    Continuous fun x => ∫ ω, K (G x) (U x ω) ∂P := by
  refine continuous_of_dominated (bound := fun _ => M) (fun x => ?_)
    (fun x => Eventually.of_forall fun ω => hK_bdd _ _) (integrable_const M)
    (Eventually.of_forall fun ω => hK.comp (hG.prodMk (hUc ω)))
  exact ((hK.comp (continuous_const.prodMk continuous_id)).measurable.comp
    (hUm x)).aestronglyMeasurable

namespace McKeanVlasov

variable {P : Measure Ω} {a : E → E} {K : E → E → E} {Ma La M L₁ L₂ : ℝ} {ξ : Ω → E}
  {B : ℝ → Ω → E} {Y Y' : ℝ → Ω → E}

/-- The law term of the drift, written with the law `P.map (Y s)` of `Y s`. -/
theorem drift_eq (h : CoeffBounds a K Ma La M L₁ L₂) {s : ℝ} (hYm : Measurable (Y s))
    (ω : Ω) : drift P a K Y s ω = a (Y s ω) + ∫ z, K (Y s ω) z ∂(P.map (Y s)) := by
  rw [drift, integral_map hYm.aemeasurable (h.continuous_K_apply _).aestronglyMeasurable]

/-- The drift is measurable in `ω` if each `Y s` is measurable. -/
theorem measurable_drift [IsFiniteMeasure P] (h : CoeffBounds a K Ma La M L₁ L₂)
    (hYm : ∀ t, Measurable (Y t)) (s : ℝ) : Measurable (drift P a K Y s) := by
  have hc : Continuous fun x => ∫ ω', K x (Y s ω') ∂P :=
    continuous_integral_comp P h.continuous_K h.norm_K_le continuous_id (U := fun _ => Y s)
      (fun _ => hYm s) fun _ => continuous_const
  exact (h.continuous_a.measurable.comp (hYm s)).add (hc.measurable.comp (hYm s))

/-- The drift is continuous in `s` along a process with measurable sections and continuous
paths. -/
theorem continuous_drift [IsFiniteMeasure P] (h : CoeffBounds a K Ma La M L₁ L₂)
    (hYm : ∀ t, Measurable (Y t)) (hYc : ∀ ω, Continuous fun t => Y t ω) (ω : Ω) :
    Continuous fun s => drift P a K Y s ω :=
  (h.continuous_a.comp (hYc ω)).add
    (continuous_integral_comp P h.continuous_K h.norm_K_le (hYc ω) hYm hYc)

/-- The drift is jointly strongly measurable in `(s, ω)`. -/
theorem stronglyMeasurable_uncurry_drift [IsFiniteMeasure P]
    (h : CoeffBounds a K Ma La M L₁ L₂) (hYm : ∀ t, Measurable (Y t))
    (hYc : ∀ ω, Continuous fun t => Y t ω) :
    StronglyMeasurable (Function.uncurry (drift P a K Y)) :=
  stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (fun ω => continuous_drift h hYm hYc ω) fun s => (measurable_drift h hYm s).stronglyMeasurable

/-- **Lipschitz bound in the law through the natural coupling.** If `‖Y s - Y' s‖ ≤ δ`
everywhere on `Ω`, then the drifts along `Y` and `Y'` differ by at most `(La + L₁ + L₂) δ`. -/
theorem norm_drift_sub_drift_le [IsProbabilityMeasure P] (h : CoeffBounds a K Ma La M L₁ L₂)
    {s δ : ℝ} (hYm : Measurable (Y s)) (hY'm : Measurable (Y' s))
    (hδ : ∀ ω, ‖Y s ω - Y' s ω‖ ≤ δ) (ω : Ω) :
    ‖drift P a K Y s ω - drift P a K Y' s ω‖ ≤ (La + L₁ + L₂) * δ := by
  have hint : ∀ U : Ω → E, Measurable U → ∀ x, Integrable (fun ω' => K x (U ω')) P :=
    fun U hU x => Integrable.of_bound ((h.continuous_K_apply x).measurable.comp
      hU).aestronglyMeasurable M (Eventually.of_forall fun _ => h.norm_K_le _ _)
  have h1 : ‖a (Y s ω) - a (Y' s ω)‖ ≤ La * δ :=
    (h.norm_a_sub_le _ _).trans (mul_le_mul_of_nonneg_left (hδ ω) h.La_nonneg)
  have h2 : ‖∫ ω', K (Y s ω) (Y s ω') ∂P - ∫ ω', K (Y' s ω) (Y' s ω') ∂P‖ ≤
      (L₁ + L₂) * δ := by
    rw [← integral_sub (hint _ hYm _) (hint _ hY'm _)]
    have := norm_integral_le_of_norm_le_const (μ := P) (C := (L₁ + L₂) * δ)
      (f := fun ω' => K (Y s ω) (Y s ω') - K (Y' s ω) (Y' s ω'))
      (Eventually.of_forall fun ω' => by
        calc _ ≤ L₁ * ‖Y s ω - Y' s ω‖ + L₂ * ‖Y s ω' - Y' s ω'‖ := h.norm_K_sub_le _ _ _ _
          _ ≤ L₁ * δ + L₂ * δ :=
              add_le_add (mul_le_mul_of_nonneg_left (hδ ω) h.L₁_nonneg)
                (mul_le_mul_of_nonneg_left (hδ ω') h.L₂_nonneg)
          _ = (L₁ + L₂) * δ := by ring)
    simpa using this
  calc ‖drift P a K Y s ω - drift P a K Y' s ω‖
      = ‖(a (Y s ω) - a (Y' s ω)) +
          (∫ ω', K (Y s ω) (Y s ω') ∂P - ∫ ω', K (Y' s ω) (Y' s ω') ∂P)‖ := by
        unfold drift; congr 1; abel
    _ ≤ La * δ + (L₁ + L₂) * δ := (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = (La + L₁ + L₂) * δ := by ring

/-! ### The Picard step -/

/-- The Picard step of a process with measurable sections and continuous paths has measurable
sections: the time integral of the jointly measurable drift is measurable in `ω`. -/
theorem measurable_picardStep [IsFiniteMeasure P] (h : CoeffBounds a K Ma La M L₁ L₂)
    (hξ : Measurable ξ) (hBm : ∀ t, Measurable (B t)) (hYm : ∀ t, Measurable (Y t))
    (hYc : ∀ ω, Continuous fun t => Y t ω) (t : ℝ) :
    Measurable (picardStep P a K ξ B Y t) := by
  have hint : Measurable fun ω => ∫ s in (0 : ℝ)..max t 0, drift P a K Y s ω := by
    simp_rw [intervalIntegral.integral_of_le (le_max_right t 0)]
    exact ((stronglyMeasurable_uncurry_drift h hYm hYc).integral_prod_left
      (μ := volume.restrict (Ioc 0 (max t 0)))).measurable
  exact (hξ.add hint).add (hBm t)

/-- The Picard step of a process with measurable sections and continuous paths has continuous
paths. -/
theorem continuous_picardStep [IsFiniteMeasure P] (h : CoeffBounds a K Ma La M L₁ L₂)
    (hBc : ∀ ω, Continuous fun t => B t ω) (hYm : ∀ t, Measurable (Y t))
    (hYc : ∀ ω, Continuous fun t => Y t ω) (ω : Ω) :
    Continuous fun t => picardStep P a K ξ B Y t ω := by
  have hprim : Continuous fun T => ∫ s in (0 : ℝ)..T, drift P a K Y s ω :=
    intervalIntegral.continuous_primitive
      (fun _ _ => (continuous_drift h hYm hYc ω).intervalIntegrable _ _) 0
  exact (continuous_const.add (hprim.comp (continuous_id.max continuous_const))).add (hBc ω)

/-- **Contraction estimate for the Picard step.** If `‖Y s - Y' s‖ ≤ g s` on `Ω` for
`s ∈ [0, max t 0]`, then
`‖picardStep Y t ω - picardStep Y' t ω‖ ≤ (La + L₁ + L₂) ∫₀^{max t 0} g`. -/
theorem norm_picardStep_sub_le [IsProbabilityMeasure P] (h : CoeffBounds a K Ma La M L₁ L₂)
    (hYm : ∀ t, Measurable (Y t)) (hYc : ∀ ω, Continuous fun t => Y t ω)
    (hY'm : ∀ t, Measurable (Y' t)) (hY'c : ∀ ω, Continuous fun t => Y' t ω) {g : ℝ → ℝ}
    {t : ℝ} (hg : IntervalIntegrable g volume 0 (max t 0))
    (hle : ∀ s ∈ Icc 0 (max t 0), ∀ ω, ‖Y s ω - Y' s ω‖ ≤ g s) (ω : Ω) :
    ‖picardStep P a K ξ B Y t ω - picardStep P a K ξ B Y' t ω‖ ≤
      (La + L₁ + L₂) * ∫ s in (0 : ℝ)..max t 0, g s := by
  have heq : picardStep P a K ξ B Y t ω - picardStep P a K ξ B Y' t ω =
      ∫ s in (0 : ℝ)..max t 0, (drift P a K Y s ω - drift P a K Y' s ω) := by
    rw [intervalIntegral.integral_sub ((continuous_drift h hYm hYc ω).intervalIntegrable _ _)
      ((continuous_drift h hY'm hY'c ω).intervalIntegrable _ _)]
    unfold picardStep
    abel
  rw [heq, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le (le_max_right t 0)
    (Eventually.of_forall fun s hs => ?_) (hg.const_mul _)
  exact norm_drift_sub_drift_le h (hYm s) (hY'm s) (hle s ⟨hs.1.le, hs.2⟩) ω

/-! ### The Picard iterates -/

/-- The Picard iterates have measurable sections and continuous paths. -/
theorem measurable_and_continuous_picardIter [IsFiniteMeasure P]
    (h : CoeffBounds a K Ma La M L₁ L₂) (hξ : Measurable ξ) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (k : ℕ) :
    (∀ t, Measurable (picardIter P a K ξ B k t)) ∧
      ∀ ω, Continuous fun t => picardIter P a K ξ B k t ω := by
  induction k with
  | zero => exact ⟨fun t => hξ.add (hBm t), fun ω => continuous_const.add (hBc ω)⟩
  | succ k ih =>
    exact ⟨measurable_picardStep h hξ hBm ih.1 ih.2, continuous_picardStep h hBc ih.1 ih.2⟩

/-- The Picard iterates have measurable sections. -/
theorem measurable_picardIter [IsFiniteMeasure P] (h : CoeffBounds a K Ma La M L₁ L₂)
    (hξ : Measurable ξ) (hBm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω)
    (k : ℕ) (t : ℝ) : Measurable (picardIter P a K ξ B k t) :=
  (measurable_and_continuous_picardIter h hξ hBm hBc k).1 t

/-- The Picard iterates have continuous paths. -/
theorem continuous_picardIter [IsFiniteMeasure P] (h : CoeffBounds a K Ma La M L₁ L₂)
    (hξ : Measurable ξ) (hBm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω)
    (k : ℕ) (ω : Ω) : Continuous fun t => picardIter P a K ξ B k t ω :=
  (measurable_and_continuous_picardIter h hξ hBm hBc k).2 ω

/-- **The Picard bound.** Uniformly in `ω`,
`‖Y^{k+1} t ω - Yᵏ t ω‖ ≤ (Ma + M) (La + L₁ + L₂)ᵏ (max t 0)^{k+1} / (k+1)!`. -/
theorem norm_picardIter_succ_sub_le [IsProbabilityMeasure P]
    (h : CoeffBounds a K Ma La M L₁ L₂) (hξ : Measurable ξ) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (k : ℕ) (t : ℝ) (ω : Ω) :
    ‖picardIter P a K ξ B (k + 1) t ω - picardIter P a K ξ B k t ω‖ ≤
      picardBound (Ma + M) (La + L₁ + L₂) (max t 0) k := by
  induction k generalizing t ω with
  | zero =>
    have heq : picardIter P a K ξ B 1 t ω - picardIter P a K ξ B 0 t ω =
        ∫ s in (0 : ℝ)..max t 0, drift P a K (picardIter P a K ξ B 0) s ω := by
      rw [picardIter_succ, picardStep, picardIter_zero]
      abel
    rw [heq]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const fun s _ =>
      norm_drift_le h _ s ω).trans_eq ?_
    rw [sub_zero, abs_of_nonneg (le_max_right t 0)]
    simp [picardBound]
  | succ k ih =>
    have hk := measurable_and_continuous_picardIter h hξ hBm hBc (P := P) (a := a) (K := K)
    set Λ := La + L₁ + L₂
    set C := Ma + M
    refine (norm_picardStep_sub_le h (hk (k + 1)).1 (hk (k + 1)).2 (hk k).1 (hk k).2
      (g := fun s => C * Λ ^ k / (k + 1)! * s ^ (k + 1))
      (Continuous.intervalIntegrable (by fun_prop) _ _) (fun s hs ω' => ?_) ω).trans_eq ?_
    · refine (ih s ω').trans_eq ?_
      rw [max_eq_left hs.1, picardBound]
      ring
    · rw [intervalIntegral.integral_const_mul, integral_pow, picardBound,
        Nat.factorial_succ (k + 1)]
      push_cast
      field_simp
      ring

/-- The Picard bound on `[0, T]`, for `t ≤ T`. -/
theorem norm_picardIter_succ_sub_le_of_le [IsProbabilityMeasure P]
    (h : CoeffBounds a K Ma La M L₁ L₂) (hξ : Measurable ξ) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) {T t : ℝ} (hT : 0 ≤ T) (ht : t ≤ T) (k : ℕ)
    (ω : Ω) :
    ‖picardIter P a K ξ B (k + 1) t ω - picardIter P a K ξ B k t ω‖ ≤
      picardBound (Ma + M) (La + L₁ + L₂) T k := by
  refine (norm_picardIter_succ_sub_le h hξ hBm hBc k t ω).trans ?_
  unfold picardBound
  have := h.bound_nonneg
  have := h.lip_nonneg
  gcongr
  exact max_le ht hT

/-- The Picard iterates converge pointwise to `picardLimit`. -/
theorem tendsto_picardIter [CompleteSpace E] [IsProbabilityMeasure P]
    (h : CoeffBounds a K Ma La M L₁ L₂) (hξ : Measurable ξ) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (t : ℝ) (ω : Ω) :
    Tendsto (fun k => picardIter P a K ξ B k t ω) atTop (𝓝 (picardLimit P a K ξ B t ω)) := by
  have hc : CauchySeq fun k => picardIter P a K ξ B k t ω :=
    cauchySeq_of_dist_le_of_summable _ (fun k => by
      rw [dist_comm, dist_eq_norm]
      exact norm_picardIter_succ_sub_le h hξ hBm hBc k t ω)
      (summable_picardBound h.bound_nonneg h.lip_nonneg (le_max_right t 0))
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete hc)

/-- **Uniform convergence of the Picard iterates.** For `t ≤ T` with `T ≥ 0` and every `ω`,
`‖Yⁿ t ω - Y t ω‖` is bounded by the tail `∑_{m} picardBound (Ma + M) (La + L₁ + L₂) T (m + n)`,
which tends to `0` as `n → ∞`. -/
theorem norm_picardIter_sub_picardLimit_le [CompleteSpace E] [IsProbabilityMeasure P]
    (h : CoeffBounds a K Ma La M L₁ L₂) (hξ : Measurable ξ) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) {T t : ℝ} (hT : 0 ≤ T) (ht : t ≤ T) (n : ℕ)
    (ω : Ω) :
    ‖picardIter P a K ξ B n t ω - picardLimit P a K ξ B t ω‖ ≤
      ∑' m, picardBound (Ma + M) (La + L₁ + L₂) T (m + n) := by
  rw [← dist_eq_norm]
  refine (dist_le_tsum_of_dist_le_of_tendsto _ (fun k => ?_)
    (summable_picardBound h.bound_nonneg h.lip_nonneg hT) (tendsto_picardIter h hξ hBm hBc t ω)
    n).trans_eq (tsum_congr fun m => by rw [add_comm n m])
  rw [dist_comm, dist_eq_norm]
  exact norm_picardIter_succ_sub_le_of_le h hξ hBm hBc hT ht k ω

/-- The limit of the Picard iterates has measurable sections. -/
theorem measurable_picardLimit [CompleteSpace E] [IsProbabilityMeasure P]
    (h : CoeffBounds a K Ma La M L₁ L₂) (hξ : Measurable ξ) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (t : ℝ) : Measurable (picardLimit P a K ξ B t) :=
  measurable_of_tendsto_metrizable (fun k => measurable_picardIter h hξ hBm hBc k t)
    (tendsto_pi_nhds.2 fun ω => tendsto_picardIter h hξ hBm hBc t ω)

/-- The limit of the Picard iterates has continuous paths: the convergence is locally uniform
in time. -/
theorem continuous_picardLimit [CompleteSpace E] [IsProbabilityMeasure P]
    (h : CoeffBounds a K Ma La M L₁ L₂) (hξ : Measurable ξ) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (ω : Ω) :
    Continuous fun t => picardLimit P a K ξ B t ω := by
  refine TendstoLocallyUniformly.continuous (F := fun k t => picardIter P a K ξ B k t ω)
    (p := atTop) ?_ (Frequently.of_forall fun k => continuous_picardIter h hξ hBm hBc k ω)
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  have hT : (0 : ℝ) ≤ max x 0 + 1 := by positivity
  refine ⟨Iio (max x 0 + 1), Iio_mem_nhds ((le_max_left x 0).trans_lt (lt_add_one _)), ?_⟩
  filter_upwards [(tendsto_sum_nat_add (picardBound (Ma + M) (La + L₁ + L₂)
    (max x 0 + 1))).eventually (gt_mem_nhds hε)] with n hn y hy
  rw [dist_comm, dist_eq_norm]
  exact (norm_picardIter_sub_picardLimit_le h hξ hBm hBc hT (le_of_lt hy) n ω).trans_lt hn

/-- **The limit of the Picard iterates is a fixed point of the Picard step.** -/
theorem picardLimit_eq_picardStep [CompleteSpace E] [IsProbabilityMeasure P]
    (h : CoeffBounds a K Ma La M L₁ L₂) (hξ : Measurable ξ) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (t : ℝ) (ω : Ω) :
    picardLimit P a K ξ B t ω = picardStep P a K ξ B (picardLimit P a K ξ B) t ω := by
  have hT : 0 ≤ max t 0 := le_max_right t 0
  set tail : ℕ → ℝ := fun n => ∑' m, picardBound (Ma + M) (La + L₁ + L₂) (max t 0) (m + n)
  have h1 : Tendsto (fun k => picardIter P a K ξ B (k + 1) t ω) atTop
      (𝓝 (picardLimit P a K ξ B t ω)) :=
    (tendsto_picardIter h hξ hBm hBc t ω).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun k => picardIter P a K ξ B (k + 1) t ω) atTop
      (𝓝 (picardStep P a K ξ B (picardLimit P a K ξ B) t ω)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n => (La + L₁ + L₂) * (max t 0 * tail n)) atTop (𝓝 0) := by
      simpa using ((tendsto_sum_nat_add (picardBound (Ma + M) (La + L₁ + L₂)
        (max t 0))).const_mul (max t 0)).const_mul (La + L₁ + L₂)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim
    have := norm_picardStep_sub_le (P := P) (ξ := ξ) (B := B) h
      (measurable_picardIter h hξ hBm hBc n) (continuous_picardIter h hξ hBm hBc n)
      (measurable_picardLimit (P := P) h hξ hBm hBc)
      (continuous_picardLimit (P := P) h hξ hBm hBc)
      (g := fun _ => tail n) intervalIntegrable_const
      (fun s hs ω' => norm_picardIter_sub_picardLimit_le h hξ hBm hBc hT hs.2 n ω') ω
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    exact this
  exact tendsto_nhds_unique h1 h2

/-- For every `ω` and `T`, the path of the limit `Y` of the Picard iterates solves on `[0, T]`
the integral equation with drift `u s x = a x + ∫ K x z d(Law Y s)(z)` and forcing `B · ω`, in the
sense of `IsForcedSolution`. -/
theorem isForcedSolution_picardLimit [CompleteSpace E] [IsProbabilityMeasure P]
    (h : CoeffBounds a K Ma La M L₁ L₂) (hξ : Measurable ξ) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (ω : Ω) (T : ℝ) :
    IsForcedSolution (fun s x => a x + ∫ z, K x z ∂(P.map (picardLimit P a K ξ B s)))
      (fun t => B t ω) (ξ ω) T (fun t => picardLimit P a K ξ B t ω) := by
  have hYm := measurable_picardLimit (P := P) h hξ hBm hBc
  have hYc := continuous_picardLimit (P := P) h hξ hBm hBc
  have hdrift : ∀ s, a (picardLimit P a K ξ B s ω) +
      ∫ z, K (picardLimit P a K ξ B s ω) z ∂(P.map (picardLimit P a K ξ B s)) =
        drift P a K (picardLimit P a K ξ B) s ω := fun s => (drift_eq h (hYm s) ω).symm
  refine ⟨(hYc ω).continuousOn, (hBc ω).continuousOn, ?_, fun t ht => ?_⟩
  · simp only [hdrift]
    exact (continuous_drift h hYm hYc ω).continuousOn
  · simp only [hdrift]
    rw [picardLimit_eq_picardStep h hξ hBm hBc t ω, picardStep, max_eq_left ht.1]

end McKeanVlasov

/-! ### Existence -/

/-- **Existence for the McKean–Vlasov equation** (Lemma 3.1 of the paper, existence part), in
the form of `IsForcedSolution`. Let `a` be bounded and `La`-Lipschitz, and let `K` be bounded with
`‖K x y - K x' y'‖ ≤ L₁ ‖x - x'‖ + L₂ ‖y - y'‖`. For a measurable initial value `ξ` and a forcing
`B` with continuous paths and measurable time sections, there is a process `Y` with measurable
time sections and continuous paths such that, for every `ω` and `T`, the path `Y · ω` solves on
`[0, T]` the equation with drift `u s x = a x + ∫ K x z d(Law Y s)(z)` and forcing `B · ω`. -/
theorem McKeanVlasov.exists_isForcedSolution [CompleteSpace E] (P : Measure Ω)
    [IsProbabilityMeasure P] {ξ : Ω → E} (hξ : Measurable ξ) {B : ℝ → Ω → E}
    (hBc : ∀ ω, Continuous fun t => B t ω) (hBm : ∀ t, Measurable (B t)) {a : E → E}
    {Ma La : ℝ} (ha_bdd : ∀ x, ‖a x‖ ≤ Ma) (ha_lip : ∀ x x', ‖a x - a x'‖ ≤ La * ‖x - x'‖)
    (hLa : 0 ≤ La) {K : E → E → E} {M L₁ L₂ : ℝ} (hK_bdd : ∀ x y, ‖K x y‖ ≤ M)
    (hK_lip : ∀ x x' y y', ‖K x y - K x' y'‖ ≤ L₁ * ‖x - x'‖ + L₂ * ‖y - y'‖)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    ∃ Y : ℝ → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous fun t => Y t ω) ∧
      ∀ ω T, IsForcedSolution (fun s x => a x + ∫ z, K x z ∂(P.map (Y s))) (fun t => B t ω)
        (ξ ω) T (fun t => Y t ω) := by
  have h : McKeanVlasov.CoeffBounds a K Ma La M L₁ L₂ :=
    ⟨ha_bdd, ha_lip, hK_bdd, hK_lip, hLa, hL₁, hL₂⟩
  exact ⟨McKeanVlasov.picardLimit P a K ξ B, McKeanVlasov.measurable_picardLimit h hξ hBm hBc,
    McKeanVlasov.continuous_picardLimit h hξ hBm hBc,
    McKeanVlasov.isForcedSolution_picardLimit h hξ hBm hBc⟩

/-- **Existence for the McKean–Vlasov equation** (Lemma 3.1 of the paper, existence part). Let
`a` be bounded and `La`-Lipschitz, and let `K` be bounded with
`‖K x y - K x' y'‖ ≤ L₁ ‖x - x'‖ + L₂ ‖y - y'‖`. For a measurable initial value `ξ` and a forcing
`B` with continuous paths and measurable time sections, there is a process `Y` with measurable
time sections and continuous paths such that for all `ω` and `t ≥ 0`
`Y t ω = ξ ω + ∫₀ᵗ (a (Y s ω) + ∫ K (Y s ω) z d(Law Y s)(z)) ds + B t ω`.

The process is the limit of the Picard iterates `McKeanVlasov.picardIter`. -/
theorem McKeanVlasov.exists_solution [CompleteSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    {ξ : Ω → E} (hξ : Measurable ξ) {B : ℝ → Ω → E} (hBc : ∀ ω, Continuous fun t => B t ω)
    (hBm : ∀ t, Measurable (B t)) {a : E → E} {Ma La : ℝ} (ha_bdd : ∀ x, ‖a x‖ ≤ Ma)
    (ha_lip : ∀ x x', ‖a x - a x'‖ ≤ La * ‖x - x'‖) (hLa : 0 ≤ La) {K : E → E → E}
    {M L₁ L₂ : ℝ} (hK_bdd : ∀ x y, ‖K x y‖ ≤ M)
    (hK_lip : ∀ x x' y y', ‖K x y - K x' y'‖ ≤ L₁ * ‖x - x'‖ + L₂ * ‖y - y'‖)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    ∃ Y : ℝ → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous fun t => Y t ω) ∧
      ∀ ω t, 0 ≤ t → Y t ω = ξ ω +
        (∫ s in (0 : ℝ)..t, (a (Y s ω) + ∫ z, K (Y s ω) z ∂(P.map (Y s)))) + B t ω := by
  obtain ⟨Y, hYm, hYc, hY⟩ :=
    McKeanVlasov.exists_isForcedSolution P hξ hBc hBm ha_bdd ha_lip hLa hK_bdd hK_lip hL₁ hL₂
  exact ⟨Y, hYm, hYc, fun ω t ht => (hY ω t).eq_add_integral t ⟨ht, le_rfl⟩⟩

/-- **Existence of pathwise solutions with additive forcing**, the case `K = 0` (used for the
particle system). Let `a` be bounded and `La`-Lipschitz. For a measurable initial value `ξ` and a
forcing `B` with continuous paths and measurable time sections, there is a process `Y` with
measurable time sections and continuous paths such that for every `ω` and `T`, the path `Y · ω`
solves `x t = ξ ω + ∫₀ᵗ a (x s) ds + B t ω` on `[0, T]` in the sense of `IsForcedSolution`. -/
theorem exists_isForcedSolution [CompleteSpace E] {ξ : Ω → E} (hξ : Measurable ξ)
    {B : ℝ → Ω → E} (hBc : ∀ ω, Continuous fun t => B t ω) (hBm : ∀ t, Measurable (B t))
    {a : E → E} {Ma La : ℝ} (ha_bdd : ∀ x, ‖a x‖ ≤ Ma)
    (ha_lip : ∀ x x', ‖a x - a x'‖ ≤ La * ‖x - x'‖) (hLa : 0 ≤ La) :
    ∃ Y : ℝ → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous fun t => Y t ω) ∧
      ∀ ω T, IsForcedSolution (fun _ => a) (fun t => B t ω) (ξ ω) T (fun t => Y t ω) := by
  rcases isEmpty_or_nonempty Ω with hΩ | ⟨⟨ω₀⟩⟩
  · exact ⟨fun _ _ => 0, fun _ => measurable_const, fun ω => isEmptyElim ω,
      fun ω => isEmptyElim ω⟩
  obtain ⟨Y, hYm, hYc, hY⟩ := McKeanVlasov.exists_isForcedSolution (Measure.dirac ω₀) hξ hBc
    hBm ha_bdd ha_lip hLa (K := fun _ _ => 0) (M := 0) (L₁ := 0) (L₂ := 0) (fun _ _ => by simp)
    (fun _ _ _ _ => by simp) le_rfl le_rfl
  refine ⟨Y, hYm, hYc, fun ω T => ?_⟩
  simpa using hY ω T

/-- **Existence of pathwise solutions with additive forcing**, the case `K = 0` (used for the
particle system). Let `a` be bounded and `La`-Lipschitz. For a measurable initial value `ξ` and a
forcing `B` with continuous paths and measurable time sections, there is a process `Y` with
measurable time sections and continuous paths such that for all `ω` and `t ≥ 0`
`Y t ω = ξ ω + ∫₀ᵗ a (Y s ω) ds + B t ω`. -/
theorem exists_pathwise_solution [CompleteSpace E] {ξ : Ω → E} (hξ : Measurable ξ)
    {B : ℝ → Ω → E} (hBc : ∀ ω, Continuous fun t => B t ω) (hBm : ∀ t, Measurable (B t))
    {a : E → E} {Ma La : ℝ} (ha_bdd : ∀ x, ‖a x‖ ≤ Ma)
    (ha_lip : ∀ x x', ‖a x - a x'‖ ≤ La * ‖x - x'‖) (hLa : 0 ≤ La) :
    ∃ Y : ℝ → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous fun t => Y t ω) ∧
      ∀ ω t, 0 ≤ t → Y t ω = ξ ω + (∫ s in (0 : ℝ)..t, a (Y s ω)) + B t ω := by
  obtain ⟨Y, hYm, hYc, hY⟩ := exists_isForcedSolution hξ hBc hBm ha_bdd ha_lip hLa
  exact ⟨Y, hYm, hYc, fun ω t ht => (hY ω t).eq_add_integral t ⟨ht, le_rfl⟩⟩

end SharpWasserstein.Sharp
