import SharpWasserstein.BoundedFlow
import SharpWasserstein.RandomMapTransport
import SharpWasserstein.EuclideanDrift

/-! Constructed coordinatewise random flows, exact preservation of tensor
laws under independent noise, and synchronous transport stability. -/

noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal

namespace SharpWasserstein.DecoupledFlow

variable {d : ℕ} {v : ℝ → Position d → Position d} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
  (hl : ∀ t, LipschitzWith K (v t))

/-- Apply the constructed one-particle flow independently in every coordinate. -/
def solution {N : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (p : Configuration d N × (Fin N → C(Icc 0 T, Position d))) (t : ℝ) : Configuration d N :=
  fun i => BoundedFlow.flow hv hb hl hT (p.1 i) (p.2 i) t

theorem solution_coordinate_trajectory {N : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (p : Configuration d N × (Fin N → C(Icc 0 T, Position d))) (i : Fin N) :
    FiniteAdditiveTrajectory v (BoundedFlow.noiseExtension hT (p.2 i)) (p.1 i) T
      (fun t => solution hv hb hl hT p t i) :=
  BoundedFlow.flow_trajectory hv hb hl hT (p.1 i) (p.2 i)

theorem solution_measurable {N : ℕ} {T : ℝ}
    [MeasurableSpace C(Icc 0 T, Position d)] [BorelSpace C(Icc 0 T, Position d)]
    (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Measurable (fun p : Configuration d N × (Fin N → C(Icc 0 T, Position d)) =>
      solution hv hb hl hT p t) := by
  apply measurable_pi_lambda
  intro i
  have hi : Measurable (fun p : Configuration d N × (Fin N → C(Icc 0 T, Position d)) =>
      (p.1 i, p.2 i)) :=
    ((measurable_pi_apply i |>.comp measurable_fst).prodMk
      (measurable_pi_apply i |>.comp measurable_snd))
  exact (BoundedFlow.flow_continuous hv hb hl hT ht).measurable.comp hi

theorem solution_productCost_le {N : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (x y : Configuration d N) (w : Fin N → C(Icc 0 T, Position d))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    productCost (solution hv hb hl hT (x,w) t) (solution hv hb hl hT (y,w) t) ≤
      (d * Real.exp ((K : ℝ) * t) ^ 2) * productCost x y := by
  rw [productCost_eq_sum_positionSq, productCost_eq_sum_positionSq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := (solution_coordinate_trajectory hv hb hl hT (x,w) i).stability
    (fun s _ => hl s) (solution_coordinate_trajectory hv hb hl hT (y,w) i) ht
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 h
  calc
    positionSq (solution hv hb hl hT (x,w) t i - solution hv hb hl hT (y,w) t i) ≤
      d * ‖solution hv hb hl hT (x,w) t i - solution hv hb hl hT (y,w) t i‖ ^ 2 :=
        positionSq_le_norm_sq _
    _ ≤ d * (‖x i - y i‖ * Real.exp ((K : ℝ) * t)) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (d * Real.exp ((K : ℝ) * t) ^ 2) * ‖x i - y i‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_sq_le_positionSq _) (by positivity)

variable {N : ℕ} {T : ℝ} [MeasurableSpace C(Icc 0 T, Position d)]
  [BorelSpace C(Icc 0 T, Position d)]

/-- Flow a possibly correlated initial law with i.i.d. continuous input paths. -/
def law (hT : 0 ≤ T) (P : Measure (Configuration d N))
    (ξ : Measure C(Icc 0 T, Position d)) (t : ℝ) : Measure (Configuration d N) :=
  randomMapLaw (fun p => solution hv hb hl hT p t) P (Measure.pi fun _ : Fin N => ξ)

theorem law_probability (hT : 0 ≤ T) (P : Measure (Configuration d N))
    (ξ : Measure C(Icc 0 T, Position d)) [IsProbabilityMeasure P] [IsProbabilityMeasure ξ]
    {t : ℝ} (ht : t ∈ Icc 0 T) : IsProbabilityMeasure (law hv hb hl hT P ξ t) :=
  randomMapLaw_probability _ (solution_measurable hv hb hl hT ht) P _

/-- Exact tensor-law identity for the concrete coordinatewise solution. -/
theorem law_tensor (hT : 0 ≤ T) (μ : Measure (Position d))
    (ξ : Measure C(Icc 0 T, Position d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ξ]
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    law hv hb hl hT (tensorLaw μ N) ξ t =
      tensorLaw (Measure.map (fun p : Position d × C(Icc 0 T, Position d) =>
        BoundedFlow.flow hv hb hl hT p.1 p.2 t) (μ.prod ξ)) N := by
  let F : Position d × C(Icc 0 T, Position d) → Position d :=
    fun p => BoundedFlow.flow hv hb hl hT p.1 p.2 t
  have hF : Measurable F := (BoundedFlow.flow_continuous hv hb hl hT ht).measurable
  letI : IsProbabilityMeasure (Measure.map F (μ.prod ξ)) :=
    Measure.isProbabilityMeasure_map hF.aemeasurable
  have hU := measurePreserving_arrowProdEquivProdArrow (Position d)
    C(Icc 0 T, Position d) (Fin N) (fun _ => μ) (fun _ => ξ)
  unfold law randomMapLaw tensorLaw
  rw [← hU.map_eq, Measure.map_map (solution_measurable hv hb hl hT ht) hU.measurable]
  change Measure.map (fun q i => F (q i)) (Measure.pi fun _ : Fin N => μ.prod ξ) =
    Measure.pi fun _ : Fin N => Measure.map F (μ.prod ξ)
  exact Measure.pi_map_pi (fun _ => hF.aemeasurable)

/-- Synchronous coupling gives actual stability, uniformly in the level N. -/
theorem law_wassersteinSq_le (hT : 0 ≤ T) (P Q : Measure (Configuration d N))
    (ξ : Measure C(Icc 0 T, Position d))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure ξ]
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    wassersteinSq (law hv hb hl hT P ξ t) (law hv hb hl hT Q ξ t) ≤
      ENNReal.ofReal (d * Real.exp ((K : ℝ) * t) ^ 2) * wassersteinSq P Q := by
  exact wassersteinSq_randomMapLaw_le _ (solution_measurable hv hb hl hT ht) _ P Q
    (by positivity) (fun x y w => solution_productCost_le hv hb hl hT x y w ht)

end SharpWasserstein.DecoupledFlow
