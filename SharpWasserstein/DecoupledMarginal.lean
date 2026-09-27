import SharpWasserstein.DecoupledFlow
import SharpWasserstein.BrownianProductNoise

/-! Exact marginal and permutation commutation of the constructed coordinatewise
flow under independent continuous noise. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace SharpWasserstein.DecoupledFlow

variable {d : ℕ} {v : ℝ → Position d → Position d} {M K : ℝ≥0}
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
    (hl : ∀ t, LipschitzWith K (v t))
    {T : ℝ} [MeasurableSpace C(Icc 0 T, Position d)] [BorelSpace C(Icc 0 T, Position d)]

/-- Every marginal evolves by the same actual decoupled transition. -/
theorem law_marginal {m N : ℕ} (hm : m ≤ N) (hT : 0 ≤ T)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (ξ : Measure C(Icc 0 T, Position d)) [IsProbabilityMeasure ξ]
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    marginal hm (law hv hb hl hT P ξ t) = law hv hb hl hT (marginal hm P) ξ t := by
  let R : (Fin N → C(Icc 0 T, Position d)) → Fin m → C(Icc 0 T, Position d) :=
    fun w i ↦ w (Fin.castLE hm i)
  have hR : Measurable R := measurable_pi_lambda _ fun i ↦ measurable_pi_apply _
  have hinput : (P.prod (Measure.pi fun _ : Fin N ↦ ξ)).map (Prod.map (restrictCoordinates hm) R) =
      (marginal hm P).prod (Measure.pi fun _ : Fin m ↦ ξ) := by
    rw [← Measure.map_prod_map P _ (measurable_restrictCoordinates hm) hR]
    rw [probability_pi_map_prefix ξ hm]
    rfl
  dsimp only [marginal] at hinput
  unfold marginal law randomMapLaw
  rw [Measure.map_map (measurable_restrictCoordinates hm) (solution_measurable hv hb hl hT ht)]
  rw [← hinput, Measure.map_map (solution_measurable hv hb hl hT ht)
    ((measurable_restrictCoordinates hm).prodMap hR)]
  rfl

/-- Exchangeability survives the actual independent-noise coordinatewise flow. -/
theorem law_exchangeable {N : ℕ} (hT : 0 ≤ T)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P] (hP : Exchangeable P)
    (ξ : Measure C(Icc 0 T, Position d)) [IsProbabilityMeasure ξ]
    {t : ℝ} (ht : t ∈ Icc 0 T) : Exchangeable (law hv hb hl hT P ξ t) := by
  intro e
  let R : (Fin N → C(Icc 0 T, Position d)) → Fin N → C(Icc 0 T, Position d) := fun w i ↦ w (e i)
  let S : Configuration d N → Configuration d N := fun x i ↦ x (e i)
  have hR : Measurable R := measurable_pi_lambda _ fun i ↦ measurable_pi_apply _
  have hS : Measurable S := measurable_pi_lambda _ fun i ↦ measurable_pi_apply _
  have hnoise : (Measure.pi fun _ : Fin N ↦ ξ).map R = Measure.pi fun _ : Fin N ↦ ξ := by
    simpa [R, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft'] using
      (measurePreserving_piCongrLeft (fun _ : Fin N ↦ ξ) e.symm).map_eq
  have hinput : (P.prod (Measure.pi fun _ : Fin N ↦ ξ)).map (Prod.map S R) =
      P.prod (Measure.pi fun _ : Fin N ↦ ξ) := by
    rw [← Measure.map_prod_map P _ hS hR, hnoise, hP e]
  unfold law randomMapLaw
  rw [Measure.map_map hS (solution_measurable hv hb hl hT ht)]
  have heq : S ∘ (fun p ↦ solution hv hb hl hT p t) =
      (fun p ↦ solution hv hb hl hT p t) ∘ Prod.map S R := rfl
  change Measure.map (S ∘ _) _ = _
  rw [heq, ← Measure.map_map (solution_measurable hv hb hl hT ht) (hS.prodMap hR), hinput]

end SharpWasserstein.DecoupledFlow
