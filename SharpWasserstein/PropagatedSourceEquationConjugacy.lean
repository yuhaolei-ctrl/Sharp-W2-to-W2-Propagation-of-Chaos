import SharpWasserstein.FlowSemigroupDerivative
import SharpWasserstein.EuclideanFlow

/-! Exact conjugacy of the selected continuous-input flow and its probability
expectation under a genuine continuous linear equivalence. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal
namespace SharpWasserstein.PropagatedSourceEquation
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Actual drift expressed through the fixed linear coordinate equivalence. -/
def equivDrift (L : E ≃L[ℝ] F) (b : E → E) (y : F) : F := L (b (L.symm y))

/-- Pointwise application of the linear coordinate map to a continuous input. -/
def equivPath (L : E ≃L[ℝ] F) {T : ℝ} (w : C(Icc 0 T,E)) : C(Icc 0 T,F) :=
  (⟨L,L.continuous⟩ : C(E,F)).comp w

omit [CompleteSpace E] [CompleteSpace F] in
theorem equivPath_continuous (L : E ≃L[ℝ] F) {T : ℝ} :
    Continuous (equivPath (T := T) L) := ContinuousMap.continuous_postcomp (⟨L,L.continuous⟩ : C(E,F))

/-- Uniqueness of the actual integral equation identifies both selected flows. -/
theorem flow_equiv (L : E ≃L[ℝ] F) {b : E → E} {M K M' K' : ℝ≥0}
    (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
    (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)
    (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift L b)))
    (hb' : ∀ _ : ℝ, ∀ y, ‖equivDrift L b y‖ ≤ M')
    (hl' : ∀ _ : ℝ, LipschitzWith K' (equivDrift L b))
    {T : ℝ} (hT : 0 ≤ T) (x : E) (w : C(Icc 0 T,E)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    BoundedFlow.flow hv' hb' hl' hT (L x) (equivPath L w) t =
      L (BoundedFlow.flow hv hb hl hT x w t) := by
  apply BoundedFlow.flow_eq_of_trajectory hv' hb' hl' hT (L x) (equivPath L w)
    (X := fun r => L (BoundedFlow.flow hv hb hl hT x w r)) _ ht
  exact (BoundedFlow.flow_trajectory hv hb hl hT x w).map_equiv L

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {T : ℝ} [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)]
  [MeasurableSpace C(Icc 0 T,F)] [BorelSpace C(Icc 0 T,F)]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- The pushed path law gives the same actual endpoint expectation after
linear change of coordinates, including the exact Euclidean normalization. -/
theorem expectation_equiv (L : E ≃L[ℝ] F) {b : E → E} {M K M' K' : ℝ≥0}
    (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
    (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)
    (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift L b)))
    (hb' : ∀ _ : ℝ, ∀ y, ‖equivDrift L b y‖ ≤ M')
    (hl' : ∀ _ : ℝ, LipschitzWith K' (equivDrift L b))
    (hT : 0 ≤ T) (ξ : Measure C(Icc 0 T,E)) (x : E)
    {t : ℝ} (ht : t ∈ Icc 0 T) {φ : F → ℝ} (hφ : Continuous φ) :
    FlowSemigroupDerivative.expectation hv' hb' hl' hT (ξ.map (equivPath L)) (t := t) φ (L x) =
      FlowSemigroupDerivative.expectation hv hb hl hT ξ (t := t) (φ ∘ L) x := by
  have hi : AEStronglyMeasurable
      (fun w => φ (BoundedFlow.flow hv' hb' hl' hT (L x) w t)) (ξ.map (equivPath L)) :=
    (hφ.comp ((BoundedFlow.flow_continuous hv' hb' hl' hT ht).comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  unfold FlowSemigroupDerivative.expectation
  rw [integral_map (equivPath_continuous L).measurable.aemeasurable hi]
  apply integral_congr_ae
  exact Eventually.of_forall (fun w => congrArg φ (flow_equiv L hv hb hl hv' hb' hl' hT x w ht))

end SharpWasserstein.PropagatedSourceEquation
