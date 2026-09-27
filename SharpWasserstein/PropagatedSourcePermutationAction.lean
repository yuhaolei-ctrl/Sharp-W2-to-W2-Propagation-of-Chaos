import SharpWasserstein.PropagatedSourcePermutation
import SharpWasserstein.PeriodicSourceConvolutionAction

/-! Permutation invariance of the literal noncompact source action used for
periodic smoothing. The symmetry statement needs only continuity of the test;
when applied to bounded C¹ tests, the previously proved action estimates and
random-Jacobian representation give its usual distributional meaning. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff
namespace SharpWasserstein.PropagatedSourcePermutation
open WeightedTangent PropagatedSourceEquation FlowSemigroupDerivative
variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  {b : Point n → Point n} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)
  {T : ℝ} [MeasurableSpace C(Icc 0 T, Point n)] [BorelSpace C(Icc 0 T, Point n)]
  (hT : 0 ≤ T) (L : Point n ≃L[ℝ] Point n)
  (hcomm : ∀ x, b (L x) = L (b x))

include hcomm in
omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
/-- Actual semigroup covariance also holds for continuous noncompact tests. -/
theorem expectation_covariant_continuous (ξ : Measure C(Icc 0 T, Point n))
    (hξ : ξ.map (equivPath L) = ξ) {t : ℝ} (ht : t ∈ Icc 0 T)
    {F : Point n → ℝ} (hF : Continuous F) (x : Point n) :
    expectation hv hb hl hT ξ (t := t) F (L x) =
      expectation hv hb hl hT ξ (t := t) (F ∘ L) x := by
  unfold expectation
  have hi : AEStronglyMeasurable
      (fun w => F (BoundedFlow.flow hv hb hl hT (L x) w t)) (ξ.map (equivPath L)) :=
    (hF.comp ((BoundedFlow.flow_continuous hv hb hl hT ht).comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  rw [← hξ, integral_map (equivPath_continuous L).measurable.aemeasurable hi]
  rw [hξ]
  apply integral_congr_ae
  exact Eventually.of_forall (fun w => congrArg F
    (flow_covariant hv hb hl hT L hcomm x w ht))

include hcomm in
/-- The literal noncompact differentiated-expectation pairing is invariant.
The change of variables is a measurable equivalence and therefore does not
introduce an unproved integrability premise. -/
theorem semigroupPairing_invariant (ξ : Measure C(Icc 0 T, Point n))
    (hξ : ξ.map (equivPath L) = ξ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (μ : Measure (Point n)) (hμ : μ.map L = μ)
    (u : Point n → Point n) (hue : ∀ᵐ x ∂μ, u (L x) = L (u x))
    {F : Point n → ℝ} (hF : Continuous F) :
    (∫ x, fderiv ℝ (expectation hv hb hl hT ξ (t := t) (F ∘ L)) x (u x) ∂μ) =
      ∫ x, fderiv ℝ (expectation hv hb hl hT ξ (t := t) F) x (u x) ∂μ := by
  have he : expectation hv hb hl hT ξ (t := t) (F ∘ L) =
      expectation hv hb hl hT ξ (t := t) F ∘ L := by
    funext x
    exact (expectation_covariant_continuous hv hb hl hT L hcomm ξ hξ ht hF x).symm
  rw [he]
  simp_rw [L.comp_right_fderiv]
  have hp : (∫ x, fderiv ℝ (expectation hv hb hl hT ξ (t := t) F) (L x) (L (u x)) ∂μ) =
      ∫ x, fderiv ℝ (expectation hv hb hl hT ξ (t := t) F) (L x) (u (L x)) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hue] with x hx
    rw [hx]
  change (∫ x, fderiv ℝ (expectation hv hb hl hT ξ (t := t) F) (L x) (L (u x)) ∂μ) = _
  rw [hp]
  have hi := integral_map_equiv (μ := μ) L.toHomeomorph.toMeasurableEquiv
    (fun x => fderiv ℝ (expectation hv hb hl hT ξ (t := t) F) x (u x))
  change (∫ x, fderiv ℝ (expectation hv hb hl hT ξ (t := t) F) x (u x) ∂μ.map L) =
    ∫ x, fderiv ℝ (expectation hv hb hl hT ξ (t := t) F) (L x) (u (L x)) ∂μ at hi
  rw [hμ] at hi
  exact hi.symm

include hcomm in
/-- This is the exact clamped source action used by periodic convolution, for
all real times and in particular for bounded smooth periodic kernel tests. -/
theorem action_invariant (ξ : Measure C(Icc 0 T, Point n)) [IsProbabilityMeasure ξ]
    (hξ : ξ.map (equivPath L) = ξ) (μ : Measure (Point n)) [IsFiniteMeasure μ]
    (hμ : μ.map L = μ) (u : Point n → Point n)
    (hue : ∀ᵐ x ∂μ, u (L x) = L (u x)) {F : Point n → ℝ} (hF : Continuous F) (r : ℝ) :
    PeriodicSourceConvolution.action hv hb hl hT ξ μ u (F ∘ L) r =
      PeriodicSourceConvolution.action hv hb hl hT ξ μ u F r :=
  semigroupPairing_invariant hv hb hl hT L hcomm ξ hξ
    (projIcc 0 T hT r).property μ hμ u hue hF

end SharpWasserstein.PropagatedSourcePermutation
