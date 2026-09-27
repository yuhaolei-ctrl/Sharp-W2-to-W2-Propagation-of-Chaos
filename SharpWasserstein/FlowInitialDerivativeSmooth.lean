import SharpWasserstein.FlowInitialDerivativeGlobal
import SharpWasserstein.NoiseAverageSmooth

/-! The initial-data derivative result applies to genuine C_b^infinity drifts:
the Lipschitz bound on the first derivative is derived from the actual globally
bounded second derivative, rather than supplied as an analytic conclusion. -/
noncomputable section
open Set
open scoped NNReal ContDiff
namespace SharpWasserstein.FlowInitialDerivative
open NoiseAverage
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem autonomousFlow_hasFDerivAt_and_norm_of_boundedSmooth
    {b : E → E} {M K : ℝ≥0} (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
    (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
    {T : ℝ} (hT : 0 ≤ T) (w : C(Icc 0 T,E)) (x : E) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasFDerivAt (fun y => autonomousFlow hb hLip hT y w t)
      (fderiv ℝ (fun y => autonomousFlow hb hLip hT y w t) x) x ∧
    ‖fderiv ℝ (fun y => autonomousFlow hb hLip hT y w t) x‖ ≤ Real.exp ((K:ℝ)*t) := by
  have hbd := hbs.differentiable (by simp)
  have hDs : ContDiff ℝ ∞ (fderiv ℝ b) := (contDiff_infty_iff_fderiv.mp hbs).2
  obtain ⟨K₁,hD⟩ := hB.fderiv.lipschitz (hDs.differentiable (by simp))
  exact autonomousFlow_hasFDerivAt_and_norm hb hLip hbd hD hT w x ht

/-- Direct API for the pre-existing actual BoundedFlow construction, with no
restriction on the finite horizon and no smoothness assumption on the input path. -/
theorem boundedFlow_hasFDerivAt_and_norm_of_boundedSmooth
    {b : E → E} {M K : ℝ≥0}
    (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
    (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)
    (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
    {T : ℝ} (hT : 0 ≤ T) (w : C(Icc 0 T,E)) (x : E) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasFDerivAt (fun y => BoundedFlow.flow hv hb hl hT y w t)
      (fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y w t) x) x ∧
    ‖fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y w t) x‖ ≤ Real.exp ((K:ℝ)*t) := by
  simpa only [autonomousFlow] using
    autonomousFlow_hasFDerivAt_and_norm_of_boundedSmooth (hb 0) (hl 0) hbs hB hT w x ht

end SharpWasserstein.FlowInitialDerivative
