module

public import SharpWasserstein.Compat
public import SharpWasserstein.SwitchSourceDerivativeJacobian

@[expose] public section

/-! The actual continuous semigroup supplies the moving C¹ tests needed for
the switch comparison. All their regularity and bounds are proved here. -/
noncomputable section
open Set MeasureTheory
open scoped Topology NNReal ContDiff
namespace SharpWasserstein.SwitchSourceDerivative
open FlowSemigroupDerivative PropagatedSourceEquation NoiseAverage
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {b : E → E} {M K : ℝ≥0}
  (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
  {T : ℝ} (hT : 0 ≤ T)
  [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)]
  (ξ : Measure C(Icc 0 T,E)) [IsProbabilityMeasure ξ]

/-- A fixed-horizon realization of the true remaining-time transition. -/
def remainingTest (F : E → ℝ) (τ r : ℝ) (x : E) : ℝ :=
  clampedExpectation (hLip.continuous.comp continuous_snd)
    (fun _ => hb) (fun _ => hLip) hT ξ F (τ-r) x

variable (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  {F : E → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
  {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L)

include hbs hB hF hC hL in
theorem remainingTest_contDiff_one (τ r : ℝ) :
    ContDiff ℝ 1 (remainingTest hb hLip hT ξ F τ r) :=
  expectation_contDiff_one (hLip.continuous.comp continuous_snd)
    (fun _ => hb) (fun _ => hLip) hT ξ (projIcc 0 T hT (τ-r)).property hbs hB hF hC hL

omit [FiniteDimensional ℝ E] [BorelSpace C(Icc 0 T,E)] in
include hC in
theorem remainingTest_norm_le (τ r : ℝ) (x : E) :
    ‖remainingTest hb hLip hT ξ F τ r x‖ ≤ C := by
  apply (norm_integral_le_of_norm_le_const (μ := ξ) (C := C)
    (Filter.Eventually.of_forall (fun _ => hC _))).trans
  simp only [probReal_univ,mul_one,le_refl]

omit [FiniteDimensional ℝ E] in
include hF hC in
theorem remainingTest_continuous (τ : ℝ) :
    Continuous (fun p : ℝ × E => remainingTest hb hLip hT ξ F τ p.1 p.2) :=
  (clampedExpectation_continuous (hLip.continuous.comp continuous_snd)
    (fun _ => hb) (fun _ => hLip) hT ξ hF.continuous hC).comp
      ((continuous_const.sub continuous_fst).prodMk continuous_snd)

include hbs hB hF hC hL in
theorem remainingTest_fderiv_joint_continuous (τ : ℝ) :
    Continuous (fun p : ℝ × E => fderiv ℝ (remainingTest hb hLip hT ξ F τ p.1) p.2) := by
  have hc : Continuous (fun p : ℝ × E => (p.2,projIcc 0 T hT (τ-p.1))) :=
    continuous_snd.prodMk (continuous_projIcc.comp (continuous_const.sub continuous_fst))
  exact (expectation_fderiv_joint_continuous hb hLip hbs hB hT ξ hF hC hL).comp hc

include hbs hB hF hC hL in
theorem remainingTest_fderiv_norm_le (τ r : ℝ) (x : E) :
    ‖fderiv ℝ (remainingTest hb hLip hT ξ F τ r) x‖ ≤ (L:ℝ)*Real.exp ((K:ℝ)*T) :=
  clampedExpectation_fderiv_norm_le (hLip.continuous.comp continuous_snd)
    (fun _ => hb) (fun _ => hLip) hT ξ hbs hB hF hC hL (τ-r) x

end SharpWasserstein.SwitchSourceDerivative
