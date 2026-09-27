import SharpWasserstein.FlowSemigroupDerivative
import Mathlib.MeasureTheory.Integral.Prod

/-! The differentiated probability expectation acts on an actual finite-energy
initial vector field by the integral of the pushed Jacobian vector. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff Topology
namespace SharpWasserstein.FlowSemigroupDerivative
open FlowInitialDerivative NoiseAverage
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {b : E → E} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)
  {T : ℝ} [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)]
  (hT : 0 ≤ T) (ξ : Measure C(Icc 0 T,E)) [IsProbabilityMeasure ξ]
  {t : ℝ} (ht : t ∈ Icc 0 T)
  (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  (μ : Measure E) [IsFiniteMeasure μ]

include ht hbs hB

/-- Finiteness of the initial L² energy proves the actual joint scalar pairing
is integrable, allowing Fubini without a totalized-integral gap. -/
theorem integrable_differential_pairing
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {L : ℝ≥0}
    (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) {u : E → E} (hu : MemLp u 2 μ) :
    Integrable (fun q : E × C(Icc 0 T,E) =>
      fderiv ℝ F (BoundedFlow.flow hv hb hl hT q.1 q.2 t)
        (fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y q.2 t) q.1 (u q.1))) (μ.prod ξ) := by
  have hup : MemLp (fun q : E × C(Icc 0 T,E) => u q.1) 2 (μ.prod ξ) :=
    hu.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := ξ))
  have hm : AEStronglyMeasurable (fun q : E × C(Icc 0 T,E) =>
      fderiv ℝ F (BoundedFlow.flow hv hb hl hT q.1 q.2 t)
        (fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y q.2 t) q.1 (u q.1))) (μ.prod ξ) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      ((differential_continuous hv hb hl hT ht hbs hB hF).aestronglyMeasurable.prodMk hup.1)
  apply Integrable.mono' (((hup.integrable (by norm_num)).norm).const_mul ((L:ℝ)*Real.exp ((K:ℝ)*t))) hm
  filter_upwards [] with q
  have hJ := (boundedFlow_hasFDerivAt_and_norm_of_boundedSmooth hv hb hl hbs hB hT q.2 q.1 ht).2
  calc
    _ ≤ ‖fderiv ℝ F (BoundedFlow.flow hv hb hl hT q.1 q.2 t)‖ *
        ‖fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y q.2 t) q.1 (u q.1)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (L:ℝ) * (Real.exp ((K:ℝ)*t)*‖u q.1‖) :=
      mul_le_mul (hL _) ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))) (norm_nonneg _) L.coe_nonneg
    _ = _ := by ring

/-- The initial source applied to the actual semigroup derivative is exactly
the pushed random flux pairing. -/
theorem integral_fderiv_expectation_eq
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) {u : E → E} (hu : MemLp u 2 μ) :
    (∫ x, fderiv ℝ (expectation hv hb hl hT ξ (t := t) F) x (u x) ∂μ) =
      ∫ q : E × C(Icc 0 T,E), fderiv ℝ F (BoundedFlow.flow hv hb hl hT q.1 q.2 t)
        (fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y q.2 t) q.1 (u q.1)) ∂μ.prod ξ := by
  calc
    _ = ∫ x, ∫ w, fderiv ℝ F (BoundedFlow.flow hv hb hl hT x w t)
        (fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y w t) x (u x)) ∂ξ ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => fderiv_expectation_apply hv hb hl hT ξ ht hbs hB hF hC hL x (u x))
    _ = _ := (integral_prod _ (integrable_differential_pairing hv hb hl hT ξ ht hbs hB μ hF hL hu)).symm

end SharpWasserstein.FlowSemigroupDerivative
