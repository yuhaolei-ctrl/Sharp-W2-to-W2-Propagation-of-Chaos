import SharpWasserstein.FlowJacobianDriftSmooth
import SharpWasserstein.FlowSemigroupDerivative

/-! Joint space/path/time continuity of the actual initial Jacobian and of
its probability-averaged test differential. These are derived from the global
variational equation and its stability, not assumed backward regularity. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ContDiff
namespace SharpWasserstein.SwitchSourceDerivative
open FlowInitialDerivative FlowJacobianDrift NoiseAverage
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {b : E → E} {M K : ℝ≥0}
  (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
  (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  {T : ℝ} (hT : 0 ≤ T)

include hbs hB

/-- The true initial Jacobian is jointly continuous in initial position,
continuous input, and evaluation time on the entire closed interval. -/
theorem flow_fderiv_joint_continuous :
    Continuous (fun p : (E × C(Icc 0 T,E)) × Icc 0 T =>
      fderiv ℝ (fun y => autonomousFlow hb hLip hT y p.1.2 p.2) p.1.1) := by
  apply continuous_iff_seqContinuous.mpr
  intro pk p hp
  have hDs : ContDiff ℝ ∞ (fderiv ℝ b) := (contDiff_infty_iff_fderiv.mp hbs).2
  obtain ⟨K₁,hD⟩ := hB.fderiv.lipschitz (hDs.differentiable (by simp))
  have hflow (s : ℝ) (hs : s ∈ Icc 0 T) :
      Tendsto (fun n => autonomousFlow hb hLip hT (pk n).1.1 (pk n).1.2 s) atTop
        (𝓝 (autonomousFlow hb hLip hT p.1.1 p.1.2 s)) :=
    (BoundedFlow.flow_continuous (v := fun _ : ℝ => b)
      (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hT hs).continuousAt.tendsto.comp (continuous_fst.continuousAt.tendsto.comp hp)
  have hJ := jacobian_tendstoUniformlyOn_of_boundedSmooth
    (fun _ => hb) (fun _ => hLip) (fun _ => hbs) (fun _ => hB)
    hb hLip hbs hB hT (fun n => (pk n).1.2) p.1.2 (fun n => (pk n).1.1) p.1.1 hflow
    (fun _ _ hy => hD.continuous.continuousAt.tendsto.comp hy)
  have ht : Tendsto (fun n => ((pk n).2:ℝ)) atTop (𝓝[Icc 0 T] (p.2:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨continuous_subtype_val.continuousAt.tendsto.comp (continuous_snd.continuousAt.tendsto.comp hp),
      Eventually.of_forall (fun n => (pk n).2.property)⟩
  simpa only [Function.comp_def,jacobian,projIcc_of_mem _ (pk _).2.property,projIcc_of_mem _ p.2.property] using
    hJ.tendsto_comp ((jacobian_continuous hb hLip (hbs.differentiable (by simp)) hD hT p.1.2 p.1.1).continuousAt.continuousWithinAt) ht

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)]
  (ξ : Measure C(Icc 0 T,E)) [IsProbabilityMeasure ξ]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Joint continuity of the differential of the actual transition expectation,
including both ends of the time interval. -/
theorem expectation_fderiv_joint_continuous
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) :
    Continuous (fun p : E × Icc 0 T =>
      fderiv ℝ (FlowSemigroupDerivative.expectation
        (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip)
        hT ξ (t := p.2) F) p.1) := by
  have he : (fun p : E × Icc 0 T =>
      fderiv ℝ (FlowSemigroupDerivative.expectation
        (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip)
        hT ξ (t := p.2) F) p.1) = fun p => ∫ w,
          (fderiv ℝ F (autonomousFlow hb hLip hT p.1 w p.2)).comp
            (fderiv ℝ (fun y => autonomousFlow hb hLip hT y w p.2) p.1) ∂ξ := by
    funext p
    exact (FlowSemigroupDerivative.hasFDerivAt_expectation
      (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip)
      hT ξ p.2.property hbs hB hF hC hL p.1).fderiv
  rw [he]
  apply continuous_of_dominated (bound := fun _ => (L:ℝ)*Real.exp ((K:ℝ)*T))
  · intro p
    exact (FlowSemigroupDerivative.integrable_differential
      (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip)
      hT ξ p.2.property hbs hB hF hL p.1).1
  · intro p
    filter_upwards [] with w
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (hL _) (boundedFlow_hasFDerivAt_and_norm_of_boundedSmooth
        (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip)
        hbs hB hT w p.1 p.2.property).2 (norm_nonneg _) L.coe_nonneg).trans
        (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left p.2.property.2 K.coe_nonneg)) L.coe_nonneg))
  · exact integrable_const _
  · filter_upwards [] with w
    have hc : Continuous (fun p : E × Icc 0 T => ((p.1,w),p.2)) :=
      (continuous_fst.prodMk continuous_const).prodMk continuous_snd
    exact ((hF.continuous_fderiv (by norm_num)).comp
      ((BoundedFlow.flow_joint_continuous (v := fun _ : ℝ => b)
        (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hT).comp hc)).clm_comp
      ((flow_fderiv_joint_continuous hb hLip hbs hB hT).comp hc)

end SharpWasserstein.SwitchSourceDerivative
