module

public import SharpWasserstein.Compat
public import SharpWasserstein.FlowJacobianContinuitySmooth
public import SharpWasserstein.BoundedNoiseAverage
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! Differentiating the genuine continuous-input flow expectation. The
initial-value derivative is constructed previously; the derivative of the
probability expectation is proved by dominated differentiation. -/
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

/-- Actual averaging of the constructed flow endpoint over the input law. -/
def expectation (F : E → ℝ) (x : E) : ℝ :=
  ∫ w, F (BoundedFlow.flow hv hb hl hT x w t) ∂ξ

include ht

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)] in
/-- The fixed-path initial map has its sharp synchronous Lipschitz constant. -/
theorem initialMap_lipschitz (w : C(Icc 0 T,E)) :
    LipschitzWith ⟨Real.exp ((K:ℝ)*t),by positivity⟩
      (fun x => BoundedFlow.flow hv hb hl hT x w t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm]
  change ‖BoundedFlow.flow hv hb hl hT x w t-BoundedFlow.flow hv hb hl hT y w t‖ ≤ Real.exp ((K:ℝ)*t)*‖x-y‖
  have hh := BoundedFlow.flow_difference_le hv hb hl hT x y w w ht
  simpa only [sub_self,norm_zero,add_zero,mul_comm,NNReal.coe_mk] using hh

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- A bounded continuous observable is integrable along every actual flow. -/
theorem integrable_observable {F : E → ℝ} (hF : Continuous F)
    {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) (x : E) :
    Integrable (fun w => F (BoundedFlow.flow hv hb hl hT x w t)) ξ := by
  apply Integrable.of_bound
    ((hF.comp ((BoundedFlow.flow_continuous hv hb hl hT ht).comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable) C
  exact Eventually.of_forall (fun _ => hC _)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)] in
/-- Actual derivative integrands are jointly continuous, before integration. -/
theorem differential_continuous
    (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) :
    Continuous (fun p : E × C(Icc 0 T,E) =>
      (fderiv ℝ F (BoundedFlow.flow hv hb hl hT p.1 p.2 t)).comp
        (fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y p.2 t) p.1)) :=
  ((hF.continuous_fderiv (by norm_num)).comp
    (BoundedFlow.flow_continuous hv hb hl hT ht)).clm_comp
      (boundedFlow_fderiv_continuous_of_boundedSmooth hv hb hl hbs hB hT ht)

omit [MeasurableSpace E] [BorelSpace E] in
/-- A bounded observable gradient gives an integrable operator derivative. -/
theorem integrable_differential
    (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {L : ℝ≥0}
    (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (x : E) :
    Integrable (fun w =>
      (fderiv ℝ F (BoundedFlow.flow hv hb hl hT x w t)).comp
        (fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y w t) x)) ξ := by
  apply Integrable.of_bound
    (((differential_continuous hv hb hl hT ht hbs hB hF).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable) ((L:ℝ)*Real.exp ((K:ℝ)*t))
  filter_upwards [] with w
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (hL _) (boundedFlow_hasFDerivAt_and_norm_of_boundedSmooth
      hv hb hl hbs hB hT w x ht).2 (norm_nonneg _) L.coe_nonneg)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The actual semigroup derivative is the Bochner integral of DF(X)∘J. -/
theorem hasFDerivAt_expectation
    (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (x : E) :
    HasFDerivAt (expectation hv hb hl hT ξ (t := t) F)
      (∫ w, (fderiv ℝ F (BoundedFlow.flow hv hb hl hT x w t)).comp
        (fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y w t) x) ∂ξ) x := by
  have hFL : LipschitzWith L F := lipschitzWith_of_nnnorm_fderiv_le
    (hF.differentiable (by norm_num)) hL
  have hLip : ∀ᵐ w ∂ξ, LipschitzOnWith (Real.nnabs ((L:ℝ)*Real.exp ((K:ℝ)*t)))
      (fun y => F (BoundedFlow.flow hv hb hl hT y w t)) univ := by
    filter_upwards [] with w
    have hh := (hFL.comp (initialMap_lipschitz hv hb hl hT ht w)).lipschitzOnWith (s := univ)
    have hc : Real.nnabs ((L:ℝ)*Real.exp ((K:ℝ)*t)) =
        L * NNReal.mk (Real.exp ((K:ℝ)*t)) (by positivity) := by
      apply NNReal.eq
      change |(L:ℝ)*Real.exp ((K:ℝ)*t)| = (L:ℝ)*Real.exp ((K:ℝ)*t)
      exact abs_of_nonneg (by positivity)
    rw [hc]
    exact hh
  have hdiff : ∀ᵐ w ∂ξ, HasFDerivAt (fun y => F (BoundedFlow.flow hv hb hl hT y w t))
      ((fderiv ℝ F (BoundedFlow.flow hv hb hl hT x w t)).comp
        (fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y w t) x)) x := by
    filter_upwards [] with w
    exact ((hF.differentiable (by norm_num)) _).hasFDerivAt.comp x
      (boundedFlow_hasFDerivAt_and_norm_of_boundedSmooth hv hb hl hbs hB hT w x ht).1
  exact (hasFDerivAt_integral_of_dominated_loc_of_lip (μ := ξ)
    (F := fun y w => F (BoundedFlow.flow hv hb hl hT y w t))
    (bound := fun _ => (L:ℝ)*Real.exp ((K:ℝ)*t)) (s := univ) (by simp)
    (Eventually.of_forall (fun y => (integrable_observable hv hb hl hT ξ ht hF.continuous hC y).1))
    (integrable_observable hv hb hl hT ξ ht hF.continuous hC x)
    (integrable_differential hv hb hl hT ξ ht hbs hB hF hL x).1
    hLip (integrable_const _) hdiff).2

omit [MeasurableSpace E] [BorelSpace E] in
/-- Applying the semigroup derivative gives the genuine scalar flux pairing. -/
theorem fderiv_expectation_apply
    (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (x u : E) :
    fderiv ℝ (expectation hv hb hl hT ξ (t := t) F) x u =
      ∫ w, fderiv ℝ F (BoundedFlow.flow hv hb hl hT x w t)
        (fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y w t) x u) ∂ξ := by
  rw [(hasFDerivAt_expectation hv hb hl hT ξ ht hbs hB hF hC hL x).fderiv]
  exact ContinuousLinearMap.integral_apply
    (integrable_differential hv hb hl hT ξ ht hbs hB hF hL x) u

omit [MeasurableSpace E] [BorelSpace E] in
/-- The actual expectation is C¹, including continuity of its integrated
operator derivative. -/
theorem expectation_contDiff_one
    (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) :
    ContDiff ℝ 1 (expectation hv hb hl hT ξ (t := t) F) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun x => ∫ w, (fderiv ℝ F (BoundedFlow.flow hv hb hl hT x w t)).comp
    (fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y w t) x) ∂ξ, ?_,
    hasFDerivAt_expectation hv hb hl hT ξ ht hbs hB hF hC hL⟩
  apply continuous_of_dominated (bound := fun _ => (L:ℝ)*Real.exp ((K:ℝ)*t))
  · intro x
    exact (integrable_differential hv hb hl hT ξ ht hbs hB hF hL x).1
  · intro x
    filter_upwards [] with w
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hL _) (boundedFlow_hasFDerivAt_and_norm_of_boundedSmooth
        hv hb hl hbs hB hT w x ht).2 (norm_nonneg _) L.coe_nonneg)
  · exact integrable_const _
  · filter_upwards [] with w
    exact (differential_continuous hv hb hl hT ht hbs hB hF).comp
      (continuous_id.prodMk continuous_const)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The actual semigroup derivative satisfies the dimension-free gradient bound. -/
theorem norm_fderiv_expectation_le
    (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (x : E) :
    ‖fderiv ℝ (expectation hv hb hl hT ξ (t := t) F) x‖ ≤
      (L:ℝ)*Real.exp ((K:ℝ)*t) := by
  rw [(hasFDerivAt_expectation hv hb hl hT ξ ht hbs hB hF hC hL x).fderiv]
  apply (norm_integral_le_of_norm_le_const (μ := ξ) (C := (L:ℝ)*Real.exp ((K:ℝ)*t)) ?_).trans
  · simp only [probReal_univ,mul_one,le_refl]
  · filter_upwards [] with w
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hL _) (boundedFlow_hasFDerivAt_and_norm_of_boundedSmooth
        hv hb hl hbs hB hT w x ht).2 (norm_nonneg _) L.coe_nonneg)

omit ht [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [BorelSpace C(Icc 0 T,E)] in
/-- A probability input law concentrated on paths starting at zero gives the
identity operator at time zero. -/
theorem expectation_zero (hzero : ∀ᵐ w ∂ξ, w ⟨0,le_rfl,hT⟩ = 0) (F : E → ℝ) :
    expectation hv hb hl hT ξ (t := 0) F = F := by
  funext x
  change (∫ w, F (BoundedFlow.flow hv hb hl hT x w 0) ∂ξ) = F x
  calc
    _ = ∫ _, F x ∂ξ := by
      apply integral_congr_ae
      filter_upwards [hzero] with w hw
      have hx := (BoundedFlow.flow_trajectory hv hb hl hT x w).equation 0 ⟨le_rfl,hT⟩
      simp only [intervalIntegral.integral_same,add_zero,BoundedFlow.noiseExtension,
        projIcc_of_mem _ (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),hw,add_zero] at hx
      rw [hx]
    _ = _ := by simp

end SharpWasserstein.FlowSemigroupDerivative
