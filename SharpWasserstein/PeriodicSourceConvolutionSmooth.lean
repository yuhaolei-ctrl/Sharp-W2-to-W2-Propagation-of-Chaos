import SharpWasserstein.PeriodicSourceConvolutionJointBounds
import SharpWasserstein.PeriodicSourceConvolutionDual

/-! Genuine spatial smoothness of source actions and their differentiated
generator actions. All mixed derivative bounds come from the actual translated
kernel, and all integration weights are the actual integrable JV flux. -/
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology ContDiff BoundedContinuousFunction
namespace SharpWasserstein.PeriodicSourceConvolution
open WeightedTangent NoiseAverage PropagatedSourceEquation FlowSemigroupDerivative
open PeriodicIntegrationByParts PeriodicPositiveKernel PeriodicBochner

section General
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {b : E → E} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ,∀ x,‖b x‖ ≤ M) (hl : ∀ _ : ℝ,LipschitzWith K b)
  {T : ℝ} [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)] (hT : 0 ≤ T)
  (ξ : Measure C(Icc 0 T,E)) [IsProbabilityMeasure ξ]
  (μ : Measure E) [IsFiniteMeasure μ]
  (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)

include hbs hB
/-- Smooth bounded mixed derivatives may be integrated against the genuine
transported initial vector, with no source-density regularity premise. -/
theorem action_smooth_param {f : P → E → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hBjoint : AllDerivativesBounded (Function.uncurry f)) (hBf : UniformDerivatives f)
    {u : E → E} (hu : MemLp u 2 μ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContDiff ℝ ∞ (fun p => action hv hb hl hT ξ μ u (f p) t) := by
  letI : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
  have hf' (p : P) : ContDiff ℝ ∞ (f p) := hf.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨C,_,hC⟩ := hBf.bounded
  obtain ⟨L,hL0,hL⟩ := hBf.fderiv.bounded
  let V := fun q : E × C(Icc 0 T,E) =>
    fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y q.2 t) q.1 (u q.1)
  have hV : MemLp V 2 (μ.prod ξ) := FlowInitialDerivative.boundedFlow_fderiv_apply_memLp
    hv hb hl hbs hB hT ht (μ.prod ξ)
      (hu.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := ξ)))
  have he (p : P) : action hv hb hl hT ξ μ u (f p) t =
      ∫ q : E × C(Icc 0 T,E),fderiv ℝ (f p) (BoundedFlow.flow hv hb hl hT q.1 q.2 t) (V q) ∂μ.prod ξ :=
    action_eq_randomFlux hv hb hl hT ξ μ hbs hB
      ((hf' p).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) (hC p)
      (L := NNReal.mk L hL0) (hL p) hu ht
  let Z : E × C(Icc 0 T,E) → P×E := fun q => (0,BoundedFlow.flow hv hb hl hT q.1 q.2 t)
  have hZ : StronglyMeasurable Z := stronglyMeasurable_const.prodMk
    (BoundedFlow.flow_continuous hv hb hl hT ht).stronglyMeasurable
  let W : E × C(Icc 0 T,E) → (E →L[ℝ] ℝ) →L[ℝ] ℝ := fun q =>
    ContinuousLinearMap.apply ℝ ℝ (V q)
  have hW : Integrable W (μ.prod ξ) :=
    (ContinuousLinearMap.apply ℝ ℝ).integrable_comp (hV.integrable (by norm_num))
  have hh := WeightedConvolution.contDiff_infty_operatorAverage (μ.prod ξ) Z hZ hW
    (joint_fderiv hf) (joint_fderiv_bounded hf hBjoint)
  have hc := hh.comp (ContinuousLinearMap.inl ℝ P E).contDiff
  convert hc using 1
  funext p
  rw [he]
  simp only [Function.comp_def,WeightedConvolution.operatorAverage,Z,W,
    ContinuousLinearMap.inl_apply,Prod.mk_add_mk,add_zero,zero_add,
    Function.uncurry_def,ContinuousLinearMap.apply_apply]
end General

variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Configuration d N → Configuration d N} {M' K' : ℝ≥0}
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) b)))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) b y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) b))
  {T : ℝ} (hT : 0 ≤ T) (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
  {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 μ)

include hbs hB hu
/-- Actual source convolution is C∞ in space for any initial finite-energy flux. -/
theorem convolvedSource_smooth (κ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContDiff ℝ ∞ (convolvedSource hv' hb' hl' hT μ (u := u) κ t) :=
  action_smooth_param hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ
    (equivDrift_smooth _ hbs) (equivDrift_allDerivativesBounded _ hbs hB)
    (joint_euclideanKernelTest κ) (joint_euclideanKernelTest_bounded κ)
    (euclideanKernelTest_uniform κ) hu ht

omit hbs hB hu [BorelSpace (Point (N*d))] [IsFiniteMeasure μ] in
/-- Periodicity is inherited from the actual reflected kernel. -/
theorem convolvedSource_periodic (κ t : ℝ) :
    Periodic (convolvedSource hv' hb' hl' hT μ (u := u) κ t) := by
  intro i x
  have he : euclideanKernelTest κ (x+Pi.single i 1) = euclideanKernelTest κ x := by
    funext y
    unfold euclideanKernelTest
    rw [add_sub_right_comm,kernel_periodic]
  unfold convolvedSource
  rw [he]

/-- Every actual spatial derivative has a global bound. -/
theorem convolvedSource_allDerivativesBounded (κ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    AllDerivativesBounded (convolvedSource hv' hb' hl' hT μ (u := u) κ t) :=
  PeriodicSmoothBounds.iteratedFDeriv_bound
    (convolvedSource_periodic hv' hb' hl' hT μ κ t)
    (convolvedSource_smooth hv' hb' hl' hT hbs hB μ hu κ ht)

/-- The actual time-derivative source, expressed on coordinate space. -/
def convolvedSourceTimeDerivative (κ t : ℝ) (x : Coordinates (N*d)) : ℝ :=
  action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u
    (euclideanGenerator b (euclideanKernelTest κ x)) t

/-- Its C∞ spatial regularity follows from the genuine joint generator bounds. -/
theorem convolvedSourceTimeDerivative_smooth (κ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContDiff ℝ ∞ (convolvedSourceTimeDerivative hv' hb' hl' hT μ (u := u) κ t) :=
  action_smooth_param hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ
    (equivDrift_smooth _ hbs) (equivDrift_allDerivativesBounded _ hbs hB)
    (joint_euclideanGenerator (joint_euclideanKernelTest κ) hbs)
    (joint_euclideanGenerator_bounded (joint_euclideanKernelTest κ) (joint_euclideanKernelTest_bounded κ) hbs hB)
    (uniform_euclideanGenerator hbs hB (euclideanKernelTest_smooth κ) (euclideanKernelTest_uniform κ)) hu ht

omit hbs hB hu [BorelSpace (Point (N*d))] [IsFiniteMeasure μ] in
theorem convolvedSourceTimeDerivative_periodic (κ t : ℝ) :
    Periodic (convolvedSourceTimeDerivative hv' hb' hl' hT μ (u := u) κ t) := by
  intro i x
  have he : euclideanKernelTest κ (x+Pi.single i 1) = euclideanKernelTest κ x := by
    funext y
    unfold euclideanKernelTest
    rw [add_sub_right_comm,kernel_periodic]
  unfold convolvedSourceTimeDerivative
  rw [he]

theorem convolvedSourceTimeDerivative_allDerivativesBounded (κ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    AllDerivativesBounded (convolvedSourceTimeDerivative hv' hb' hl' hT μ (u := u) κ t) :=
  PeriodicSmoothBounds.iteratedFDeriv_bound
    (convolvedSourceTimeDerivative_periodic hv' hb' hl' hT μ κ t)
    (convolvedSourceTimeDerivative_smooth hv' hb' hl' hT hbs hB μ hu κ ht)

/-- The BCF derivative is exactly the coordinate-space smooth function. -/
@[simp] theorem convolvedSourceDerivativeBCF_apply (κ t : ℝ) (y : Point (N*d)) :
    convolvedSourceDerivativeBCF hv' hb' hl' hT hbs hB μ hu κ t y =
      convolvedSourceTimeDerivative hv' hb' hl' hT μ (u := u) κ t (coordinateEquiv (N*d) y) := rfl

end SharpWasserstein.PeriodicSourceConvolution
