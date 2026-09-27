import SharpWasserstein.PeriodicSourceConvolutionFunctional
import SharpWasserstein.PeriodicSourceConvolutionMass

/-! Genuine dual-norm differentiation of the actual convolved propagated
source. Both the BCF derivative and its zero mass are proved; the dual source
acts on the actual periodic closed gradient space through an explicit fixed
bounded reconstruction/projection operator. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology ContDiff InnerProductSpace BoundedContinuousFunction
namespace SharpWasserstein.PeriodicSourceConvolution
open WeightedTangent NoiseAverage PropagatedSourceEquation FlowSemigroupDerivative
open PeriodicIntegrationByParts PeriodicBochner PeriodicGalerkin PeriodicSmoothGradient

variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

/-- Actual cube integration is a continuous linear functional on BCF. -/
def cubeIntegral : (Point n →ᵇ ℝ) →L[ℝ] ℝ :=
  (L1.integralCLM (μ := cubePoint)).comp (BoundedContinuousFunction.toLp 1 cubePoint ℝ)

@[simp] theorem cubeIntegral_apply (f : Point n →ᵇ ℝ) :
    cubeIntegral f = ∫ x,f x ∂cubePoint := by
  change L1.integralCLM (BoundedContinuousFunction.toLp 1 cubePoint ℝ f) = _
  rw [← L1.integral_def,L1.integral_eq_integral]
  exact integral_congr_ae (BoundedContinuousFunction.coeFn_toLp 1 (cubePoint (n := n)) ℝ f)

variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Configuration d N → Configuration d N} {M K M' K' : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ,∀ x,‖b x‖ ≤ M) (hl : ∀ _ : ℝ,LipschitzWith K b)
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) b)))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) b y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) b))
  {T : ℝ} (hT : 0 ≤ T) (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
  {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 μ)

/-- The actual convolved source as a continuous functional on the whole cube
closure, defined through its periodic orthogonal projection. -/
def convolvedFunctional (κ t : ℝ) : gradientClosure (cubePoint (n := N*d)) →L[ℝ] ℝ :=
  sourceFunctional (convolvedSourceBCF hv' hb' hl' hT hbs hB μ hu κ t)

/-- The actual derivative source action in the same dual norm. -/
def convolvedFunctionalDerivative (κ t : ℝ) : gradientClosure (cubePoint (n := N*d)) →L[ℝ] ℝ :=
  sourceFunctional (convolvedSourceDerivativeBCF hv' hb' hl' hT hbs hB μ hu κ t)

/-- Exact scalar-source pairing for every genuine smooth periodic test. -/
theorem convolvedFunctional_periodicGradient (κ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (f : SmoothPeriodicTest (N*d)) :
    convolvedFunctional hv' hb' hl' hT hbs hB μ hu κ t (periodicGradientMap f) =
      ∫ x,convolvedSource hv' hb' hl' hT μ (u := u) κ t x*f.val x ∂cube (N*d) := by
  rw [convolvedFunctional,sourceFunctional_periodicGradient_of_mean_zero _
    (convolvedSourceBCF_integral_eq_zero hv' hb' hl' hT hbs hB μ hu κ ht)]
  simp only [convolvedSourceBCF_apply,ContinuousLinearEquiv.apply_symm_apply]

include hv hb hl
/-- The actual ℓ-curve has a proved derivative in the continuous dual norm. -/
theorem convolvedFunctional_hasDerivWithinAt (κ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (convolvedFunctional hv' hb' hl' hT hbs hB μ hu κ)
      (convolvedFunctionalDerivative hv' hb' hl' hT hbs hB μ hu κ t) (Icc 0 T) t :=
  sourceFunctional_hasDerivWithinAt
    (convolvedSourceBCF_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs hB μ hu κ ht)

theorem convolvedFunctional_hasDerivAt (κ : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (convolvedFunctional hv' hb' hl' hT hbs hB μ hu κ)
      (convolvedFunctionalDerivative hv' hb' hl' hT hbs hB μ hu κ t) t :=
  sourceFunctional_hasDerivAt
    (convolvedSourceBCF_hasDerivAt hv hb hl hv' hb' hl' hT hbs hB μ hu κ ht)

/-- The derivative source has zero mass as a consequence of the proved BCF
curve and its exact mass conservation, also at nondegenerate endpoints. -/
theorem convolvedSourceDerivativeBCF_integral_eq_zero (κ : ℝ) (hTpos : 0 < T)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ y,convolvedSourceDerivativeBCF hv' hb' hl' hT hbs hB μ hu κ t y ∂cubePoint) = 0 := by
  have hd := (cubeIntegral (n := N*d)).hasFDerivAt.comp_hasDerivWithinAt t
    (convolvedSourceBCF_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs hB μ hu κ ht)
  have hz : HasDerivWithinAt (fun s => cubeIntegral
      (convolvedSourceBCF hv' hb' hl' hT hbs hB μ hu κ s)) 0 (Icc 0 T) t :=
    (hasDerivWithinAt_const t (Icc 0 T) (0 : ℝ)).congr
      (fun s hs => by rw [cubeIntegral_apply,convolvedSourceBCF_integral_eq_zero hv' hb' hl' hT hbs hB μ hu κ hs])
      (by rw [cubeIntegral_apply,convolvedSourceBCF_integral_eq_zero hv' hb' hl' hT hbs hB μ hu κ ht])
  have he := (hd.derivWithin (uniqueDiffOn_Icc hTpos t ht)).symm.trans
    (hz.derivWithin (uniqueDiffOn_Icc hTpos t ht))
  simpa only [cubeIntegral_apply] using he

/-- The derivative functional also represents the actual uncentered source derivative. -/
theorem convolvedFunctionalDerivative_periodicGradient (κ : ℝ) (hTpos : 0 < T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (f : SmoothPeriodicTest (N*d)) :
    convolvedFunctionalDerivative hv' hb' hl' hT hbs hB μ hu κ t (periodicGradientMap f) =
      ∫ x,convolvedSourceDerivativeBCF hv' hb' hl' hT hbs hB μ hu κ t
        ((coordinateEquiv (N*d)).symm x)*f.val x ∂cube (N*d) :=
  sourceFunctional_periodicGradient_of_mean_zero _
    (convolvedSourceDerivativeBCF_integral_eq_zero hv hb hl hv' hb' hl' hT hbs hB μ hu κ hTpos ht) f

end SharpWasserstein.PeriodicSourceConvolution
