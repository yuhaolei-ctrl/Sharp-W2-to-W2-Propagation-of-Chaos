import SharpWasserstein.PeriodicSourceConvolutionBCF
import SharpWasserstein.PeriodicConvolutionPDEIntegral
import SharpWasserstein.PeriodicGalerkin

/-! The genuine convolved source has exactly zero mass. This follows from
periodic integration by parts and the actual random JV flux, including for
singular initial laws. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators ContDiff BoundedContinuousFunction
namespace SharpWasserstein.PeriodicSourceConvolution
open WeightedTangent NoiseAverage PropagatedSourceEquation FlowSemigroupDerivative
open PeriodicIntegrationByParts PeriodicPositiveKernel PeriodicBochner PeriodicGalerkin

/-- Every translated periodic kernel derivative has zero cube mean. -/
theorem integral_kernel_fderiv_eq_zero {n : ℕ} (κ : ℝ) (y v : Coordinates n) :
    (∫ x,fderiv ℝ (kernel κ) (x-y) v ∂cube n) = 0 := by
  simp_rw [PeriodicConvolution.fderiv_eq_sum_coordinatePartial]
  have hi (i : Fin n) : Integrable (fun x => coordinatePartial (kernel κ) i (x-y)*v i) (cube n) :=
    continuous_integrable_cube (((continuous_coordinatePartial
      ((kernel_smooth n κ).of_le (by simp)) i).comp
        (continuous_id.sub continuous_const)).mul continuous_const)
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_mul_const,PeriodicConvolution.integral_cube_sub
    (periodic_coordinatePartial (kernel_periodic n κ) i)
    (continuous_coordinatePartial ((kernel_smooth n κ).of_le (by simp)) i),
    integral_coordinatePartial_eq_zero ((kernel_smooth n κ).of_le (by simp)) (kernel_periodic n κ),
    zero_mul]

/-- A genuine Fubini statement for arbitrary integrable random vector fluxes. -/
theorem integral_random_kernel_fderiv_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (κ : ℝ) (P : Measure Ω) [SFinite P]
    {X V : Ω → Coordinates n} (hX : Measurable X) (hV : Integrable V P) :
    (∫ x,∫ q,fderiv ℝ (kernel κ) (x-X q) (V q) ∂P ∂cube n) = 0 := by
  have hB : AllDerivativesBounded (kernel (n := n) κ) := kernel_derivatives_bounded n κ
  obtain ⟨D,_,hD⟩ := hB.fderiv.bounded
  have hi : Integrable (fun p : Coordinates n × Ω =>
      fderiv ℝ (kernel κ) (p.1-X p.2) (V p.2)) ((cube n).prod P) := by
    apply ((hV.norm.comp_snd (cube n)).const_mul D).mono'
    · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        ((((kernel_smooth n κ).continuous_fderiv (by simp)).measurable.comp
          (measurable_fst.sub (hX.comp measurable_snd))).aestronglyMeasurable.prodMk
            hV.aestronglyMeasurable.comp_snd)
    · exact Eventually.of_forall fun p => (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hD _) (norm_nonneg _))
  rw [integral_integral_swap hi]
  simp_rw [integral_kernel_fderiv_eq_zero]
  simp

variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Configuration d N → Configuration d N} {M' K' : ℝ≥0}
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) b)))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) b y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) b))
  {T : ℝ} (hT : 0 ≤ T) (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
  {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 μ)

include hbs hB hu

/-- The actual source convolution has zero mass at every physical time. -/
theorem convolvedSource_integral_eq_zero (κ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ x,convolvedSource hv' hb' hl' hT μ (u := u) κ t x ∂cube (N*d)) = 0 := by
  simp_rw [convolvedSource_eq_randomFlux hv' hb' hl' hT hbs hB μ hu κ _ ht]
  rw [integral_neg]
  have hX := (coordinateEquiv (N*d)).continuous.measurable.comp
    (PropagatedFlux.Flow.endpoint_measurable hv' hb' hl' hT ht)
  have hV := (coordinateEquiv (N*d)).toContinuousLinearMap.integrable_comp
    ((PropagatedFlux.Flow.velocity_memLp hv' hb' hl' hT (euclideanBrownianPathLaw d N T) ht
      (equivDrift_smooth _ hbs) (equivDrift_allDerivativesBounded _ hbs hB) μ hu).integrable (by norm_num))
  have he := integral_random_kernel_fderiv_eq_zero κ (μ.prod (euclideanBrownianPathLaw d N T)) hX hV
  dsimp only [Function.comp_def] at he
  have hn := congrArg Neg.neg he
  simp only [neg_zero] at hn
  convert hn using 1; rfl

/-- Zero mass in the exact Euclidean BCF/cube realization used by the energy. -/
theorem convolvedSourceBCF_integral_eq_zero (κ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ y,convolvedSourceBCF hv' hb' hl' hT hbs hB μ hu κ t y ∂cubePoint) = 0 := by
  rw [integral_cubePoint]
  simp_rw [convolvedSourceBCF_apply,ContinuousLinearEquiv.apply_symm_apply]
  exact convolvedSource_integral_eq_zero hv' hb' hl' hT hbs hB μ hu κ ht

end SharpWasserstein.PeriodicSourceConvolution
