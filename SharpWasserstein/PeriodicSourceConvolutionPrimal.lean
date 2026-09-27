import SharpWasserstein.PeriodicSourceConvolutionAction
import SharpWasserstein.PropagatedSourceEquationBrownian
import SharpWasserstein.WeakTimeEulerConsistency
import SharpWasserstein.BoundedDerivativeLinear

/-! The actual Brownian primal equation on bounded smooth tests, including
periodic convolution kernels. It follows from the constructed weak law and
its proved bounded-test extension. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ENNReal ContDiff Interval
namespace SharpWasserstein.PeriodicSourceConvolution
open FlowSemigroupDerivative PropagatedSourceEquation WeightedTangent NoiseAverage
variable {d N : ℕ} {b : Configuration d N → Configuration d N} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ,∀ x,‖b x‖ ≤ M) (hl : ∀ _ : ℝ,LipschitzWith K b)
  {T : ℝ} (hT : 0 ≤ T)
  [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]

/-- Every bounded smooth test with actual bounded derivatives satisfies the
primal Brownian equation on every subinterval of the fixed horizon. -/
theorem brownian_primal_bounded
    {F : Configuration d N → ℝ} (hF : ContDiff ℝ ∞ F) (hBF : AllDerivativesBounded F)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : Configuration d N) :
    expectation hv hb hl hT (BrownianNoise.configurationLaw d N T) (t := t) F x-
      expectation hv hb hl hT (BrownianNoise.configurationLaw d N T) (t := s) F x =
        ∫ r in s..t,clampedExpectation hv hb hl hT (BrownianNoise.configurationLaw d N T)
          (generator b F) r x := by
  have hμ : HasSecondMoment (Measure.dirac x) := by
    simp only [HasSecondMoment,lintegral_dirac]
    exact ENNReal.ofReal_lt_top
  have he := WeakEvolution.equation_time_bounded_configuration_interval
    (BrownianFlow.globalLaw_weakEvolution hv hb hl (Measure.dirac x) hμ) hl hb hF hBF hs.1 ht.1
  have hdf := (contDiff_infty_iff_fderiv.mp hF).2
  have hddf := (contDiff_infty_iff_fderiv.mp hdf).2
  obtain ⟨L,hL⟩ := hBF.lipschitz (hF.differentiable (by simp))
  obtain ⟨L₁,hL₁⟩ := hBF.fderiv.lipschitz (hdf.differentiable (by simp))
  obtain ⟨L₂,hL₂⟩ := hBF.fderiv.fderiv.lipschitz (hddf.differentiable (by simp))
  have hG : Continuous (generator b F) :=
    (generator_lipschitz_of_derivatives
      (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hL hL₁ hL₂ (hl 0) (hb 0)).continuous
  rw [brownianExpectation_eq_globalLaw hv hb hl hT x hF.continuous ht,
    brownianExpectation_eq_globalLaw hv hb hl hT x hF.continuous hs,he.2]
  apply intervalIntegral.integral_congr
  intro r hr
  have hrT : r ∈ Icc 0 T := ⟨(le_min hs.1 ht.1).trans hr.1,hr.2.trans (max_le hs.2 ht.2)⟩
  dsimp only
  rw [clampedExpectation_of_mem hv hb hl hT _ _ hrT]
  exact (brownianExpectation_eq_globalLaw hv hb hl hT x hG hrT).symm

include hv hb hl in
/-- Exact Euclidean conjugation supplies the bounded-test equation for the
same actual sqrt-two Brownian paths used by propagated finite-energy sources. -/
theorem euclidean_brownian_primal_bounded {M' K' : ℝ≥0}
    (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) b)))
    (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) b y‖ ≤ M')
    (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) b))
    {F : Point (N*d) → ℝ} (hF : ContDiff ℝ ∞ F) (hBF : AllDerivativesBounded F)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (y : Point (N*d)) :
    expectation hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (t := t) F y-
      expectation hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (t := s) F y =
        ∫ r in s..t,clampedExpectation hv' hb' hl' hT (euclideanBrownianPathLaw d N T)
          (euclideanGenerator b F) r y := by
  let L := configurationEuclidean d N
  have hp : ContDiff ℝ ∞ (F ∘ L) := hF.comp L.contDiff
  have hBp : AllDerivativesBounded (F ∘ L) := hBF.comp_linear hF L.toContinuousLinearMap
  have he (r : ℝ) (hr : r ∈ Icc 0 T) :
      expectation hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (t := r) F y =
        expectation hv hb hl hT (BrownianNoise.configurationLaw d N T) (t := r) (F ∘ L) (L.symm y) := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply,euclideanBrownianPathLaw,L] using
      expectation_equiv L hv hb hl hv' hb' hl' hT (BrownianNoise.configurationLaw d N T)
        (L.symm y) hr hF.continuous
  rw [he t ht,he s hs,brownian_primal_bounded hv hb hl hT hp hBp hs ht]
  have hdf := (contDiff_infty_iff_fderiv.mp hp).2
  have hddf := (contDiff_infty_iff_fderiv.mp hdf).2
  obtain ⟨A,hA⟩ := hBp.lipschitz (hp.differentiable (by simp))
  obtain ⟨A₁,hA₁⟩ := hBp.fderiv.lipschitz (hdf.differentiable (by simp))
  obtain ⟨A₂,hA₂⟩ := hBp.fderiv.fderiv.lipschitz (hddf.differentiable (by simp))
  have hG : Continuous (euclideanGenerator b F) :=
    (generator_lipschitz_of_derivatives
      (hp.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hA hA₁ hA₂ (hl 0) (hb 0)).continuous.comp L.symm.continuous
  apply intervalIntegral.integral_congr
  intro r hr
  have hrT : r ∈ Icc 0 T := ⟨(le_min hs.1 ht.1).trans hr.1,hr.2.trans (max_le hs.2 ht.2)⟩
  dsimp only
  rw [clampedExpectation_of_mem hv hb hl hT _ _ hrT,
    clampedExpectation_of_mem hv' hb' hl' hT _ _ hrT]
  have hh := expectation_equiv L hv hb hl hv' hb' hl' hT (BrownianNoise.configurationLaw d N T)
    (L.symm y) hrT hG
  have hfun : euclideanGenerator b F ∘ L = generator b (F ∘ L) := by
    funext x
    simp only [euclideanGenerator,Function.comp_def,ContinuousLinearEquiv.symm_apply_apply,L]
  simpa only [ContinuousLinearEquiv.apply_symm_apply,hfun,euclideanBrownianPathLaw,L] using hh.symm

end SharpWasserstein.PeriodicSourceConvolution
