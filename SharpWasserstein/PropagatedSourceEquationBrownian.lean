import SharpWasserstein.PropagatedSourceEquationConjugacy
import SharpWasserstein.PropagatedSourceEquationMeasurable
import SharpWasserstein.BrownianFlowWeak

/-! The primal integral identity for the actual Brownian input law, first in
configuration coordinates and then under the exact Euclidean coordinate map. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff Interval
namespace SharpWasserstein.PropagatedSourceEquation
open FlowSemigroupDerivative WeightedTangent
variable {d N : ℕ} {b : Configuration d N → Configuration d N} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)
  {T : ℝ} (hT : 0 ≤ T)

theorem brownianExpectation_eq_globalLaw (x : Configuration d N)
    {φ : Configuration d N → ℝ} (hφ : Continuous φ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    expectation hv hb hl hT (BrownianNoise.configurationLaw d N T) (t := t) φ x =
      ∫ z,φ z ∂BrownianFlow.globalLaw hv hb hl (Measure.dirac x) t := by
  rw [BrownianFlow.globalLaw_eq hv hb hl hT (Measure.dirac x) ht,
    BrownianFlow.law_integral_eq hv hb hl hT (Measure.dirac x) hφ ht,Measure.dirac_prod]
  have hm : AEStronglyMeasurable
      (fun p : Configuration d N × C(Icc 0 T,Configuration d N) =>
        φ (BoundedFlow.flow hv hb hl hT p.1 p.2 t))
      ((BrownianNoise.configurationLaw d N T).map (fun w => (x,w))) :=
    (hφ.comp (BoundedFlow.flow_continuous hv hb hl hT ht)).aestronglyMeasurable
  exact (integral_map measurable_prodMk_left.aemeasurable hm).symm

/-- The actual Brownian weak equation supplies the primal identity on every
subinterval, for the same fixed-horizon path law. -/
theorem brownian_primal_identity
    {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : Configuration d N) :
    expectation hv hb hl hT (BrownianNoise.configurationLaw d N T) (t := t) φ x -
      expectation hv hb hl hT (BrownianNoise.configurationLaw d N T) (t := s) φ x =
        ∫ r in s..t,clampedExpectation hv hb hl hT (BrownianNoise.configurationLaw d N T)
          (generator b φ) r x := by
  let g : ℝ → ℝ := fun r => ∫ z,generator b φ z ∂BrownianFlow.globalLaw hv hb hl (Measure.dirac x) r
  have he (r : ℝ) (hr : r ∈ Icc 0 T) :
      expectation hv hb hl hT (BrownianNoise.configurationLaw d N T) (t := r) φ x - φ x =
        ∫ a in (0:ℝ)..r,g a := by
    rw [brownianExpectation_eq_globalLaw hv hb hl hT x hφ.1.continuous hr]
    have hh := BrownianFlow.globalLaw_equation hv hb hl (Measure.dirac x) hφ hr.1
    simpa only [BrownianFlow.globalLaw_initial,integral_dirac,g] using hh
  calc
    _ = (expectation hv hb hl hT (BrownianNoise.configurationLaw d N T) (t := t) φ x - φ x) -
        (expectation hv hb hl hT (BrownianNoise.configurationLaw d N T) (t := s) φ x - φ x) := by ring
    _ = (∫ r in (0:ℝ)..t,g r)-(∫ r in (0:ℝ)..s,g r) := by rw [he t ht,he s hs]
    _ = ∫ r in s..t,g r := intervalIntegral.integral_interval_sub_left
      (BrownianFlow.globalLaw_timeIntegrable hv hb hl (Measure.dirac x) hφ ht.1)
      (BrownianFlow.globalLaw_timeIntegrable hv hb hl (Measure.dirac x) hφ hs.1)
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hrT : r ∈ Icc 0 T := ⟨(le_min hs.1 ht.1).trans hr.1,hr.2.trans (max_le hs.2 ht.2)⟩
      dsimp only
      rw [clampedExpectation_of_mem hv hb hl hT _ _ hrT]
      exact (brownianExpectation_eq_globalLaw hv hb hl hT x
        (CompactGenerator.generator_continuous hφ (hl 0).continuous) hrT).symm

variable [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]

/-- The genuine Brownian path law in the exact unnormalized Euclidean coordinates. -/
def euclideanBrownianPathLaw (d N : ℕ) (T : ℝ) : Measure C(Icc 0 T,Point (N*d)) :=
  (BrownianNoise.configurationLaw d N T).map (equivPath (configurationEuclidean d N))

instance euclideanBrownianPathLaw_probability : IsProbabilityMeasure (euclideanBrownianPathLaw d N T) :=
  Measure.isProbabilityMeasure_map (equivPath_continuous (configurationEuclidean d N)).measurable.aemeasurable

/-- The manuscript generator expressed exactly in Euclidean coordinates. -/
def euclideanGenerator (b : Configuration d N → Configuration d N) (F : Point (N*d) → ℝ) :
    Point (N*d) → ℝ := generator b (F ∘ configurationEuclidean d N) ∘ (configurationEuclidean d N).symm

omit [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))] in
/-- The actual generator preserves compact smooth tests when the drift is smooth. -/
theorem euclideanGenerator_test (hbs : ContDiff ℝ ∞ b) (φ : Test (N*d)) :
    ContDiff ℝ ∞ (euclideanGenerator b φ) ∧ HasCompactSupport (euclideanGenerator b φ) :=
  smoothCompactTest_euclidean (CompactGenerator.generator_smooth (smoothCompactTest_pullback φ) hbs)

def euclideanGeneratorTest (hbs : ContDiff ℝ ∞ b) (φ : Test (N*d)) : Test (N*d) :=
  ⟨euclideanGenerator b φ,euclideanGenerator_test hbs φ⟩

include hv hb hl in
omit [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))] in
/-- The actual Euclidean Brownian expectation satisfies the primal weak
identity. Its Lipschitz bound is the supplied true Euclidean drift bound. -/
theorem euclidean_brownian_primal_identity {M' K' : ℝ≥0}
    (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) b)))
    (hb' : ∀ _ : ℝ, ∀ y, ‖equivDrift (configurationEuclidean d N) b y‖ ≤ M')
    (hl' : ∀ _ : ℝ, LipschitzWith K' (equivDrift (configurationEuclidean d N) b))
    (φ : Test (N*d)) {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (y : Point (N*d)) :
    expectation hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (t := t) φ y -
      expectation hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (t := s) φ y =
        ∫ r in s..t,clampedExpectation hv' hb' hl' hT (euclideanBrownianPathLaw d N T)
          (euclideanGenerator b φ) r y := by
  let L := configurationEuclidean d N
  have he (r : ℝ) (hr : r ∈ Icc 0 T) :
      expectation hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (t := r) φ y =
        expectation hv hb hl hT (BrownianNoise.configurationLaw d N T) (t := r)
          ((φ : Point (N*d) → ℝ) ∘ L) (L.symm y) := by
    simpa only [euclideanBrownianPathLaw, L, ContinuousLinearEquiv.apply_symm_apply] using
      expectation_equiv L hv hb hl hv' hb' hl' hT (BrownianNoise.configurationLaw d N T)
        (L.symm y) hr φ.property.1.continuous
  rw [he t ht,he s hs,brownian_primal_identity hv hb hl hT (smoothCompactTest_pullback φ) hs ht]
  apply intervalIntegral.integral_congr
  intro r hr
  have hrT : r ∈ Icc 0 T := ⟨(le_min hs.1 ht.1).trans hr.1,hr.2.trans (max_le hs.2 ht.2)⟩
  dsimp only
  rw [clampedExpectation_of_mem hv hb hl hT _ _ hrT,
    clampedExpectation_of_mem hv' hb' hl' hT _ _ hrT]
  have hG : Continuous (euclideanGenerator b φ) :=
    (CompactGenerator.generator_continuous (smoothCompactTest_pullback φ) (hl 0).continuous).comp L.symm.continuous
  have hh := expectation_equiv L hv hb hl hv' hb' hl' hT (BrownianNoise.configurationLaw d N T)
    (L.symm y) hrT hG
  have hfun : euclideanGenerator b φ ∘ L = generator b ((φ : Point (N*d) → ℝ) ∘ L) := by
    funext x
    simp only [euclideanGenerator,Function.comp_def,ContinuousLinearEquiv.symm_apply_apply,L]
  simpa only [ContinuousLinearEquiv.apply_symm_apply,hfun,euclideanBrownianPathLaw,L] using hh.symm

end SharpWasserstein.PropagatedSourceEquation
