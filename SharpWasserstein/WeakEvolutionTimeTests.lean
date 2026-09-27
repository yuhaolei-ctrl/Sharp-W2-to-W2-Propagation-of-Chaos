import SharpWasserstein.WeakEvolutionBoundedTests
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Genuine time derivatives of bounded smooth observables of weak solutions.
The time dependence of the generator expectation is justified by narrow
continuity and the actual product law with a Dirac time coordinate. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff InnerProductSpace Interval BoundedContinuousFunction
namespace SharpWasserstein

/-- Jointly continuous bounded observables integrate continuously against an
actual narrowly continuous curve of probability measures. -/
theorem continuous_integral_varying_probability {E : Type*} [MeasurableSpace E]
    [PseudoMetricSpace E] [SecondCountableTopology E] [BorelSpace E]
    (μ : ℝ → ProbabilityMeasure E) (hμ : Continuous μ)
    (F : ℝ × E → ℝ) (hF : Continuous F) {C : ℝ} (hC : ∀ p, ‖F p‖ ≤ C) :
    Continuous (fun t ↦ ∫ x, F (t,x) ∂(μ t : Measure E)) := by
  let f : (ℝ × E) →ᵇ ℝ := {
    toFun := F
    continuous_toFun := hF
    map_bounded' := ⟨2*C, fun p q ↦ (dist_le_norm_add_norm (F p) (F q)).trans (by linarith [hC p, hC q])⟩ }
  have hp : Continuous (fun t ↦ (diracProba t).prod (μ t)) :=
    ProbabilityMeasure.continuous_prod.comp (continuous_diracProba.prodMk hμ)
  have hc := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp hp
  convert hc using 1
  funext t
  change (∫ x, F (t,x) ∂(μ t : Measure E)) =
    ∫ p, f p ∂((Measure.dirac t).prod (μ t : Measure E))
  rw [integral_prod _ (f.integrable _), integral_dirac]
  rfl

open WeightedTangent
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
namespace WeakEvolution
variable {v : ℝ → Configuration d N → Configuration d N}
  {P : ℝ → Measure (Configuration d N)} (h : WeakEvolution v P)

include h in
/-- The expectation of the genuine generator is continuous. This is proved
from actual weak-law continuity and a continuous bounded drift. -/
theorem continuous_generator_expectation
    (hv : Continuous (Function.uncurry v)) {M : ℝ}
    (hM : ∀ s x, ‖configurationEuclidean d N (v s x)‖ ≤ M)
    (f : Point (N*d) → ℝ) (hf : ContDiff ℝ ∞ f) {B D : ℝ}
    (hfb : ∀ x, ‖gradient f x‖ ≤ B) (hfd : ∀ x, |PDEPairings.laplacian f x| ≤ D) :
    Continuous (fun s ↦ ∫ x, generator (v (max 0 s)) (f ∘ configurationEuclidean d N) x ∂P (max 0 s)) := by
  apply continuous_integral_varying_probability (probabilityCurve h) (continuous_probabilityCurve h)
    (fun p ↦ generator (v (max 0 p.1)) (f ∘ configurationEuclidean d N) p.2)
  · simp_rw [generator_pullback]
    apply Continuous.add
    · exact (BochnerIdentity.smooth_laplacian hf).continuous.comp
        ((configurationEuclidean d N).continuous.comp continuous_snd)
    · exact (((configurationEuclidean d N).continuous.comp
        (hv.comp ((continuous_const.max continuous_fst).prodMk continuous_snd))).inner
        ((BochnerIdentity.smooth_gradient hf).continuous.comp
          ((configurationEuclidean d N).continuous.comp continuous_snd)))
  · intro p
    exact generator_pullback_norm_le f (v (max 0 p.1)) (hM _) hfb hfd p.2

include h in
/-- Actual bounded continuous observables are continuous along the weak law. -/
theorem continuous_integral_bounded
    (f : Configuration d N → ℝ) (hf : Continuous f) {A : ℝ} (hA : ∀ x, ‖f x‖ ≤ A) :
    Continuous (fun s ↦ ∫ x, f x ∂P (max 0 s)) := by
  exact continuous_integral_varying_probability (probabilityCurve h) (continuous_probabilityCurve h)
    (fun p ↦ f p.2) (hf.comp continuous_snd) (fun p ↦ hA p.2)

include h in
/-- Every bounded smooth observable with bounded first and second generator
terms has its claimed genuine time derivative at each positive time. -/
theorem hasDerivAt_integral_bounded_smooth
    (hv : Continuous (Function.uncurry v)) {M : ℝ}
    (hM : ∀ s x, ‖configurationEuclidean d N (v s x)‖ ≤ M)
    (f : Point (N*d) → ℝ) (hf : ContDiff ℝ ∞ f) {A B D : ℝ}
    (hfa : ∀ x, |f x| ≤ A) (hfb : ∀ x, ‖gradient f x‖ ≤ B)
    (hfd : ∀ x, |PDEPairings.laplacian f x| ≤ D) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ ∫ x, f (configurationEuclidean d N x) ∂P s)
      (∫ x, generator (v t) (f ∘ configurationEuclidean d N) x ∂P t) t := by
  let G (s : ℝ) := ∫ x, generator (v (max 0 s)) (f ∘ configurationEuclidean d N) x ∂P (max 0 s)
  have hGc : Continuous G := continuous_generator_expectation h hv hM f hf hfb hfd
  have hder : HasDerivAt (fun s ↦ (∫ x, f (configurationEuclidean d N x) ∂P 0) + ∫ u in 0..s, G u) (G t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hGc.intervalIntegrable 0 t)
      hGc.stronglyMeasurable.stronglyMeasurableAtFilter hGc.continuousAt).const_add _
  have hEq : (fun s ↦ ∫ x, f (configurationEuclidean d N x) ∂P s) =ᶠ[𝓝 t]
      (fun s ↦ (∫ x, f (configurationEuclidean d N x) ∂P 0) + ∫ u in 0..s, G u) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    have heq := (equation_bounded_smooth h
      (fun u _ ↦ (hv.comp (continuous_const.prodMk continuous_id)).measurable)
      (fun u _ ↦ hM u) f hf hfa hfb hfd s hs.le).2
    have hi : (∫ u in 0..s, G u) =
        ∫ u in 0..s, ∫ x, generator (v u) (f ∘ configurationEuclidean d N) x ∂P u := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu0 : 0 ≤ u := (show u ∈ Icc 0 s by simpa only [uIcc_of_le hs.le] using hu).1
      simp only [G, max_eq_right hu0]
    rw [hi]
    linarith
  have hd := hder.congr_of_eventuallyEq hEq
  simpa only [G, max_eq_right ht.le] using hd

include h in
/-- The genuine weak identity for separated time-dependent tests `a(t) f(x)`.
Both temporal differentiation and endpoint continuity are derived for the actual weak law. -/
theorem equation_timeFactor_bounded_smooth
    (hv : Continuous (Function.uncurry v)) {M : ℝ}
    (hM : ∀ s x, ‖configurationEuclidean d N (v s x)‖ ≤ M)
    (f : Point (N*d) → ℝ) (hf : ContDiff ℝ ∞ f) {A B D : ℝ}
    (hfa : ∀ x, |f x| ≤ A) (hfb : ∀ x, ‖gradient f x‖ ≤ B)
    (hfd : ∀ x, |PDEPairings.laplacian f x| ≤ D)
    (a a' : ℝ → ℝ) (ha : ∀ s, HasDerivAt a (a' s) s)
    (t : ℝ) (ht : 0 ≤ t) (ha' : ContinuousOn a' (Icc 0 t)) :
    a t * (∫ x, f (configurationEuclidean d N x) ∂P t) -
        a 0 * (∫ x, f (configurationEuclidean d N x) ∂P 0) =
      ∫ s in 0..t,
        a' s * (∫ x, f (configurationEuclidean d N x) ∂P s) +
        a s * (∫ x, generator (v s) (f ∘ configurationEuclidean d N) x ∂P s) := by
  let F (s : ℝ) := ∫ x, f (configurationEuclidean d N x) ∂P s
  let G (s : ℝ) := ∫ x, generator (v s) (f ∘ configurationEuclidean d N) x ∂P s
  have hFc : ContinuousOn F (Icc 0 t) := by
    apply (continuous_integral_bounded h (f ∘ configurationEuclidean d N)
      (hf.continuous.comp (configurationEuclidean d N).continuous) (fun x ↦ hfa _)).continuousOn.congr
    intro s hs
    simp only [F, max_eq_right hs.1, Function.comp_apply]
  have hGc : ContinuousOn G (Icc 0 t) := by
    apply (continuous_generator_expectation h hv hM f hf hfb hfd).continuousOn.congr
    intro s hs
    simp only [G, max_eq_right hs.1]
  have hac : Continuous a := continuous_iff_continuousAt.mpr fun s ↦ (ha s).continuousAt
  have hd (s : ℝ) (hs : s ∈ Ioo 0 t) :
      HasDerivAt (fun u ↦ a u * F u) (a' s * F s + a s * G s) s :=
    (ha s).mul (hasDerivAt_integral_bounded_smooth h hv hM f hf hfa hfb hfd hs.1)
  have hcont : ContinuousOn (fun s ↦ a' s * F s + a s * G s) (Icc 0 t) :=
    fun s hs ↦ ((ha' s hs).mul (hFc s hs)).add
      ((hac.continuousAt.continuousWithinAt).mul (hGc s hs))
  have hint : IntervalIntegrable (fun s ↦ a' s * F s + a s * G s) volume 0 t :=
    (show ContinuousOn (fun s ↦ a' s * F s + a s * G s) (uIcc 0 t) by
      simpa only [uIcc_of_le ht, Pi.add_apply, Pi.mul_apply] using hcont).intervalIntegrable
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
    (hac.continuousOn.mul hFc) hd hint).symm

end WeakEvolution
end SharpWasserstein
