module

public import SharpWasserstein.Compat
public import SharpWasserstein.EulerianTransportTests
public import SharpWasserstein.ProbabilityParameterIntegral
public import SharpWasserstein.ProbabilityUniformTests

@[expose] public section

/-! The actual weak continuity equation with bounded smooth tests. Narrow
continuity yields the uniform test modulus needed for deterministic Euler
comparison; no Lagrangian representation or transport estimate is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ContDiff Interval BoundedContinuousFunction
namespace SharpWasserstein.EulerianTransport
open NoiseAverage
variable {d N : ℕ}

/-- A zero-diffusion weak equation on a prescribed time interval. The test
class contains compact smooth tests and is stable under the explicitly
constructed deterministic Euler pullbacks. -/
structure WeakContinuity (v : ℝ → Configuration d N → Configuration d N)
    (μ : ℝ → ProbabilityMeasure (Configuration d N)) (T : ℝ) : Prop where
  continuous : Continuous μ
  equation : ∀ φ : Configuration d N → ℝ, ContDiff ℝ ∞ φ → AllDerivativesBounded φ →
    ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      IntervalIntegrable (fun r => ∫ x, generator (v r) φ x ∂(μ r : Measure _)) volume s t ∧
      (∫ x, φ x ∂(μ t : Measure _)) - (∫ x, φ x ∂(μ s : Measure _)) =
        ∫ r in s..t, ∫ x, generator (v r) φ x ∂(μ r : Measure _)

theorem generator_norm_le {φ : Configuration d N → ℝ} {L M : ℝ≥0}
    (hL : LipschitzWith L φ) {b : Configuration d N → Configuration d N}
    (hM : ∀ x, ‖b x‖ ≤ M) (x : Configuration d N) : ‖generator b φ x‖ ≤ (L:ℝ)*M :=
  (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hL) (hM x) (norm_nonneg _) L.coe_nonneg)

theorem generator_lipschitz {φ : Configuration d N → ℝ} {L L₁ K M : ℝ≥0}
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    {b : Configuration d N → Configuration d N} (hb : LipschitzWith K b)
    (hM : ∀ x, ‖b x‖ ≤ M) : LipschitzWith (L₁*M+L*K) (generator b φ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have he : generator b φ x - generator b φ y =
      (fderiv ℝ φ x-fderiv ℝ φ y) (b x)+fderiv ℝ φ y (b x-b y) := by
    simp only [generator, sub_apply, map_sub]
    ring
  rw [he]
  calc
    _ ≤ ‖(fderiv ℝ φ x-fderiv ℝ φ y) (b x)‖+‖fderiv ℝ φ y (b x-b y)‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ φ x-fderiv ℝ φ y‖*‖b x‖+‖fderiv ℝ φ y‖*‖b x-b y‖ :=
      add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ ((L₁:ℝ)*‖x-y‖)*M+L*((K:ℝ)*‖x-y‖) :=
      add_le_add (mul_le_mul (hL₁.norm_sub_le x y) (hM x) (norm_nonneg _) (by positivity))
        (mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hL) (hb.norm_sub_le x y) (norm_nonneg _) L.coe_nonneg)
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul, dist_eq_norm]; ring

theorem generator_drift_difference_le {φ : Configuration d N → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (b c : Configuration d N → Configuration d N) (x : Configuration d N) :
    ‖generator b φ x-generator c φ x‖ ≤ (L:ℝ)*‖b x-c x‖ := by
  rw [generator, generator, ← map_sub]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hL) (norm_nonneg _))

theorem integral_generator_drift_difference_le
    {v : ℝ → Configuration d N → Configuration d N} {K M : ℝ≥0}
    (hv : ∀ t, LipschitzWith K (v t)) (hM : ∀ t x, ‖v t x‖ ≤ M)
    {φ : Configuration d N → ℝ} {L L₁ : ℝ≥0}
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    (μ : ℝ → ProbabilityMeasure (Configuration d N)) (s t : ℝ) :
    ‖(∫ x, generator (v t) φ x ∂(μ s : Measure _))-
      (∫ x, generator (v s) φ x ∂(μ s : Measure _))‖ ≤
      (L:ℝ)*ProbabilityDriftVariation.variation v μ (t,s) := by
  have hGi (r : ℝ) : Integrable (generator (v r) φ) (μ s : Measure _) :=
    Integrable.of_bound (generator_lipschitz hL hL₁ (hv r) (hM r)).continuous.aestronglyMeasurable
      ((L:ℝ)*M) (Eventually.of_forall (generator_norm_le hL (hM r)))
  have hvi : Integrable (fun x => ‖v t x-v s x‖) (μ s : Measure _) :=
    Integrable.of_bound ((hv t).continuous.sub (hv s).continuous).norm.aestronglyMeasurable (2*(M:ℝ))
      (Eventually.of_forall fun x => by
        rw [norm_norm]
        exact (norm_sub_le _ _).trans (by linarith [hM t x,hM s x]))
  rw [← integral_sub (hGi t) (hGi s)]
  calc
    _ ≤ ∫ x, ‖generator (v t) φ x-generator (v s) φ x‖ ∂(μ s : Measure _) := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (L:ℝ)*‖v t x-v s x‖ ∂(μ s : Measure _) :=
      integral_mono ((hGi t).sub (hGi s)).norm (hvi.const_mul L)
        (fun x => generator_drift_difference_le hL (v t) (v s) x)
    _ = _ := by rw [integral_const_mul]; rfl

/-- Uniform continuity of actual first-order generator expectations for an entire
bounded-Lipschitz test family, derived from the narrow curve and joint drift continuity. -/
theorem uniform_generator_expectation
    (μ : ℝ → ProbabilityMeasure (Configuration d N)) (hμ : Continuous μ)
    {v : ℝ → Configuration d N → Configuration d N} (hvC : Continuous (Function.uncurry v))
    {K M : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (hM : ∀ t x, ‖v t x‖ ≤ M)
    (T : ℝ) (L L₁ : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, dist s t < δ →
      ∀ φ : Configuration d N → ℝ, LipschitzWith L φ → LipschitzWith L₁ (fderiv ℝ φ) →
        ‖(∫ x, generator (v s) φ x ∂(μ s : Measure _))-
          (∫ x, generator (v t) φ x ∂(μ t : Measure _))‖ < ε := by
  let A : ℝ≥0 := L*M
  let D : ℝ≥0 := L₁*M+L*K
  obtain ⟨δ₁,hδ₁,hd₁⟩ := continuous_probabilityCurve_uniform_lipschitz_tests
    μ hμ T A D (show 0 < ε/2 by positivity)
  have hden : 0 < 2*((L:ℝ)+1) := by positivity
  obtain ⟨δ₂,hδ₂,hd₂⟩ := ProbabilityDriftVariation.uniform_variation hvC hM μ hμ T
    (show 0 < ε/(2*((L:ℝ)+1)) from div_pos hε hden)
  refine ⟨min δ₁ δ₂,lt_min hδ₁ hδ₂,fun s hs t ht hst φ hL hL₁ => ?_⟩
  have hGn : ∀ x, ‖generator (v s) φ x‖ ≤ A := generator_norm_le hL (hM s)
  have hGL : LipschitzWith D (generator (v s) φ) := generator_lipschitz hL hL₁ (hv s) (hM s)
  let f : Configuration d N →ᵇ ℝ := {
    toFun := generator (v s) φ
    continuous_toFun := hGL.continuous
    map_bounded' := ⟨2*(A:ℝ),fun x y => (dist_le_norm_add_norm _ _).trans (by linarith [hGn x,hGn y])⟩ }
  have hfn : ‖f‖ ≤ (A:ℝ) := (BoundedContinuousFunction.norm_le A.coe_nonneg).mpr hGn
  have hlaw := hd₁ s hs t ht (hst.trans_le (min_le_left _ _)) f hfn hGL
  change ‖(∫ x, generator (v s) φ x ∂(μ s : Measure _))-
    (∫ x, generator (v s) φ x ∂(μ t : Measure _))‖ < ε/2 at hlaw
  have hvar := hd₂ t ht s hs (hst.trans_le (min_le_right _ _))
  have hdrift := integral_generator_drift_difference_le hv hM hL hL₁ μ t s
  have hsmall : (L:ℝ)*ProbabilityDriftVariation.variation v μ (s,t) < ε/2 := by
    have hn : 0 ≤ ProbabilityDriftVariation.variation v μ (s,t) := integral_nonneg (fun _ => norm_nonneg _)
    have hvb : (2*((L:ℝ)+1))*ProbabilityDriftVariation.variation v μ (s,t) < ε := by
      have hh := (lt_div_iff₀ hden).mp hvar
      nlinarith
    nlinarith
  have halg : (∫ x, generator (v s) φ x ∂(μ s : Measure _))-
      (∫ x, generator (v t) φ x ∂(μ t : Measure _)) =
      ((∫ x, generator (v s) φ x ∂(μ s : Measure _))-
       (∫ x, generator (v s) φ x ∂(μ t : Measure _)))+
      ((∫ x, generator (v s) φ x ∂(μ t : Measure _))-
       (∫ x, generator (v t) φ x ∂(μ t : Measure _))) := by ring
  rw [halg]
  exact (norm_add_le _ _).trans_lt (by linarith [hdrift.trans_lt hsmall])

theorem WeakContinuity.uniform_weak_step_error
    {v : ℝ → Configuration d N → Configuration d N}
    {μ : ℝ → ProbabilityMeasure (Configuration d N)} {T : ℝ} (h : WeakContinuity v μ T)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t, LipschitzWith K (v t)) (hM : ∀ t x, ‖v t x‖ ≤ M)
    (L L₁ : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t → t-s < δ →
      ∀ φ : Configuration d N → ℝ, ContDiff ℝ ∞ φ → AllDerivativesBounded φ →
        LipschitzWith L φ → LipschitzWith L₁ (fderiv ℝ φ) →
        ‖(∫ x, φ x ∂(μ t : Measure _))-(∫ x, φ x ∂(μ s : Measure _))-
          (t-s)*(∫ x, generator (v s) φ x ∂(μ s : Measure _))‖ ≤ (t-s)*ε := by
  obtain ⟨δ,hδ,hd⟩ := uniform_generator_expectation μ h.continuous hvC hv hM T L L₁ hε
  refine ⟨δ,hδ,fun s hs t ht hst hsmall φ hφ hB hL hL₁ => ?_⟩
  have heq := h.equation φ hφ hB s hs t ht
  have he : (∫ x, φ x ∂(μ t : Measure _))-(∫ x, φ x ∂(μ s : Measure _))-
      (t-s)*(∫ x, generator (v s) φ x ∂(μ s : Measure _)) =
      ∫ r in s..t, (∫ x, generator (v r) φ x ∂(μ r : Measure _))-
        (∫ x, generator (v s) φ x ∂(μ s : Measure _)) := by
    rw [intervalIntegral.integral_sub heq.1 intervalIntegrable_const,intervalIntegral.integral_const,
      heq.2,smul_eq_mul]
  rw [he]
  have hbound : ∀ r ∈ Ι s t,
      ‖(∫ x, generator (v r) φ x ∂(μ r : Measure _))-
        (∫ x, generator (v s) φ x ∂(μ s : Measure _))‖ ≤ ε := by
    intro r hr
    rw [uIoc_of_le hst] at hr
    have hrs : r ∈ Icc 0 T := ⟨hs.1.trans hr.1.le,hr.2.trans ht.2⟩
    have hdr : dist r s < δ := by
      rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hr.1.le)]
      exact (sub_le_sub_right hr.2 s).trans_lt hsmall
    exact (hd r hrs s hs hdr φ hL hL₁).le
  simpa only [abs_of_nonneg (sub_nonneg.mpr hst),mul_comm] using
    intervalIntegral.norm_integral_le_of_norm_le_const hbound

/-- The explicitly constructed Euler test has a genuine integrated consistency error. -/
theorem integral_step_error_bound {b : Configuration d N → Configuration d N}
    {K M L L₁ : ℝ≥0} (hb : LipschitzWith K b) (hM : ∀ x, ‖b x‖ ≤ M)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hB : AllDerivativesBounded φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (δ : ℝ≥0) :
    ‖(∫ x, step b δ φ x ∂μ)-(∫ x, φ x ∂μ)-(δ:ℝ)*(∫ x, generator b φ x ∂μ)‖ ≤
      (L₁:ℝ)*(δ:ℝ)^2*(M:ℝ)^2 := by
  obtain ⟨A,_,hA⟩ := hB.bounded
  have hiφ : Integrable φ μ := Integrable.of_bound hφ.continuous.aestronglyMeasurable A
    (Eventually.of_forall hA)
  have hiG : Integrable (generator b φ) μ := Integrable.of_bound
    (generator_lipschitz hL hL₁ hb hM).continuous.aestronglyMeasurable ((L:ℝ)*M)
    (Eventually.of_forall (generator_norm_le hL hM))
  have hist : Integrable (step b δ φ) μ := Integrable.of_bound
    (lipschitz_step hb δ hL).continuous.aestronglyMeasurable A
    (Eventually.of_forall (fun x => hA (BackwardEuler.mean b δ x)))
  have he : (∫ x, step b δ φ x ∂μ)-(∫ x, φ x ∂μ)-(δ:ℝ)*(∫ x, generator b φ x ∂μ) =
      ∫ x, step b δ φ x-φ x-(δ:ℝ)*generator b φ x ∂μ := by
    have hs := integral_sub (hist.sub hiφ) (hiG.const_mul (δ:ℝ))
    simp only [Pi.sub_apply] at hs
    rw [hs,integral_sub hist hiφ,integral_const_mul]
  rw [he]
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ := μ)
    (Eventually.of_forall (step_error_le hM δ (hφ.differentiable (by simp)) hL₁))

end SharpWasserstein.EulerianTransport
