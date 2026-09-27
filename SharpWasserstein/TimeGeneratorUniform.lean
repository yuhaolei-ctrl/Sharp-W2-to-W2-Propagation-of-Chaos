import SharpWasserstein.ProbabilityParameterIntegral
import SharpWasserstein.ProbabilityUniformTests
import SharpWasserstein.QuantitativeGenerator

/-! Uniform generator continuity for actual narrow probability curves and
jointly continuous bounded time-dependent drifts. The time modulus follows
from the hypotheses; it is not an additional assumption on the weak solution. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace SharpWasserstein
variable {d N : ℕ}

theorem generator_drift_difference_norm_le
    {φ : Configuration d N → ℝ} {L : ℝ≥0} (hL : LipschitzWith L φ)
    (b c : Configuration d N → Configuration d N) (x : Configuration d N) :
    ‖generator b φ x-generator c φ x‖ ≤ (L:ℝ)*‖b x-c x‖ := by
  have he : generator b φ x-generator c φ x = fderiv ℝ φ x (b x-c x) := by
    simp only [generator_eq_laplacian_add_fderiv,map_sub]
    ring
  rw [he]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hL) (norm_nonneg _))

theorem integral_generator_drift_difference_le
    {v : ℝ → Configuration d N → Configuration d N}
    {K M : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (hM : ∀ t x, ‖v t x‖ ≤ M)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ 2 φ)
    {L L₁ L₂ : ℝ≥0} (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    (hL₂ : LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ)))
    (μ : ℝ → ProbabilityMeasure (Configuration d N)) (s t : ℝ) :
    ‖(∫ x, generator (v t) φ x ∂(μ s : Measure _))-
      (∫ x, generator (v s) φ x ∂(μ s : Measure _))‖ ≤
      (L:ℝ)*ProbabilityDriftVariation.variation v μ (t,s) := by
  have hGi (r : ℝ) : Integrable (generator (v r) φ) (μ s : Measure _) :=
    Integrable.mono' (integrable_const ((N*d:ℕ)*(L₁:ℝ)+L*M))
      (generator_lipschitz_of_derivatives hφ hL hL₁ hL₂ (hv r) (hM r)).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (generator_norm_le_of_derivatives hφ hL hL₁ (hM r)))
  have hvi : Integrable (fun x => ‖v t x-v s x‖) (μ s : Measure _) :=
    Integrable.mono' (integrable_const (2*(M:ℝ)))
      ((hv t).continuous.sub (hv s).continuous).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [norm_norm]
        exact (norm_sub_le _ _).trans (by linarith [hM t x,hM s x]))
  rw [← integral_sub (hGi t) (hGi s)]
  calc
    _ ≤ ∫ x, ‖generator (v t) φ x-generator (v s) φ x‖ ∂(μ s : Measure _) := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (L:ℝ)*‖v t x-v s x‖ ∂(μ s : Measure _) :=
      integral_mono ((hGi t).sub (hGi s)).norm (hvi.const_mul L)
        (fun x => generator_drift_difference_norm_le hL (v t) (v s) x)
    _ = _ := by rw [integral_const_mul]; rfl

theorem continuous_probabilityCurve_uniform_time_generators
    (μ : ℝ → ProbabilityMeasure (Configuration d N)) (hμ : Continuous μ)
    {v : ℝ → Configuration d N → Configuration d N} (hvC : Continuous (Function.uncurry v))
    {K M : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (hM : ∀ t x, ‖v t x‖ ≤ M)
    (T : ℝ) (L L₁ L₂ : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, dist s t < δ →
      ∀ φ : Configuration d N → ℝ, ContDiff ℝ 2 φ → LipschitzWith L φ →
        LipschitzWith L₁ (fderiv ℝ φ) → LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ)) →
        ‖(∫ x, generator (v s) φ x ∂(μ s : Measure _))-
          (∫ x, generator (v t) φ x ∂(μ t : Measure _))‖ < ε := by
  let A : ℝ≥0 := (N*d:ℕ)*L₁+L*M
  let D : ℝ≥0 := (N*d:ℕ)*L₂+L₁*M+L*K
  obtain ⟨δ₁,hδ₁,hd₁⟩ := continuous_probabilityCurve_uniform_lipschitz_tests
    μ hμ T A D (show 0 < ε/2 by positivity)
  have hden : 0 < 2*((L:ℝ)+1) := by positivity
  obtain ⟨δ₂,hδ₂,hd₂⟩ := ProbabilityDriftVariation.uniform_variation hvC hM μ hμ T
    (show 0 < ε/(2*((L:ℝ)+1)) from div_pos hε hden)
  refine ⟨min δ₁ δ₂,lt_min hδ₁ hδ₂,fun s hs t ht hst φ hφ hL hL₁ hL₂ => ?_⟩
  have hGn : ∀ x, ‖generator (v s) φ x‖ ≤ A := generator_norm_le_of_derivatives hφ hL hL₁ (hM s)
  have hGL : LipschitzWith D (generator (v s) φ) :=
    generator_lipschitz_of_derivatives hφ hL hL₁ hL₂ (hv s) (hM s)
  let f : Configuration d N →ᵇ ℝ := {
    toFun := generator (v s) φ
    continuous_toFun := hGL.continuous
    map_bounded' := ⟨2*(A:ℝ),fun x y => (dist_le_norm_add_norm _ _).trans (by linarith [hGn x,hGn y])⟩ }
  have hfn : ‖f‖ ≤ (A:ℝ) := (BoundedContinuousFunction.norm_le A.coe_nonneg).mpr hGn
  have hlaw := hd₁ s hs t ht (hst.trans_le (min_le_left _ _)) f hfn hGL
  change ‖(∫ x, generator (v s) φ x ∂(μ s : Measure _))-
    (∫ x, generator (v s) φ x ∂(μ t : Measure _))‖ < ε/2 at hlaw
  have hvar := hd₂ t ht s hs (hst.trans_le (min_le_right _ _))
  have hdrift := integral_generator_drift_difference_le hv hM hφ hL hL₁ hL₂ μ t s
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

end SharpWasserstein
