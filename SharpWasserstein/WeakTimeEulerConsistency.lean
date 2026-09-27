import SharpWasserstein.TimeGeneratorUniform
import SharpWasserstein.BoundedConfigurationTests

/-! Uniform one-step consistency for actual weak evolutions with jointly
continuous bounded time-dependent drifts. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ContDiff Interval BoundedContinuousFunction
namespace SharpWasserstein.WeakEvolution
open WeightedTangent NoiseAverage
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {v : ℝ → Configuration d N → Configuration d N} {P : ℝ → Measure (Configuration d N)}
  (h : WeakEvolution v P)

include h

theorem uniform_time_generator_expectation {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ r, LipschitzWith K (v r)) (hM : ∀ r x, ‖v r x‖ ≤ M) (T : ℝ) (L L₁ L₂ : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, dist s t < δ →
      ∀ φ : Configuration d N → ℝ, ContDiff ℝ 2 φ → LipschitzWith L φ →
        LipschitzWith L₁ (fderiv ℝ φ) → LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ)) →
        ‖(∫ x, generator (v s) φ x ∂P s)-(∫ x, generator (v t) φ x ∂P t)‖ < ε := by
  obtain ⟨δ,hδ,hd⟩ := continuous_probabilityCurve_uniform_time_generators
    (probabilityCurve h) (continuous_probabilityCurve h) hvC hv hM T L L₁ L₂ hε
  refine ⟨δ,hδ,fun s hs t ht hst φ hφ hL hL₁ hL₂ => ?_⟩
  have hh := hd s hs t ht hst φ hφ hL hL₁ hL₂
  change ‖(∫ x, generator (v s) φ x ∂P (max 0 s))-(∫ x, generator (v t) φ x ∂P (max 0 t))‖ < ε at hh
  simpa only [max_eq_right hs.1,max_eq_right ht.1] using hh

theorem equation_time_bounded_configuration_interval {K M : ℝ≥0}
    (hv : ∀ r, LipschitzWith K (v r)) (hM : ∀ r x, ‖v r x‖ ≤ M) {φ : Configuration d N → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hB : AllDerivativesBounded φ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IntervalIntegrable (fun r => ∫ x, generator (v r) φ x ∂P r) volume s t ∧
      (∫ x, φ x ∂P t)-(∫ x, φ x ∂P s) = ∫ r in s..t, ∫ x, generator (v r) φ x ∂P r := by
  have hME (r : ℝ) (_ : 0 ≤ r) (x : Configuration d N) :
      ‖configurationEuclidean d N (v r x)‖ ≤ ‖(configurationEuclidean d N).toContinuousLinearMap‖*(M:ℝ) :=
    ((configurationEuclidean d N).toContinuousLinearMap.le_opNorm (v r x)).trans
      (mul_le_mul_of_nonneg_left (hM r x) (norm_nonneg _))
  have h₀s := equation_bounded_configuration h (fun r _ => (hv r).continuous.measurable) hME hφ hB s hs
  have h₀t := equation_bounded_configuration h (fun r _ => (hv r).continuous.measurable) hME hφ hB t ht
  refine ⟨h₀s.1.symm.trans h₀t.1,?_⟩
  rw [← intervalIntegral.integral_interval_sub_left h₀t.1 h₀s.1,← h₀t.2,← h₀s.2]
  ring

theorem uniform_time_weak_step_error {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ r, LipschitzWith K (v r)) (hM : ∀ r x, ‖v r x‖ ≤ M) (T : ℝ) (L L₁ L₂ : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t → t-s < δ →
      ∀ φ : Configuration d N → ℝ, ContDiff ℝ ∞ φ → AllDerivativesBounded φ →
        LipschitzWith L φ → LipschitzWith L₁ (fderiv ℝ φ) →
        LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ)) →
        ‖(∫ x, φ x ∂P t)-(∫ x, φ x ∂P s)-(t-s)*(∫ x, generator (v s) φ x ∂P s)‖ ≤ (t-s)*ε := by
  obtain ⟨δ,hδ,hd⟩ := uniform_time_generator_expectation h hvC hv hM T L L₁ L₂ hε
  refine ⟨δ,hδ,fun s hs t ht hst hsmall φ hφ hB hL hL₁ hL₂ => ?_⟩
  have heq := equation_time_bounded_configuration_interval h hv hM hφ hB hs.1 ht.1
  have he : (∫ x, φ x ∂P t)-(∫ x, φ x ∂P s)-(t-s)*(∫ x, generator (v s) φ x ∂P s) =
      ∫ r in s..t, (∫ x, generator (v r) φ x ∂P r)-(∫ x, generator (v s) φ x ∂P s) := by
    rw [intervalIntegral.integral_sub heq.1 intervalIntegrable_const,intervalIntegral.integral_const,
      heq.2,smul_eq_mul]
  rw [he]
  have hbound : ∀ r ∈ Ι s t, ‖(∫ x, generator (v r) φ x ∂P r)-(∫ x, generator (v s) φ x ∂P s)‖ ≤ ε := by
    intro r hr
    rw [uIoc_of_le hst] at hr
    have hrs : r ∈ Icc 0 T := ⟨hs.1.trans hr.1.le,hr.2.trans ht.2⟩
    have hdr : dist r s < δ := by
      rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hr.1.le)]
      exact (sub_le_sub_right hr.2 s).trans_lt hsmall
    exact (hd r hrs s hs hdr φ (hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hL hL₁ hL₂).le
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa only [abs_of_nonneg (sub_nonneg.mpr hst),mul_comm] using hnorm

end SharpWasserstein.WeakEvolution
