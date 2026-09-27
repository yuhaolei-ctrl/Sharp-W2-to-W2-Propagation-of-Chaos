import SharpWasserstein.ProbabilityUniformTests
import SharpWasserstein.QuantitativeGenerator
import SharpWasserstein.BoundedConfigurationTests

/-! Uniform one-step consistency of the actual weak equation over bounded
smooth test families. The time modulus is derived from narrow continuity;
it is not assumed separately for the changing backward Euler tests. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ContDiff Interval BoundedContinuousFunction
namespace SharpWasserstein.WeakEvolution
open WeightedTangent NoiseAverage
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Configuration d N → Configuration d N} {P : ℝ → Measure (Configuration d N)}
  (h : WeakEvolution (fun _ => b) P)

include h

theorem uniform_generator_expectation {K M : ℝ≥0} (hb : LipschitzWith K b)
    (hM : ∀ x, ‖b x‖ ≤ M) (T : ℝ) (L L₁ L₂ : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, dist s t < δ →
      ∀ φ : Configuration d N → ℝ, ContDiff ℝ 2 φ → LipschitzWith L φ →
        LipschitzWith L₁ (fderiv ℝ φ) → LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ)) →
        ‖(∫ x, generator b φ x ∂P s)-(∫ x, generator b φ x ∂P t)‖ < ε := by
  let A : ℝ≥0 := (N*d:ℕ)*L₁+L*M
  let D : ℝ≥0 := (N*d:ℕ)*L₂+L₁*M+L*K
  obtain ⟨δ,hδ,hd⟩ := continuous_probabilityCurve_uniform_lipschitz_tests
    (probabilityCurve h) (continuous_probabilityCurve h) T A D hε
  refine ⟨δ,hδ,fun s hs t ht hst φ hφ hL hL₁ hL₂ => ?_⟩
  have hGn : ∀ x, ‖generator b φ x‖ ≤ A := generator_norm_le_of_derivatives hφ hL hL₁ hM
  have hGL : LipschitzWith D (generator b φ) := generator_lipschitz_of_derivatives hφ hL hL₁ hL₂ hb hM
  let f : Configuration d N →ᵇ ℝ := {
    toFun := generator b φ
    continuous_toFun := hGL.continuous
    map_bounded' := ⟨2*(A:ℝ), fun x y => (dist_le_norm_add_norm _ _).trans (by linarith [hGn x,hGn y])⟩ }
  have hfn : ‖f‖ ≤ (A:ℝ) := (BoundedContinuousFunction.norm_le A.coe_nonneg).mpr hGn
  have hh := hd s hs t ht hst f hfn hGL
  change ‖(∫ x, generator b φ x ∂P (max 0 s))-(∫ x, generator b φ x ∂P (max 0 t))‖ < ε at hh
  simpa only [max_eq_right hs.1,max_eq_right ht.1] using hh

theorem equation_bounded_configuration_interval {K M : ℝ≥0} (hb : LipschitzWith K b)
    (hM : ∀ x, ‖b x‖ ≤ M) {φ : Configuration d N → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hB : AllDerivativesBounded φ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IntervalIntegrable (fun r => ∫ x, generator b φ x ∂P r) volume s t ∧
      (∫ x, φ x ∂P t)-(∫ x, φ x ∂P s) = ∫ r in s..t, ∫ x, generator b φ x ∂P r := by
  have hME (r : ℝ) (_ : 0 ≤ r) (x : Configuration d N) :
      ‖configurationEuclidean d N (b x)‖ ≤ ‖(configurationEuclidean d N).toContinuousLinearMap‖*(M:ℝ) :=
    ((configurationEuclidean d N).toContinuousLinearMap.le_opNorm (b x)).trans
      (mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _))
  have h₀s := equation_bounded_configuration h (fun _ _ => hb.continuous.measurable) hME hφ hB s hs
  have h₀t := equation_bounded_configuration h (fun _ _ => hb.continuous.measurable) hME hφ hB t ht
  refine ⟨h₀s.1.symm.trans h₀t.1,?_⟩
  rw [← intervalIntegral.integral_interval_sub_left h₀t.1 h₀s.1,← h₀t.2,← h₀s.2]
  ring

theorem uniform_weak_step_error {K M : ℝ≥0} (hb : LipschitzWith K b)
    (hM : ∀ x, ‖b x‖ ≤ M) (T : ℝ) (L L₁ L₂ : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t → t-s < δ →
      ∀ φ : Configuration d N → ℝ, ContDiff ℝ ∞ φ → AllDerivativesBounded φ →
        LipschitzWith L φ → LipschitzWith L₁ (fderiv ℝ φ) →
        LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ)) →
        ‖(∫ x, φ x ∂P t)-(∫ x, φ x ∂P s)-(t-s)*(∫ x, generator b φ x ∂P s)‖ ≤ (t-s)*ε := by
  obtain ⟨δ,hδ,hd⟩ := uniform_generator_expectation h hb hM T L L₁ L₂ hε
  refine ⟨δ,hδ,fun s hs t ht hst hsmall φ hφ hB hL hL₁ hL₂ => ?_⟩
  have heq := equation_bounded_configuration_interval h hb hM hφ hB hs.1 ht.1
  have he : (∫ x, φ x ∂P t)-(∫ x, φ x ∂P s)-(t-s)*(∫ x, generator b φ x ∂P s) =
      ∫ r in s..t, (∫ x, generator b φ x ∂P r)-(∫ x, generator b φ x ∂P s) := by
    rw [intervalIntegral.integral_sub heq.1 intervalIntegrable_const,intervalIntegral.integral_const,
      heq.2,smul_eq_mul]
  rw [he]
  have hbound : ∀ r ∈ Ι s t, ‖(∫ x, generator b φ x ∂P r)-(∫ x, generator b φ x ∂P s)‖ ≤ ε := by
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
