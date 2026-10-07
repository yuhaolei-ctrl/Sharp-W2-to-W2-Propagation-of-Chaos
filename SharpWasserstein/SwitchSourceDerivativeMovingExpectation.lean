module

public import SharpWasserstein.Compat
public import SharpWasserstein.SwitchSourceDerivativeMovingTest

@[expose] public section

/-! Differentiation of actual transition comparisons with a moving C¹ test.
The identity is proved by the pathwise moving-test theorem and a constant
integrable quotient bound. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ContDiff
namespace SharpWasserstein.SwitchSourceDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {v q : ℝ → E → E} {M A K H : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hbv : ∀ r x, ‖v r x‖ ≤ M)
  (hlv : ∀ r, LipschitzWith K (v r))
  (hq : Continuous (Function.uncurry q)) (hbq : ∀ r x, ‖q r x‖ ≤ A)
  (hlq : ∀ r, LipschitzWith H (q r))
  {T : ℝ} (hT : 0 ≤ T)
  [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)]

/-- Genuine first-order comparison for moving tests and arbitrary independent
initial laws/noise. The spatial differential may vary in time continuously. -/
theorem integral_moving_flowTestDifference_hasDerivWithinAt_zero
    (μ : Measure E) [IsFiniteMeasure μ] (ξ : Measure C(Icc 0 T,E)) [IsProbabilityMeasure ξ]
    (hzero : ∀ᵐ w ∂ξ, w ⟨0,le_rfl,hT⟩ = 0)
    {F : ℝ → E → ℝ} (hF : ∀ r, ContDiff ℝ 1 (F r))
    (hDF : Continuous (fun p : ℝ × E => fderiv ℝ (F p.1) p.2))
    {L : ℝ≥0} (hL : ∀ r x, ‖fderiv ℝ (F r) x‖ ≤ L) :
    HasDerivWithinAt
      (fun r => ∫ p,flowTestDifference hv hbv hlv hq hbq hlq hT (F r) r p ∂μ.prod ξ)
      (∫ x,fderiv ℝ (F 0) x (v 0 x-q 0 x) ∂μ) (Icc 0 T) 0 := by
  have hFL (r : ℝ) : LipschitzWith L (F r) := lipschitzWith_of_nnnorm_fderiv_le
    ((hF r).differentiable (by norm_num)) (hL r)
  have hpzero : ∀ᵐ p ∂μ.prod ξ, p.2 ⟨0,le_rfl,hT⟩ = 0 :=
    Measure.quasiMeasurePreserving_snd.ae hzero
  have hlim : Tendsto
      (fun r => ∫ p,r⁻¹*flowTestDifference hv hbv hlv hq hbq hlq hT (F r) r p ∂μ.prod ξ)
      (𝓝[Icc 0 T \ {0}] (0:ℝ))
      (𝓝 (∫ p,fderiv ℝ (F 0) p.1 (v 0 p.1-q 0 p.1) ∂μ.prod ξ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (μ := μ.prod ξ) (l := 𝓝[Icc 0 T \ {0}] (0:ℝ))
      (F := fun r p => r⁻¹*flowTestDifference hv hbv hlv hq hbq hlq hT (F r) r p)
      (f := fun p => fderiv ℝ (F 0) p.1 (v 0 p.1-q 0 p.1))
      (fun _ => (L:ℝ)*(M+A)) ?_ ?_ (integrable_const _) ?_
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact ((flowTestDifference_continuous hv hbv hlv hq hbq hlq hT
        (hF r).continuous hr.1).const_mul r⁻¹).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with r hr
      filter_upwards [] with p
      have hr0 : r ≠ 0 := hr.2
      have hn := flowTestDifference_norm_le hv hbv hlv hq hbq hlq hT (hFL r) hr.1 p
      rw [norm_mul,Real.norm_eq_abs,abs_inv,abs_of_nonneg hr.1.1]
      calc
        r⁻¹*‖flowTestDifference hv hbv hlv hq hbq hlq hT (F r) r p‖ ≤ r⁻¹*((L:ℝ)*(M+A)*r) :=
          mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hr.1.1)
        _ = _ := by field_simp
    · filter_upwards [hpzero] with p hp
      have hh := hasDerivWithinAt_iff_tendsto_slope.mp
        (trajectory_moving_test_difference_hasDerivWithinAt_zero hT
          (show BoundedFlow.noiseExtension hT p.2 0 = 0 from by
            simpa only [BoundedFlow.noiseExtension,projIcc_of_mem _
              (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩)] using hp)
          (BoundedFlow.flow_trajectory hv hbv hlv hT p.1 p.2)
          (BoundedFlow.flow_trajectory hq hbq hlq hT p.1 p.2)
          (fun r _ => hbv r) (fun r _ => hbq r) hF hDF hL)
      have he : slope (fun r => flowTestDifference hv hbv hlv hq hbq hlq hT (F r) r p) 0 =
          fun r => r⁻¹*flowTestDifference hv hbv hlv hq hbq hlq hT (F r) r p := by
        funext r
        simp only [slope_def_module,sub_zero,
          flowTestDifference_zero hv hbv hlv hq hbq hlq hT (F 0) p,smul_eq_mul]
      change Tendsto (slope (fun r => flowTestDifference hv hbv hlv hq hbq hlq hT (F r) r p) 0) _ _ at hh
      rw [he] at hh
      exact hh
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  have he : (∫ p,fderiv ℝ (F 0) p.1 (v 0 p.1-q 0 p.1) ∂μ.prod ξ) =
      ∫ x,fderiv ℝ (F 0) x (v 0 x-q 0 x) ∂μ := by
    simpa only [probReal_univ,one_smul] using
      (integral_fun_fst (μ := μ) (ν := ξ) (fun x => fderiv ℝ (F 0) x (v 0 x-q 0 x)))
  rw [he] at hlim
  convert hlim using 1
  ext r
  simp only [slope_def_module,sub_zero,flowTestDifference_zero,integral_zero,
    integral_const_mul,smul_eq_mul]

end SharpWasserstein.SwitchSourceDerivative
