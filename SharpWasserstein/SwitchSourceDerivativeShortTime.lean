module

public import SharpWasserstein.Compat
public import SharpWasserstein.SwitchSourceDerivativePathwise
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-! An actual first-order difference of transition expectations, proved from
synchronous continuous-input flows and dominated convergence. The test is
only C¹ with bounded differential; no generator/backward-PDE assumption is
made, and the shared input law can in particular be the sqrt(2)-Brownian law. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ContDiff
namespace SharpWasserstein.SwitchSourceDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {v q : ℝ → E → E} {M A K H : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hbv : ∀ r x, ‖v r x‖ ≤ M)
  (hlv : ∀ r, LipschitzWith K (v r))
  (hq : Continuous (Function.uncurry q)) (hbq : ∀ r x, ‖q r x‖ ≤ A)
  (hlq : ∀ r, LipschitzWith H (q r))
  {T : ℝ} (hT : 0 ≤ T)
  [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)]

/-- Difference of the actual selected flows evaluated in a scalar test. -/
def flowTestDifference (F : E → ℝ) (r : ℝ) (p : E × C(Icc 0 T,E)) : ℝ :=
  F (BoundedFlow.flow hv hbv hlv hT p.1 p.2 r)-
    F (BoundedFlow.flow hq hbq hlq hT p.1 p.2 r)

omit [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)] in
theorem flowTestDifference_zero (F : E → ℝ) (p : E × C(Icc 0 T,E)) :
    flowTestDifference hv hbv hlv hq hbq hlq hT F 0 p = 0 := by
  simp only [flowTestDifference,
    (BoundedFlow.flow_trajectory hv hbv hlv hT p.1 p.2).equation 0 ⟨le_rfl,hT⟩,
    (BoundedFlow.flow_trajectory hq hbq hlq hT p.1 p.2).equation 0 ⟨le_rfl,hT⟩,
    intervalIntegral.integral_same,add_zero,sub_self]

omit [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)] in
theorem flowTestDifference_continuous {F : E → ℝ} (hF : Continuous F)
    {r : ℝ} (hr : r ∈ Icc 0 T) :
    Continuous (flowTestDifference hv hbv hlv hq hbq hlq hT F r) :=
  (hF.comp (BoundedFlow.flow_continuous hv hbv hlv hT hr)).sub
    (hF.comp (BoundedFlow.flow_continuous hq hbq hlq hT hr))

omit [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)] in
theorem flowTestDifference_norm_le {F : E → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) {r : ℝ} (hr : r ∈ Icc 0 T) (p : E × C(Icc 0 T,E)) :
    ‖flowTestDifference hv hbv hlv hq hbq hlq hT F r p‖ ≤
      (L:ℝ)*(M+A)*r :=
  trajectory_test_difference_norm_le
    (BoundedFlow.flow_trajectory hv hbv hlv hT p.1 p.2)
    (BoundedFlow.flow_trajectory hq hbq hlq hT p.1 p.2)
    (fun r _ => hbv r) (fun r _ => hbq r) hr hF

omit [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)] in
theorem flowTestDifference_hasDerivWithinAt_zero
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) (p : E × C(Icc 0 T,E))
    (hw : p.2 ⟨0,le_rfl,hT⟩ = 0) :
    HasDerivWithinAt (fun r => flowTestDifference hv hbv hlv hq hbq hlq hT F r p)
      (fderiv ℝ F p.1 (v 0 p.1-q 0 p.1)) (Icc 0 T) 0 := by
  apply trajectory_test_difference_hasDerivWithinAt_zero hT _
    (BoundedFlow.flow_trajectory hv hbv hlv hT p.1 p.2)
    (BoundedFlow.flow_trajectory hq hbq hlq hT p.1 p.2) hF
  simpa only [BoundedFlow.noiseExtension,projIcc_of_mem _ (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩)] using hw

/-- The difference of the two actual transition expectations is differentiable
at zero. Its derivative is precisely the first-order drift-difference pairing.
Only the initial measure is finite; no moment of it or of the noise is needed. -/
theorem integral_flowTestDifference_hasDerivWithinAt_zero [SecondCountableTopology E]
    (μ : Measure E) [IsFiniteMeasure μ] (ξ : Measure C(Icc 0 T,E)) [IsProbabilityMeasure ξ]
    (hzero : ∀ᵐ w ∂ξ, w ⟨0,le_rfl,hT⟩ = 0)
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {L : ℝ≥0}
    (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) :
    HasDerivWithinAt
      (fun r => ∫ p,flowTestDifference hv hbv hlv hq hbq hlq hT F r p ∂μ.prod ξ)
      (∫ x,fderiv ℝ F x (v 0 x-q 0 x) ∂μ) (Icc 0 T) 0 := by
  have hFL : LipschitzWith L F := lipschitzWith_of_nnnorm_fderiv_le
    (hF.differentiable (by norm_num)) hL
  have hpzero : ∀ᵐ p ∂μ.prod ξ, p.2 ⟨0,le_rfl,hT⟩ = 0 :=
    Measure.quasiMeasurePreserving_snd.ae hzero
  have hlim : Tendsto
      (fun r => ∫ p,r⁻¹*flowTestDifference hv hbv hlv hq hbq hlq hT F r p ∂μ.prod ξ)
      (𝓝[Icc 0 T \ {0}] (0:ℝ))
      (𝓝 (∫ p,fderiv ℝ F p.1 (v 0 p.1-q 0 p.1) ∂μ.prod ξ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (μ := μ.prod ξ) (l := 𝓝[Icc 0 T \ {0}] (0:ℝ))
      (F := fun r p => r⁻¹*flowTestDifference hv hbv hlv hq hbq hlq hT F r p)
      (f := fun p => fderiv ℝ F p.1 (v 0 p.1-q 0 p.1))
      (fun _ => (L:ℝ)*(M+A)) ?_ ?_ (integrable_const _) ?_
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact ((flowTestDifference_continuous hv hbv hlv hq hbq hlq hT hF.continuous hr.1).const_mul r⁻¹).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with r hr
      filter_upwards [] with p
      have hr0 : r ≠ 0 := hr.2
      have hn := flowTestDifference_norm_le hv hbv hlv hq hbq hlq hT hFL hr.1 p
      rw [norm_mul,Real.norm_eq_abs,abs_inv,abs_of_nonneg hr.1.1]
      calc
        r⁻¹*‖flowTestDifference hv hbv hlv hq hbq hlq hT F r p‖ ≤ r⁻¹*((L:ℝ)*(M+A)*r) :=
          mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hr.1.1)
        _ = _ := by field_simp
    · filter_upwards [hpzero] with p hp
      have hh := hasDerivWithinAt_iff_tendsto_slope.mp
        (flowTestDifference_hasDerivWithinAt_zero hv hbv hlv hq hbq hlq hT hF p hp)
      have he : slope (fun r => flowTestDifference hv hbv hlv hq hbq hlq hT F r p) 0 =
          fun r => r⁻¹*flowTestDifference hv hbv hlv hq hbq hlq hT F r p := by
        funext r
        simp only [slope_def_module,sub_zero,
          flowTestDifference_zero hv hbv hlv hq hbq hlq hT F p,smul_eq_mul]
      rw [he] at hh
      exact hh
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  have he : (∫ p,fderiv ℝ F p.1 (v 0 p.1-q 0 p.1) ∂μ.prod ξ) =
      ∫ x,fderiv ℝ F x (v 0 x-q 0 x) ∂μ := by
    simpa only [probReal_univ,one_smul] using
      (integral_fun_fst (μ := μ) (ν := ξ) (fun x => fderiv ℝ F x (v 0 x-q 0 x)))
  rw [he] at hlim
  convert hlim using 1
  ext r
  simp only [slope_def_module,sub_zero,flowTestDifference_zero,integral_zero,
    integral_const_mul,smul_eq_mul]

end SharpWasserstein.SwitchSourceDerivative
