module

public import SharpWasserstein.Compat
public import SharpWasserstein.RoughFiniteActionInterface
public import SharpWasserstein.PrescribedSwitchIntervalEnergy
public import SharpWasserstein.PrescribedSwitchMetricIdentification
public import SharpWasserstein.PrescribedSwitchCommonLabel

@[expose] public section

/-! Exact reduction of the manuscript's interpolation length to the rough
finite-action transport theorem. No source-energy, entropy, metric-continuity,
or initial-data hypothesis is silently supplied by this reduction. The one
remaining analytic premise is explicitly named in the theorem arguments. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace SharpWasserstein.SwitchSourceDerivative
open WeightedTangent RegularizedBrownianSource RoughEulerianTransport
variable (htransport : UniformFiniteActionTransport)
  {d N k : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)
  {T : ℝ} (hT : 0 ≤ T) (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
  (hP : HasSecondMoment P) (hex : Exchangeable P) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
  (hinit : ∀ j,∀ hj : j ≤ N,wassersteinSq (marginal hj P) (tensorLaw (μ 0) j) ≤
    ENNReal.ofReal (C₀*(j:ℝ)^2/(N:ℝ)^2)) (hkpos : 1 ≤ k) (hk : k ≤ N)

include htransport hP hex hC₀ hinit hkpos

theorem prescribedMetricCurve_length_of_finiteAction :
    dist (prescribedMarginalMetricCurve hN hb hbound hM hL₁ hL₂ hμ hT P hP hk 0)
      (prescribedMarginalMetricCurve hN hb hbound hM hL₁ hL₂ hμ hT P hP hk T) ≤
      (Real.sqrt (propagationConstant d M L₁ L₂ C₀ T)*((k:ℝ)/N))*(T+3*Real.sqrt T) := by
  rcases eq_or_lt_of_le hT with hzero | hpos
  · subst T
    simp
  let C := propagationConstant d M L₁ L₂ C₀ T
  have hC : 0 ≤ C := propagationConstant_nonneg d hM hL₁ hC₀ hT
  apply GeometricEndpointLength.endpoint_of_local_action hpos (by positivity)
    (prescribedMarginalMetricCurve_continuous hN hb hbound hM hL₁ hL₂ hμ hT P hP hk).continuousAt.continuousWithinAt
  intro a b ha hab hbT
  let E := C*(1+1/a)*(k:ℝ)^2/(N:ℝ)^2
  have hE : 0 ≤ E := by unfold E; positivity
  have hc := (prescribed_marginal_compactDistributionContinuity hN hb hbound hM hL₁ hL₂ hμ hT P hk).translate ha.le hbT
  have ht := htransport d k
    (fun r => prescribedMarginalCurve hN hb hbound hM hL₁ hL₂ hμ hT P hk (a+r))
    (fun r => prescribedMarginalSource hN hb hbound hM hL₁ hL₂ hμ hT P hk (a+r))
    (b-a) E (sub_nonneg.mpr hab) hE hc
    ⟨(prescribedMarginalCommonLabel hN hb hbound hM hL₁ hL₂ hμ hT P hP hk).translate a⟩
    (fun r _ => prescribedMarginalCurve_secondMoment hN hb hbound hM hL₁ hL₂ hμ hT P hP hk (a+r))
    (fun r hr φ => prescribedMarginalCurve_testObjective_le hN hb hbound hM hL₁ hL₂ hμ hT P hP hex hC₀ hinit hkpos hk
      ha (by linarith [hr.1]) (by linarith [hr.2]) φ)
  simp only [add_zero,add_sub_cancel] at ht
  rw [prescribedMarginalCurve_map_configuration hN hb hbound hM hL₁ hL₂ hμ hT P hP hk a,
    prescribedMarginalCurve_map_configuration hN hb hbound hM hL₁ hL₂ hμ hT P hP hk b] at ht
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
  rw [ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _) hE)] at hreal
  rw [quadraticProbability_dist_eq,Real.sq_sqrt ENNReal.toReal_nonneg]
  refine hreal.trans ?_
  apply le_of_eq
  dsimp only [E]
  rw [mul_pow,Real.sq_sqrt hC]
  ring

/-- The root-cost length interface consumed by the exact final manuscript
endpoint assembly; only rough finite-action transport remains a premise. -/
theorem prescribed_switch_length_of_finiteAction :
    Real.sqrt (wassersteinSq
      (marginal hk (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P 0))
      (marginal hk (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P T))).toReal ≤
      Real.sqrt (propagationConstant d M L₁ L₂ C₀ T)*(T+3*Real.sqrt T)*((k:ℝ)/N) := by
  have he := prescribedMetricCurve_length_of_finiteAction htransport hN hb hbound hM hL₁ hL₂ hμ hT P hP hex hC₀ hinit hkpos hk
  rw [quadraticProbability_dist_eq] at he
  simp only [prescribedMarginalMetricCurve,projIcc_of_mem _ (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),
    projIcc_of_mem _ (show T ∈ Icc 0 T from ⟨hT,le_rfl⟩)] at he
  convert he using 1
  ring

end SharpWasserstein.SwitchSourceDerivative
