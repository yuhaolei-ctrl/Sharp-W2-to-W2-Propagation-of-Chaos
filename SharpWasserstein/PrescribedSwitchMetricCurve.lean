module

public import SharpWasserstein.Compat
public import SharpWasserstein.SwitchCurveProperties
public import SharpWasserstein.GeometricEndpointLength

@[expose] public section

/-! The actual switch marginal as a continuous curve in the quadratic
transport pseudometric. Its distance uses the manuscript's unnormalized
sum-of-squares coupling infimum. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace SharpWasserstein.SwitchSourceDerivative
variable {d N k : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)
  {T : ℝ} (hT : 0 ≤ T) (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
  (hP : HasSecondMoment P) (hk : k ≤ N)

def prescribedMarginalMetricCurve (s : ℝ) : QuadraticProbabilityLaw d k := by
  let r := projIcc 0 T hT s
  letI : IsProbabilityMeasure (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P r) :=
    SwitchCurve.law_probability hN hb hbound hM hL₁ hL₂ _ _ _ hT P r.property
  exact ⟨marginal hk (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P r),inferInstance,
    hasSecondMoment_marginal hk (SwitchCurve.law_secondMoment hN hb hbound hM hL₁ hL₂ _ _ _ hT P hP r.property)⟩

theorem prescribedMarginalMetricCurve_continuous :
    Continuous (prescribedMarginalMetricCurve hN hb hbound hM hL₁ hL₂ hμ hT P hP hk) := by
  let Q (s : Icc 0 T) : QuadraticProbabilityLaw d k :=
    prescribedMarginalMetricCurve hN hb hbound hM hL₁ hL₂ hμ hT P hP hk s
  have hQ : Continuous Q := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hz := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (SwitchCurve.marginal_wassersteinSq_tendsto hN hb hbound hM hL₁ hL₂
        (DecoupledFlow.liftDrift_continuous N (PrescribedReference.singleDrift_continuous hb hbound hL₁ hμ))
        (DecoupledFlow.liftDrift_bound N (PrescribedReference.singleDrift_bound hbound hM hμ))
        (DecoupledFlow.liftDrift_lipschitz N (PrescribedReference.singleDrift_lipschitz hb hbound hL₁ hμ)) hT P hk t)
    simpa only [ENNReal.toReal_zero,Real.sqrt_zero,quadraticProbability_dist_eq,Q,
      prescribedMarginalMetricCurve,PrescribedSwitchCurve.law,Function.comp_def,projIcc_of_mem _ t.property,projIcc_of_mem _ (Subtype.property _)] using hz.sqrt
  have hc := hQ.comp (continuous_projIcc (h := hT))
  convert hc using 1
  funext s
  simp only [Q,prescribedMarginalMetricCurve,Function.comp_def,
    projIcc_of_mem _ (projIcc 0 T hT s).property]

theorem prescribedMarginalMetricCurve_distance_sq {s t : ℝ}
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    dist (prescribedMarginalMetricCurve hN hb hbound hM hL₁ hL₂ hμ hT P hP hk s)
      (prescribedMarginalMetricCurve hN hb hbound hM hL₁ hL₂ hμ hT P hP hk t)^2 =
      (wassersteinSq (marginal hk (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s))
        (marginal hk (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P t))).toReal := by
  rw [quadraticProbability_dist_eq,Real.sq_sqrt ENNReal.toReal_nonneg]
  simp only [prescribedMarginalMetricCurve,projIcc_of_mem _ hs,projIcc_of_mem _ ht]

end SharpWasserstein.SwitchSourceDerivative
