module

public import SharpWasserstein.Compat
public import SharpWasserstein.PrescribedSwitchMetricCurve
public import SharpWasserstein.PrescribedSwitchMarginalSourceContinuity

@[expose] public section

/-! Exact identification of the Eulerian Euclidean marginal and the actual
configuration transport curve, with every needed P₂ hypothesis derived from
the original initial law. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace SharpWasserstein.SwitchSourceDerivative
open WeightedTangent InitialSourceMarginal
variable {d N k : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)
  {T : ℝ} (hT : 0 ≤ T) (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
  (hP : HasSecondMoment P) (hk : k ≤ N)

theorem prescribedMarginalCurve_eq_metric (s : ℝ) :
    (prescribedMarginalCurve hN hb hbound hM hL₁ hL₂ hμ hT P hk s : Measure _) =
      euclideanLaw (prescribedMarginalMetricCurve hN hb hbound hM hL₁ hL₂ hμ hT P hP hk s).measure := by
  simp only [prescribedMarginalCurve,ProbabilityMeasure.toMeasure_map,prescribedEuclideanCurve,
    ProbabilityMeasure.coe_mk,prescribedMarginalMetricCurve]
  exact map_marginalProjection hk _

theorem prescribedMarginalCurve_map_configuration (s : ℝ) :
    (prescribedMarginalCurve hN hb hbound hM hL₁ hL₂ hμ hT P hk s : Measure _).map
      (configurationEuclidean d k).symm =
      (prescribedMarginalMetricCurve hN hb hbound hM hL₁ hL₂ hμ hT P hP hk s).measure := by
  rw [prescribedMarginalCurve_eq_metric hN hb hbound hM hL₁ hL₂ hμ hT P hP hk s]
  unfold euclideanLaw
  rw [Measure.map_map (configurationEuclidean d k).symm.continuous.measurable
    (configurationEuclidean d k).continuous.measurable]
  simp only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply,Measure.map_id']

include hP in
theorem prescribedMarginalCurve_secondMoment (s : ℝ) :
    Integrable (fun x : Point (k*d) => ‖x‖^2)
      (prescribedMarginalCurve hN hb hbound hM hL₁ hL₂ hμ hT P hk s : Measure _) := by
  rw [prescribedMarginalCurve_eq_metric hN hb hbound hM hL₁ hL₂ hμ hT P hP hk s]
  exact integrable_norm_sq_euclideanLaw
    (prescribedMarginalMetricCurve hN hb hbound hM hL₁ hL₂ hμ hT P hP hk s).secondMoment

end SharpWasserstein.SwitchSourceDerivative
