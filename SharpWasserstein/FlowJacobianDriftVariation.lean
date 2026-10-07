module

public import SharpWasserstein.Compat
public import SharpWasserstein.FlowJacobianDriftEquation

@[expose] public section

/-! Global time continuity and the actual differential variational equation
follow from the proved global integral identity for the initial Jacobian. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology Interval
namespace SharpWasserstein.FlowJacobianDrift
open FlowInitialDerivative PropagatedSourceEquation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {b : E → E} {M K K₁ : ℝ≥0}
  (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
  (hbd : Differentiable ℝ b) (hDb : LipschitzWith K₁ (fderiv ℝ b))
  {T : ℝ} (hT : 0 ≤ T) (w : C(Icc 0 T,E)) (x : E)

include hbd hDb in
theorem jacobian_continuousOn : ContinuousOn (jacobian hb hLip hT w x) (Icc 0 T) :=
  (continuous_const.add (intervalIntegral.continuous_primitive
    (fun s t => (driftIntegral_hasFDerivAt hb hLip hbd hDb hT w x s t).1) 0)).continuousOn.congr
    (fun _t ht => jacobian_eq_integral hb hLip hbd hDb hT w x ht)

include hbd hDb in
/-- Joint measurability was sufficient for the integral identity; it now gives
actual continuity in time of the clamped initial Jacobian. -/
theorem jacobian_continuous : Continuous (jacobian hb hLip hT w x) := by
  have hh := (jacobian_continuousOn hb hLip hbd hDb hT w x).comp_continuous
    (continuous_subtype_val.comp continuous_projIcc : Continuous (fun r : ℝ => (projIcc 0 T hT r).val))
    (fun r => (projIcc 0 T hT r).property)
  change Continuous (fun r => fderiv ℝ (fun y => autonomousFlow hb hLip hT y w (projIcc 0 T hT r)) x)
  simpa only [Function.comp_def,jacobian,projIcc_of_mem _ (projIcc 0 T hT _).property] using hh

include hDb in
omit [FiniteDimensional ℝ E] in
theorem coefficient_continuous : Continuous (coefficient hb hLip hT w x) :=
  hDb.continuous.comp ((clampedFlow_continuous (hLip.continuous.comp continuous_snd)
    (fun _ => hb) (fun _ => hLip) hT).comp
      ((continuous_const.prodMk continuous_id).prodMk continuous_const))

include hbd hDb in
/-- The constructed initial Jacobian solves the actual global variational ODE. -/
theorem jacobian_linearVariation :
    LinearVariation (coefficient hb hLip hT w x) T (jacobian hb hLip hT w x) := by
  refine ⟨jacobian_continuousOn hb hLip hbd hDb hT w x,?_,?_⟩
  · simpa only [intervalIntegral.integral_same,add_zero] using
      jacobian_eq_integral hb hLip hbd hDb hT w x ⟨le_rfl,hT⟩
  · intro t ht
    have hc := (coefficient_continuous hb hLip hDb hT w x).clm_comp
      (jacobian_continuous hb hLip hbd hDb hT w x)
    have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add
        (ContinuousLinearMap.id ℝ E)
    exact hd.hasDerivWithinAt.congr_of_mem
      (fun s hs => jacobian_eq_integral hb hLip hbd hDb hT w x hs) ht

omit [FiniteDimensional ℝ E] in
/-- The coefficient bound is the genuine spatial Lipschitz constant. -/
theorem coefficient_norm_le (r : ℝ) : ‖coefficient hb hLip hT w x r‖ ≤ K :=
  norm_fderiv_le_of_lipschitz ℝ hLip

end SharpWasserstein.FlowJacobianDrift
