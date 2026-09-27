import SharpWasserstein.PropagatedSourceEquationMeasurable
import SharpWasserstein.FlowJacobianContinuityLocal

/-! The global variational integral equation is derived by differentiating
the constructed flow equation, not postulated as an additional flow property. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology Interval
namespace SharpWasserstein.FlowJacobianDrift
open FlowInitialDerivative PropagatedSourceEquation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {b : E → E} {M K K₁ : ℝ≥0}
  (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
  (hbd : Differentiable ℝ b) (hDb : LipschitzWith K₁ (fderiv ℝ b))
  {T : ℝ} (hT : 0 ≤ T) (w : C(Icc 0 T,E))

/-- The actual Jacobian of the selected initial-value solution, at clamped time. -/
def jacobian (x : E) (r : ℝ) : E →L[ℝ] E :=
  fderiv ℝ (fun y => autonomousFlow hb hLip hT y w (projIcc 0 T hT r)) x

/-- The genuine drift derivative evaluated along the actual solution. -/
def coefficient (x : E) (r : ℝ) : E →L[ℝ] E :=
  fderiv ℝ b (autonomousFlow hb hLip hT x w (projIcc 0 T hT r))

include hbd hDb in
/-- Differentiation under the genuine drift time integral is justified by
measurability and the uniform synchronous Lipschitz estimate. -/
theorem driftIntegral_hasFDerivAt (x : E) (s t : ℝ) :
    IntervalIntegrable (fun r => (coefficient hb hLip hT w x r).comp (jacobian hb hLip hT w x r)) volume s t ∧
    HasFDerivAt (fun y => ∫ r in s..t,b (autonomousFlow hb hLip hT y w (projIcc 0 T hT r)))
      (∫ r in s..t,(coefficient hb hLip hT w x r).comp (jacobian hb hLip hT w x r)) x := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  let hv := hLip.continuous.comp (continuous_snd : Continuous (Prod.snd : ℝ × E → E))
  have hc : Continuous (fun q : ℝ × E => b (autonomousFlow hb hLip hT q.2 w (projIcc 0 T hT q.1))) :=
    hLip.continuous.comp ((clampedFlow_continuous hv (fun _ => hb) (fun _ => hLip) hT).comp
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd))
  have hd (r : ℝ) (y : E) : HasFDerivAt
      (fun z => b (autonomousFlow hb hLip hT z w (projIcc 0 T hT r)))
      ((coefficient hb hLip hT w y r).comp (jacobian hb hLip hT w y r)) y :=
    (hbd _).hasFDerivAt.comp y
      (autonomousFlow_hasFDerivAt_and_norm hb hLip hbd hDb hT w y (projIcc 0 T hT r).property).1
  have hl (r : ℝ) : LipschitzWith (NNReal.mk ((K:ℝ)*Real.exp ((K:ℝ)*T)) (by positivity))
      (fun y => b (autonomousFlow hb hLip hT y w (projIcc 0 T hT r))) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (fun y => (hd r y).differentiableAt)
    intro y
    rw [(hd r y).fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hLip)
        ((autonomousFlow_hasFDerivAt_and_norm hb hLip hbd hDb hT w y
          (projIcc 0 T hT r).property).2.trans (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (projIcc 0 T hT r).property.2 K.coe_nonneg)))
        (norm_nonneg _) K.coe_nonneg)
  apply hasFDerivAt_integral_of_dominated_loc_of_lip_interval (μ := volume)
    (F := fun y r => b (autonomousFlow hb hLip hT y w (projIcc 0 T hT r)))
    (bound := fun _ => (K:ℝ)*Real.exp ((K:ℝ)*T)) (s := univ) (by simp)
  · exact Eventually.of_forall (fun y =>
      (hc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
  · exact (hc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable s t
  · have hm : Measurable (fun r => fderiv ℝ (fun y => b (autonomousFlow hb hLip hT y w (projIcc 0 T hT r))) x) :=
      (measurable_fderiv_with_param ℝ
      (f := fun r y => b (autonomousFlow hb hLip hT y w (projIcc 0 T hT r))) hc).comp (measurable_id.prodMk measurable_const)
    have he : (fun r => fderiv ℝ (fun y => b (autonomousFlow hb hLip hT y w (projIcc 0 T hT r))) x) =
        fun r => (coefficient hb hLip hT w x r).comp (jacobian hb hLip hT w x r) :=
      funext (fun r => (hd r x).fderiv)
    rw [he] at hm
    exact hm.aestronglyMeasurable
  · filter_upwards [] with r
    have he : Real.nnabs ((K:ℝ)*Real.exp ((K:ℝ)*T)) =
        NNReal.mk ((K:ℝ)*Real.exp ((K:ℝ)*T)) (by positivity) := by
      apply NNReal.eq
      exact abs_of_nonneg (by positivity)
    rw [he]
    exact (hl r).lipschitzOnWith
  · exact intervalIntegrable_const
  · exact Eventually.of_forall (fun r => hd r x)

include hbd hDb in
/-- The global integral variational equation for the actual initial Jacobian. -/
theorem jacobian_eq_integral (x : E) {t : ℝ} (ht : t ∈ Icc 0 T) :
    jacobian hb hLip hT w x t = ContinuousLinearMap.id ℝ E +
      ∫ r in (0:ℝ)..t,(coefficient hb hLip hT w x r).comp (jacobian hb hLip hT w x r) := by
  have he : (fun y => autonomousFlow hb hLip hT y w t) =
      fun y => y + BoundedFlow.noiseExtension hT w t +
        ∫ r in (0:ℝ)..t,b (autonomousFlow hb hLip hT y w (projIcc 0 T hT r)) := by
    funext y
    have h := (BoundedFlow.flow_trajectory (v := fun _ : ℝ => b)
      (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hT y w).equation t ht
    change autonomousFlow hb hLip hT y w t = _ at h
    have hi : (∫ r in (0:ℝ)..t,b (autonomousFlow hb hLip hT y w r)) =
        ∫ r in (0:ℝ)..t,b (autonomousFlow hb hLip hT y w (projIcc 0 T hT r)) := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hrT : r ∈ Icc 0 T := ⟨(min_eq_left ht.1 ▸ hr.1), (max_eq_right ht.1 ▸ hr.2).trans ht.2⟩
      dsimp only
      rw [projIcc_of_mem _ hrT]
    change autonomousFlow hb hLip hT y w t = _
    change autonomousFlow hb hLip hT y w t = (y + ∫ r in (0:ℝ)..t,b (autonomousFlow hb hLip hT y w r)) + _ at h
    rw [h,hi]
    abel
  have hd := ((hasFDerivAt_id x).add_const (BoundedFlow.noiseExtension hT w t)).add
    (driftIntegral_hasFDerivAt hb hLip hbd hDb hT w x 0 t).2
  simp only [Pi.add_def,id_eq] at hd
  rw [← he] at hd
  simpa only [jacobian,projIcc_of_mem _ ht] using hd.fderiv

end SharpWasserstein.FlowJacobianDrift
