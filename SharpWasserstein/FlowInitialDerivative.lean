import SharpWasserstein.FlowInitialDerivativeRemainder

/-! Actual short-time initial-value differentiability of bounded autonomous
continuous-input flows. The Jacobian is constructed by Picard–Lindelöf, and
Taylor–Grönwall identifies it as the Fréchet derivative of the selected flow. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal Topology
namespace SharpWasserstein.FlowInitialDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The existing constructed flow, specialized to an autonomous drift. -/
def autonomousFlow {b : E → E} {M K : ℝ≥0} (hb : ∀ x, ‖b x‖ ≤ M)
    (hLip : LipschitzWith K b) {T : ℝ} (hT : 0 ≤ T)
    (x : E) (w : C(Icc 0 T,E)) : ℝ → E :=
  BoundedFlow.flow (v := fun _ : ℝ => b) (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hT x w

/-- A constructed operator curve is the actual initial-value derivative at
every time of a short interval. No differentiability or variational solution
is supplied as an assumption. -/
theorem exists_flow_jacobian_short {b : E → E} {M K K₁ : ℝ≥0}
    (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
    (hbd : Differentiable ℝ b) (hDb : LipschitzWith K₁ (fderiv ℝ b))
    {T : ℝ} (hT : 0 ≤ T) (hshort : 2*(K:ℝ)*T ≤ 1)
    (x : E) (w : C(Icc 0 T,E)) :
    ∃ J : ℝ → E →L[ℝ] E,
      J 0 = ContinuousLinearMap.id ℝ E ∧
      ∀ t ∈ Icc 0 T,
        HasFDerivAt (fun y => autonomousFlow hb hLip hT y w t) (J t) x ∧
        ‖J t‖ ≤ Real.exp ((K:ℝ)*t) := by
  let X := autonomousFlow hb hLip hT x w
  have hX : FiniteAdditiveTrajectory (fun _ => b) (BoundedFlow.noiseExtension hT w) x T X :=
    BoundedFlow.flow_trajectory (v := fun _ : ℝ => b) (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hT x w
  let c : ℝ → ℝ := fun s => (projIcc 0 T hT s).val
  let A : ℝ → E →L[ℝ] E := fun s => fderiv ℝ b (X (c s))
  have hc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  have hAc : Continuous A := hDb.continuous.comp
    (hX.continuous.comp_continuous hc (fun s => (projIcc 0 T hT s).property))
  have hAn : ∀ s, ‖A s‖ ≤ K := fun _ => norm_fderiv_le_of_lipschitz ℝ hLip
  obtain ⟨J,hJ⟩ := exists_linearVariation_short hAc hAn hT hshort
  have hAe : ∀ s ∈ Icc 0 T, A s = fderiv ℝ b (X s) := by
    intro s hs
    simp only [A,c,projIcc_of_mem _ hs]
  refine ⟨J,hJ.initial,fun t ht => ⟨?_,hJ.norm_le_exp (fun s _ => hAn s) ht⟩⟩
  let C : ℝ := (K₁:ℝ)*Real.exp ((K:ℝ)*T)^2 / ((K:ℝ)+1) *
    (Real.exp (((K:ℝ)+1)*t)-1)
  have hC : 0 ≤ C := by
    apply mul_nonneg (by positivity)
    exact sub_nonneg.mpr (Real.one_le_exp (mul_nonneg (by positivity) ht.1))
  apply hasFDerivAt_of_quadratic_error x (J t) hC
  intro y
  have hY : FiniteAdditiveTrajectory (fun _ => b) (BoundedFlow.noiseExtension hT w) y T
      (autonomousFlow hb hLip hT y w) :=
    BoundedFlow.flow_trajectory (v := fun _ : ℝ => b) (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hT y w
  exact trajectory_linearization_error hbd hLip hDb hX hY hJ hAe ht

/-- The actual Fréchet derivative has the sharp exponential operator bound. -/
theorem flow_fderiv_norm_le_exp_short {b : E → E} {M K K₁ : ℝ≥0}
    (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
    (hbd : Differentiable ℝ b) (hDb : LipschitzWith K₁ (fderiv ℝ b))
    {T : ℝ} (hT : 0 ≤ T) (hshort : 2*(K:ℝ)*T ≤ 1)
    (x : E) (w : C(Icc 0 T,E)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    DifferentiableAt ℝ (fun y => autonomousFlow hb hLip hT y w t) x ∧
    ‖fderiv ℝ (fun y => autonomousFlow hb hLip hT y w t) x‖ ≤ Real.exp ((K:ℝ)*t) := by
  obtain ⟨J,_,hJ⟩ := exists_flow_jacobian_short hb hLip hbd hDb hT hshort x w
  exact ⟨(hJ t ht).1.differentiableAt,by rw [(hJ t ht).1.fderiv]; exact (hJ t ht).2⟩

end SharpWasserstein.FlowInitialDerivative
