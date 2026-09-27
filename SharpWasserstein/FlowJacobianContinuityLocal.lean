import SharpWasserstein.FlowInitialDerivativeGlobal

/-! Operator-norm continuity of the actual initial Jacobian on short intervals.
The comparison below uses constructed variational equations and synchronous
flow stability; derivative continuity is not an input hypothesis. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal Topology
namespace SharpWasserstein.FlowInitialDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Retain the constructed variational equation as well as its identification
with the actual initial derivative. -/
theorem exists_flow_variation_short {b : E → E} {M K K₁ : ℝ≥0}
    (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
    (hbd : Differentiable ℝ b) (hDb : LipschitzWith K₁ (fderiv ℝ b))
    {T : ℝ} (hT : 0 ≤ T) (hshort : 2*(K:ℝ)*T ≤ 1)
    (x : E) (w : C(Icc 0 T,E)) :
    ∃ (A J : ℝ → E →L[ℝ] E), LinearVariation A T J ∧
      (∀ s, ‖A s‖ ≤ K) ∧
      (∀ s ∈ Icc 0 T, A s = fderiv ℝ b (autonomousFlow hb hLip hT x w s)) ∧
      ∀ s ∈ Icc 0 T,
        HasFDerivAt (fun y => autonomousFlow hb hLip hT y w s) (J s) x := by
  let X := autonomousFlow hb hLip hT x w
  have hX : FiniteAdditiveTrajectory (fun _ => b) (BoundedFlow.noiseExtension hT w) x T X :=
    BoundedFlow.flow_trajectory (v := fun _ : ℝ => b)
      (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hT x w
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
  refine ⟨A,J,hJ,hAn,hAe,fun t ht => ?_⟩
  let C : ℝ := (K₁:ℝ)*Real.exp ((K:ℝ)*T)^2 / ((K:ℝ)+1) *
    (Real.exp (((K:ℝ)+1)*t)-1)
  have hC : 0 ≤ C := by
    apply mul_nonneg (by positivity)
    exact sub_nonneg.mpr (Real.one_le_exp (mul_nonneg (by positivity) ht.1))
  apply hasFDerivAt_of_quadratic_error x (J t) hC
  intro y
  exact trajectory_linearization_error hbd hLip hDb hX
    (BoundedFlow.flow_trajectory (v := fun _ : ℝ => b)
      (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hT y w)
    hJ hAe ht

omit [CompleteSpace E] in
/-- Quantitative stability of two actual operator variational equations. -/
theorem LinearVariation.difference_le {A B J H : ℝ → E →L[ℝ] E}
    {K : ℝ≥0} {D T t : ℝ} (hJ : LinearVariation A T J) (hH : LinearVariation B T H)
    (hA : ∀ s ∈ Icc 0 T, ‖A s‖ ≤ K) (hB : ∀ s ∈ Icc 0 T, ‖B s‖ ≤ K)
    (hD : 0 ≤ D) (hAB : ∀ s ∈ Icc 0 T, ‖A s-B s‖ ≤ D) (ht : t ∈ Icc 0 T) :
    ‖J t-H t‖ ≤ D*Real.exp ((K:ℝ)*T)/((K:ℝ)+1) *
      (Real.exp (((K:ℝ)+1)*t)-1) := by
  have hc : ContinuousOn (fun s => J s-H s) (Icc 0 t) :=
    (hJ.continuous.sub hH.continuous).mono (Icc_subset_Icc_right ht.2)
  have hd : ∀ s ∈ Ico 0 t, HasDerivWithinAt (fun r => J r-H r)
      ((A s).comp (J s)-(B s).comp (H s)) (Ici s) s := by
    intro s hs
    exact (hJ.derivative_right ⟨hs.1,hs.2.trans_le ht.2⟩).sub
      (hH.derivative_right ⟨hs.1,hs.2.trans_le ht.2⟩)
  have hn : ∀ s ∈ Ico 0 t,
      ‖(A s).comp (J s)-(B s).comp (H s)‖ ≤
        ((K:ℝ)+1)*‖J s-H s‖+D*Real.exp ((K:ℝ)*T) := by
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1,hs.2.le.trans ht.2⟩
    have he : (A s).comp (J s)-(B s).comp (H s) =
        (A s).comp (J s-H s)+(A s-B s).comp (H s) := by
      simp only [ContinuousLinearMap.comp_sub,ContinuousLinearMap.sub_comp]
      abel
    have hHn : ‖H s‖ ≤ Real.exp ((K:ℝ)*T) :=
      (hH.norm_le_exp hB hsT).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsT.2 K.coe_nonneg))
    rw [he]
    calc
      _ ≤ ‖(A s).comp (J s-H s)‖+‖(A s-B s).comp (H s)‖ := norm_add_le _ _
      _ ≤ (K:ℝ)*‖J s-H s‖+D*Real.exp ((K:ℝ)*T) :=
        add_le_add ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right (hA s hsT) (norm_nonneg _)))
          ((ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul (hAB s hsT) hHn (norm_nonneg _) hD))
      _ ≤ _ := by nlinarith [norm_nonneg (J s-H s)]
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le hc hd
    (show ‖J 0-H 0‖ ≤ 0 by rw [hJ.initial,hH.initial,sub_self,norm_zero]) hn t ⟨ht.1,le_rfl⟩
  simpa only [gronwallBound_of_K_ne_0 (show (K:ℝ)+1 ≠ 0 by positivity),
    zero_mul,zero_add,sub_zero] using hh

/-- The actual Jacobian is jointly Lipschitz in initial point and continuous
input on short intervals. The constant is independent of both parameters. -/
theorem autonomousFlow_fderiv_lipschitz_short {b : E → E} {M K K₁ : ℝ≥0}
    (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
    (hbd : Differentiable ℝ b) (hDb : LipschitzWith K₁ (fderiv ℝ b))
    {T : ℝ} (hT : 0 ≤ T) (hshort : 2*(K:ℝ)*T ≤ 1)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∃ C : ℝ≥0, LipschitzWith C (fun p : E × C(Icc 0 T,E) =>
      fderiv ℝ (fun y => autonomousFlow hb hLip hT y p.2 t) p.1) := by
  let c : ℝ := 2*(K₁:ℝ)*Real.exp ((K:ℝ)*T)^2/((K:ℝ)+1)*
    (Real.exp (((K:ℝ)+1)*t)-1)
  have hc : 0 ≤ c := by
    apply mul_nonneg (by positivity)
    exact sub_nonneg.mpr (Real.one_le_exp (mul_nonneg (by positivity) ht.1))
  refine ⟨⟨c,hc⟩,LipschitzWith.of_dist_le_mul (fun p q => ?_)⟩
  obtain ⟨A,J,hJ,hAn,hAe,hJd⟩ := exists_flow_variation_short hb hLip hbd hDb hT hshort p.1 p.2
  obtain ⟨B,H,hH,hBn,hBe,hHd⟩ := exists_flow_variation_short hb hLip hbd hDb hT hshort q.1 q.2
  rw [(hJd t ht).fderiv,(hHd t ht).fderiv,dist_eq_norm]
  let D : ℝ := 2*(K₁:ℝ)*Real.exp ((K:ℝ)*T)*dist p q
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hAB : ∀ s ∈ Icc 0 T, ‖A s-B s‖ ≤ D := by
    intro s hs
    rw [hAe s hs,hBe s hs]
    have hflow := BoundedFlow.flow_lipschitz (v := fun _ : ℝ => b)
      (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hT hs
    have hn := hDb.norm_sub_le (autonomousFlow hb hLip hT p.1 p.2 s)
      (autonomousFlow hb hLip hT q.1 q.2 s)
    apply hn.trans
    have hh := hflow.dist_le_mul p q
    rw [dist_eq_norm] at hh
    change ‖autonomousFlow hb hLip hT p.1 p.2 s-autonomousFlow hb hLip hT q.1 q.2 s‖ ≤
      2*Real.exp ((K:ℝ)*s)*dist p q at hh
    calc
      _ ≤ (K₁:ℝ)*(2*Real.exp ((K:ℝ)*s)*dist p q) := mul_le_mul_of_nonneg_left hh K₁.coe_nonneg
      _ ≤ (K₁:ℝ)*(2*Real.exp ((K:ℝ)*T)*dist p q) := by gcongr; exact hs.2
      _ = D := by dsimp [D]; ring
  have hh := hJ.difference_le hH (fun s _ => hAn s) (fun s _ => hBn s) hD hAB ht
  change ‖J t-H t‖ ≤ c*dist p q
  convert hh using 1
  dsimp [c,D]
  ring

end SharpWasserstein.FlowInitialDerivative
