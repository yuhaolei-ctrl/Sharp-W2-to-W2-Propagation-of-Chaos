import SharpWasserstein.FlowJacobianContinuityLocal

/-! Joint continuity of the genuine initial Jacobian for arbitrary finite
horizons, obtained by composing the actual short-interval flows. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal Topology
namespace SharpWasserstein
namespace BoundedFlow
variable {E : Type*} [NormedAddCommGroup E]

/-- Restriction of continuous input paths is continuous in the uniform topology. -/
theorem restrictPath_continuous {S T : ℝ} (hST : S ≤ T) :
    Continuous (restrictPath (E := E) hST) := by
  let i : C(Icc 0 S,Icc 0 T) :=
    ⟨fun t => ⟨t,t.property.1,t.property.2.trans hST⟩,
      continuous_subtype_val.subtype_mk _⟩
  exact ContinuousMap.continuous_precomp i

/-- The shifted increment path depends continuously on the full input path. -/
theorem shiftPath_continuous {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) :
    Continuous (shiftPath (E := E) hS hT) := by
  let i : C(Icc 0 T,Icc 0 (S+T)) :=
    ⟨fun t => ⟨S+t,add_nonneg hS t.property.1,add_le_add_right t.property.2 S⟩,
      (continuous_const.add continuous_subtype_val).subtype_mk _⟩
  have he : shiftPath (E := E) hS hT = fun w =>
      w.comp i-ContinuousMap.const _ (w ⟨S,hS,le_add_of_nonneg_right hT⟩) := by
    funext w
    ext t
    rfl
  rw [he]
  exact (ContinuousMap.continuous_precomp i).sub
    (ContinuousMap.continuous_const'.comp (continuous_eval_const _))
end BoundedFlow
namespace FlowInitialDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Operator-norm joint continuity for finitely many short flow intervals. -/
theorem autonomousFlow_fderiv_continuous_multiple {b : E → E} {M K K₁ : ℝ≥0}
    (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
    (hbd : Differentiable ℝ b) (hDb : LipschitzWith K₁ (fderiv ℝ b))
    {δ : ℝ} (hδ : 0 ≤ δ) (hshort : 2*(K:ℝ)*δ ≤ 1) (n : ℕ)
    {T : ℝ} (hT : 0 ≤ T) (hEq : T = (n:ℝ)*δ) :
    Continuous (fun p : E × C(Icc 0 T,E) =>
      fderiv ℝ (fun y => autonomousFlow hb hLip hT y p.2 T) p.1) := by
  induction n generalizing T with
  | zero =>
    have hz : T = 0 := by simpa only [Nat.cast_zero,zero_mul] using hEq
    clear hEq
    subst T
    have he : (fun p : E × C(Icc 0 (0:ℝ),E) =>
        fderiv ℝ (fun y => autonomousFlow hb hLip le_rfl y p.2 0) p.1) =
        fun _ => ContinuousLinearMap.id ℝ E := by
      funext p
      have hf : (fun y => autonomousFlow hb hLip le_rfl y p.2 0) =
          fun y => y+p.2 ⟨0,le_rfl,le_rfl⟩ := by
        funext y
        have h := (BoundedFlow.flow_trajectory (v := fun _ : ℝ => b)
          (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) le_rfl y p.2).equation 0 ⟨le_rfl,le_rfl⟩
        simpa only [autonomousFlow,intervalIntegral.integral_same,add_zero,
          BoundedFlow.noiseExtension,projIcc_of_mem _ (show (0:ℝ) ∈ Icc 0 0 from ⟨le_rfl,le_rfl⟩)] using h
      rw [hf]
      exact ((hasFDerivAt_id p.1).add_const _).fderiv
    rw [he]
    exact continuous_const
  | succ n ih =>
    have hsum : T = (n:ℝ)*δ+δ := by rw [hEq]; push_cast; ring
    clear hEq
    subst T
    have hS : 0 ≤ (n:ℝ)*δ := mul_nonneg (Nat.cast_nonneg n) hδ
    let P : E × C(Icc 0 ((n:ℝ)*δ+δ),E) → E × C(Icc 0 ((n:ℝ)*δ),E) :=
      fun p => (p.1,BoundedFlow.restrictPath (le_add_of_nonneg_right hδ) p.2)
    have hP : Continuous P := continuous_fst.prodMk
      ((BoundedFlow.restrictPath_continuous (le_add_of_nonneg_right hδ)).comp continuous_snd)
    let Q : E × C(Icc 0 ((n:ℝ)*δ+δ),E) → E × C(Icc 0 δ,E) :=
      fun p => (autonomousFlow hb hLip hS (P p).1 (P p).2 ((n:ℝ)*δ),
        BoundedFlow.shiftPath hS hδ p.2)
    have hQ : Continuous Q :=
      ((BoundedFlow.flow_continuous (v := fun _ : ℝ => b)
        (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hS ⟨hS,le_rfl⟩).comp hP).prodMk
        ((BoundedFlow.shiftPath_continuous hS hδ).comp continuous_snd)
    have hfirst := (ih hS rfl).comp hP
    obtain ⟨C,hsecond⟩ := autonomousFlow_fderiv_lipschitz_short hb hLip hbd hDb hδ hshort ⟨hδ,le_rfl⟩
    have hc := (hsecond.continuous.comp hQ).clm_comp hfirst
    convert hc using 1
    funext p
    have he : (fun y => autonomousFlow hb hLip (add_nonneg hS hδ) y p.2 ((n:ℝ)*δ+δ)) =
        (fun y => autonomousFlow hb hLip hδ y (Q p).2 δ) ∘
          (fun y => autonomousFlow hb hLip hS y (P p).2 ((n:ℝ)*δ)) := by
      funext y
      exact BoundedFlow.flow_add (hLip.continuous.comp continuous_snd) (fun _ => hb)
        (fun _ => hLip) hS hδ y p.2
    rw [he]
    exact fderiv_comp _
      (autonomousFlow_endpoint_differentiable hb hLip hbd hDb hδ (Q p).2 _)
      (autonomousFlow_endpoint_differentiable hb hLip hbd hDb hS (P p).2 _)

/-- The initial Jacobian of the actual endpoint map is jointly continuous in
initial point and continuous forcing, for every finite horizon. -/
theorem autonomousFlow_endpoint_fderiv_continuous {b : E → E} {M K K₁ : ℝ≥0}
    (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
    (hbd : Differentiable ℝ b) (hDb : LipschitzWith K₁ (fderiv ℝ b))
    {T : ℝ} (hT : 0 ≤ T) :
    Continuous (fun p : E × C(Icc 0 T,E) =>
      fderiv ℝ (fun y => autonomousFlow hb hLip hT y p.2 T) p.1) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (2*(K:ℝ)*T)
  let δ : ℝ := T/(n+1)
  have hd : 0 ≤ δ := div_nonneg hT (by positivity)
  have hs : 2*(K:ℝ)*δ ≤ 1 := by
    dsimp [δ]
    rw [← mul_div_assoc,div_le_iff₀ (by positivity)]
    linarith
  have he : ((n+1:ℕ):ℝ)*δ = T := by dsimp [δ]; push_cast; field_simp
  exact autonomousFlow_fderiv_continuous_multiple hb hLip hbd hDb hd hs (n+1) hT he.symm

/-- Fixed-time operator-norm continuity on the original continuous-path space. -/
theorem autonomousFlow_fderiv_continuous {b : E → E} {M K K₁ : ℝ≥0}
    (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
    (hbd : Differentiable ℝ b) (hDb : LipschitzWith K₁ (fderiv ℝ b))
    {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Continuous (fun p : E × C(Icc 0 T,E) =>
      fderiv ℝ (fun y => autonomousFlow hb hLip hT y p.2 t) p.1) := by
  have hc := (autonomousFlow_endpoint_fderiv_continuous hb hLip hbd hDb ht.1).comp
    (continuous_fst.prodMk ((BoundedFlow.restrictPath_continuous ht.2).comp continuous_snd))
  convert hc using 1
  funext p
  congr 1
  funext y
  exact (BoundedFlow.flow_restrict (v := fun _ : ℝ => b)
    (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) ht.1 ht.2 y p.2 ⟨ht.1,le_rfl⟩).symm

end FlowInitialDerivative
end SharpWasserstein
