module

public import SharpWasserstein.Compat
public import SharpWasserstein.FlowInitialDerivative
public import SharpWasserstein.FlowSemigroup

@[expose] public section

/-! Global finite-horizon initial-value differentiability, obtained by composing
the constructed short-time differentiable flows. The sharp derivative bound
comes from actual synchronous stability, without multiplying coarse constants. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal Topology
namespace SharpWasserstein.FlowInitialDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Finite compositions of the genuine short-time flows are differentiable. -/
theorem autonomousFlow_endpoint_differentiable_multiple {b : E → E} {M K K₁ : ℝ≥0}
    (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
    (hbd : Differentiable ℝ b) (hDb : LipschitzWith K₁ (fderiv ℝ b))
    {δ : ℝ} (hδ : 0 ≤ δ) (hshort : 2*(K:ℝ)*δ ≤ 1) (n : ℕ)
    {T : ℝ} (hT : 0 ≤ T) (hEq : T = (n:ℝ)*δ) (w : C(Icc 0 T,E)) :
    Differentiable ℝ (fun x => autonomousFlow hb hLip hT x w T) := by
  induction n generalizing T with
  | zero =>
    have hz : T = 0 := by simpa only [Nat.cast_zero,zero_mul] using hEq
    clear hEq
    subst T
    have he : (fun x => autonomousFlow hb hLip (by positivity : (0:ℝ) ≤ 0) x w 0) =
        fun x => x + w ⟨0,le_rfl,le_rfl⟩ := by
      funext x
      have h := (BoundedFlow.flow_trajectory (v := fun _ : ℝ => b)
        (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) le_rfl x w).equation 0 ⟨le_rfl,le_rfl⟩
      simpa only [autonomousFlow,intervalIntegral.integral_same,add_zero,
        BoundedFlow.noiseExtension,projIcc_of_mem _ (show (0:ℝ) ∈ Icc 0 0 from ⟨le_rfl,le_rfl⟩)] using h
    rw [he]
    exact differentiable_id.add_const _
  | succ n ih =>
    have hsum : T = (n:ℝ)*δ+δ := by rw [hEq]; push_cast; ring
    clear hEq
    subst T
    have hS : 0 ≤ (n:ℝ)*δ := mul_nonneg (Nat.cast_nonneg n) hδ
    let wp := BoundedFlow.restrictPath (le_add_of_nonneg_right hδ) w
    let wf := BoundedFlow.shiftPath hS hδ w
    have h1 := ih hS rfl wp
    have h2 : Differentiable ℝ (fun x => autonomousFlow hb hLip hδ x wf δ) := by
      intro x
      exact (flow_fderiv_norm_le_exp_short hb hLip hbd hDb hδ hshort x wf ⟨hδ,le_rfl⟩).1
    have he : (fun x => autonomousFlow hb hLip (add_nonneg hS hδ) x w ((n:ℝ)*δ+δ)) =
        (fun x => autonomousFlow hb hLip hδ x wf δ) ∘
          (fun x => autonomousFlow hb hLip hS x wp ((n:ℝ)*δ)) := by
      funext x
      exact BoundedFlow.flow_add (hLip.continuous.comp continuous_snd) (fun _ => hb)
        (fun _ => hLip) hS hδ x w
    rw [he]
    exact h2.comp h1

/-- Arbitrary finite-horizon differentiability in the initial point of the
actual bounded autonomous flow with a continuous additive input. -/
theorem autonomousFlow_endpoint_differentiable {b : E → E} {M K K₁ : ℝ≥0}
    (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
    (hbd : Differentiable ℝ b) (hDb : LipschitzWith K₁ (fderiv ℝ b))
    {T : ℝ} (hT : 0 ≤ T) (w : C(Icc 0 T,E)) :
    Differentiable ℝ (fun x => autonomousFlow hb hLip hT x w T) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (2*(K:ℝ)*T)
  let δ : ℝ := T/(n+1)
  have hd : 0 ≤ δ := div_nonneg hT (by positivity)
  have hs : 2*(K:ℝ)*δ ≤ 1 := by
    dsimp [δ]
    rw [← mul_div_assoc,div_le_iff₀ (by positivity)]
    linarith
  have he : ((n+1:ℕ):ℝ)*δ = T := by dsimp [δ]; push_cast; field_simp
  exact autonomousFlow_endpoint_differentiable_multiple hb hLip hbd hDb hd hs (n+1) hT he.symm w

/-- Every time evaluation is genuinely Fréchet differentiable, with the
operator norm bounded by exp(Kt) from the actual flow stability estimate. -/
theorem autonomousFlow_hasFDerivAt_and_norm {b : E → E} {M K K₁ : ℝ≥0}
    (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
    (hbd : Differentiable ℝ b) (hDb : LipschitzWith K₁ (fderiv ℝ b))
    {T : ℝ} (hT : 0 ≤ T) (w : C(Icc 0 T,E)) (x : E) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasFDerivAt (fun y => autonomousFlow hb hLip hT y w t)
      (fderiv ℝ (fun y => autonomousFlow hb hLip hT y w t) x) x ∧
    ‖fderiv ℝ (fun y => autonomousFlow hb hLip hT y w t) x‖ ≤ Real.exp ((K:ℝ)*t) := by
  have he : (fun y => autonomousFlow hb hLip ht.1 y (BoundedFlow.restrictPath ht.2 w) t) =
      (fun y => autonomousFlow hb hLip hT y w t) := by
    funext y
    exact BoundedFlow.flow_restrict (v := fun _ : ℝ => b)
      (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) ht.1 ht.2 y w ⟨ht.1,le_rfl⟩
  have hd := autonomousFlow_endpoint_differentiable hb hLip hbd hDb ht.1 (BoundedFlow.restrictPath ht.2 w)
  rw [he] at hd
  refine ⟨(hd x).hasFDerivAt, ?_⟩
  have hL : LipschitzWith ⟨Real.exp ((K:ℝ)*t),by positivity⟩
      (fun y => autonomousFlow hb hLip hT y w t) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [dist_eq_norm,dist_eq_norm]
    change ‖autonomousFlow hb hLip hT y w t-autonomousFlow hb hLip hT z w t‖ ≤
      Real.exp ((K:ℝ)*t)*‖y-z‖
    have h := BoundedFlow.flow_difference_le (v := fun _ : ℝ => b)
      (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hT y z w w ht
    simpa only [autonomousFlow,sub_self,norm_zero,add_zero,mul_comm,NNReal.coe_mk] using h
  exact norm_fderiv_le_of_lipschitz ℝ hL

end SharpWasserstein.FlowInitialDerivative
