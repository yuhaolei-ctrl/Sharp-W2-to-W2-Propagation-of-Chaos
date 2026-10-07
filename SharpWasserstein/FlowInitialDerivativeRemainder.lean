module

public import SharpWasserstein.Compat
public import SharpWasserstein.FlowInitialDerivativeLinear
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-! Actual linearization error of two continuous-forcing trajectories, obtained
from a genuine variational ODE, Taylor's inequality, and Grönwall. -/
noncomputable section
open Set MeasureTheory Metric Filter Asymptotics
open scoped NNReal Interval Topology
namespace SharpWasserstein.FlowInitialDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem taylor_error_le_lipschitz_fderiv {b : E → E} {K₁ : ℝ≥0}
    (hb : Differentiable ℝ b) (hDb : LipschitzWith K₁ (fderiv ℝ b)) (x y : E) :
    ‖b y-b x-fderiv ℝ b x (y-x)‖ ≤ (K₁:ℝ)*‖y-x‖^2 := by
  have hh := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (f := b) (φ := fderiv ℝ b x) (fun z _ => hb z)
    (fun z hz => (hDb.norm_sub_le z x).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) K₁.coe_nonneg))
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [pow_two,mul_assoc] using hh

/-- A true trajectory has quadratic error against a true variational solution.
The coefficient is finite and independent of the perturbation in the initial data. -/
theorem trajectory_linearization_error {b : E → E} {w X Y : ℝ → E}
    {x y : E} {K K₁ : ℝ≥0} {T t : ℝ} {A : ℝ → E →L[ℝ] E} {J : ℝ → E →L[ℝ] E}
    (hb : Differentiable ℝ b) (hLip : LipschitzWith K b)
    (hDb : LipschitzWith K₁ (fderiv ℝ b))
    (hX : FiniteAdditiveTrajectory (fun _ => b) w x T X)
    (hY : FiniteAdditiveTrajectory (fun _ => b) w y T Y)
    (hJ : LinearVariation A T J) (hA : ∀ s ∈ Icc 0 T, A s = fderiv ℝ b (X s))
    (ht : t ∈ Icc 0 T) :
    ‖Y t-X t-J t (y-x)‖ ≤
      ((K₁:ℝ)*Real.exp ((K:ℝ)*T)^2 / ((K:ℝ)+1) *
        (Real.exp (((K:ℝ)+1)*t)-1))*‖y-x‖^2 := by
  let R : ℝ → E := fun s => Y s-X s-J s (y-x)
  let C : ℝ := (K₁:ℝ)*Real.exp ((K:ℝ)*T)^2
  have hc : ContinuousOn R (Icc 0 t) :=
    ((hY.continuous.sub hX.continuous).sub (hJ.continuous.clm_apply continuousOn_const)).mono
      (Icc_subset_Icc_right ht.2)
  have hi : R 0 = 0 := by
    dsimp [R]
    rw [hX.equation 0 ⟨le_rfl,ht.1.trans ht.2⟩,hY.equation 0 ⟨le_rfl,ht.1.trans ht.2⟩,hJ.initial]
    simp
  have hd : ∀ s ∈ Ico 0 t, HasDerivWithinAt R
      (b (Y s)-b (X s)-(A s) (J s (y-x))) (Ici s) s := by
    intro s hs
    have hsT : s ∈ Ico 0 T := ⟨hs.1,hs.2.trans_le ht.2⟩
    have hdiff : HasDerivWithinAt (fun r => Y r-X r) (b (Y s)-b (X s)) (Ici s) s := by
      convert (hY.compensated_derivative_right hsT).sub (hX.compensated_derivative_right hsT) using 1
      ext r
      change Y r-X r = (Y r-w r)-(X r-w r)
      abel
    have hlin := (hJ.derivative_right hsT).clm_apply (hasDerivWithinAt_const s (Ici s) (y-x))
    simpa only [R,Pi.sub_def,map_zero,add_zero,ContinuousLinearMap.comp_apply] using hdiff.sub hlin
  have hbound : ∀ s ∈ Ico 0 t,
      ‖b (Y s)-b (X s)-(A s) (J s (y-x))‖ ≤ ((K:ℝ)+1)*‖R s‖+C*‖y-x‖^2 := by
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1,hs.2.le.trans ht.2⟩
    have hsep : ‖Y s-X s‖ ≤ ‖y-x‖*Real.exp ((K:ℝ)*T) := by
      apply (hY.stability (fun _ _ => hLip) hX hsT).trans
      gcongr
      exact hsT.2
    have hTaylor := taylor_error_le_lipschitz_fderiv hb hDb (X s) (Y s)
    have hnA : ‖A s‖ ≤ K := by rw [hA s hsT]; exact norm_fderiv_le_of_lipschitz ℝ hLip
    have he : b (Y s)-b (X s)-(A s) (J s (y-x)) =
        (b (Y s)-b (X s)-fderiv ℝ b (X s) (Y s-X s))+(A s) (R s) := by
      rw [hA s hsT]
      dsimp [R]
      simp only [map_sub]
      abel
    rw [he]
    calc
      _ ≤ ‖b (Y s)-b (X s)-fderiv ℝ b (X s) (Y s-X s)‖+‖(A s) (R s)‖ := norm_add_le _ _
      _ ≤ (K₁:ℝ)*‖Y s-X s‖^2 + (K:ℝ)*‖R s‖ :=
        add_le_add hTaylor ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right hnA (norm_nonneg _)))
      _ ≤ (K₁:ℝ)*(‖y-x‖*Real.exp ((K:ℝ)*T))^2 + (K:ℝ)*‖R s‖ := by gcongr
      _ ≤ _ := by dsimp [C]; nlinarith [norm_nonneg (R s)]
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le hc hd
    (show ‖R 0‖ ≤ 0 by rw [hi,norm_zero]) hbound t ⟨ht.1,le_rfl⟩
  have hK : (K:ℝ)+1 ≠ 0 := by positivity
  simpa only [gronwallBound_of_K_ne_0 hK,zero_mul,zero_add,sub_zero,R,C,
    div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh

omit [CompleteSpace E] in
/-- A global quadratic remainder estimate implies the genuine Fréchet derivative. -/
theorem hasFDerivAt_of_quadratic_error {f : E → E} (x : E) (J : E →L[ℝ] E)
    {C : ℝ} (hC : 0 ≤ C) (hR : ∀ y, ‖f y-f x-J (y-x)‖ ≤ C*‖y-x‖^2) :
    HasFDerivAt f J x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  have hδ : 0 < ε/(C+1) := div_pos hε (by positivity)
  have hsmall : ∀ᶠ z : E in 𝓝 0, ‖z‖ < ε/(C+1) :=
    (continuous_norm.tendsto 0).eventually (gt_mem_nhds (by simpa using hδ))
  filter_upwards [hsmall] with z hz
  have hr := hR (x+z)
  rw [add_sub_cancel_left] at hr
  have he : C*‖z‖ ≤ ε := by
    have hz' : ‖z‖*(C+1) < ε := (lt_div_iff₀ (by positivity)).mp hz
    nlinarith [norm_nonneg z]
  exact hr.trans (by simpa only [pow_two,mul_assoc] using mul_le_mul_of_nonneg_right he (norm_nonneg z))

end SharpWasserstein.FlowInitialDerivative
