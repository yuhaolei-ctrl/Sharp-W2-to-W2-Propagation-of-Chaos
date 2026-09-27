import SharpWasserstein.BoundedFlow
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Synchronous first-order comparison. The additive input may be nowhere
 differentiable: it cancels before the derivative is taken. A C¹ observable
 requires no second derivative, because strict differentiability controls its
 difference at two moving points. -/
noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped Topology NNReal Interval ContDiff
namespace SharpWasserstein.SwitchSourceDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A chain rule for a difference of two rough curves. Only their difference
is differentiable; the individual curves need merely be continuous. -/
theorem strict_test_difference_hasDerivWithinAt
    {X Y : ℝ → E} {x a : E} {s : Set ℝ} {F : E → ℝ} {D : E →L[ℝ] ℝ}
    (hX : ContinuousWithinAt X s 0) (hY : ContinuousWithinAt Y s 0)
    (hX₀ : X 0 = x) (hY₀ : Y 0 = x)
    (hXY : HasDerivWithinAt (fun t => X t-Y t) a s 0)
    (hF : HasStrictFDerivAt F D x) :
    HasDerivWithinAt (fun t => F (X t)-F (Y t)) (D a) s 0 := by
  have hp : Tendsto (fun t => (X t,Y t)) (𝓝[s] 0) (𝓝 (x,x)) := by
    simpa only [hX₀,hY₀] using hX.prodMk_nhds hY
  have hb : (fun t => X t-Y t) =O[𝓝[s] 0] (fun t : ℝ => t-0) := by
    simpa only [hX₀,hY₀,sub_self,sub_zero] using hXY.hasFDerivWithinAt.isBigO_sub
  have he := (hF.isLittleO.comp_tendsto hp).trans_isBigO hb
  have hd : HasDerivWithinAt (fun t => D (X t-Y t)) (D a) s 0 :=
    D.hasFDerivAt.comp_hasDerivWithinAt 0 hXY
  apply HasDerivWithinAt.of_isLittleO
  exact (he.add hd.isLittleO).congr_left (fun t => by
    simp only [Function.comp_def,hX₀,hY₀,sub_self,map_zero,sub_zero]
    ring)

/-- The actual two integral equations give the compensated difference
 derivative, including their common initial time. -/
theorem trajectory_difference_hasDerivWithinAt
    {v q : ℝ → E → E} {w X Y : ℝ → E} {x y : E} {T t : ℝ}
    (hX : FiniteAdditiveTrajectory v w x T X)
    (hY : FiniteAdditiveTrajectory q w y T Y) (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun r => X r-Y r) (v t (X t)-q t (Y t)) (Icc 0 T) t := by
  convert (hX.compensated_derivative ht).sub (hY.compensated_derivative ht) using 1
  ext r
  change X r-Y r = (X r-w r)-(Y r-w r)
  abel

/-- A genuine local switching derivative for arbitrary continuous additive
input, with the drift difference in the reference-minus-particle direction. -/
theorem trajectory_test_difference_hasDerivWithinAt_zero
    {v q : ℝ → E → E} {w X Y : ℝ → E} {x : E} {T : ℝ}
    (hT : 0 ≤ T) (hw : w 0 = 0)
    (hX : FiniteAdditiveTrajectory v w x T X)
    (hY : FiniteAdditiveTrajectory q w x T Y)
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) :
    HasDerivWithinAt (fun r => F (X r)-F (Y r))
      (fderiv ℝ F x (v 0 x-q 0 x)) (Icc 0 T) 0 := by
  have hx := hX.initial hT hw
  have hy := hY.initial hT hw
  apply strict_test_difference_hasDerivWithinAt
    (hX.continuous 0 ⟨le_rfl,hT⟩) (hY.continuous 0 ⟨le_rfl,hT⟩) hx hy
  · simpa only [hx,hy] using trajectory_difference_hasDerivWithinAt hX hY ⟨le_rfl,hT⟩
  · exact hF.hasStrictFDerivAt (by norm_num)

omit [CompleteSpace E] in
/-- Bounded drifts give a deterministic integrable dominator for the
 difference quotient; no moment or modulus assumption on the input is used. -/
theorem trajectory_difference_norm_le
    {v q : ℝ → E → E} {w X Y : ℝ → E} {x : E} {T t M A : ℝ}
    (hX : FiniteAdditiveTrajectory v w x T X)
    (hY : FiniteAdditiveTrajectory q w x T Y)
    (hv : ∀ r ∈ Icc 0 T, ∀ z, ‖v r z‖ ≤ M)
    (hq : ∀ r ∈ Icc 0 T, ∀ z, ‖q r z‖ ≤ A) (ht : t ∈ Icc 0 T) :
    ‖X t-Y t‖ ≤ (M+A)*t := by
  have hXi : IntervalIntegrable (fun r => v r (X r)) volume 0 t := (hX.driftContinuous.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have hYi : IntervalIntegrable (fun r => q r (Y r)) volume 0 t := (hY.driftContinuous.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have he : X t-Y t = ∫ r in (0:ℝ)..t, v r (X r)-q r (Y r) := by
    rw [intervalIntegral.integral_sub hXi hYi,hX.equation t ht,hY.equation t ht]
    abel
  rw [he]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := t) (C := M+A) (f := fun r => v r (X r)-q r (Y r)) (by
      intro r hr
      have hrT : r ∈ Icc 0 T := ⟨(uIoc_of_le ht.1 ▸ hr).1.le,(uIoc_of_le ht.1 ▸ hr).2.trans ht.2⟩
      exact (norm_sub_le _ _).trans (add_le_add (hv r hrT _) (hq r hrT _)))
  simpa only [sub_zero,abs_of_nonneg ht.1] using hn

omit [CompleteSpace E] in
/-- Bounded C¹ tests have uniformly bounded synchronous difference quotients. -/
theorem trajectory_test_difference_norm_le
    {v q : ℝ → E → E} {w X Y : ℝ → E} {x : E} {T t M A : ℝ}
    (hX : FiniteAdditiveTrajectory v w x T X)
    (hY : FiniteAdditiveTrajectory q w x T Y)
    (hv : ∀ r ∈ Icc 0 T, ∀ z, ‖v r z‖ ≤ M)
    (hq : ∀ r ∈ Icc 0 T, ∀ z, ‖q r z‖ ≤ A) (ht : t ∈ Icc 0 T)
    {F : E → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) :
    ‖F (X t)-F (Y t)‖ ≤ (L:ℝ)*(M+A)*t := by
  have hh := hF.dist_le_mul (X t) (Y t)
  rw [dist_eq_norm,dist_eq_norm] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left
    (trajectory_difference_norm_le hX hY hv hq ht) L.coe_nonneg).trans_eq (by ring))

end SharpWasserstein.SwitchSourceDerivative
