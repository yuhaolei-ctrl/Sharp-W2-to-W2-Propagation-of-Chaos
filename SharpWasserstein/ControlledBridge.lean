module

public import SharpWasserstein.Compat
public import SharpWasserstein.FiniteTrajectory
public import SharpWasserstein.RegularizationRates

@[expose] public section

/-! The actual deterministic bridge and its control energy. Its trajectory
and terminal meeting are proved directly from the integral equation; no
change-of-measure identity is assumed here. -/

noncomputable section
open Set MeasureTheory
open scoped NNReal Interval

namespace SharpWasserstein.ControlledBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def path (X : ℝ → E) (x y : E) (T t : ℝ) : E := X t + (1-t/T) • (y-x)

def control (v : ℝ → E → E) (X : ℝ → E) (x y : E) (T t : ℝ) : E :=
  v t (X t) - v t (path X x y T t) - T⁻¹ • (y-x)

theorem path_terminal {X : ℝ → E} (x y : E) {T : ℝ} (hT : T ≠ 0) :
    path X x y T T = X T := by simp [path, hT]

theorem path_initial {X : ℝ → E} {x : E} (y : E) {T : ℝ} (hx : X 0 = x) :
    path X x y T 0 = y := by simp [path,hx]

theorem control_norm_le {v : ℝ → E → E} {X : ℝ → E} (x y : E)
    {T t : ℝ} {K : ℝ≥0} (hv : LipschitzWith K (v t)) (hT : 0 < T)
    (ht : t ∈ Icc 0 T) :
    ‖control v X x y T t‖ ≤ RegularizationRates.bridgeRate K T t * ‖y-x‖ := by
  have ha : 0 ≤ 1-t/T := sub_nonneg.mpr ((div_le_one hT).mpr ht.2)
  have hd : ‖X t - path X x y T t‖ = (1-t/T) * ‖y-x‖ := by
    rw [path, norm_sub_rev]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  have hdiff := hv.dist_le_mul (X t) (path X x y T t)
  simp only [dist_eq_norm, hd] at hdiff
  unfold control
  calc
    _ ≤ ‖v t (X t) - v t (path X x y T t)‖ + ‖T⁻¹ • (y-x)‖ := norm_sub_le _ _
    _ ≤ _ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT)]
      unfold RegularizationRates.bridgeRate
      simpa only [one_div, add_mul, mul_assoc] using add_le_add hdiff (le_refl (T⁻¹ * ‖y-x‖))

theorem path_trajectory [CompleteSpace E]
    {v : ℝ → E → E} {w X : ℝ → E} {x : E} (y : E) {T : ℝ}
    (h : FiniteAdditiveTrajectory v w x T X) :
    FiniteAdditiveTrajectory (fun t z => v t z + control v X x y T t) w y T (path X x y T) := by
  have hc : Continuous (fun t : ℝ => (1-t/T) • (y-x)) := by fun_prop
  refine ⟨h.continuous.add hc.continuousOn, ?_, ?_⟩
  · have he : (fun t => v t (path X x y T t) + control v X x y T t) =
        (fun t => v t (X t) - T⁻¹ • (y-x)) := by funext t; unfold control; abel
    rw [he]
    exact h.driftContinuous.sub continuousOn_const
  · intro t ht
    have hi : IntervalIntegrable (fun s => v s (X s)) volume 0 t :=
      (h.driftContinuous.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    have he : (fun s => v s (path X x y T s) + control v X x y T s) =
        (fun s => v s (X s) - T⁻¹ • (y-x)) := by funext s; unfold control; abel
    rw [he, intervalIntegral.integral_sub hi intervalIntegrable_const, intervalIntegral.integral_const]
    unfold path
    rw [h.equation t ht]
    simp only [sub_zero, smul_smul, div_eq_mul_inv, sub_smul, one_smul]
    abel

theorem path_continuousOn {X : ℝ → E} (x y : E) (T : ℝ)
    (hX : ContinuousOn X (Icc 0 T)) : ContinuousOn (path X x y T) (Icc 0 T) :=
  hX.add (by fun_prop : Continuous (fun t : ℝ => (1-t/T) • (y-x))).continuousOn

theorem control_continuousOn {v : ℝ → E → E} {X : ℝ → E} (x y : E) (T : ℝ)
    (hv : Continuous (Function.uncurry v)) (hX : ContinuousOn X (Icc 0 T)) :
    ContinuousOn (control v X x y T) (Icc 0 T) :=
  ((hv.comp_continuousOn (continuousOn_id.prodMk hX)).sub
    (hv.comp_continuousOn (continuousOn_id.prodMk (path_continuousOn x y T hX)))).sub continuousOn_const

/-- The actual control energy has the exact coefficient used in the
entropy-cost lemma for sqrt(2) noise. -/
theorem control_energy_le {v : ℝ → E → E} {X : ℝ → E} (x y : E)
    {T : ℝ} {K : ℝ≥0} (hT : 0 < T)
    (hv : Continuous (Function.uncurry v)) (hl : ∀ t, LipschitzWith K (v t))
    (hX : ContinuousOn X (Icc 0 T)) :
    (1/4 : ℝ) * (∫ t in (0 : ℝ)..T, ‖control v X x y T t‖ ^ 2) ≤
      RegularizationRates.bridgeCost K T * ‖y-x‖ ^ 2 := by
  have hi : IntervalIntegrable (fun t => ‖control v X x y T t‖ ^ 2) volume 0 T :=
    ((control_continuousOn x y T hv hX).norm.pow 2).intervalIntegrable_of_Icc hT.le
  have hj := (RegularizationRates.intervalIntegrable_bridgeRate_sq K T).mul_const (‖y-x‖^2)
  have hm := intervalIntegral.integral_mono_on hT.le hi hj (fun t ht => by
    have ha : 0 ≤ RegularizationRates.bridgeRate K T t := by
      unfold RegularizationRates.bridgeRate
      exact add_nonneg (mul_nonneg K.coe_nonneg (sub_nonneg.mpr ((div_le_one hT).mpr ht.2))) (by positivity)
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha (norm_nonneg _))).mpr
      (control_norm_le (X := X) x y (hl t) hT ht)
    simpa only [mul_pow] using hs)
  have hm' := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 1/4)
  rw [intervalIntegral.integral_mul_const, ← mul_assoc,
    RegularizationRates.integral_bridgeRate_sq K T hT] at hm'
  exact hm'

end SharpWasserstein.ControlledBridge
