module

public import SharpWasserstein.Compat
public import SharpWasserstein.DriftBounds
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! Pathwise stability for genuine integral equations with a common additive
forcing. The forcing cancels; it is never differentiated. This applies to
continuous Brownian sample paths once the integral solution is constructed. -/

noncomputable section
open Set MeasureTheory
open scoped Interval NNReal

namespace SharpWasserstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure AdditiveTrajectory (v : ℝ → E → E) (w : ℝ → E) (x₀ : E)
    (X : ℝ → E) : Prop where
  continuous : ContinuousOn X (Ici 0)
  driftContinuous : ContinuousOn (fun t => v t (X t)) (Ici 0)
  equation : ∀ t, 0 ≤ t → X t = x₀ + (∫ s in (0 : ℝ)..t, v s (X s)) + w t

/-- Cancel a common forcing in two actual integral equations. -/
theorem additiveTrajectory_difference_integral
    {v : ℝ → E → E} {w X Y : ℝ → E} {x₀ y₀ : E}
    (hX : AdditiveTrajectory v w x₀ X) (hY : AdditiveTrajectory v w y₀ Y)
    {t : ℝ} (ht : 0 ≤ t) :
    X t - Y t = x₀ - y₀ + ∫ s in (0 : ℝ)..t, (v s (X s) - v s (Y s)) := by
  have hIX : IntervalIntegrable (fun s => v s (X s)) volume 0 t :=
    (hX.driftContinuous.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc ht
  have hIY : IntervalIntegrable (fun s => v s (Y s)) volume 0 t :=
    (hY.driftContinuous.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc ht
  rw [intervalIntegral.integral_sub hIX hIY, hX.equation t ht, hY.equation t ht]
  abel

variable [CompleteSpace E]

/-- The difference is right differentiable even if the common forcing is nowhere differentiable. -/
theorem additiveTrajectory_difference_derivative
    {v : ℝ → E → E} {w X Y : ℝ → E} {x₀ y₀ : E}
    (hX : AdditiveTrajectory v w x₀ X) (hY : AdditiveTrajectory v w y₀ Y)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => X s - Y s) (v t (X t) - v t (Y t)) (Ici t) t := by
  let f : ℝ → E := fun s => v (max 0 s) (X (max 0 s)) - v (max 0 s) (Y (max 0 s))
  have hf : Continuous f := (hX.driftContinuous.sub hY.driftContinuous).comp_continuous
    (continuous_const.max continuous_id) (fun s => le_max_left 0 s)
  have hEq : ∀ s, 0 ≤ s → X s - Y s = x₀ - y₀ + ∫ u in (0 : ℝ)..s, f u := by
    intro s hs
    rw [additiveTrajectory_difference_integral hX hY hs]
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : 0 ≤ u := (show u ∈ Icc 0 s from by simpa [uIcc_of_le hs] using hu).1
    simp only [f, max_eq_right hu0]
  have hder : HasDerivWithinAt (fun s => x₀ - y₀ + ∫ u in (0 : ℝ)..s, f u)
      (f t) (Ici t) t := ((intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable 0 t) (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt).const_add (x₀ - y₀)).hasDerivWithinAt
  have hft : f t = v t (X t) - v t (Y t) := by simp only [f, max_eq_right ht]
  rw [hft] at hder
  exact hder.congr_of_mem (fun s hs => hEq s (ht.trans hs)) (mem_Ici.2 le_rfl)

/-- Grönwall stability follows from the integral equations themselves. -/
theorem additiveTrajectory_stability
    {v : ℝ → E → E} {w X Y : ℝ → E} {x₀ y₀ : E} {K : ℝ≥0}
    (hv : ∀ t, 0 ≤ t → LipschitzWith K (v t))
    (hX : AdditiveTrajectory v w x₀ X) (hY : AdditiveTrajectory v w y₀ Y)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖X t - Y t‖ ≤ ‖x₀ - y₀‖ * Real.exp ((K : ℝ) * t) := by
  have hi : X 0 - Y 0 = x₀ - y₀ := by
    simpa using additiveTrajectory_difference_integral hX hY (t := 0) le_rfl
  have hc : ContinuousOn (fun s => X s - Y s) (Icc 0 t) :=
    (hX.continuous.sub hY.continuous).mono Icc_subset_Ici_self
  have hd : ∀ s ∈ Ico 0 t, HasDerivWithinAt (fun u => X u - Y u)
      (v s (X s) - v s (Y s)) (Ici s) s :=
    fun s hs => additiveTrajectory_difference_derivative hX hY hs.1
  have hb : ∀ s ∈ Ico 0 t,
      ‖v s (X s) - v s (Y s)‖ ≤ (K : ℝ) * ‖X s - Y s‖ + 0 := by
    intro s hs
    simpa only [dist_eq_norm, add_zero] using (hv s hs.1).dist_le_mul (X s) (Y s)
  have h := norm_le_gronwallBound_of_norm_deriv_right_le hc hd
    (show ‖X 0 - Y 0‖ ≤ ‖x₀ - y₀‖ by rw [hi]) hb t ⟨ht, le_rfl⟩
  simpa only [gronwallBound_ε0, sub_zero] using h

/-- Uniqueness for the same initial point and additive forcing. -/
theorem additiveTrajectory_unique
    {v : ℝ → E → E} {w X Y : ℝ → E} {x₀ : E} {K : ℝ≥0}
    (hv : ∀ t, 0 ≤ t → LipschitzWith K (v t))
    (hX : AdditiveTrajectory v w x₀ X) (hY : AdditiveTrajectory v w x₀ Y) :
    ∀ t, 0 ≤ t → X t = Y t := by
  intro t ht
  have h := additiveTrajectory_stability hv hX hY ht
  simpa only [sub_self, norm_zero, zero_mul, norm_le_zero_iff, sub_eq_zero] using h

end SharpWasserstein
