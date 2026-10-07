module

public import SharpWasserstein.Compat
public import SharpWasserstein.SynchronousStability
public import Mathlib.Analysis.ODE.ExistUnique

@[expose] public section

/-! Actual existence of continuous-forcing integral solutions on every finite
horizon for globally bounded, globally Lipschitz drifts. Picard--Lindelöf is
applied to the translated ODE, so no derivative of the forcing is assumed. -/

noncomputable section
open Set MeasureTheory Metric
open scoped Interval NNReal

namespace SharpWasserstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure FiniteAdditiveTrajectory (v : ℝ → E → E) (w : ℝ → E) (x₀ : E)
    (T : ℝ) (X : ℝ → E) : Prop where
  continuous : ContinuousOn X (Icc 0 T)
  driftContinuous : ContinuousOn (fun t => v t (X t)) (Icc 0 T)
  equation : ∀ t ∈ Icc 0 T, X t = x₀ + (∫ s in (0 : ℝ)..t, v s (X s)) + w t

/-- Boundedness lets the Picard--Lindelöf ball grow with any prescribed horizon. -/
theorem exists_finiteAdditiveTrajectory
    [CompleteSpace E]
    {v : ℝ → E → E} {w : ℝ → E} {M K : ℝ≥0}
    (hv : Continuous (Function.uncurry v)) (hw : Continuous w)
    (hbound : ∀ t x, ‖v t x‖ ≤ M)
    (hlip : ∀ t, LipschitzWith K (v t)) (x₀ : E) {T : ℝ} (hT : 0 ≤ T) :
    ∃ X, FiniteAdditiveTrajectory v w x₀ T X := by
  let f : ℝ → E → E := fun t x => v t (x + w t)
  have hf : Continuous (Function.uncurry f) := hv.comp
    (continuous_fst.prodMk (continuous_snd.add (hw.comp continuous_fst)))
  have hpic : IsPicardLindelof f (⟨0, ⟨le_rfl, hT⟩⟩ : Icc 0 T) x₀
      ⟨(M : ℝ) * T, by positivity⟩ 0 M K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t _
      apply LipschitzWith.lipschitzOnWith
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa [f, dist_add_right] using (hlip t).dist_le_mul (x + w t) (y + w t)
    · intro x _
      exact (hf.comp (continuous_id.prodMk continuous_const)).continuousOn
    · intro t _ x _
      exact hbound t (x + w t)
    · change (M : ℝ) * max (T - 0) (0 - 0) ≤ (M : ℝ) * T - 0
      simp [max_eq_left hT]
  obtain ⟨Y, hY₀, hY⟩ := hpic.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hYc : ContinuousOn Y (Icc 0 T) := HasDerivWithinAt.continuousOn hY
  have hfc : ContinuousOn (fun t => f t (Y t)) (Icc 0 T) :=
    hf.comp_continuousOn (continuousOn_id.prodMk hYc)
  have hEq : ∀ t ∈ Icc 0 T, Y t = x₀ + ∫ s in (0 : ℝ)..t, f s (Y s) := by
    intro t ht
    have hs : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      (hYc.mono hs) (fun s hst =>
        (hY s (hs ⟨hst.1.le, hst.2.le⟩)).hasDerivAt
          (Icc_mem_nhds hst.1 (hst.2.trans_le ht.2)))
      ((hfc.mono hs).intervalIntegrable_of_Icc ht.1)
    rw [hY₀] at hFTC
    rw [hFTC]
    abel
  refine ⟨fun t => Y t + w t, hYc.add hw.continuousOn, hfc, ?_⟩
  intro t ht
  rw [hEq t ht]

/-- An existing global trajectory restricts to every finite horizon. -/
theorem AdditiveTrajectory.finite {v : ℝ → E → E} {w X : ℝ → E} {x₀ : E}
    (h : AdditiveTrajectory v w x₀ X) (T : ℝ) :
    FiniteAdditiveTrajectory v w x₀ T X :=
  ⟨h.continuous.mono Icc_subset_Ici_self,
    h.driftContinuous.mono Icc_subset_Ici_self, fun t ht => h.equation t ht.1⟩

/-- The label is the genuine initial point when the forcing starts at zero. -/
theorem FiniteAdditiveTrajectory.initial {v : ℝ → E → E} {w X : ℝ → E}
    {x₀ : E} {T : ℝ} (h : FiniteAdditiveTrajectory v w x₀ T X)
    (hT : 0 ≤ T) (hw : w 0 = 0) : X 0 = x₀ := by
  simpa [hw] using h.equation 0 ⟨le_rfl, hT⟩

/-- The compensated path is differentiable even for nondifferentiable forcing. -/
theorem FiniteAdditiveTrajectory.compensated_derivative [CompleteSpace E]
    {v : ℝ → E → E} {w X : ℝ → E} {x₀ : E} {T t : ℝ}
    (h : FiniteAdditiveTrajectory v w x₀ T X) (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun s => X s - w s) (v t (X t)) (Icc 0 T) t := by
  let c : ℝ → ℝ := fun s => (projIcc 0 T (ht.1.trans ht.2) s).val
  let f : ℝ → E := fun s => v (c s) (X (c s))
  have hc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  have hf : Continuous f := h.driftContinuous.comp_continuous hc
    (fun s => (projIcc 0 T (ht.1.trans ht.2) s).property)
  have heq : ∀ s ∈ Icc 0 T, X s - w s = x₀ + ∫ u in (0 : ℝ)..s, f u := by
    intro s hs
    rw [h.equation s hs, add_sub_cancel_right]
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Icc 0 T := Icc_subset_Icc_right hs.2
      (by simpa only [uIcc_of_le hs.1] using hu)
    simp only [f, c, projIcc_of_mem _ hu']
  have hft : f t = v t (X t) := by simp only [f, c, projIcc_of_mem _ ht]
  have hder : HasDerivWithinAt (fun s => x₀ + ∫ u in (0 : ℝ)..s, f u)
      (f t) (Icc 0 T) t := ((intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable 0 t) (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt).const_add x₀).hasDerivWithinAt
  rw [hft] at hder
  exact hder.congr_of_mem heq ht

/-- Interior-right derivative needed by the finite-horizon Grönwall theorem. -/
theorem FiniteAdditiveTrajectory.compensated_derivative_right [CompleteSpace E]
    {v : ℝ → E → E} {w X : ℝ → E} {x₀ : E} {T t : ℝ}
    (h : FiniteAdditiveTrajectory v w x₀ T X) (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun s => X s - w s) (v t (X t)) (Ici t) t := by
  apply (h.compensated_derivative ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
  change Icc 0 T ∈ nhdsWithin t (Ici t)
  rw [← Ici_inter_Iic]
  exact Filter.inter_mem
    (Filter.mem_of_superset self_mem_nhdsWithin (fun s hs => ht.1.trans hs))
    (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht.2))

/-- Finite-horizon synchronous stability for the constructed solutions. -/
theorem FiniteAdditiveTrajectory.stability [CompleteSpace E]
    {v : ℝ → E → E} {w X Y : ℝ → E} {x₀ y₀ : E} {K : ℝ≥0} {T t : ℝ}
    (hv : ∀ s ∈ Icc 0 T, LipschitzWith K (v s))
    (hX : FiniteAdditiveTrajectory v w x₀ T X)
    (hY : FiniteAdditiveTrajectory v w y₀ T Y) (ht : t ∈ Icc 0 T) :
    ‖X t - Y t‖ ≤ ‖x₀ - y₀‖ * Real.exp ((K : ℝ) * t) := by
  have hi : X 0 - Y 0 = x₀ - y₀ := by
    rw [hX.equation 0 ⟨le_rfl, ht.1.trans ht.2⟩,
      hY.equation 0 ⟨le_rfl, ht.1.trans ht.2⟩]
    simp
  have hc : ContinuousOn (fun s => X s - Y s) (Icc 0 t) :=
    (hX.continuous.sub hY.continuous).mono (Icc_subset_Icc_right ht.2)
  have hd : ∀ s ∈ Ico 0 t, HasDerivWithinAt (fun u => X u - Y u)
      (v s (X s) - v s (Y s)) (Ici s) s := by
    intro s hs
    have hsT : s ∈ Ico 0 T := ⟨hs.1, hs.2.trans_le ht.2⟩
    convert (hX.compensated_derivative_right hsT).sub
      (hY.compensated_derivative_right hsT) using 1
    ext s
    change X s - Y s = (X s - w s) - (Y s - w s)
    abel
  have hb : ∀ s ∈ Ico 0 t,
      ‖v s (X s) - v s (Y s)‖ ≤ (K : ℝ) * ‖X s - Y s‖ + 0 := by
    intro s hs
    simpa only [dist_eq_norm, add_zero] using
      (hv s ⟨hs.1, hs.2.le.trans ht.2⟩).dist_le_mul (X s) (Y s)
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hc hd
    (show ‖X 0 - Y 0‖ ≤ ‖x₀ - y₀‖ by rw [hi]) hb t ⟨ht.1, le_rfl⟩
  simpa only [gronwallBound_ε0, sub_zero] using hg

end SharpWasserstein
