module

public import SharpWasserstein.Compat
public import SharpWasserstein.BoundedFlow
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

@[expose] public section

/-! Constructed short-time variational equations for continuous operator fields.
No solution of the variational equation is postulated: Picard–Lindelöf constructs
it and the actual differential equation gives the exponential operator bound. -/
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal Interval
namespace SharpWasserstein.FlowInitialDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

structure LinearVariation (A : ℝ → E →L[ℝ] E) (T : ℝ)
    (J : ℝ → E →L[ℝ] E) : Prop where
  continuous : ContinuousOn J (Icc 0 T)
  initial : J 0 = ContinuousLinearMap.id ℝ E
  derivative : ∀ t ∈ Icc 0 T,
    HasDerivWithinAt J ((A t).comp (J t)) (Icc 0 T) t

theorem exists_linearVariation_short {A : ℝ → E →L[ℝ] E} {K : ℝ≥0}
    (hA : Continuous A) (hK : ∀ t, ‖A t‖ ≤ K) {T : ℝ}
    (hT : 0 ≤ T) (hshort : 2*(K:ℝ)*T ≤ 1) :
    ∃ J, LinearVariation A T J := by
  let f : ℝ → (E →L[ℝ] E) → E →L[ℝ] E := fun t J => (A t).comp J
  have hpic : IsPicardLindelof f (⟨0,⟨le_rfl,hT⟩⟩ : Icc 0 T)
      (ContinuousLinearMap.id ℝ E) 1 0 (2*K) K := by
    refine ⟨?_,?_,?_,?_⟩
    · intro t _
      apply LipschitzWith.lipschitzOnWith
      apply LipschitzWith.of_dist_le_mul
      intro J H
      rw [dist_eq_norm,dist_eq_norm]
      change ‖(A t).comp J-(A t).comp H‖ ≤ (K:ℝ)*‖J-H‖
      rw [← ContinuousLinearMap.comp_sub]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hK t) (norm_nonneg _))
    · intro J _
      exact (hA.clm_comp continuous_const).continuousOn
    · intro t _ J hJ
      have hJdist : ‖J-ContinuousLinearMap.id ℝ E‖ ≤ 1 := by
        simpa only [mem_closedBall,dist_eq_norm,NNReal.coe_one] using hJ
      have hJn : ‖J‖ ≤ 2 := by
        have hn := norm_add_le (J-ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E)
        rw [sub_add_cancel] at hn
        linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)]
      calc ‖f t J‖ ≤ ‖A t‖*‖J‖ := ContinuousLinearMap.opNorm_comp_le _ _
           _ ≤ (K:ℝ)*2 := mul_le_mul (hK t) hJn (norm_nonneg _) K.coe_nonneg
           _ = (2*K:ℝ≥0) := by simp only [NNReal.coe_mul,NNReal.coe_ofNat]; ring
    · simpa only [sub_zero, max_eq_left hT, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_one,
        NNReal.coe_zero] using hshort
  obtain ⟨J,hJ₀,hJ⟩ := hpic.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨J,HasDerivWithinAt.continuousOn hJ,hJ₀,hJ⟩

omit [CompleteSpace E] in
theorem LinearVariation.derivative_right {A : ℝ → E →L[ℝ] E} {T : ℝ}
    {J : ℝ → E →L[ℝ] E} (hJ : LinearVariation A T J) {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt J ((A t).comp (J t)) (Ici t) t := by
  apply (hJ.derivative t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin
  change Icc 0 T ∈ nhdsWithin t (Ici t)
  rw [← Ici_inter_Iic]
  exact Filter.inter_mem
    (Filter.mem_of_superset self_mem_nhdsWithin (fun s hs => ht.1.trans hs))
    (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht.2))

omit [CompleteSpace E] in
/-- The actual variational solution has the sharp dimension-free exponential bound. -/
theorem LinearVariation.norm_le_exp {A : ℝ → E →L[ℝ] E} {K : ℝ≥0} {T : ℝ}
    {J : ℝ → E →L[ℝ] E} (hJ : LinearVariation A T J)
    (hK : ∀ s ∈ Icc 0 T, ‖A s‖ ≤ K) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖J t‖ ≤ Real.exp ((K:ℝ)*t) := by
  have hb : ∀ s ∈ Ico 0 t, ‖(A s).comp (J s)‖ ≤ (K:ℝ)*‖J s‖+0 := by
    intro s hs
    simpa only [add_zero] using (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hK s ⟨hs.1,hs.2.le.trans ht.2⟩) (norm_nonneg _))
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le
    (hJ.continuous.mono (Icc_subset_Icc_right ht.2))
    (fun s hs => hJ.derivative_right ⟨hs.1,hs.2.trans_le ht.2⟩)
    (show ‖J 0‖ ≤ 1 by rw [hJ.initial]; exact ContinuousLinearMap.norm_id_le) hb t ⟨ht.1,le_rfl⟩
  simpa only [gronwallBound_ε0,sub_zero,one_mul] using hg

end SharpWasserstein.FlowInitialDerivative
