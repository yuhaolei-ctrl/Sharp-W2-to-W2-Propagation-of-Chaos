import SharpWasserstein.FlowJacobianDriftVariation

/-! Quantitative stability of the genuine variational equations under an
integrated coefficient error. This requires no uniform derivative convergence. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology Interval
namespace SharpWasserstein.FlowJacobianDrift
open FlowInitialDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Integration of an actual variational ODE. -/
theorem variation_integral_eq {A J : ℝ → E →L[ℝ] E} {T : ℝ}
    (hA : Continuous A) (hJ : LinearVariation A T J) {t : ℝ} (ht : t ∈ Icc 0 T) :
    J t = ContinuousLinearMap.id ℝ E + ∫ s in (0:ℝ)..t,(A s).comp (J s) := by
  have hs : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hc := hA.continuousOn.clm_comp hJ.continuous
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hJ.continuous.mono hs)
    (fun s hst => (hJ.derivative s (hs ⟨hst.1.le,hst.2.le⟩)).hasDerivAt
      (Icc_mem_nhds hst.1 (hst.2.trans_le ht.2)))
    ((hc.mono hs).intervalIntegrable_of_Icc ht.1)
  rw [hJ.initial] at he
  rw [he]
  abel

/-- A coefficient error integrated in time controls the actual Jacobian error.
The coefficient is dimension free and uses the full operator norm. -/
theorem variation_difference_le_integral {A B J H : ℝ → E →L[ℝ] E}
    {K : ℝ≥0} {T : ℝ} (hT : 0 ≤ T)
    (hAc : Continuous A) (hBc : Continuous B)
    (hJ : LinearVariation A T J) (hH : LinearVariation B T H)
    (hA : ∀ s ∈ Icc 0 T, ‖A s‖ ≤ K) (hB : ∀ s ∈ Icc 0 T, ‖B s‖ ≤ K)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖J t-H t‖ ≤ ((∫ s in (0:ℝ)..T,‖B s-A s‖)*Real.exp ((K:ℝ)*T))*Real.exp ((K:ℝ)*t) := by
  let F : ℝ → E →L[ℝ] E := fun s => (B s-A s).comp (H s)
  let U : ℝ → E →L[ℝ] E := fun s => ∫ r in (0:ℝ)..s,F r
  let D : ℝ := (∫ s in (0:ℝ)..T,‖B s-A s‖)*Real.exp ((K:ℝ)*T)
  have hFc : ContinuousOn F (Icc 0 T) := (hBc.sub hAc).continuousOn.clm_comp hH.continuous
  have hFi (s : ℝ) (hs : s ∈ Icc 0 T) : IntervalIntegrable F volume 0 s :=
    (hFc.mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1
  have hUc : ContinuousOn U (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using
      (intervalIntegral.continuousOn_primitive_interval' (hFi T ⟨hT,le_rfl⟩) left_mem_uIcc)
  have hUn (s : ℝ) (hs : s ∈ Icc 0 T) : ‖U s‖ ≤ D := by
    calc
      _ ≤ ∫ r in (0:ℝ)..s,‖F r‖ := intervalIntegral.norm_integral_le_integral_norm hs.1
      _ ≤ ∫ r in (0:ℝ)..s,‖B r-A r‖*Real.exp ((K:ℝ)*T) := by
        apply intervalIntegral.integral_mono_on hs.1 (hFi s hs).norm
          (((hBc.sub hAc).norm.mul continuous_const).intervalIntegrable 0 s)
        intro r hr
        have hrT := (Icc_subset_Icc_right hs.2) hr
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left ((hH.norm_le_exp hB hrT).trans
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrT.2 K.coe_nonneg))) (norm_nonneg _))
      _ = (∫ r in (0:ℝ)..s,‖B r-A r‖)*Real.exp ((K:ℝ)*T) := by rw [intervalIntegral.integral_mul_const]
      _ ≤ D := mul_le_mul_of_nonneg_right
        (intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
          (Eventually.of_forall (fun _ => norm_nonneg _)) ((hBc.sub hAc).norm.intervalIntegrable 0 T))
        (Real.exp_pos _).le
  have hJtr : FiniteAdditiveTrajectory (fun s L => (A s).comp L) (fun _ => 0)
      (ContinuousLinearMap.id ℝ E) T J := by
    refine ⟨hJ.continuous,hAc.continuousOn.clm_comp hJ.continuous,?_⟩
    intro s hs
    simpa only [add_zero] using variation_integral_eq hAc hJ hs
  have hHtr : FiniteAdditiveTrajectory (fun s L => (A s).comp L) U
      (ContinuousLinearMap.id ℝ E) T H := by
    refine ⟨hH.continuous,hAc.continuousOn.clm_comp hH.continuous,?_⟩
    intro s hs
    have hi : (∫ r in (0:ℝ)..s,(A r).comp (H r)) + U s =
        ∫ r in (0:ℝ)..s,(B r).comp (H r) := by
      dsimp only [U]
      rw [← intervalIntegral.integral_add
        (((hAc.continuousOn.clm_comp hH.continuous).mono
          (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1) (hFi s hs)]
      apply intervalIntegral.integral_congr
      intro r _
      dsimp only [F]
      rw [ContinuousLinearMap.sub_comp]
      abel
    rw [add_assoc,hi]
    exact variation_integral_eq hBc hH hs
  have hLip : ∀ s ∈ Icc 0 T, LipschitzWith K (fun L : E →L[ℝ] E => (A s).comp L) := by
    intro s hs
    apply LipschitzWith.of_dist_le_mul
    intro V W
    rw [dist_eq_norm,dist_eq_norm,← ContinuousLinearMap.comp_sub]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hA s hs) (norm_nonneg _))
  have hh := hJtr.forcing_stability hLip continuousOn_const hUc
    (fun s hs => by simpa only [zero_sub,norm_neg] using hUn s hs) hHtr ht
  simpa only [sub_self,norm_zero,zero_add] using hh

end SharpWasserstein.FlowJacobianDrift
