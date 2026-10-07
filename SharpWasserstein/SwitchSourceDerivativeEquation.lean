module

public import SharpWasserstein.Compat
public import SharpWasserstein.SwitchSourceDerivativeRight

@[expose] public section

/-! The actual switch source is continuous in time. The derived right
derivative therefore gives the full integrated source identity and the
ordinary derivative at every interior switch time. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal ContDiff Interval
namespace SharpWasserstein.SwitchSourceDerivative
open NoiseAverage
variable {d N : ℕ} {b : Configuration d N → Configuration d N} {A H : ℝ≥0}
  (hb : ∀ x, ‖b x‖ ≤ A) (hLip : LipschitzWith H b)
  {v : ℝ → Configuration d N → Configuration d N} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hbv : ∀ r x, ‖v r x‖ ≤ M)
  (hlv : ∀ r, LipschitzWith K (v r))
  {T : ℝ} (hT : 0 ≤ T)
  (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
  {F : Configuration d N → ℝ} (hF : ContDiff ℝ 1 F)
  {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L)

include hbs hB hF hC hL in
/-- Actual continuity of the propagated drift-difference pairing, including
variation of the reference law and the remaining transition time. -/
theorem sourcePairing_continuousOn :
    ContinuousOn (sourcePairing hb hLip hv hbv hlv hT μ F) (Ici 0) := by
  apply BrownianFlow.globalLaw_boundedExpectation_continuous hv hbv hlv μ
  · exact (remainingTest_fderiv_joint_continuous hb hLip hT
      (BrownianNoise.configurationLaw d N T) hbs hB hF hC hL T).clm_apply
        (hv.sub (hLip.continuous.comp continuous_snd))
  · intro s x
    change ‖fderiv ℝ (remainingTest hb hLip hT
      (BrownianNoise.configurationLaw d N T) F T s) x (v s x-b x)‖ ≤ _
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (remainingTest_fderiv_norm_le hb hLip hT
        (BrownianNoise.configurationLaw d N T) hbs hB hF hC hL T s x)
        ((norm_sub_le _ _).trans (add_le_add (hbv s x) (hb x)))
          (norm_nonneg _) (by positivity))

include hT hF hC in
/-- Actual switch expectation continuity, derived directly from its remaining
transition representation and the reference law's continuous path construction. -/
theorem switch_integral_continuousOn :
    ContinuousOn (fun s => ∫ x,F x ∂switchLaw hb hLip hv hbv hlv (T := T) μ s) (Icc 0 T) := by
  have hc := BrownianFlow.globalLaw_boundedExpectation_continuousOn_Icc hv hbv hlv μ
    (g := remainingTest hb hLip hT (BrownianNoise.configurationLaw d N T) F T)
    (remainingTest_continuous hb hLip hT (BrownianNoise.configurationLaw d N T) hF hC T)
    (fun s x => by simpa only [Real.norm_eq_abs] using
      remainingTest_norm_le hb hLip hT (BrownianNoise.configurationLaw d N T) hC T s x) hT
  apply hc.congr
  intro s hs
  letI := BrownianFlow.globalLaw_probability hv hbv hlv μ hs.1
  exact (integral_remainingTest_eq hb hLip hT hF.continuous hC
    (BrownianFlow.globalLaw hv hbv hlv μ s) ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩).symm

include hbs hB hF hC hL

/-- The actual switch law satisfies the homogeneous propagated-source
identity against every bounded C¹ test with bounded first differential. -/
theorem switch_integral_sub_eq_integral {s t : ℝ} (hs : s ∈ Icc 0 T)
    (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    (∫ x,F x ∂switchLaw hb hLip hv hbv hlv (T := T) μ t)-
      (∫ x,F x ∂switchLaw hb hLip hv hbv hlv (T := T) μ s) =
      ∫ r in s..t,sourcePairing hb hLip hv hbv hlv hT μ F r := by
  have hc := switch_integral_continuousOn hb hLip hv hbv hlv hT μ hF hC
  have hG := sourcePairing_continuousOn hb hLip hv hbv hlv hT hbs hB μ hF hC hL
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hst
    (hc.mono (Icc_subset_Icc hs.1 ht.2))
  · intro r hr
    exact (switch_integral_hasDerivWithinAt_right hb hLip hv hbv hlv hT hbs hB μ hF hC hL
      ⟨hs.1.trans hr.1.le,hr.2.trans_le ht.2⟩).mono Ioi_subset_Ici_self
  · exact (hG.mono (fun r hr => hs.1.trans hr.1)).intervalIntegrable_of_Icc hst

/-- Full ordinary switch derivative at every interior time. This is obtained
from the derived integrated identity, not from an assumed backward equation. -/
theorem switch_integral_hasDerivAt {s : ℝ} (hs : s ∈ Ioo 0 T) :
    HasDerivAt
      (fun r => ∫ x,F x ∂switchLaw hb hLip hv hbv hlv (T := T) μ r)
      (sourcePairing hb hLip hv hbv hlv hT μ F s) s := by
  let G := sourcePairing hb hLip hv hbv hlv hT μ F
  have hGc : ContinuousOn G (Ici 0) :=
    sourcePairing_continuousOn hb hLip hv hbv hlv hT hbs hB μ hF hC hL
  have hGi : IntervalIntegrable G volume 0 s :=
    (hGc.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hs.1.le
  have hGa : ContinuousAt G s := (hGc s hs.1.le).continuousAt (Ici_mem_nhds hs.1)
  have hd := (intervalIntegral.integral_hasDerivAt_right hGi
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi (hGc.mono Ioi_subset_Ici_self) s hs.1) hGa).const_add
      (∫ x,F x ∂switchLaw hb hLip hv hbv hlv (T := T) μ 0)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hs.1 hs.2] with r hr
  have he := switch_integral_sub_eq_integral hb hLip hv hbv hlv hT hbs hB μ hF hC hL
    (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩) hr hr.1
  dsimp only [G] at *
  linarith

end SharpWasserstein.SwitchSourceDerivative
